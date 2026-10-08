(*! Step 1 of the variable scheduler: the DFG builder.  A state monad over
    [dfg_state_t] walks an action's [tf_ops], emitting one node per operation
    and sharing one node per variable read. !*)

Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.
Require Koika.BitsToLists.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Trustformer.Utils.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Export Trustformer.DFG.
Require Import Trustformer.Contract.

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.Program.Wf.

Import ListNotations.

Section Build.

  Context (ctx: TFSchedContext).

  Local Notation states_var := (tfs_spec_states ctx).
  Local Notation states_var_eq_dec := (tfs_spec_states_eq_dec ctx).
  Local Notation states_var_size := (tfs_spec_states_size ctx).

  Local Notation inputs_var := (tfs_spec_inputs ctx).
  Local Notation inputs_var_size := (tfs_spec_inputs_size ctx).

  Local Notation outputs_var := (tfs_spec_outputs ctx).
  Local Notation outputs_var_eq_dec := (tfs_spec_outputs_eq_dec ctx).
  Local Notation outputs_var_size := (tfs_spec_outputs_size ctx).

  Local Notation ips_var := (tfs_spec_ips ctx).
  Local Notation ips_var_eq_dec := (tfs_spec_ips_eq_dec ctx).
  Local Notation ip_of := (tfs_spec_ip ctx).

  Local Notation spec_action := (tfs_spec_action ctx).
  Local Notation spec_action_fin := (tfs_spec_action_fin ctx).
  Local Notation spec_action_ops := (tfs_spec_action_ops ctx).

  
  (* ============================ *)
  (* = Step 1: DFG Construction = *)
  (* ============================ *)

  (* --- DFG Definitions --- *)
  Local Notation dfg_vars := (@dfg_vars_t states_var outputs_var).
  Local Notation dfg_op := (@dfg_op_t states_var inputs_var outputs_var ips_var).
  Local Notation dfg_node := (@dfg_node_t states_var inputs_var outputs_var ips_var).
  Local Notation dfg_state := (@dfg_state_t states_var inputs_var outputs_var ips_var). 

  Instance dfg_vars_eq_dec : EqDec dfg_vars.
  Proof.
    constructor. intros.
    decide equality.
    apply states_var_eq_dec.
    apply outputs_var_eq_dec.
  Defined.

  Definition dfg_var_size (v: dfg_vars) : nat :=
    match v with
    | DFG_SVar sv => states_var_size sv
    | DFG_OVar ov => outputs_var_size ov
    end.

  (* --- State Monad --- *)

  Definition M (A : Type) := dfg_state -> (A * dfg_state).
  Definition ret {A : Type} (x : A) : M A := fun s => (x, s).
  Definition bind {A B : Type} (m : M A) (f : A -> M B) : M B :=
    fun s => let (x, s') := m s in f x s'.
  Notation "'let!' x ':=' m 'in' k" := (bind m (fun x => k)) (at level 60, right associativity).

  Definition get_state : M dfg_state := fun s => (s, s).
  Definition put_state (s : dfg_state) : M unit := fun _ => (tt, s).

  (* --- Helpers --- *)

  Definition emit (op : dfg_op) (sz: sz_t) : M nid_t :=
    let! s := get_state in
    let next_id := length (graph s) in
    let new_node := {| nid := next_id; op := op; sz := sz |} in
    let! _ := put_state ({| graph := new_node :: graph s; var_map := var_map s |}) in
    ret next_id.

  (* The most recent [DFG_Sample] on [v] in PROGRAM ORDER; [graph] is
     latest-first, so [find] returns it.  One IP has one set of request wires,
     so two calls that can both fire take turns on this edge. *)
  Definition guards_disjoint (g1 g2: list (nid_t * bool)) : bool :=
    existsb (fun l1 => existsb (fun l2 =>
               andb (Nat.eqb (fst l1) (fst l2))
                    (negb (Bool.eqb (snd l1) (snd l2)))) g2) g1.

  Definition last_sample (dfg: dfg_state) (p: ips_var)
    (en: list (nid_t * bool)) : option nid_t :=
    match find (fun nd => match op nd with
                          | DFG_Sample p' _ en' =>
                              if ips_var_eq_dec.(eq_dec) p' p
                              then negb (guards_disjoint en en') else false
                          | _ => false
                          end) (graph dfg) with
    | Some nd => Some (nid nd)
    | None => None
    end.

  (* Every call on [p] this one must wait for: the most recent non-disjoint
     sample, plus one per arm mutually exclusive with it.  Waiting on only the
     most recent lets an untaken arm wave this call through (sim/tb_arms.sv). *)
  Definition pending_samples (dfg: dfg_state) (p: ips_var)
    (en: list (nid_t * bool)) : list nid_t :=
    map fst
      (fold_left (fun acc nd =>
         match op nd with
         | DFG_Sample p' _ en' =>
             if ips_var_eq_dec.(eq_dec) p' p then
               if guards_disjoint en en' then acc
               else if forallb (fun q => guards_disjoint (snd q) en') acc
                    then acc ++ [(nid nd, en')]
                    else acc
             else acc
         | _ => acc
         end) (graph dfg) []).

  (* DEFERRED: where the branch condition is not critical this could select the
     TAKEN arm, as a non-critical phi does, instead of conjoining both.  Sound
     either way; worth nothing in any design here, so it is not done. *)
  Fixpoint join_pendings (prevs: list nid_t) : M (option nid_t) :=
    match prevs with
    | [] => ret None
    | q :: rest =>
        let! r := join_pendings rest in
        match r with
        | None => ret (Some q)
        | Some h => let! j := emit (DFG_Join q h) 1 in ret (Some j)
        end
    end.

  (* wide enough to count 0 .. n-1 *)
  Definition counter_sz (n: nat) : nat := S (Nat.log2 n).

  (* The wait: ONE node, whose buffer counts -- see [compile_dfg_buffers]. *)
  Definition stall_chain (n: nat) (id: nid_t) : M nid_t :=
    match n with
    | 0 => ret id
    | _ => emit (DFG_Stall n id) (counter_sz n)
    end.

  (* --- Variable & Output Management --- *)

  Definition ensure_var (dfg_v: dfg_vars) : M nid_t :=
    let! id := emit (DFG_Var dfg_v) (dfg_var_size dfg_v) in
    let! s' := get_state in
    let new_map := (dfg_v, id) :: filter (fun '(k, _) => if (eq_dec k dfg_v) then false else true) (var_map s') in
    let! _ := put_state ({| graph := graph s'; var_map := new_map |}) in
    ret id.

  (* Reads are shared on the GRAPH: a [DFG_Var v] is the register's value at
     action start, so every branch sees the same node.  The taint and
     declassification analyses are node-id based and rely on that sharing. *)
  Definition read_var (dfg_v : dfg_vars) : M nid_t :=
    let! s := get_state in
    match find (fun nd =>
                  match op nd with
                  | DFG_Var v' =>
                      andb (andb (if eq_dec v' dfg_v then true else false)
                                 (Nat.eqb (sz nd) (dfg_var_size dfg_v)))
                           (Nat.ltb 0 (nid nd))
                  | _ => false
                  end) (graph s) with
    | Some nd => ret (nid nd)
    | None => emit (DFG_Var dfg_v) (dfg_var_size dfg_v)
    end.

  (* [var_map] holds the variables the action ASSIGNS, so reads stay out of it
     and [merge_key] keeps its symmetric case at a branch end.  An assignment
     wins over the read cache, hence the [var_map] lookup first. *)
  Definition get_var (dfg_v : dfg_vars) : M nid_t :=
    let! s := get_state in
      match BitsToLists.list_assoc (var_map s) dfg_v with
      | Some id => ret id
      | None => read_var dfg_v
      end.

  Definition set_var (dfg_v : dfg_vars) (id : nid_t) : M unit :=
    let! s := get_state in
    let new_map := (dfg_v, id) :: filter (fun '(k, _) => if (eq_dec k dfg_v) then false else true) (var_map s) in
    put_state ({| graph := graph s; var_map := new_map |}).

  (* --- Expression Compiler --- *)

  Fixpoint dataflow_expr (e : tf_expr) (sz: sz_t) : M nid_t :=
    match e with
    | tf_const val => emit (DFG_Const val) sz
    | tf_svar v => 
      let! src_id := get_var (DFG_SVar v) in
      if Nat.eqb (dfg_var_size (DFG_SVar v)) sz then
        ret src_id
      else
        emit (DFG_Resize src_id) sz
    | tf_ivar v => 
      let! src_id := emit (DFG_Input v) sz in
      if Nat.eqb (inputs_var_size v) sz then
        ret src_id
      else
        emit (DFG_Resize src_id) sz
    | tf_ovar v => 
      let! src_id := get_var (DFG_OVar v) in
      if Nat.eqb (dfg_var_size (DFG_OVar v)) sz then
        ret src_id
      else
        emit (DFG_Resize src_id) sz
    | tf_op1 op src =>
      match op with
      | tf_not =>
        let! src_id := dataflow_expr src sz in
        emit (DFG_Unary op src_id) sz
      | tf_resize source_size =>
        let! src_id := dataflow_expr src source_size in
        emit (DFG_Unary op src_id) sz
      | tf_slice source_size _ =>
        let! src_id := dataflow_expr src source_size in
        emit (DFG_Unary op src_id) sz
      end
    | tf_op2 op src1 src2 =>
      match op with
      | tf_cmp szC _ =>
        let! id1 := dataflow_expr src1 szC in
        let! id2 := dataflow_expr src2 szC in
        emit (DFG_Binary op id1 id2) sz
      (* SPIKE: the only binary op whose two operands have DIFFERENT declared
         widths, which is why the uniform tactic in [dataflow_expr_fg] has to
         gain a case rather than absorbing this one. *)
      | tf_concat hz lz =>
        let! id1 := dataflow_expr src1 hz in
        let! id2 := dataflow_expr src2 lz in
        emit (DFG_Binary op id1 id2) sz
      | tf_islice s =>
        let! id1 := dataflow_expr src1 s in
        let! id2 := dataflow_expr src2 (Nat.log2_up s) in
        emit (DFG_Binary op id1 id2) sz
      | _ =>
        let! id1 := dataflow_expr src1 sz in
        let! id2 := dataflow_expr src2 sz in
        emit (DFG_Binary op id1 id2) sz
      end
    | tf_expr_if cond then_expr else_expr =>
      let! cond_id := dataflow_expr cond 1 in
      let! then_id := dataflow_expr then_expr sz in
      let! else_id := dataflow_expr else_expr sz in
      emit (DFG_Phi cond_id then_id else_id) sz
    end.

  (* --- Generic Map Merger --- *)
  
  Definition merge_key 
    (cond_id : nid_t) 
    (k : dfg_vars) 
    (val_t_opt val_e_opt : option nid_t) 
    : M (option nid_t) :=
    match val_t_opt, val_e_opt with
    | Some vt, Some ve =>
        if eq_dec vt ve then
          ret (Some vt)
        else 
          let! phi := emit (DFG_Phi cond_id vt ve) (dfg_var_size k) in
          ret (Some phi)
    | Some vt, None => 
        let! ve := ensure_var k in
        let! phi := emit (DFG_Phi cond_id vt ve) (dfg_var_size k) in
        ret (Some phi)
    | None, Some ve =>
        let! vt := ensure_var k in
        let! phi := emit (DFG_Phi cond_id vt ve) (dfg_var_size k) in
        ret (Some phi)
    | None, None => ret None
    end.

  Fixpoint merge_loop 
    (cond_id : nid_t)
    (map_then map_else : list (dfg_vars * nid_t)) 
    (keys : list (dfg_vars * nid_t)) 
    (acc : list (dfg_vars * nid_t)) 
    : M (list (dfg_vars * nid_t)) :=
    match keys with
    | [] => ret acc
    | (k, _) :: rest =>
        match BitsToLists.list_assoc acc k with
        | Some _ => merge_loop cond_id map_then map_else rest acc
        | None => 
            let val_t := BitsToLists.list_assoc map_then k in
            let val_e := BitsToLists.list_assoc map_else k in
            
            let! res_opt := merge_key cond_id k val_t val_e in
            
            match res_opt with
            | Some final_id => merge_loop cond_id map_then map_else rest ((k, final_id) :: acc)
            | None => merge_loop cond_id map_then map_else rest acc
            end
        end
    end.

  Definition merge_maps 
    (cond_id : nid_t) 
    (map_orig map_then map_else : list (dfg_vars * nid_t)) 
    : M (list (dfg_vars * nid_t)) :=
    
    merge_loop cond_id map_then map_else (map_then ++ map_else) [].

  (* --- Operations Compiler --- *)

  (* [en] is the path condition every drive in [ops] fires under: a conjunction
     of branch literals, [] at the top of an action.  Only a DRIVE needs it --
     an assignment is made conditional by the phi that [merge_maps] builds. *)
  Fixpoint dataflow_ops (en : list (nid_t * bool)) (ops : tf_ops) : M unit :=
    match ops with
    | tf_ops_base op =>
      match op with
      | tf_nop => ret tt
      | tf_assign dst expr =>
        let! res_id := dataflow_expr expr (dfg_var_size (DFG_SVar dst)) in
        set_var (DFG_SVar dst) res_id
      | tf_output dst expr =>
        let! res_id := dataflow_expr expr (dfg_var_size (DFG_OVar dst)) in
        set_var (DFG_OVar dst) res_id
      (* THE ROUND TRIP, as a graph: arg -> drive -> stall<lat> -> sample.  A
         drive is an always-op ([compile_dfg_drives]), so the request is on the
         wire DURING the action and [lat] runs from the cycle it is driven. *)
      | tf_call ip dst arg =>
        let! s0 := get_state in
        let! arg_id := dataflow_expr arg (ip_req_sz (ip_of ip)) in
        (* SEQUENCING: the pending calls on this IP are conjoined FIRST, so the
           drive still has its ordering join at [S drive_id], and that join
           waits for every response that could still be outstanding. *)
        let! prev_opt := join_pendings (pending_samples s0 ip en) in
        let! drive_id := emit (DFG_Drive ip arg_id en) (ip_req_sz (ip_of ip)) in
        let! head := match prev_opt with
                     | None => ret drive_id
                     | Some prev => emit (DFG_Join drive_id prev) 1
                     end in
        let! stall_id := stall_chain (ip_lat (ip_of ip)) head in
        let! samp_id := emit (DFG_Sample ip stall_id en) (dfg_var_size (DFG_SVar dst)) in
        set_var (DFG_SVar dst) samp_id
      end
    | tf_ops_cons op1 op2 =>
      let! _ := dataflow_ops en op1 in
      dataflow_ops en op2
    | tf_ops_if cond then_ops else_ops =>
      let! cond_id := dataflow_expr cond 1 in
      
      let! s_orig := get_state in
      
      (* Then Branch *)
      let! _ := dataflow_ops ((cond_id, true) :: en) then_ops in
      let! s_then := get_state in
      
      (* Restore maps *)
      let! _ := put_state ({| 
        graph := graph s_then; 
        var_map := var_map s_orig
      |}) in
      
      (* Else Branch *)
      let! _ := dataflow_ops ((cond_id, false) :: en) else_ops in
      let! s_else := get_state in
      
      (* Merge Maps *)
      let! final_vars := merge_maps cond_id 
        (var_map s_orig) (var_map s_then) (var_map s_else) in
    
      (* Update final state *)
      let! s := get_state in
      put_state ({| 
        graph := graph s; 
        var_map := final_vars
      |})
    end.

  (* --- Entry Point --- *)

  Definition build_dfg (action : spec_action) : dfg_state :=
    let ops := spec_action_ops action in
    let empty_state := {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |} in
    let (_, final_state) := dataflow_ops [] ops empty_state in
    {| graph := rev (graph final_state); var_map := var_map final_state |}.

  Definition get_args (node: dfg_node) : list nid_t :=
    match op node with
    | DFG_Const _ => []
    | DFG_Input _ => []
    | DFG_Var _ => []
    | DFG_Unary _ arg => [arg]
    | DFG_Binary _ arg1 arg2 => [arg1; arg2]
    | DFG_Resize arg => [arg]
    | DFG_Phi cond then_id else_id => [cond; then_id; else_id]
    | DFG_Stall _ arg => [arg]
    | DFG_Drive _ arg en => arg :: map fst en
    | DFG_Sample _ tok _ => [tok]
    | DFG_Join a b => [a; b]
    | DFG_Empty => []
    end.
End Build.
