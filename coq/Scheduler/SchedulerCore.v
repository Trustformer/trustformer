Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.
Require Koika.BitsToLists.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Trustformer.Utils.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Export Trustformer.Scheduler.DFG.
Require Import Trustformer.Scheduler.Contract.
Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.Program.Wf.

Import ListNotations.


(* Steps 1-6 of the variable scheduler: DFG construction, cost, target cycles,
   buffer allocation, taint and declassification, and the TF lowering.
   VariableScheduler.v proves the record obligations on top of these. *)

Section SchedulerCore.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation states_var := (tfs_spec_states ctx).
  Local Notation states_var_eq_dec := (tfs_spec_states_eq_dec ctx).
  Local Notation states_var_fin := (tfs_spec_states_fin ctx).
  Local Notation states_var_names := (tfs_spec_states_names ctx).
  Local Notation states_var_size := (tfs_spec_states_size ctx).
  Local Notation states_var_init := (tfs_spec_states_init ctx).

  Local Notation inputs_var := (tfs_spec_inputs ctx).
  Local Notation inputs_var_eq_dec := (tfs_spec_inputs_eq_dec ctx).
  Local Notation inputs_var_fin := (tfs_spec_inputs_fin ctx).
  Local Notation inputs_var_size := (tfs_spec_inputs_size ctx).
  Local Notation inputs_var_class := (tfs_spec_inputs_class ctx).

  Local Notation outputs_var := (tfs_spec_outputs ctx).
  Local Notation outputs_var_eq_dec := (tfs_spec_outputs_eq_dec ctx).
  Local Notation outputs_var_fin := (tfs_spec_outputs_fin ctx).
  Local Notation outputs_var_size := (tfs_spec_outputs_size ctx).
  Local Notation outputs_var_class := (tfs_spec_outputs_class ctx).

  Local Notation ips_var := (tfs_spec_ips ctx).
  Local Notation ips_var_eq_dec := (tfs_spec_ips_eq_dec ctx).
  Local Notation ips_var_fin := (tfs_spec_ips_fin ctx).
  Local Notation ip_of := (tfs_spec_ip ctx).

  Local Notation spec_action := (tfs_spec_action ctx).
  Local Notation spec_action_eq_dec := (tfs_spec_action_eq_dec ctx).
  Local Notation spec_action_fin := (tfs_spec_action_fin ctx).
  Local Notation spec_action_ops := (tfs_spec_action_ops ctx).
  Local Notation spec_all_actions := (@finite_elements spec_action spec_action_fin).
  Local Notation spec_action_index := (@finite_index spec_action spec_action_fin).

  Hint Extern 0 (FiniteType states_var) => exact (tfs_spec_states_fin ctx) : typeclass_instances.
  
  Hint Extern 0 (Show states_var) => exact (tfs_spec_states_names ctx) : typeclass_instances.
  Hint Extern 0 (Show inputs_var) => exact (tfs_spec_inputs_names ctx) : typeclass_instances.
  Hint Extern 0 (Show outputs_var) => exact (tfs_spec_outputs_names ctx) : typeclass_instances.
  Hint Extern 0 (Show ips_var) => exact (tfs_spec_ips_names ctx) : typeclass_instances.

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
        let! drive_id := emit (DFG_Drive ip arg_id en) (ip_req_sz (ip_of ip)) in
        (* SEQUENCING: an earlier call on this IP puts a JOIN of this drive and
           that call's sample under the stall.  A [DFG_Binary]'s validity is the
           AND of its arguments, so the join waits for the previous response. *)
        let! head := match last_sample s0 ip en with
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

  (* ============================ *)
  (* = Step 2: Cost Calculation = *)
  (* ============================ *)

  Definition cost_t := nat.

  Definition cost_fn (d: dfg_op) (sz: nat) : cost_t :=
    match d with
    | DFG_Const _ => 0
    | DFG_Input _ => 0
    | DFG_Var _ => 0
    | DFG_Unary op _ => match op with
                        | tf_not => 1
                        | tf_resize _ => 0
                      end
    | DFG_Binary op _ _ => match op with
                        | tf_and => 1
                        | tf_or => 1
                        | tf_xor => 1
                        | tf_add => 2
                        | tf_sub => 2
                        | tf_mul => 5
                        | tf_cmp _ _ => 1
                        (* SPIKE: concatenation is pure wiring. *)
                        | tf_concat _ _ => 0
                        end
    | DFG_Resize _ => 0
    | DFG_Phi _ _ _ => 1
    (* SPIKE: a stall is a register, not combinational logic.  The real W-b
       design needs a separate [must_buffer] predicate rather than an inflated
       cost -- see the archive's DEBT-2. *)
    (* [ip_lat] is in CYCLES, so scale by [cost_limit]: a whole multiple shifts
       [calc_target_cycle]'s quotient by exactly that many cycles, whatever the
       remainder.  Regressions: StallLatencySpike [sep_pad_r0..r5], [sep_lat_0..6]. *)
    | DFG_Stall lat _ => lat * cost_limit
    (* SPIKE 2b: a drive and a sample are wiring, not logic. *)
    | DFG_Drive _ _ _ => 0
    | DFG_Sample _ _ _ => 0
    (* Same as the [DFG_Binary tf_or] it replaces, so the schedule is unmoved:
       its validity is a real AND gate even though it carries no value. *)
    | DFG_Join _ _ => 1
    | DFG_Empty => 0
    end.

  Definition list_assoc_set_all_max {K: Type} {eq: EqDec K} (l: list (K * nat)) (k: list K) (v: nat)
    : list (K * nat) :=
    fold_left (fun acc key => 
      if Nat.leb (match BitsToLists.list_assoc acc key with
              | Some existing => existing
              | None => 0
              end) v then
        BitsToLists.list_assoc_set acc key v
      else
        acc
    ) k l.

  Definition calc_backward_cost (dfg : dfg_state) : list (nid_t * cost_t) :=
    let aux (cost_map: list (nid_t * cost_t)) (node : dfg_node) : list (nid_t * cost_t) :=
      let cost := match BitsToLists.list_assoc cost_map (nid node) with
                  | Some c => c
                  | None => 0
                  end in
      list_assoc_set_all_max cost_map ((nid node) :: get_args node) (cost + cost_fn (op node) (sz node))
    in
    fold_left aux (List.rev (graph dfg)) [].

  (* Steps 3-6 stay simple: performant HLS is out of scope here. *)

  (* ============================== *)
  (* = Step 3: Distance Splitting = *)
  (* ============================== *)

  Definition cycle_t := nat.

  Definition calc_target_cycle (cost_map: list (nid_t * cost_t)) : list (nid_t * cycle_t) :=
    map (fun '(nid, c) => (nid, c / cost_limit)) cost_map.

  (* Definition calc_max_cycle (cost_map: list (nid_t * cycle_t)) : cycle_t :=
    fold_left (fun amax '(_, c) => Nat.max amax c) cost_map 0. *)

  (* ============================== *)
  (* = Step 4: Buffer Allocation  = *)
  (* ============================== *)

  (* A source op holds one value for the whole action -- constants are literals,
     inputs are latched at action start, state is written at done -- so it is
     re-read in any later stage and stays buffer-free. *)
  Definition source_op (o : dfg_op) : bool :=
    match o with
    | DFG_Const _ | DFG_Input _ | DFG_Var _ => true
    | _ => false
    end.

  Definition is_source (dfg : dfg_state) (n : nid_t) : bool :=
    source_op (op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0; |})).

  (* A sample reads a LIVE wire and a later call on the same port moves it, so
     its answer is latched whatever the schedule does with it.  Leaving that to
     the cycle-crossing test reads the wire again in a later cycle. *)
  Definition sample_nodes (dfg: dfg_state) : list nid_t :=
    map nid (filter (fun nd => match op nd with
                               | DFG_Sample _ _ _ => true
                               | _ => false
                               end) (graph dfg)).

  Definition require_buffer (dfg : dfg_state) (cycle_costs : list (nid_t * cycle_t)) : list (nid_t) :=
    let aux (cost_map: list (nid_t)) (node : dfg_node) : list (nid_t) :=
      let n_cycle := match BitsToLists.list_assoc cycle_costs (nid node) with
                      | Some c => c
                      | None => 0 (* should not happen *)
                      end in
      filter (fun x => if is_source dfg x then false else
                      match BitsToLists.list_assoc cycle_costs x with
                      | Some c => negb (Nat.eqb c n_cycle)
                      | None => false (* should not happen *)
                      end ) (get_args node) ++ cost_map
    in
    nodup Nat.eq_dec (fold_left aux (graph dfg) []
                        ++ filter (fun x => if is_source dfg x then false else
                                          match BitsToLists.list_assoc cycle_costs x with
                                          | Some 0 => false
                                          | _ => true
                                          end ) (map snd (var_map dfg))
                        ++ sample_nodes dfg).

  Definition get_sizes_and_idx (dfg : dfg_state) (nodes: list nid_t) : list (nid_t * (nat * sz_t)) :=
    rev (fst (
      fold_left (fun '(acc, idx) nid =>
        let node := nth nid (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0; |} in
        ((nid, (idx, sz node)) :: acc, S idx)
      ) nodes ([], 0))).

  Definition buffer_needs 
    :=
    (* Determine the DFG of each operation *)
    let dfgs := map build_dfg spec_all_actions in
    (* Calculate the cost maps for each DFG *)
    let cost_maps := map calc_backward_cost dfgs in
    (* Calculate the target cycles for each node *)
    let cycle_maps := map calc_target_cycle cost_maps in
    (* Determine the required buffers across all actions *)
    let buffers := map (fun '(dfg, cycle_map) => get_sizes_and_idx dfg (require_buffer dfg cycle_map)) (combine dfgs cycle_maps) in
    
    buffers.

  (* The buffer table, computed ONCE by [tfs_schedule] and passed to everything below. *)
  Context (bn : list (list (nid_t * (nat * sz_t)))).

  Local Notation tf_dfg_states := (tf_dfg_states_t (states_var:=states_var) (ips_var:=ips_var) (buffer_needs:=bn)).
  Definition test := tf_dfg_states.

  Instance show_tf_dfg_states : Show tf_dfg_states :=
    { show := fun dfg_s =>
        match dfg_s with
        | tf_dfg_s s => String.append "s_" (show s)
        | tf_dfg_b a_idx n_idx => String.append "b_" (String.append (show (index_to_nat a_idx)) (String.append "_" (show (index_to_nat n_idx))))
        | tf_dfg_v a_idx n_idx => String.append "v_" (String.append (show (index_to_nat a_idx)) (String.append "_" (show (index_to_nat n_idx))))
        | tf_dfg_done => "done"
        | tf_dfg_ov p => String.append "ip_" (show p)
        end }.

  Definition tf_dfg_states_size (dfg_s: tf_dfg_states) : sz_t :=
    match dfg_s with
    | tf_dfg_s s => states_var_size s
    | tf_dfg_b a_idx b_idx => snd (snd (nth (index_to_nat b_idx) (nth (index_to_nat a_idx) bn []) (0, (0, 0))))
    | tf_dfg_v a_idx b_idx => 1
    | tf_dfg_done => 1
    | tf_dfg_ov p => 1 + ip_req_sz (ip_of p)
    end.

  (* ============================== *)
  (* = Step 5: Taint Analysis     = *)
  (* ============================== *)

  (* Declassification sites: the roots of assignments to destinations the
     attacker observes, so [DFG_OVar] filtered on the DECLARED class and
     [DFG_SVar] excluded.  GENERAL_REQUIREMENTS.md 1.1, REVIEW.md 2.3. *)
  Definition public_dsts (dfg: dfg_state) : list (nid_t) :=
    map snd (filter (fun '(v, _) =>
      match v with
      | DFG_OVar o => match outputs_var_class o with
                      | Public => true
                      | Secret => false
                      end
      | DFG_SVar _ => false
      end) (var_map dfg)).

  (* Every declassification instance the user's rules emit for this DFG.
     Instances are generated from the current graph, so node ids can never go
     stale across a re-elaboration. *)
  Definition decl_instances (dfg: dfg_state) : list decl_instance :=
    flat_map (fun r => r dfg) (tfs_spec_decls ctx).

  (* Only unconditional instances may seed the taint fold: a node that is
     derivable merely on some path is not unconditionally untainted. *)
  Definition uncond_instances (dfg: dfg_state) : list decl_instance :=
    filter (fun i => match di_guard i with [] => true | _ => false end)
           (decl_instances dfg).

  Definition mem_nid (n: nid_t) (l: list nid_t) : bool := existsb (Nat.eqb n) l.

  (* Re-adding a target already in [acc] would let the accumulator grow by
     [|instances|] on every one of the [length (graph dfg)] iterations. *)
  Definition saturate_step (dfg: dfg_state) (acc: list nid_t) : list nid_t :=
    fold_left
      (fun acc i =>
         if forallb (fun s => mem_nid s acc) (di_sources i)
            && negb (mem_nid (di_target i) acc)
         then di_target i :: acc
         else acc)
      (uncond_instances dfg) acc.

  (* [saturate_step] only ever adds nodes, so an unchanged length means the
     fixpoint is reached and the remaining rounds would be idle. *)
  Fixpoint saturate (fuel: nat) (dfg: dfg_state) (acc: list nid_t) : list nid_t :=
    match fuel with
    | 0 => acc
    | S f =>
        let acc' := saturate_step dfg acc in
        if Nat.eqb (length acc') (length acc) then acc else saturate f dfg acc'
    end.

  (* Constants and public inputs agree across any two runs, so they are
     derivable under the empty guard and seed both saturations. *)
  (* Values that enter the graph already known to the attacker: constants, and
     inputs declared [Public].  A [Secret] input comes from inside the trust
     boundary, so it belongs with the taint sources. *)
  Definition trivially_public (dfg: dfg_state) : list nid_t :=
    filter (fun k => match op (nth k (graph dfg)
                                 {| nid := 0; op := DFG_Empty; sz := 0 |}) with
                     | DFG_Const _ => true
                     | DFG_Input v => match inputs_var_class v with
                                      | Public => true
                                      | Secret => false
                                      end
                     | _ => false
                     end)
           (List.seq 1 (length (graph dfg) - 1)).

  (* Every node the attacker can derive a value for. Whitebox untainting is the
     saturation below; it must stay computable without the taint set, since the
     fold below consumes this as a seed. *)
  Definition untainted_roots (dfg: dfg_state) : list (nid_t) :=
    saturate (length (graph dfg)) dfg (public_dsts dfg ++ trivially_public dfg).

  (* ============================== *)
  (* = Guards and their checker   = *)
  (* ============================== *)

  (* A path guard is a conjunction of selector literals: [(c, true)] means the
     then-branch of the phi with condition [c] was taken. *)
  Definition lit := (nid_t * bool)%type.

  Definition lit_eqb (x y: lit) : bool :=
    Nat.eqb (fst x) (fst y) && Bool.eqb (snd x) (snd y).

  Definition guard_incl (g pi: list lit) : bool :=
    forallb (fun a => existsb (lit_eqb a) pi) g.

  Definition get_tainted (dfg: dfg_state) : list (nid_t) :=
    let untainted := untainted_roots dfg in
    let aux (taint_map: list (nid_t)) (node : dfg_node) : list (nid_t) :=
      let args := get_args node in
      (* Only a read of pre-action secret state is a taint source: inputs and reads of
         the pre-action output state are both visible to the attacker. *)
      (* Taint SOURCES, one rule per point a value enters the graph: a constant
         is public, an input and a [DFG_OVar] take their declared class, and a
         [DFG_SVar] is secret -- states ARE the secrets under the attacker model. *)
      let self_tainted := match op node with
        | DFG_Var (DFG_SVar _) => true
        | DFG_Var (DFG_OVar o) => match outputs_var_class o with
                                  | Public => false
                                  | Secret => true
                                  end
        | DFG_Input v => match inputs_var_class v with
                         | Public => false
                         | Secret => true
                         end
        (* An IP link is outside the attacker model, so a sample is always a
           taint source.  Without this arm the wildcard swallows it and IPR
           goes unsound. *)
        | DFG_Sample _ _ _ => true
        | _ => false
        end in
      (* If node depends on secrets it is tainted *)
      let is_tainted := self_tainted || existsb (fun arg_id =>
        match mem arg_id taint_map with
        | inl m => true
        | inr _ => false
        end) args 
      in
      (* An output node is declassified here. *)
      match mem (nid node) untainted with
        | inl m => taint_map
        | inr _ => if is_tainted then (nid node) :: taint_map else taint_map
      end
    in
    fold_left aux (graph dfg) [].


  (* Transitive constant-time tagging is deliberately absent: only a *derivable*
     latency is required, and a critical phi already waits for both branches.
     See agents/taint-tagging-soundness/PLAN.md issue E. *)

  (* Facts "node [c] is derivable whenever guard [g] holds", seeded from
     [untainted_roots] and saturated by [decl_compose].  DISJUNCTION is several
     entries for one node, hence the Cartesian product below. *)
  Definition gfact := (nid_t * list lit)%type.

  Definition gfacts_of (base: list gfact) (c: nid_t) : list (list lit) :=
    map snd (filter (fun f => Nat.eqb (fst f) c) base).

  Definition declassified_at (base: list gfact) (c: nid_t) (pi: list lit) : bool :=
    existsb (fun g => guard_incl g pi) (gfacts_of base c).

  (* A fact already known under a weaker guard makes the new one redundant. *)
  Definition gsubsumed (base: list gfact) (c: nid_t) (g: list lit) : bool :=
    existsb (fun g0 => guard_incl g0 g) (gfacts_of base c).

  (* Empty when some source has no fact at all. *)
  Fixpoint gcombine (base: list gfact) (ss: list nid_t) : list (list lit) :=
    match ss with
    | [] => [[]]
    | s :: rest =>
        flat_map (fun g => map (fun gr => g ++ gr) (gcombine base rest))
                 (gfacts_of base s)
    end.

  Definition gadd_of (i: decl_instance) (acc: list gfact) (gs: list lit)
    : list gfact :=
    if gsubsumed acc (di_target i) (di_guard i ++ gs) then acc
    else acc ++ [(di_target i, di_guard i ++ gs)].

  Definition gstep1 (acc: list gfact) (i: decl_instance) : list gfact :=
    fold_left (gadd_of i) (gcombine acc (di_sources i)) acc.

  Definition gsaturate_step (dfg: dfg_state) (base: list gfact) : list gfact :=
    fold_left gstep1 (decl_instances dfg) base.

  Fixpoint gsaturate (fuel: nat) (dfg: dfg_state) (base: list gfact) : list gfact :=
    match fuel with
    | 0 => base
    | S f =>
        let base' := gsaturate_step dfg base in
        if Nat.eqb (length base') (length base) then base else gsaturate f dfg base'
    end.

  Definition decl_facts (dfg: dfg_state) : list gfact :=
    gsaturate (length (graph dfg)) dfg
      (map (fun n => (n, [])) (untainted_roots dfg)).

  (* ============================== *)
  (* = Step 6: TF Compilations    = *)
  (* ============================== *)

  Local Notation expr_t := (@tf_expr tf_dfg_states (inputs_var + ips_var) outputs_var).

  Definition valid_expr_and (expr1: expr_t) (expr2: expr_t) : expr_t :=
    match expr1, expr2 with
    | tf_const 1, e2 => e2
    | e1, tf_const 1 => e1
    | _, _ => tf_op2 tf_and expr1 expr2
    end.

  Definition valid_expr_if (cond: expr_t) (then_expr: expr_t) (else_expr: expr_t) : expr_t :=
    match then_expr, else_expr with
    | tf_const 1, tf_const 1 => tf_const 1
    | _, _ => tf_expr_if cond then_expr else_expr
    end.


  (* First the expression, then the valid signal.  [pi] is the path of selector
     literals this occurrence is compiled under: criticality is per OCCURRENCE,
     since a declassification holds exactly where its guard does. *)

  (* A phi is critical at this occurrence when its condition is tainted and NO
     recorded guard for it is implied by the path. *)
  Definition phi_crit (tainted: list nid_t) (dfacts: list gfact)
      (c: nid_t) (pi: list lit) : bool :=
    mem_nid c tainted && negb (declassified_at dfacts c pi).

  (* A CRITICAL phi reads both branch validities unconditionally, so it compiles
     its branches under the UNEXTENDED path; a selecting phi extends it with the
     selector. *)
  Definition phi_path (crit: bool) (c: nid_t) (b: bool) (pi: list lit) : list lit :=
    if crit then pi else (c, b) :: pi.

  (* ---------------------------------------------------------------- *)
  (* DIAGNOSTICS.  Staying critical is a silent pessimisation, so the   *)
  (* compiler also reports, per phi occurrence, WHY it could not use a  *)
  (* declassification.                                                  *)
  (* ---------------------------------------------------------------- *)

  Inductive crit_reason :=
  (* the condition is tainted and no rule instance targets it *)
  | CR_no_rule (c: nid_t)
  (* an instance targets it, but these of its sources have no fact at all, so
     the composition could not fire *)
  | CR_sources_unknown (c: nid_t) (unknown_sources: list nid_t)
  (* it IS declassified, but no recorded guard is implied by this occurrence's
     path; one entry per recorded guard, listing the literals the path lacks *)
  | CR_guard_unmet (c: nid_t) (missing: list (list lit)).

  Definition guard_missing (g pi: list lit) : list lit :=
    filter (fun a => negb (existsb (lit_eqb a) pi)) g.

  Definition phi_crit_reason (dfg: dfg_state) (tainted: list nid_t) (base: list gfact)
      (c: nid_t) (pi: list lit)
    : option crit_reason :=
    if negb (mem_nid c tainted) then None
    else
      match gfacts_of base c with
      | [] =>
          match find (fun i => Nat.eqb (di_target i) c) (decl_instances dfg) with
          | Some i =>
              Some (CR_sources_unknown c
                      (filter (fun s => match gfacts_of base s with
                                        | [] => true
                                        | _ => false
                                        end)
                              (di_sources i)))
          | None => Some (CR_no_rule c)
          end
      | gs =>
          if declassified_at base c pi then None
          else Some (CR_guard_unmet c (map (fun g => guard_missing g pi) gs))
      end.

  (* The diagnostic never disagrees with the compiler about WHETHER a phi
     occurrence is critical; it only adds the reason. *)
  Lemma phi_crit_reason_none (dfg: dfg_state) (tainted: list nid_t) (base: list gfact)
      (c: nid_t) (pi: list lit) :
    phi_crit_reason dfg tainted base c pi = None
    <-> phi_crit tainted base c pi = false.
  Proof.
    unfold phi_crit_reason, phi_crit, declassified_at. cbv zeta.
    destruct (mem_nid c tainted) eqn:Hm; cbn [negb andb];
      [ | split; intro H; reflexivity ].
    destruct (gfacts_of base c) as [| g0 gs] eqn:Hgs;
      cbn [existsb negb].
    - destruct (find _ (decl_instances dfg)); split; intro H; discriminate.
    - destruct (guard_incl g0 pi || existsb (fun g => guard_incl g pi) gs);
        cbn [negb]; split; intro H; (reflexivity || discriminate).
  Qed.

  (* Walks the same cone [compile_dfg_expr_aux] does, under the same paths.
     [tainted] and [dfacts] are threaded for the same reason they are there. *)
  Fixpoint crit_report_aux (dfg: dfg_state) (tainted: list nid_t) (dfacts: list gfact)
      (pi: list lit) (fuel: nat)
      (n: nid_t) (bufs: list (nid_t * (nat * sz_t))) : list crit_reason :=
    match fuel with
    | 0 => []
    | S fuel' =>
        match BitsToLists.list_assoc bufs n with
        | Some _ => []
        | None =>
            let node := nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |} in
            match op node with
            | DFG_Unary _ a => crit_report_aux dfg tainted dfacts pi fuel' a bufs
            | DFG_Resize a => crit_report_aux dfg tainted dfacts pi fuel' a bufs
            | DFG_Binary _ a1 a2 =>
                crit_report_aux dfg tainted dfacts pi fuel' a1 bufs
                ++ crit_report_aux dfg tainted dfacts pi fuel' a2 bufs
            | DFG_Phi c t e =>
                let crit := phi_crit tainted dfacts c pi in
                (match phi_crit_reason dfg tainted dfacts c pi with Some r => [r] | None => [] end)
                ++ crit_report_aux dfg tainted dfacts pi fuel' c bufs
                ++ crit_report_aux dfg tainted dfacts (phi_path crit c true pi) fuel' t bufs
                ++ crit_report_aux dfg tainted dfacts (phi_path crit c false pi) fuel' e bufs
            (* Explicit, not falling through to [_]: the archive's DEBT-3 was a
               silently under-reporting diagnostic caused by exactly that. *)
            | DFG_Stall _ a => crit_report_aux dfg tainted dfacts pi fuel' a bufs
            | DFG_Drive _ a _ => crit_report_aux dfg tainted dfacts pi fuel' a bufs
            | DFG_Sample _ t _ => crit_report_aux dfg tainted dfacts pi fuel' t bufs
            | DFG_Join a b =>
                crit_report_aux dfg tainted dfacts pi fuel' a bufs
                ++ crit_report_aux dfg tainted dfacts pi fuel' b bufs
            | _ => []
            end
        end
    end.

  (* Entry point mirroring [compile_dfg_expr]: empty path, no buffer cuts. *)
  Definition crit_report (dfg: dfg_state) (n: nid_t) : list crit_reason :=
    crit_report_aux dfg (get_tainted dfg) (decl_facts dfg) [] (length (graph dfg)) n [].

  (* Everything the scheduler compiles for an action, in one list. *)
  Definition crit_report_all (dfg: dfg_state) : list crit_reason :=
    let tainted := get_tainted dfg in
    let dfacts := decl_facts dfg in
    flat_map (fun v => crit_report_aux dfg tainted dfacts [] (length (graph dfg)) (snd v) [])
             (var_map dfg).

  (* ---------------------------------------------------------------- *)
  (* CYCLE BOUNDS.  How long an action takes for a CONCRETE input is    *)
  (* not something to compute (that is [L] in Properties/IPR.v, which   *)
  (* exists for the proofs).  What the circuit does give cheaply is the *)
  (* best and worst case, read off the same cone the compiler walks.    *)
  (* ---------------------------------------------------------------- *)

  Definition cycle_of (cycles: list (nid_t * cycle_t)) (n: nid_t) : cycle_t :=
    match BitsToLists.list_assoc cycles n with
    | Some c => c
    | None => 0
    end.

  (* A bound together with the path of branch literals that achieves it.  A
     number alone says the action is not constant time; the path says WHEN it
     is fast and when it is slow, which is the attack. *)
  Definition wcycle := (cycle_t * list lit)%type.

  Definition lit_in (a: lit) (l: list lit) : bool := existsb (lit_eqb a) l.

  Definition wunion (a b: list lit) : list lit :=
    a ++ filter (fun x => negb (lit_in x a)) b.

  (* An UPPER bound is attained as soon as its dominating subterm is, so only
     the winner's branches are required. *)
  Definition wmax (a b: wcycle) : wcycle := if Nat.ltb (fst a) (fst b) then b else a.

  (* Two LOWER bounds must BOTH be attained, so their paths conjoin.  If the two
     disagree on a branch the conjunction is unsatisfiable and the true lower
     bound is higher, so [ta_cycles_lo] stays a bound with an indicative witness. *)
  Definition wmax_lo (a b: wcycle) : wcycle :=
    (Nat.max (fst a) (fst b), wunion (snd a) (snd b)).

  Definition wmin (a b: wcycle) : wcycle := if Nat.ltb (fst b) (fst a) then b else a.

  (* Reaching a deeper stage does not change WHICH branches were taken. *)
  Definition wbump (here: cycle_t) (a: wcycle) : wcycle :=
    if Nat.ltb (fst a) here then (here, snd a) else a.

  (* A critical phi ANDs both branch validities, so it can only be ready when
     the slower branch is; a non-critical one selects, so its best case is the
     faster branch.  That difference is the entire cost of criticality. *)
  Fixpoint node_bounds_w (dfg: dfg_state) (tainted: list nid_t) (dfacts: list gfact)
      (cycles: list (nid_t * cycle_t)) (pi: list lit) (fuel: nat) (n: nid_t)
      : wcycle * wcycle :=
    match fuel with
    | 0 => ((0, pi), (0, pi))
    | S fuel' =>
        (* A source node is never buffered (see [require_buffer]), so it is
           readable in stage 0 no matter how deep its target cycle claims to be. *)
        let here := if is_source dfg n then 0 else cycle_of cycles n in
        let node := nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |} in
        match op node with
        | DFG_Unary _ a =>
            let '(l, u) := node_bounds_w dfg tainted dfacts cycles pi fuel' a in
            (wbump here l, wbump here u)
        | DFG_Resize a =>
            let '(l, u) := node_bounds_w dfg tainted dfacts cycles pi fuel' a in
            (wbump here l, wbump here u)
        | DFG_Binary _ a1 a2 =>
            let '(l1, u1) := node_bounds_w dfg tainted dfacts cycles pi fuel' a1 in
            let '(l2, u2) := node_bounds_w dfg tainted dfacts cycles pi fuel' a2 in
            (wbump here (wmax_lo l1 l2), wbump here (wmax u1 u2))
        (* SPIKE: identity for now.  W-b would add its declared latency to BOTH
           bounds here, which is exactly what keeps the latency derivable. *)
        | DFG_Stall _ a =>
            let '(l, u) := node_bounds_w dfg tainted dfacts cycles pi fuel' a in
            (wbump here l, wbump here u)
        | DFG_Drive _ a _ =>
            let '(l, u) := node_bounds_w dfg tainted dfacts cycles pi fuel' a in
            (wbump here l, wbump here u)
        | DFG_Sample _ t _ =>
            let '(l, u) := node_bounds_w dfg tainted dfacts cycles pi fuel' t in
            (wbump here l, wbump here u)
        (* Like a binary: the ordering join is valid when both arguments are. *)
        | DFG_Join a b =>
            let '(l1, u1) := node_bounds_w dfg tainted dfacts cycles pi fuel' a in
            let '(l2, u2) := node_bounds_w dfg tainted dfacts cycles pi fuel' b in
            (wbump here (wmax_lo l1 l2), wbump here (wmax u1 u2))
        | DFG_Phi c t e =>
            let crit := phi_crit tainted dfacts c pi in
            let '(lc, uc) := node_bounds_w dfg tainted dfacts cycles pi fuel' c in
            let '(lt, ut) := node_bounds_w dfg tainted dfacts cycles (phi_path crit c true pi) fuel' t in
            let '(le, ue) := node_bounds_w dfg tainted dfacts cycles (phi_path crit c false pi) fuel' e in
            (wbump here (wmax_lo lc (if crit then wmax_lo lt le else wmin lt le)),
             wbump here (wmax uc (wmax ut ue)))
        | _ => ((here, pi), (here, pi))
        end
    end.

  Definition node_bounds (dfg: dfg_state) (tainted: list nid_t) (dfacts: list gfact)
      (cycles: list (nid_t * cycle_t)) (pi: list lit) (fuel: nat) (n: nid_t)
      : cycle_t * cycle_t :=
    let '(l, u) := node_bounds_w dfg tainted dfacts cycles pi fuel n in (fst l, fst u).

  (* The action is done when every variable it writes is valid, so the bounds
     are maxima over the roots, counted in CYCLES (combinational is (1, 1)).
     [fst = snd] certifies the action is constant time. *)
  Definition action_bounds_w (dfg: dfg_state) : wcycle * wcycle :=
    let tainted := get_tainted dfg in
    let dfacts := decl_facts dfg in
    let cycles := calc_target_cycle (calc_backward_cost dfg) in
    let '(l, u) :=
      fold_left (fun '(l, u) v =>
                   let '(lv, uv) :=
                     node_bounds_w dfg tainted dfacts cycles [] (length (graph dfg)) (snd v) in
                   (wmax_lo l lv, wmax u uv))
                (var_map dfg) ((0, []), (0, [])) in
    ((S (fst l), snd l), (S (fst u), snd u)).

  Definition action_bounds (dfg: dfg_state) : cycle_t * cycle_t :=
    let '(l, u) := action_bounds_w dfg in (fst l, fst u).

  (* Agreeing bounds leave nothing for the two witness paths to distinguish:
     they are then two runs of the same length, which is what makes [fst = snd]
     readable as [constant time]. *)
  Lemma bounds_agree_witness (dfg: dfg_state) :
    fst (action_bounds dfg) = snd (action_bounds dfg) ->
    fst (fst (action_bounds_w dfg)) = fst (snd (action_bounds_w dfg)).
  Proof.
    unfold action_bounds. destruct (action_bounds_w dfg) as [l u]. cbn. auto.
  Qed.


  Fixpoint compile_dfg_expr_aux (tainted: list nid_t)
    (dfacts: list gfact) (pi: list lit)
    (fuel: nat) (a_idx: Vect.index (length bn)) (dfg: dfg_state) (nid: nid_t) (buffers: list (nid_t * (nat * sz_t))) 
    : (expr_t * expr_t)
    :=
    match fuel with
    | 0 => (tf_const 0, tf_const 0) (* should not happen *)
    | S fuel' =>
        match BitsToLists.list_assoc buffers nid with
        | Some (n_idx, n_sz) => match index_of_nat (length (nth (index_to_nat a_idx) bn [])) n_idx with
                              | Some n_idx' =>
                                  (* a stall's buffer is its COUNTER: the register
                                     is the count, and the stall carries no
                                     value, so only the validity comes back *)
                                  match op (nth nid (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0; |}) with
                                  | DFG_Stall _ _ =>
                                      (tf_const 0, tf_svar (tf_dfg_v a_idx n_idx'))
                                  | _ => (tf_svar (tf_dfg_b a_idx n_idx'), tf_svar (tf_dfg_v a_idx n_idx'))
                                  end
                              | None => (tf_const 0, tf_const 0) (* should not happen *)
                              end
        | None => 
          let node := nth nid (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0; |} in
          match op node with
          | DFG_Const n => (tf_const n, tf_const 1)
          | DFG_Input v => (tf_ivar (inl v), tf_const 1)
          | DFG_Var v => match v with
                        | DFG_SVar s_var => (tf_svar (tf_dfg_s s_var), tf_const 1)
                        | DFG_OVar o_var => (tf_ovar o_var, tf_const 1)
                        end
          | DFG_Unary op arg1 =>
              let '(arg_expr, val_expr) := compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg arg1 buffers in
              (tf_op1 op arg_expr, val_expr)
          | DFG_Binary op arg1 arg2 =>
              let '(arg1_expr, val1_expr) := compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg arg1 buffers in
              let '(arg2_expr, val2_expr) := compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg arg2 buffers in
              (tf_op2 op arg1_expr arg2_expr, valid_expr_and val1_expr val2_expr)
          | DFG_Resize arg1 =>
              let '(arg_expr, val_expr) := compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg arg1 buffers in
              let arg_node := nth arg1 (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0; |} in
              (tf_op1 (tf_resize (sz arg_node)) arg_expr, val_expr)
          | DFG_Phi cond_id then_id else_id =>
              let '(cond_expr, cond_val) := compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg cond_id buffers in
              let '(then_expr, then_val) := compile_dfg_expr_aux tainted dfacts
                (phi_path (phi_crit tainted dfacts cond_id pi) cond_id true pi) fuel' a_idx dfg then_id buffers in
              let '(else_expr, else_val) := compile_dfg_expr_aux tainted dfacts
                (phi_path (phi_crit tainted dfacts cond_id pi) cond_id false pi) fuel' a_idx dfg else_id buffers in
              (
                tf_expr_if cond_expr then_expr else_expr, 
                if phi_crit tainted dfacts cond_id pi then
                  valid_expr_and (valid_expr_and then_val else_val) cond_val
                else
                  valid_expr_and cond_val (valid_expr_if cond_expr then_val else_val)
              )
          (* A stall CARRIES NO VALUE -- it is the counter [compile_dfg_buffers]
             counts out, and the answer arrives on the wire at the sample.  Only
             its validity, which lags its argument's by [lat] cycles, is read. *)
          | DFG_Stall _ arg1 =>
              let '(_, v) := compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg arg1 buffers in
              (tf_const 0, v)
          (* A drive passes its value through: it is the message on its way to
             the port.  A sample's VALUE is the port and its VALIDITY the
             token's, which is where the round trip decouples the two. *)
          | DFG_Drive _ arg1 _ =>
              compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg arg1 buffers
          | DFG_Sample p tok _ =>
              let '(_, tok_val) := compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg tok buffers in
              (tf_ivar (inr p), tok_val)
          (* ORDERING only: the validity is the AND the sequencing needs, and
             the value is a constant because nothing reads it. *)
          | DFG_Join a b =>
              let '(_, val_a) := compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg a buffers in
              let '(_, val_b) := compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg b buffers in
              (tf_const 0, valid_expr_and val_a val_b)
          | DFG_Empty => (tf_const 0, tf_const 0) (* should not happen *)
          end
        end
    end.

  (* The analysis is evaluated once here; compilation starts at the empty path. *)
  Local Notation compile_dfg_expr fuel a_idx dfg n bufs :=
    (compile_dfg_expr_aux (get_tainted dfg) (decl_facts dfg) [] fuel a_idx dfg n bufs).

  Definition compile_dfg_buffers (a_idx: nat) (dfg: dfg_state) (buffers: list (nid_t * (nat * sz_t)))
    : list (@tf_op tf_dfg_states (inputs_var + ips_var) outputs_var Empty_set)
    :=
    (* Bound outside the [flat_map]: inlining these would re-run the whole taint
       and declassification analysis once per buffer. *)
    let tainted := get_tainted dfg in
    let dfacts := decl_facts dfg in
    let fuel := length (graph dfg) in
    match index_of_nat (length bn) a_idx with
    | None => []
    | Some a_idx' => 
      flat_map 
        ( fun '(nid, x) => 
          match index_of_nat (length (nth (index_to_nat a_idx') bn [])) (fst x) with
            | Some n_idx' => 
              let buffers' := filter (fun '(b_nid, _) => negb (Nat.eqb b_nid nid)) buffers in
              let '(expr, valid) := compile_dfg_expr_aux tainted dfacts [] fuel a_idx' dfg nid buffers' in
              (* A buffer RECOMPUTES every cycle, sound while its sources are
                 stable across the action.  A [DFG_Sample] reads a LIVE wire, so
                 its buffer LATCHES as its validity RISES and holds thereafter. *)
              let is_sample :=
                match op (nth nid (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}) with
                | DFG_Sample _ _ _ => true
                | _ => false
                end in
              (* A stall's buffer is a COUNTER: it advances while the argument is
                 valid and saturates at [lat-1], so the validity rises exactly
                 [lat] cycles after the argument's and stays up. *)
              let stall_lat :=
                match op (nth nid (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}) with
                | DFG_Stall l _ => Some l
                | _ => None
                end in
              let cnt := tf_svar (tf_dfg_b a_idx' n_idx') in
              let bexpr :=
                match stall_lat with
                | Some l =>
                    tf_expr_if (tf_op2 tf_and valid
                                  (tf_op1 tf_not (tf_op2 (tf_cmp (snd x) tf_eq) cnt (tf_const (pred l)))))
                      (tf_op2 tf_add cnt (tf_const 1)) cnt
                | None =>
                  if is_sample
                  then tf_expr_if (tf_op2 tf_and valid
                                     (tf_op1 tf_not (tf_svar (tf_dfg_v a_idx' n_idx'))))
                         expr (tf_svar (tf_dfg_b a_idx' n_idx'))
                  else expr
                end in
              let vexpr :=
                match stall_lat with
                | Some l => tf_op2 (tf_cmp (snd x) tf_eq) cnt (tf_const (pred l))
                | None => valid
                end in
              [ tf_assign (tf_dfg_b a_idx' n_idx') bexpr; tf_assign (tf_dfg_v a_idx' n_idx') vexpr ]
            | None => [] (* should not happen *)
            end ) buffers
    end.

  (* ==================================================================== *)
  (* SPIKE 2c: mid-action port drives                                     *)
  (* ==================================================================== *)

  (* The nids of every [DFG_Drive] on [p], LATEST FIRST (the fold conses
     and graph order is program order). *)
  Definition drive_nodes (dfg: dfg_state) (p: ips_var) : list nid_t :=
    fold_left (fun acc nd =>
                 match op nd with
                 | DFG_Drive p' _ _ => if ips_var_eq_dec.(eq_dec) p' p then nid nd :: acc else acc
                 | _ => acc
                 end) (graph dfg) [].

  (* Every IP, not just the ones this action calls: a drive register is live in
     the always half of EVERY action, and one with no call emits a hold. *)
  Definition driven_ports (_: dfg_state) : list ips_var :=
    @finite_elements ips_var ips_var_fin.

  (* [n]'s stall, paired with the node it waits on: the drive itself, or the
     ordering join when the call is SEQUENCED, which is why this looks through
     one binary node. *)
  Definition chain_gate (dfg: dfg_state) (n: nid_t) : option (nid_t * nid_t) :=
    let stall_of := fun (m: nid_t) =>
      match find (fun nd => match op nd with
                            | DFG_Stall _ a => Nat.eqb a m
                            | _ => false
                            end) (graph dfg) with
      | Some nd => Some (nid nd)
      | None => None
      end in
    match stall_of n with
    | Some h => Some (n, h)
    | None =>
        match find (fun nd => match op nd with
                              | DFG_Join a _ => Nat.eqb a n
                              | _ => false
                              end) (graph dfg) with
        | Some j => match stall_of (nid j) with
                    | Some h => Some (nid j, h)
                    | None => None
                    end
        | None => None
        end
    end.

  Definition chain_head (dfg: dfg_state) (n: nid_t) : option nid_t :=
    match chain_gate dfg n with Some (_, h) => Some h | None => None end.

  (* The first cycle of a stall's wait: its counter is still zero. *)
  Definition stall_start (a_idx: Vect.index (length bn)) (dfg: dfg_state)
    (buffers: list (nid_t * (nat * sz_t))) (h: nid_t) : expr_t :=
    match BitsToLists.list_assoc buffers h with
    | Some (n_idx, n_sz) =>
        match index_of_nat (length (nth (index_to_nat a_idx) bn [])) n_idx with
        | Some n_idx' =>
            tf_op2 (tf_cmp n_sz tf_eq) (tf_svar (tf_dfg_b a_idx n_idx')) (tf_const 0)
        | None => tf_const 0
        end
    | None => tf_const 0
    end.

  (* A drive is an ALWAYS-op, so the request is on the wire during the action.
     The port HOLDS its old value until the drive's validity fires, and validity
     is monotone, so it stays stable from there to the response. *)
  (* The path condition: each literal, negated on the else side; empty is [1].
     Compiled for the cycle the drive fires in, so buffers are substituted only
     for samples -- every other source is stable across the action. *)
  Definition guard_expr (tainted: list nid_t) (dfacts: list gfact) (fuel: nat)
    (a_idx: Vect.index (length bn)) (dfg: dfg_state)
    (sbufs: list (nid_t * (nat * sz_t))) (en: list (nid_t * bool)) : expr_t :=
    fold_right (fun (l : nid_t * bool) (acc : expr_t) =>
      let v := fst (compile_dfg_expr_aux tainted dfacts [] fuel a_idx dfg (fst l) sbufs) in
      let lv := if snd l then v else tf_op1 tf_not v in
      tf_op2 tf_and lv acc) (tf_const 1) en.

  Definition compile_dfg_drives (a_idx: nat) (dfg: dfg_state)
    (buffers: list (nid_t * (nat * sz_t)))
    : list (@tf_op tf_dfg_states (inputs_var + ips_var) outputs_var Empty_set) :=
    let tainted := get_tainted dfg in
    let dfacts := decl_facts dfg in
    let fuel := length (graph dfg) in
    (* the only buffers a guard keeps -- see [guard_expr] *)
    let sbufs := filter (fun '(n, _) =>
                           match op (nth n (graph dfg)
                                       {| nid := 0; op := DFG_Empty; sz := 0 |}) with
                           | DFG_Sample _ _ _ => true
                           | _ => false
                           end) buffers in
    match index_of_nat (length bn) a_idx with
    | None => []
    | Some a_idx' =>
        (* ONE scheduler register per driven port, holding {strobe, payload}.
           BOTH halves select on the PULSE: pulses are one cycle and disjoint,
           so request k's payload is taken at its own cycle and then HELD. *)
        map (fun p =>
               tf_assign (tf_dfg_ov p)
                 (tf_op2 (tf_concat 1 (ip_req_sz (ip_of p)))
                    (fold_right
                       (fun n acc =>
                          let '(_, v) := compile_dfg_expr_aux tainted dfacts [] fuel a_idx' dfg n buffers in
                          (* the path condition the call sits under: a drive in
                             an untaken branch must not reach the wire *)
                          let en_val :=
                            match op (nth n (graph dfg)
                                        {| nid := 0; op := DFG_Empty; sz := 0 |}) with
                            | DFG_Drive _ _ en => guard_expr tainted dfacts fuel a_idx' dfg sbufs en
                            | _ => tf_const 1
                            end in
                          let '(vgate, vfirst) :=
                            match chain_gate dfg n with
                            | Some (g, h) =>
                                (snd (compile_dfg_expr_aux tainted dfacts [] fuel a_idx' dfg g buffers),
                                 stall_start a_idx' dfg buffers h)
                            | None => (v, tf_const 1)
                            end in
                          tf_expr_if (tf_op2 tf_and en_val (tf_op2 tf_and vgate vfirst))
                            (tf_const 1) acc)
                       (tf_const 0) (drive_nodes dfg p))
                    (fold_right
                       (fun n acc =>
                          let '(e, v) := compile_dfg_expr_aux tainted dfacts [] fuel a_idx' dfg n buffers in
                          (* the path condition the call sits under: a drive in
                             an untaken branch must not reach the wire *)
                          let en_val :=
                            match op (nth n (graph dfg)
                                        {| nid := 0; op := DFG_Empty; sz := 0 |}) with
                            | DFG_Drive _ _ en => guard_expr tainted dfacts fuel a_idx' dfg sbufs en
                            | _ => tf_const 1
                            end in
                          let '(vgate, vfirst) :=
                            match chain_gate dfg n with
                            | Some (g, h) =>
                                (snd (compile_dfg_expr_aux tainted dfacts [] fuel a_idx' dfg g buffers),
                                 stall_start a_idx' dfg buffers h)
                            | None => (v, tf_const 1)
                            end in
                          tf_expr_if (tf_op2 tf_and en_val (tf_op2 tf_and vgate vfirst))
                            e acc)
                       (tf_svar (tf_dfg_ov p)) (drive_nodes dfg p))))
            (driven_ports dfg)
    end.

  Fixpoint combine_valid_exprs (exprs: list (@tf_expr tf_dfg_states (inputs_var + ips_var) outputs_var)) : @tf_expr tf_dfg_states (inputs_var + ips_var) outputs_var :=
    match exprs with
    | [] => tf_const 1
    | [e] => e
    | e :: rest => valid_expr_and e (combine_valid_exprs rest)
    end. 

  Definition compile_dfg_aux (a_idx: nat) (dfg: dfg_state) (buffers: list (nid_t * (nat * sz_t)))
    : list (@tf_op tf_dfg_states (inputs_var + ips_var) outputs_var Empty_set) :=
    let tainted := get_tainted dfg in
    let dfacts := decl_facts dfg in
    let fuel := length (graph dfg) in
    match index_of_nat (length bn) a_idx with
      | None => []
      | Some a_idx' => 
        map 
          ( fun '(var, nid) => 
            let '(expr, valid) := compile_dfg_expr_aux tainted dfacts [] fuel a_idx' dfg nid buffers in
            match var with
            | DFG_SVar sv =>
              tf_assign (tf_dfg_s sv) expr
            | DFG_OVar ov => 
              tf_output ov expr
            end
            ) (var_map dfg)
      end.

  Definition compile_dfg_valid (a_idx: nat) (dfg: dfg_state) (buffers: list (nid_t * (nat * sz_t)))
    : @tf_op tf_dfg_states (inputs_var + ips_var) outputs_var Empty_set :=
    let tainted := get_tainted dfg in
    let dfacts := decl_facts dfg in
    let fuel := length (graph dfg) in
    let nids := nodup Nat.eq_dec (map snd (var_map dfg)) in
    let exprs := match index_of_nat (length bn) a_idx with
      | None => []
      | Some a_idx' => map ( fun nid => snd (compile_dfg_expr_aux tainted dfacts [] fuel a_idx' dfg nid buffers)) nids
    end in
    tf_assign tf_dfg_done (combine_valid_exprs exprs).

  Definition schedule (act: spec_action)
    (* : list (list (@tf_ops tf_dfg_states inputs_var outputs_var)) := *)
    :=
    let idx := spec_action_index act in
    (* Determine the DFG of each operation *)
    let dfgs := map build_dfg spec_all_actions in
    (* Calculate the cost maps for each DFG *)
    let cost_maps := map calc_backward_cost dfgs in
    (* Calculate the target cycles for each node *)
    let cycle_maps := map calc_target_cycle cost_maps in
    (* Determine the required buffers across all actions *)
    let buffers := map (fun '(dfg, cycle_map) => get_sizes_and_idx dfg (require_buffer dfg cycle_map)) (combine dfgs cycle_maps) in

    let final_ops := compile_dfg_aux idx (nth idx dfgs {| graph := []; var_map := [] |}) (nth idx buffers []) in
    let done_signal := compile_dfg_valid idx (nth idx dfgs {| graph := []; var_map := [] |}) (nth idx buffers []) in
    
    ( 
      done_signal :: compile_dfg_buffers idx (nth idx dfgs {| graph := []; var_map := [] |}) (nth idx buffers [])
                  ++ compile_dfg_drives idx (nth idx dfgs {| graph := []; var_map := [] |}) (nth idx buffers []),
      final_ops
    ).

  Definition done_signal := tf_dfg_done (states_var:=states_var) (ips_var:=ips_var) (buffer_needs:=bn).

  Definition reset_states : list tf_dfg_states :=  
    flat_map 
      (fun a_idx => match index_of_nat (length bn) a_idx with
        | Some a_idx' =>
          flat_map (fun n_idx => match index_of_nat (length (nth (index_to_nat a_idx') bn [])) n_idx with
            | Some n_idx' =>
              [ tf_dfg_b a_idx' n_idx'; tf_dfg_v a_idx' n_idx' ]
            | None => [] (* should not happen *)
            end ) (List.seq 0 (length (nth (index_to_nat a_idx') bn [])))
        | None => [] (* should not happen *)
        end)
      (List.seq 0 (length bn)).
  (* EXPERIMENT: strobes are not in reset_states yet; the real implementation
     must add them, which needs NoDup_app in reset_states_nodup. *)

  Instance tf_dfg_states_fin2 : FiniteType2 tf_dfg_states.
  Proof.  
    unshelve econstructor.
    - intro s. destruct s.
      + exact (0, 0).
      + exact (1, finite_index state).
      + exact (3 + finite_index a_idx, finite_index n_idx).
      + exact (3 + (Datatypes.length (finite_elements (T:=(Vect.index (Datatypes.length bn))))) + finite_index a_idx, finite_index n_idx).
      + exact (2, (@finite_index ips_var ips_var_fin p)).
        
    - refine ([ [tf_dfg_done] ] ++ 
              [ map tf_dfg_s finite_elements ] ++ 
              [ map tf_dfg_ov (@finite_elements ips_var ips_var_fin) ] ++ 
              map (fun a => map (tf_dfg_b a) finite_elements) finite_elements ++ 
              map (fun a => map (tf_dfg_v a) finite_elements) finite_elements).

    - intros x n m EQ.
      destruct x; inversion EQ; clear EQ; subst.
      + (* tf_dfg_done *)
        exists [tf_dfg_done]. split; auto.
      + (* tf_dfg_s *)
        exists (map tf_dfg_s finite_elements). split; auto.
        rewrite map_nth_error with (d:=state); auto. rewrite finite_surjective. reflexivity.
      + (* tf_dfg_b *)
        exists (map (tf_dfg_b a_idx) finite_elements). split; auto.
        * cbn [nth_error List.app].
          apply nth_error_app_l.
          rewrite map_nth_error with (d:=a_idx); auto.
          change (index_to_nat a_idx) with (finite_index a_idx).
          apply (finite_surjective a_idx).
        * rewrite map_nth_error with (d:=n_idx); auto. 
          change (index_to_nat n_idx) with (finite_index n_idx).
          rewrite finite_surjective. reflexivity.
      + (* tf_dfg_v *)
        exists (map (tf_dfg_v a_idx) finite_elements). split.
        * cbn [nth_error List.app].
          rewrite nth_error_app2. 
          2: {  repeat rewrite map_length. cbn. lia. }
          repeat rewrite map_length. cbn.
          rewrite Nat.add_comm, Nat.add_sub. 
          rewrite map_nth_error with (d:=a_idx); auto.
          change (index_to_nat a_idx) with (finite_index a_idx).
          change (vect_to_list (all_indices (Datatypes.length bn))) with (finite_elements (T:=Vect.index (Datatypes.length bn))).
          apply (finite_surjective a_idx).
        * rewrite map_nth_error with (d:=n_idx); auto. 
          change (index_to_nat n_idx) with (finite_index n_idx).
          rewrite finite_surjective. reflexivity.
      + (* tf_dfg_ov -- a flat group at a LITERAL index, so this is the
           [tf_dfg_s] case verbatim *)
        exists (map tf_dfg_ov (@finite_elements ips_var ips_var_fin)). split; auto.
        rewrite map_nth_error with (d:=p); auto. rewrite finite_surjective. reflexivity.
    - intros n l Hn m x Hm.
      destruct n as [|n].
      { inversion Hn; subst. destruct m; inversion Hm; subst. reflexivity. timeout 10 scongruence use: nth_error_nil unfold: tfs_spec_states. }
      destruct n as [|n].
      { inversion Hn; subst. apply nth_error_map_inv in Hm. destruct Hm as [s [Hs ?]]; subst.
        apply finite_elements_index in Hs. subst. reflexivity. }
      (* group 2 is the flat tf_dfg_ov block -- same shape as tf_dfg_s *)
      destruct n as [|n].
      { inversion Hn; subst. apply nth_error_map_inv in Hm. destruct Hm as [o [Ho ?]]; subst.
        apply finite_elements_index in Ho. subst. reflexivity. }
      
      rewrite nth_error_app2 in Hn by (simpl; lia).
      change (S (S (S n)) - Datatypes.length [[tf_dfg_done]]) with (S (S n)) in *.

      cbn [nth_error List.app] in Hn.
      destruct (lt_dec n (length (finite_elements (T := Vect.index (Datatypes.length bn))))) as [HLT | HGE].      
      + rewrite nth_error_app1 in Hn by (rewrite map_length; auto).
        apply nth_error_map_inv in Hn. destruct Hn as [a_idx' [Ha EQ_l]]; subst l.
        apply nth_error_map_inv in Hm. destruct Hm as [n_idx' [Hn' EQ_x]]; subst x.

        apply finite_elements_index in Ha.
        apply finite_elements_index in Hn'.
        subst n m. simpl. 
        reflexivity.
      + rewrite nth_error_app2 in Hn by (rewrite map_length; lia).
        repeat rewrite map_length in Hn.
        apply nth_error_map_inv in Hn. destruct Hn as [a_idx' [Ha EQ_l]]; subst l.
        apply nth_error_map_inv in Hm. destruct Hm as [n_idx' [Hn' EQ_x]]; subst x.
        apply finite_elements_index in Ha.
        apply finite_elements_index in Hn'.
        subst m. simpl. f_equal. 
        (* hammer *) timeout 10 sauto.
    - apply Forall_app; split; [| apply Forall_app; split; [| apply Forall_app; split]].
      + repeat constructor. (* hammer *) timeout 10 sfirstorder.
      + repeat constructor. cbn [map]. rewrite map_map. apply NoDup_map_pair. apply finite_injective.
      + (* the flat tf_dfg_ov block *)
        repeat constructor. cbn [map]. rewrite map_map. apply NoDup_map_pair. apply finite_injective.
      + apply Forall_app; split.
        * (* Block for tf_dfg_b *)
          apply Forall_map. apply Forall_forall. intros a_idx' Hin.
          rewrite map_map. apply NoDup_map_pair.
          apply finite_injective.
        * (* Block for tf_dfg_v *)
          apply Forall_map. apply Forall_forall. intros a_idx' Hin.
          rewrite map_map. apply NoDup_map_pair.
          apply finite_injective.
  Defined.  

  Instance tf_dfg_states_fin : FiniteType tf_dfg_states.
  Proof.
    apply FiniteType2_FiniteType.
  Defined.

  Definition maps_to (env: (ContextEnv (FT:=(tfs_spec_states_fin ctx))).(env_t) (tf_states_type states_var_size))
    : ((ContextEnv (FT:=tf_dfg_states_fin)).(env_t) (tf_states_type tf_dfg_states_size)) :=
    (ContextEnv (FT:=tf_dfg_states_fin)).(create) (
      fun s =>
        match s as s0 return (type_denote (tf_states_type tf_dfg_states_size s0)) with
        | tf_dfg_s sv => getenv ContextEnv env sv
        | tf_dfg_b a_idx n_idx => Bits.zero
        | tf_dfg_v a_idx n_idx => Bits.zero
        | tf_dfg_done => Bits.zero
        | tf_dfg_ov _ => Bits.zero
        end
    ).

  Definition maps_from (env: (ContextEnv (FT:=tf_dfg_states_fin)).(env_t) (tf_states_type tf_dfg_states_size))
    : ((ContextEnv (FT:=(tfs_spec_states_fin ctx))).(env_t) (tf_states_type states_var_size)) :=
    (ContextEnv (FT:=(tfs_spec_states_fin ctx))).(create) (
      fun s =>
        match s as s0 return (type_denote (tf_states_type states_var_size s0)) with
        | sv => getenv ContextEnv env (tf_dfg_s sv)
        end
    ).

  Definition tf_dfg_states_init (x: tf_dfg_states) : tf_states_type tf_dfg_states_size x :=
    match x with
    | tf_dfg_s sv => states_var_init sv
    | tf_dfg_b _ _ => Bits.zero
    | tf_dfg_v _ _ => Bits.zero
    | tf_dfg_done => Bits.zero
    | tf_dfg_ov _ => Bits.zero
    end.

End SchedulerCore.
