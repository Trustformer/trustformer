Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.
Require Koika.BitsToLists.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.Contract.
Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.Program.Wf.

Import ListNotations.

Section SchedulerTypes.

  Context {states_var: Type}.
  Context {inputs_var: Type}.
  Context {outputs_var: Type}.

  Definition nid_t := nat.
  Definition sz_t := nat.

  Inductive dfg_vars_t := 
    | DFG_SVar (v: states_var)
    | DFG_OVar (v: outputs_var).

  Inductive dfg_op_t :=
    | DFG_Const (n: nat)
    | DFG_Input (v: inputs_var)
    | DFG_Var (v: dfg_vars_t)
    | DFG_Unary (op: tf_unary_ops) (arg: nid_t)
    | DFG_Binary (op: tf_binary_ops) (arg1: nid_t) (arg2: nid_t)
    | DFG_Resize (arg: nid_t)
    | DFG_Phi (cond: nid_t) (then_id: nid_t) (else_id: nid_t)
    | DFG_Empty                
    .

  Record dfg_node_t := {
    nid : nid_t;
    op : dfg_op_t;
    sz : sz_t;
  }.

  Record dfg_state_t := {
    graph : list dfg_node_t;
    var_map : list (dfg_vars_t * nid_t);
  }.

  Context {A} {buffer_needs: list (list A)}.

  Inductive tf_dfg_states_t :=
    | tf_dfg_done
    | tf_dfg_s (state: states_var)
    | tf_dfg_b (a_idx: Vect.index (length buffer_needs)) (n_idx: Vect.index (length (nth (index_to_nat a_idx) buffer_needs [])))
    | tf_dfg_v (a_idx: Vect.index (length buffer_needs)) (n_idx: Vect.index (length (nth (index_to_nat a_idx) buffer_needs [])))
    .
        
End SchedulerTypes.

Section VariableScheduler.

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

  Local Notation outputs_var := (tfs_spec_outputs ctx).
  Local Notation outputs_var_eq_dec := (tfs_spec_outputs_eq_dec ctx).
  Local Notation outputs_var_fin := (tfs_spec_outputs_fin ctx).
  Local Notation outputs_var_size := (tfs_spec_outputs_size ctx).

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

  (* ============================ *)
  (* = Step 1: DFG Construction = *)
  (* ============================ *)

  (* --- DFG Definitions --- *)
  Local Notation dfg_vars := (@dfg_vars_t states_var outputs_var).
  Local Notation dfg_op := (@dfg_op_t states_var inputs_var outputs_var).
  Local Notation dfg_node := (@dfg_node_t states_var inputs_var outputs_var).
  Local Notation dfg_state := (@dfg_state_t states_var inputs_var outputs_var). 

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

  (* --- Variable & Output Management --- *)

  Definition ensure_var (dfg_v: dfg_vars) : M nid_t :=
    let! id := emit (DFG_Var dfg_v) (dfg_var_size dfg_v) in
    let! s' := get_state in
    let new_map := (dfg_v, id) :: filter (fun '(k, _) => if (eq_dec k dfg_v) then false else true) (var_map s') in
    let! _ := put_state ({| graph := graph s'; var_map := new_map |}) in
    ret id.

  Definition get_var (dfg_v : dfg_vars) : M nid_t :=
    let! s := get_state in
      match BitsToLists.list_assoc (var_map s) dfg_v with
      | Some id => ret id
      | None => ensure_var dfg_v
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
      let! src_id := dataflow_expr src sz in
      emit (DFG_Unary op src_id) sz
    | tf_op2 op src1 src2 =>
      match op with
      | tf_cmp szC _ =>
        let! id1 := dataflow_expr src1 szC in
        let! id2 := dataflow_expr src2 szC in
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

  Fixpoint dataflow_ops (ops : tf_ops) : M unit :=
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
      end
    | tf_ops_cons op1 op2 =>
      let! _ := dataflow_ops op1 in
      dataflow_ops op2
    | tf_ops_if cond then_ops else_ops =>
      let! cond_id := dataflow_expr cond 1 in
      
      let! s_orig := get_state in
      
      (* Then Branch *)
      let! _ := dataflow_ops then_ops in
      let! s_then := get_state in
      
      (* Restore maps *)
      let! _ := put_state ({| 
        graph := graph s_then; 
        var_map := var_map s_orig
      |}) in
      
      (* Else Branch *)
      let! _ := dataflow_ops else_ops in
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
    let (_, final_state) := dataflow_ops ops empty_state in
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
    | DFG_Empty => []
    end.

  (* ============================ *)
  (* = Step 2: Cost Calculation = *)
  (* ============================ *)

  Definition cost_t := nat.

  Definition cost_fn (d: dfg_op) : cost_t :=
    match d with
    | DFG_Const _ => 0
    | DFG_Input _ => 0
    | DFG_Var _ => 0
    | DFG_Unary op _ => match op with
                      | tf_not => 1
                      end
    | DFG_Binary op _ _ => match op with
                        | tf_and => 1
                        | tf_or => 1
                        | tf_xor => 1
                        | tf_add => 2
                        | tf_sub => 2
                        | tf_mul => 5
                        | tf_cmp _ _ => 1
                        end
    | DFG_Resize _ => 0
    | DFG_Phi _ _ _ => 1
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
      list_assoc_set_all_max cost_map ((nid node) :: get_args node) (cost + cost_fn (op node))
    in
    fold_left aux (List.rev (graph dfg)) [].

  (* 
    Step 3, 4, 5, 6 are very simplistic for now.
    Good performant HLS is not our focus, so we keep it simple.
  *)

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

  Definition require_buffer (dfg : dfg_state) (cycle_costs : list (nid_t * cycle_t)) : list (nid_t) :=
    let aux (cost_map: list (nid_t)) (node : dfg_node) : list (nid_t) :=
      let n_cycle := match BitsToLists.list_assoc cycle_costs (nid node) with
                      | Some c => c
                      | None => 0 (* should not happen *)
                      end in
      filter (fun x => match BitsToLists.list_assoc cycle_costs x with
                      | Some c => negb (Nat.eqb c n_cycle)
                      | None => false (* should not happen *)
                      end ) (get_args node) ++ cost_map
    in
    nodup Nat.eq_dec (fold_left aux (graph dfg) []
                        ++ filter (fun x => match BitsToLists.list_assoc cycle_costs x with
                                          | Some 0 => false
                                          | _ => true
                                          end ) (map snd (var_map dfg))).

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

  Local Notation tf_dfg_states := (tf_dfg_states_t (states_var:=states_var) (buffer_needs:=buffer_needs)).
  Definition test := tf_dfg_states.

  Instance show_tf_dfg_states : Show tf_dfg_states :=
    { show := fun dfg_s =>
        match dfg_s with
        | tf_dfg_s s => String.append "s_" (show s)
        | tf_dfg_b a_idx n_idx => String.append "b_" (String.append (show (index_to_nat a_idx)) (String.append "_" (show (index_to_nat n_idx))))
        | tf_dfg_v a_idx n_idx => String.append "v_" (String.append (show (index_to_nat a_idx)) (String.append "_" (show (index_to_nat n_idx))))
        | tf_dfg_done => "done"
        end }.

  Definition tf_dfg_states_size (dfg_s: tf_dfg_states) : sz_t :=
    match dfg_s with
    | tf_dfg_s s => states_var_size s
    | tf_dfg_b a_idx b_idx => snd (snd (nth (index_to_nat b_idx) (nth (index_to_nat a_idx) buffer_needs []) (0, (0, 0))))
    | tf_dfg_v a_idx b_idx => 1
    | tf_dfg_done => 1
    end.

  (* ============================== *)
  (* = Step 5: Taint Analysis     = *)
  (* ============================== *)

  Definition get_tainted (dfg: dfg_state) : list (nid_t) :=
    let aux (taint_map: list (nid_t)) (node : dfg_node) : list (nid_t) :=
      let args := get_args node in
      (* Secrets are tainted *)
      let self_tainted := match op node with
        | DFG_Var _ => true
        | _ => false
        end in
      (* If node depends on secrets it is tainted *)
      let is_tainted := self_tainted || existsb (fun arg_id =>
        match mem arg_id taint_map with
        | inl m => true
        | inr _ => false
        end) args 
      in
      (* If this node is output, then its no longer tainted *)
      match mem (nid node) (map snd (var_map dfg)) with
        | inl m => taint_map
        | inr _ => if is_tainted then (nid node) :: taint_map else taint_map
      end
    in
    fold_left aux (graph dfg) [].

  (* ============================== *)
  (* = Step 6: TF Compilations    = *)
  (* ============================== *)

  Local Notation expr_t := (@tf_expr tf_dfg_states inputs_var outputs_var).

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

  (* First the expression, then the valid signal *)
  Fixpoint compile_dfg_expr (fuel: nat) (a_idx: Vect.index (length buffer_needs)) (dfg: dfg_state) (nid: nid_t) (buffers: list (nid_t * (nat * sz_t))) 
    : (expr_t * expr_t)
    :=
    match fuel with
    | 0 => (tf_const 0, tf_const 0) (* should not happen *)
    | S fuel' =>
        match BitsToLists.list_assoc buffers nid with
        | Some (n_idx, n_sz) => match index_of_nat (length (nth (index_to_nat a_idx) buffer_needs [])) n_idx with
                              | Some n_idx' => (tf_svar (tf_dfg_b a_idx n_idx'), tf_svar (tf_dfg_v a_idx n_idx'))
                              | None => (tf_const 0, tf_const 0) (* should not happen *)
                              end
        | None => 
          let node := nth nid (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0; |} in
          match op node with
          | DFG_Const n => (tf_const n, tf_const 1)
          | DFG_Input v => (tf_ivar v, tf_const 1)
          | DFG_Var v => match v with
                        | DFG_SVar s_var => (tf_svar (tf_dfg_s s_var), tf_const 1)
                        | DFG_OVar o_var => (tf_ovar o_var, tf_const 1)
                        end
          | DFG_Unary op arg1 =>
              let '(arg_expr, val_expr) := compile_dfg_expr fuel' a_idx dfg arg1 buffers in
              (tf_op1 op arg_expr, val_expr)
          | DFG_Binary op arg1 arg2 =>
              let '(arg1_expr, val1_expr) := compile_dfg_expr fuel' a_idx dfg arg1 buffers in
              let '(arg2_expr, val2_expr) := compile_dfg_expr fuel' a_idx dfg arg2 buffers in
              (tf_op2 op arg1_expr arg2_expr, valid_expr_and val1_expr val2_expr)
          | DFG_Resize arg1 =>
              let '(arg_expr, val_expr) := compile_dfg_expr fuel' a_idx dfg arg1 buffers in
              (arg_expr, val_expr)
          | DFG_Phi cond_id then_id else_id =>
              let '(cond_expr, cond_val) := compile_dfg_expr fuel' a_idx dfg cond_id buffers in
              let '(then_expr, then_val) := compile_dfg_expr fuel' a_idx dfg then_id buffers in
              let '(else_expr, else_val) := compile_dfg_expr fuel' a_idx dfg else_id buffers in
              (
                tf_expr_if cond_expr then_expr else_expr, 
                if mem cond_id (get_tainted dfg) then
                  valid_expr_and (valid_expr_and then_val else_val) cond_val
                else
                  valid_expr_and cond_val (valid_expr_if cond_expr then_val else_val)
              )
          | DFG_Empty => (tf_const 0, tf_const 0) (* should not happen *)
          end
        end
    end.

  Definition compile_dfg_buffers (a_idx: nat) (dfg: dfg_state) (buffers: list (nid_t * (nat * sz_t)))
    := 
    let fuel := length (graph dfg) in
    match index_of_nat (length buffer_needs) a_idx with
    | None => []
    | Some a_idx' => 
      flat_map 
        ( fun '(nid, x) => 
          match index_of_nat (length (nth (index_to_nat a_idx') buffer_needs [])) (fst x) with
            | Some n_idx' => 
              let buffers' := filter (fun '(b_nid, _) => negb (Nat.eqb b_nid nid)) buffers in
              let '(expr, valid) := compile_dfg_expr fuel a_idx' dfg nid buffers' in
              [ tf_assign (tf_dfg_b a_idx' n_idx') expr; tf_assign (tf_dfg_v a_idx' n_idx') valid ]
            | None => [] (* should not happen *)
            end ) buffers
    end.

  (* Fixpoint combine_pair_step (exprs : list expr_t) : list expr_t :=
    match exprs with
    | e1 :: e2 :: rest => (valid_expr_and e1 e2) :: combine_pair_step rest
    | _ => exprs
    end.

  Fixpoint combine_balanced_helper (fuel : nat) (exprs : list expr_t) : expr_t :=
    match fuel with
    | 0 => tf_const 1 (* should not happen *)
    | S f =>
      match exprs with
      | [] => tf_const 1
      | [e] => e
      | _ => combine_balanced_helper f (combine_pair_step exprs)
      end
    end.

  Definition combine_valid_exprs (exprs : list expr_t) : expr_t :=
    combine_balanced_helper (length exprs) exprs. *)

  Fixpoint combine_valid_exprs (exprs: list (@tf_expr tf_dfg_states inputs_var outputs_var)) : @tf_expr tf_dfg_states inputs_var outputs_var :=
    match exprs with
    | [] => tf_const 1
    | [e] => e
    | e :: rest => valid_expr_and e (combine_valid_exprs rest)
    end. 

  Definition compile_dfg_aux (a_idx: nat) (dfg: dfg_state) (buffers: list (nid_t * (nat * sz_t))) :=
    let fuel := length (graph dfg) in
    match index_of_nat (length buffer_needs) a_idx with
      | None => []
      | Some a_idx' => 
        map 
          ( fun '(var, nid) => 
            let '(expr, valid) := compile_dfg_expr fuel a_idx' dfg nid buffers in
            match var with
            | DFG_SVar sv =>
              tf_assign (tf_dfg_s sv) expr
            | DFG_OVar ov => 
              tf_output ov expr
            end
            ) (var_map dfg)
      end.

  Definition compile_dfg_valid (a_idx: nat) (dfg: dfg_state) (buffers: list (nid_t * (nat * sz_t))) :=
    let fuel := length (graph dfg) in
    let nids := nodup Nat.eq_dec (map snd (var_map dfg)) in
    let exprs := match index_of_nat (length buffer_needs) a_idx with
      | None => []
      | Some a_idx' => map ( fun nid => snd (compile_dfg_expr fuel a_idx' dfg nid buffers)) nids
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
      done_signal :: compile_dfg_buffers idx (nth idx dfgs {| graph := []; var_map := [] |}) (nth idx buffers []),
      final_ops
    ).

  Definition done_signal := tf_dfg_done (states_var:=states_var) (buffer_needs:=buffer_needs).

  Definition reset_states : list tf_dfg_states :=  
    flat_map 
      (fun a_idx => match index_of_nat (length buffer_needs) a_idx with
        | Some a_idx' =>
          flat_map (fun n_idx => match index_of_nat (length (nth (index_to_nat a_idx') buffer_needs [])) n_idx with
            | Some n_idx' =>
              [ tf_dfg_b a_idx' n_idx'; tf_dfg_v a_idx' n_idx' ]
            | None => [] (* should not happen *)
            end ) (List.seq 0 (length (nth (index_to_nat a_idx') buffer_needs [])))
        | None => [] (* should not happen *)
        end)
      (List.seq 0 (length buffer_needs)).

  Instance tf_dfg_states_fin2 : FiniteType2 tf_dfg_states.
  Proof.  
    unshelve econstructor.
    - intro s. destruct s.
      + exact (0, 0).
      + exact (1, finite_index state).
      + exact (2 + finite_index a_idx, finite_index n_idx).
      + exact (2 + (Datatypes.length (finite_elements (T:=(Vect.index (Datatypes.length buffer_needs))))) + finite_index a_idx, finite_index n_idx).
        
    - refine ([ [tf_dfg_done] ] ++ 
              [ map tf_dfg_s finite_elements ] ++ 
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
          change (vect_to_list (all_indices (Datatypes.length buffer_needs))) with (finite_elements (T:=Vect.index (Datatypes.length buffer_needs))).
          apply (finite_surjective a_idx).
        * rewrite map_nth_error with (d:=n_idx); auto. 
          change (index_to_nat n_idx) with (finite_index n_idx).
          rewrite finite_surjective. reflexivity.
    - intros n l Hn m x Hm.
      destruct n as [|n].
      { inversion Hn; subst. destruct m; inversion Hm; subst. reflexivity. timeout 10 scongruence use: nth_error_nil unfold: tfs_spec_states. }
      destruct n as [|n].
      { inversion Hn; subst. apply nth_error_map_inv in Hm. destruct Hm as [s [Hs ?]]; subst.
        apply finite_elements_index in Hs. subst. reflexivity. }
      
      rewrite nth_error_app2 in Hn by (simpl; lia).
      change (S (S n) - Datatypes.length [[tf_dfg_done]]) with (S n) in *.

      cbn [nth_error List.app] in Hn.
      destruct (lt_dec n (length (finite_elements (T := Vect.index (Datatypes.length buffer_needs))))) as [HLT | HGE].      
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
    - apply Forall_app; split; [| apply Forall_app; split].
      + repeat constructor. (* hammer *) timeout 10 sfirstorder.
      + repeat constructor. cbn [map]. rewrite map_map. apply NoDup_map_pair. apply finite_injective.
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
    end.

  Definition tfs_schedule : TFSchedule :=
    {|
      tfs_ctx := ctx;

      tfs_states := tf_dfg_states;
      tfs_states_size := tf_dfg_states_size;
      tfs_states_init := tf_dfg_states_init;
      
      tfs_inputs := inputs_var;
      tfs_inputs_size := inputs_var_size;
      tfs_inputs_fin := inputs_var_fin;

      tfs_outputs := outputs_var;
      tfs_outputs_size := outputs_var_size;
      tfs_outputs_fin := outputs_var_fin;

      tfs_action := spec_action;
      tfs_action_fin := spec_action_fin;

      tfs_map_to := maps_to;
      tfs_map_from := maps_from;

      tfs_schedule := schedule;
      tfs_done_signal := done_signal;
      tfs_reset_states := reset_states;
    |}.

End VariableScheduler.

Module Examples.

  Inductive dfge_s := x | y | z.
  Definition dfge_s_size (s: dfge_s) : nat := 4.

  Inductive dfge_i := in_A | in_B.
  Definition dfge_i_size (i: dfge_i) : nat := 4.

  Inductive dfge_o := out_A | out_B.
  Definition dfge_o_size (o: dfge_o) : nat := 4.

  Inductive dfge_a := action.

  Definition shd_ctx1 : TFSchedContext :=
    {|
      tfs_spec_states := dfge_s;
      tfs_spec_states_size := dfge_s_size;
      tfs_spec_states_init := fun x => Bits.zero;

      tfs_spec_inputs := dfge_i;
      tfs_spec_inputs_size := dfge_i_size;

      tfs_spec_outputs := dfge_o;
      tfs_spec_outputs_size := dfge_o_size;

      tfs_spec_action := dfge_a;
      tfs_spec_action_ops := fun a =>
        match a with
        | _ => {[  
            let $x := $in_A + #10;
            let $out_A := $x + #1
        ]}
        end;
    |}. 

  Goal True. 
    pose (cost := 10).
    pose (shd := shd_ctx1).
    pose (debug_dfg := build_dfg shd (action)); vm_compute in debug_dfg.
    pose (debug_cost := calc_backward_cost shd debug_dfg); vm_compute in debug_cost.
    pose (debug_cycle := calc_target_cycle cost debug_cost); vm_compute in debug_cycle.
    pose (debug_bufs := require_buffer shd debug_dfg debug_cycle); vm_compute in debug_bufs.
    pose (debug_sched := schedule shd cost (action)); vm_compute in debug_sched.
  Abort.

  Goal True. 
    pose (cost := 4).
    pose (shd := shd_ctx1).
    pose (debug_dfg := build_dfg shd (action)); vm_compute in debug_dfg.
    pose (debug_cost := calc_backward_cost shd debug_dfg); vm_compute in debug_cost.
    pose (debug_cycle := calc_target_cycle cost debug_cost); vm_compute in debug_cycle.
    pose (debug_bufs := require_buffer shd debug_dfg debug_cycle); vm_compute in debug_bufs.
    pose (debug_sched := schedule shd cost (action)); time vm_compute in debug_sched. (* TIME: 0.2 Seconds *)
  Abort.

  Definition shd_ctx2 : TFSchedContext :=
    {|
      tfs_spec_states := dfge_s;
      tfs_spec_states_size := dfge_s_size;
      tfs_spec_states_init := fun x => Bits.zero;

      tfs_spec_inputs := dfge_i;
      tfs_spec_inputs_size := dfge_i_size;

      tfs_spec_outputs := dfge_o;
      tfs_spec_outputs_size := dfge_o_size;

      tfs_spec_action := dfge_a;
      tfs_spec_action_ops := fun a =>
        match a with
        | _ => {[  
            let $x := $x * $x;
            (if $in_A then
              let $y := $x * $y + #1
            else
              pass
            );
            let $out_A := $y 
        ]}
        end;
    |}.

  Goal True. 
    pose (cost := 15).
    pose (shd := shd_ctx2).
    pose (debug_dfg := build_dfg shd (action)); vm_compute in debug_dfg.
    pose (debug_cost := calc_backward_cost shd debug_dfg); vm_compute in debug_cost.
    pose (debug_cycle := calc_target_cycle cost debug_cost); vm_compute in debug_cycle.
    pose (debug_bufs := require_buffer shd debug_dfg debug_cycle); vm_compute in debug_bufs.
    pose (debug_sched := schedule shd cost (action)); vm_compute in debug_sched.
  Abort.

  Goal True. 
    pose (cost := 5).
    pose (shd := shd_ctx2).
    pose (debug_dfg := build_dfg shd (action)); vm_compute in debug_dfg.
    pose (debug_cost := calc_backward_cost shd debug_dfg); vm_compute in debug_cost.
    pose (debug_cycle := calc_target_cycle cost debug_cost); vm_compute in debug_cycle.
    pose (debug_bufs := require_buffer shd debug_dfg debug_cycle); vm_compute in debug_bufs.
    pose (debug_sched := schedule shd cost (action)); time vm_compute in debug_sched.
  Abort.

  Definition no_precompute := schedule shd_ctx2 5 (action).
  Definition with_precompute := tc_compute (schedule shd_ctx2 5 (action)).

  Goal True.
    pose (debug1 := no_precompute).
    pose (debug2 := with_precompute).
    time vm_compute in debug1.
    time vm_compute in debug2.
  Abort.

  Definition shd_ctx3 : TFSchedContext :=
    {|
      tfs_spec_states := dfge_s;
      tfs_spec_states_size := dfge_s_size;
      tfs_spec_states_init := fun x => Bits.zero;

      tfs_spec_inputs := dfge_i;
      tfs_spec_inputs_size := dfge_i_size;

      tfs_spec_outputs := dfge_o;
      tfs_spec_outputs_size := dfge_o_size;

      tfs_spec_action := dfge_a;
      tfs_spec_action_ops := fun a =>
        match a with
        | _ => {[  
            let $x := $y;
            let $y := $z;
            let $z := $x
        ]}
        end;
    |}.

  Goal True. 
    pose (cost := 15).
    pose (shd := shd_ctx3).
    pose (debug_dfg := build_dfg shd (action)); vm_compute in debug_dfg.
    pose (debug_cost := calc_backward_cost shd debug_dfg); vm_compute in debug_cost.
    pose (debug_cycle := calc_target_cycle cost debug_cost); vm_compute in debug_cycle.
    pose (debug_bufs := require_buffer shd debug_dfg debug_cycle); vm_compute in debug_bufs.
    pose (debug_sched := schedule shd cost (action)); vm_compute in debug_sched.
  Abort.

End Examples.
