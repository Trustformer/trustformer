Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.
Require Koika.BitsToLists.

Require Import Coq.Logic.FunctionalExtensionality.

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
      list_assoc_set_all_max cost_map ((nid node) :: get_args node) (cost + cost_fn (op node) (sz node))
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

  Definition public_dsts (dfg: dfg_state) : list (nid_t) :=
    map snd (filter (fun '(v, _) =>
      match v with
      | DFG_OVar _ => true
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

  (* Every node the attacker can derive a value for. Whitebox untainting is the
     saturation below; it must stay computable without the taint set, since the
     fold below consumes this as a seed. *)
  Definition untainted_roots (dfg: dfg_state) : list (nid_t) :=
    saturate (length (graph dfg)) dfg (public_dsts dfg).

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
      let self_tainted := match op node with
        | DFG_Var (DFG_SVar _) => true
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
      match mem (nid node) untainted with
        | inl m => taint_map
        | inr _ => if is_tainted then (nid node) :: taint_map else taint_map
      end
    in
    fold_left aux (graph dfg) [].


  (* Transitive constant-time tagging is deliberately absent: only a *derivable*
     latency is required, and a critical phi already waits for both branches.
     See agents/taint-tagging-soundness/PLAN.md issue E. *)

  (* Producer v2.  A base of facts "node [c] is derivable whenever guard [g]
     holds", seeded from [untainted_roots] at the empty guard and saturated by
     [decl_compose]: an instance fires once every one of its sources has some
     fact, and its target's guard is the instance's own guard conjoined with
     the chosen source guards.  A declassification may therefore rest on other
     *guarded* facts -- which is what the paper's lockbox needs, since PhiCUT's
     source is a phi node that is itself only guarded-derivable.

     DISJUNCTION is expressed by several entries for the same node, not by a
     disjunctive guard: "derivable under (A or B)" is not a provable statement
     (the two runs could satisfy different disjuncts and genuinely differ),
     whereas "derivable under A" and "derivable under B" separately are, and
     the consumer only ever needs the clause the current path implies.  Hence
     the Cartesian product below: one combined guard per way of picking a fact
     for each source. *)
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

  (* Constants and inputs hold the same value in any two runs, so they are
     derivable under no guard.  Seeding them is a cost fix as much as a
     precision one: otherwise a shared constant becomes a hub -- the target of
     every phi's downward instance and then a source for every other phi --
     which makes the fact base grow cubically in the nesting depth. *)
  Definition trivially_public (dfg: dfg_state) : list nid_t :=
    filter (fun k => match op (nth k (graph dfg)
                                 {| nid := 0; op := DFG_Empty; sz := 0 |}) with
                     | DFG_Const _ => true
                     | DFG_Input _ => true
                     | _ => false
                     end)
           (List.seq 1 (length (graph dfg) - 1)).

  Definition decl_facts (dfg: dfg_state) : list gfact :=
    gsaturate (length (graph dfg)) dfg
      (map (fun n => (n, [])) (untainted_roots dfg ++ trivially_public dfg)).

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


  (* First the expression, then the valid signal.  [tainted] and [dfacts] are
     threaded rather than recomputed, and [pi] is the path of selector literals
     under which this occurrence is compiled: criticality is per *occurrence*,
     since a declassification is only valid where its guard holds. *)

  (* A phi is critical at this occurrence when its condition is tainted and NO
     recorded guard for it is implied by the path. *)
  Definition phi_crit (tainted: list nid_t) (dfacts: list gfact)
      (c: nid_t) (pi: list lit) : bool :=
    mem_nid c tainted && negb (declassified_at dfacts c pi).

  (* A CRITICAL phi reads both branch validities unconditionally, so its
     branches must not be compiled under an extended path: a declassification
     that only holds on the selected side would leak through the AND.  A
     non-critical phi selects, so its branches do learn the selector. *)
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

  Definition phi_crit_reason (dfg: dfg_state) (c: nid_t) (pi: list lit)
    : option crit_reason :=
    if negb (mem_nid c (get_tainted dfg)) then None
    else
      let base := decl_facts dfg in
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
  Lemma phi_crit_reason_none (dfg: dfg_state) (c: nid_t) (pi: list lit) :
    phi_crit_reason dfg c pi = None
    <-> phi_crit (get_tainted dfg) (decl_facts dfg) c pi = false.
  Proof.
    unfold phi_crit_reason, phi_crit, declassified_at. cbv zeta.
    destruct (mem_nid c (get_tainted dfg)) eqn:Hm; cbn [negb andb];
      [ | split; intro H; reflexivity ].
    destruct (gfacts_of (decl_facts dfg) c) as [| g0 gs] eqn:Hgs;
      cbn [existsb negb].
    - destruct (find _ (decl_instances dfg)); split; intro H; discriminate.
    - destruct (guard_incl g0 pi || existsb (fun g => guard_incl g pi) gs);
        cbn [negb]; split; intro H; (reflexivity || discriminate).
  Qed.

  (* Walks the same cone [compile_dfg_expr_aux] does, under the same paths. *)
  Fixpoint crit_report_aux (dfg: dfg_state) (pi: list lit) (fuel: nat)
      (n: nid_t) (bufs: list (nid_t * (nat * sz_t))) : list crit_reason :=
    match fuel with
    | 0 => []
    | S fuel' =>
        match BitsToLists.list_assoc bufs n with
        | Some _ => []
        | None =>
            let node := nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |} in
            match op node with
            | DFG_Unary _ a => crit_report_aux dfg pi fuel' a bufs
            | DFG_Resize a => crit_report_aux dfg pi fuel' a bufs
            | DFG_Binary _ a1 a2 =>
                crit_report_aux dfg pi fuel' a1 bufs ++ crit_report_aux dfg pi fuel' a2 bufs
            | DFG_Phi c t e =>
                let crit := phi_crit (get_tainted dfg) (decl_facts dfg) c pi in
                (match phi_crit_reason dfg c pi with Some r => [r] | None => [] end)
                ++ crit_report_aux dfg pi fuel' c bufs
                ++ crit_report_aux dfg (phi_path crit c true pi) fuel' t bufs
                ++ crit_report_aux dfg (phi_path crit c false pi) fuel' e bufs
            | _ => []
            end
        end
    end.

  (* Entry point mirroring [compile_dfg_expr]: empty path, no buffer cuts. *)
  Definition crit_report (dfg: dfg_state) (n: nid_t) : list crit_reason :=
    crit_report_aux dfg [] (length (graph dfg)) n [].

  (* Everything the scheduler compiles for an action, in one list. *)
  Definition crit_report_all (dfg: dfg_state) : list crit_reason :=
    flat_map (fun v => crit_report dfg (snd v)) (var_map dfg).

  Fixpoint compile_dfg_expr_aux (tainted: list nid_t)
    (dfacts: list gfact) (pi: list lit)
    (fuel: nat) (a_idx: Vect.index (length buffer_needs)) (dfg: dfg_state) (nid: nid_t) (buffers: list (nid_t * (nat * sz_t))) 
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
          | DFG_Empty => (tf_const 0, tf_const 0) (* should not happen *)
          end
        end
    end.

  (* The analysis is evaluated once here; compilation starts at the empty path. *)
  Local Notation compile_dfg_expr fuel a_idx dfg n bufs :=
    (compile_dfg_expr_aux (get_tainted dfg) (decl_facts dfg) [] fuel a_idx dfg n bufs).

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

  (* ==================================================================== *)
  (* Helper infrastructure for schedule_no_dup                            *)
  (* ==================================================================== *)

  (* --- generic list helpers --- *)

  Lemma map_fst_filter_incl {K V} (p: K*V -> bool) (l: list (K*V)) k:
    In k (map fst (filter p l)) -> In k (map fst l).
  Proof.
    induction l as [|[k0 v0] l IH]; simpl; [tauto|].
    destruct (p (k0,v0)); simpl.
    - intros [->|Hin]; [left; reflexivity | right; auto].
    - intro Hin; right; auto.
  Qed.

  Lemma NoDup_map_fst_filter {K V} (p: K*V -> bool) (l: list (K*V)):
    NoDup (map fst l) -> NoDup (map fst (filter p l)).
  Proof.
    induction l as [|[k0 v0] l IH]; simpl; intro Hnd; [constructor|].
    inversion Hnd; subst.
    destruct (p (k0,v0)); simpl.
    - constructor.
      + intro Hin. apply map_fst_filter_incl in Hin. contradiction.
      + apply IH; assumption.
    - apply IH; assumption.
  Qed.

  Lemma nodup_map_fst_cons_filter (k: dfg_vars) (v: nid_t) (l: list (dfg_vars * nid_t)):
    NoDup (map fst l) ->
    NoDup (map fst ((k,v) :: filter (fun '(k', _) => if eq_dec k' k then false else true) l)).
  Proof.
    intro Hnd. simpl. constructor.
    - intro Hin. apply in_map_iff in Hin. destruct Hin as [[k' v'] [Heq Hin]].
      simpl in Heq; subst k'. apply filter_In in Hin. destruct Hin as [_ Hp].
      change ((if eq_dec k k then false else true) = true) in Hp.
      rewrite eq_dec_refl in Hp. discriminate Hp.
    - apply NoDup_map_fst_filter; assumption.
  Qed.

  Lemma list_assoc_none_not_in {K V} `{EqDec K} (l: list (K*V)) (k: K):
    BitsToLists.list_assoc l k = None -> ~ In k (map fst l).
  Proof.
    induction l as [|[k0 v0] l IH]; simpl; [tauto|].
    destruct (eq_dec k k0) as [->|Hneq].
    - discriminate.
    - intros Hnone [Heq|Hin]; [apply Hneq; symmetry; exact Heq | apply IH; assumption].
  Qed.

  (* --- state-monad invariant plumbing --- *)

  Definition vm_nd (s: dfg_state) : Prop := NoDup (map fst (var_map s)).
  Definition preserves (P: dfg_state -> Prop) {A} (m: M A) := forall s, P s -> P (snd (m s)).

  Lemma preserves_ret P {A} (x: A): preserves P (ret x).
  Proof. intros s Hs; exact Hs. Qed.

  Lemma preserves_bind P {A B} (m: M A) (f: A -> M B):
    preserves P m -> (forall x, preserves P (f x)) -> preserves P (bind m f).
  Proof.
    intros Hm Hf s Hs. unfold bind.
    destruct (m s) as [x s'] eqn:Hms.
    assert (P s') as Hs'.
    { specialize (Hm s Hs). rewrite Hms in Hm. exact Hm. }
    apply (Hf x s' Hs').
  Qed.

  Lemma emit_vm op sz: preserves vm_nd (emit op sz).
  Proof.
    intros s Hs. unfold emit, bind, get_state, put_state, ret; simpl. exact Hs.
  Qed.

  Lemma ensure_var_vm v: preserves vm_nd (ensure_var v).
  Proof.
    intros s Hs. unfold vm_nd, ensure_var.
    cbn [emit bind get_state put_state ret snd fst var_map].
    apply nodup_map_fst_cons_filter. exact Hs.
  Qed.

  Lemma get_var_vm v: preserves vm_nd (get_var v).
  Proof.
    intros s Hs. unfold get_var, bind, get_state.
    destruct (BitsToLists.list_assoc (var_map s) v).
    - exact Hs.
    - apply (ensure_var_vm v s Hs).
  Qed.

  Lemma set_var_vm v id: preserves vm_nd (set_var v id).
  Proof.
    intros s Hs. unfold vm_nd, set_var.
    cbn [bind get_state put_state ret snd fst var_map].
    apply nodup_map_fst_cons_filter. exact Hs.
  Qed.

  Lemma dataflow_expr_vm: forall e sz, preserves vm_nd (dataflow_expr e sz).
  Proof.
    induction e as [val | sv | iv | ov | uop e IHe
                    | bop e1 IHe1 e2 IHe2 | ec IHe1 et IHe2 ee IHe3];
      intros sz; cbn [dataflow_expr].
    - apply emit_vm.
    - apply preserves_bind; [apply get_var_vm|]. intro x.
      destruct (Nat.eqb (dfg_var_size (DFG_SVar sv)) sz); [apply preserves_ret | apply emit_vm].
    - apply preserves_bind; [apply emit_vm|]. intro x.
      destruct (Nat.eqb (inputs_var_size iv) sz); [apply preserves_ret | apply emit_vm].
    - apply preserves_bind; [apply get_var_vm|]. intro x.
      destruct (Nat.eqb (dfg_var_size (DFG_OVar ov)) sz); [apply preserves_ret | apply emit_vm].
    - destruct uop as [| source_size].
      + apply preserves_bind; [apply IHe|]. intro x. apply emit_vm.
      + apply preserves_bind; [apply IHe|]. intro x.
        apply emit_vm.
    - destruct bop;
        (apply preserves_bind; [apply IHe1| intro x1;
         apply preserves_bind; [apply IHe2| intro x2; apply emit_vm]]).
    - apply preserves_bind; [apply IHe1|]. intro xc.
      apply preserves_bind; [apply IHe2|]. intro xt.
      apply preserves_bind; [apply IHe3|]. intro xe. apply emit_vm.
  Qed.

  Lemma merge_loop_nd cond mt me: forall keys acc s,
    NoDup (map fst acc) ->
    NoDup (map fst (fst (merge_loop cond mt me keys acc s))).
  Proof.
    induction keys as [|[k kv] rest IH]; intros acc s Hnd; cbn [merge_loop].
    - exact Hnd.
    - destruct (BitsToLists.list_assoc acc k) eqn:Ha.
      + apply IH; exact Hnd.
      + unfold bind.
        destruct (merge_key cond k (BitsToLists.list_assoc mt k)
                    (BitsToLists.list_assoc me k) s) as [res_opt s1].
        destruct res_opt as [fid|].
        * apply IH. simpl. constructor.
          -- apply list_assoc_none_not_in in Ha. exact Ha.
          -- exact Hnd.
        * apply IH; exact Hnd.
  Qed.

  Lemma dataflow_ops_vm: forall ops, preserves vm_nd (dataflow_ops ops).
  Proof.
    induction ops as [bop | o1 IHops1 o2 IHops2 | oc ot IHops1 oe IHops2];
      cbn [dataflow_ops].
    - destruct bop as [ | dst expr | dst expr].
      + apply preserves_ret.
      + apply preserves_bind; [apply dataflow_expr_vm|]. intro x. apply set_var_vm.
      + apply preserves_bind; [apply dataflow_expr_vm|]. intro x. apply set_var_vm.
    - apply preserves_bind; [apply IHops1|]. intro x. apply IHops2.
    - intros s Hs.
      unfold bind. cbn [get_state put_state].
      destruct (dataflow_expr oc 1 s) as [xc s0].
      destruct (dataflow_ops ot s0) as [u1 s1].
      destruct (dataflow_ops oe {| graph := graph s1; var_map := var_map s0 |}) as [u2 s2].
      unfold merge_maps, vm_nd.
      destruct (merge_loop xc (var_map s1) (var_map s2)
                 (var_map s1 ++ var_map s2) [] s2) as [x0 s3] eqn:Hm.
      cbn [snd var_map].
      replace x0 with (fst (merge_loop xc (var_map s1) (var_map s2)
                 (var_map s1 ++ var_map s2) [] s2)) by (rewrite Hm; reflexivity).
      apply merge_loop_nd. constructor.
  Qed.

  Lemma build_dfg_vm a: NoDup (map fst (var_map (build_dfg a))).
  Proof.
    unfold build_dfg. simpl.
    destruct (dataflow_ops (spec_action_ops a)
                {| graph := [{| nid := 0; op := DFG_Empty; sz := 0 |}]; var_map := [] |})
      as [u s'] eqn:Hd.
    simpl.
    assert (vm_nd s') as Hnd.
    { pose proof (dataflow_ops_vm (spec_action_ops a)
        {| graph := [{| nid := 0; op := DFG_Empty; sz := 0 |}]; var_map := [] |}) as Hp.
      unfold preserves in Hp. specialize (Hp ltac:(unfold vm_nd; simpl; constructor)).
      rewrite Hd in Hp. exact Hp. }
    exact Hnd.
  Qed.

  (* --- generic NoDup-of-flat_map via a key --- *)

  Lemma NoDup_flat_map_key {A B} (f: A -> list B) (l: list A):
    NoDup l ->
    (forall x, In x l -> NoDup (f x)) ->
    (forall x y b, In x l -> In y l -> In b (f x) -> In b (f y) -> x = y) ->
    NoDup (flat_map f l).
  Proof.
    intros Hnd. induction Hnd as [| a l Hnotin Hnd IH]; intros Hin Hkey; simpl.
    - constructor.
    - apply NoDup_app.
      + apply Hin. left. reflexivity.
      + apply IH.
        * intros x Hx. apply Hin. right. exact Hx.
        * intros x y b Hx Hy Hbx Hby.
          apply (Hkey x y b (or_intror Hx) (or_intror Hy) Hbx Hby).
      + intros b Hba Hbrest.
        apply in_flat_map in Hbrest. destruct Hbrest as [y [Hy Hby]].
        assert (a = y) as Heq
          by apply (Hkey a y b (or_introl eq_refl) (or_intror Hy) Hba Hby).
        subst y. contradiction.
  Qed.

  Lemma nodup_map_inj_in {A K} (g: A -> K) (l: list A):
    NoDup (map g l) -> forall x y, In x l -> In y l -> g x = g y -> x = y.
  Proof.
    induction l as [|a l IH]; intros Hnd x y Hx Hy Hg; [inversion Hx|].
    simpl in Hnd. inversion Hnd; subst.
    destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
    - reflexivity.
    - exfalso. apply H1. rewrite Hg. apply in_map. exact Hy.
    - exfalso. apply H1. rewrite <- Hg. apply in_map. exact Hx.
    - apply IH; assumption.
  Qed.

  Lemma NoDup_flat_map_of_key {A B K} (g: A -> K) (f: A -> list B) (key: B -> K) (l: list A):
    NoDup (map g l) ->
    (forall x, In x l -> NoDup (f x)) ->
    (forall x b, In x l -> In b (f x) -> key b = g x) ->
    NoDup (flat_map f l).
  Proof.
    intros Hnd Hf Hkey. apply NoDup_flat_map_key.
    - apply NoDup_map_inv with (f:=g); exact Hnd.
    - exact Hf.
    - intros x y b Hx Hy Hbx Hby.
      apply (nodup_map_inj_in g l Hnd x y Hx Hy).
      rewrite <- (Hkey x b Hx Hbx). rewrite <- (Hkey y b Hy Hby). reflexivity.
  Qed.

  (* --- get_sizes_and_idx assigns indices 0,1,2,... --- *)

  Lemma fold_idx_map (dfg: dfg_state): forall nodes acc i,
    map (fun '(_, x) => fst x) (rev (fst (fold_left
      (fun '(acc0, idx) nid =>
         let node := nth nid (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |} in
         ((nid, (idx, sz node)) :: acc0, S idx)) nodes (acc, i))))
    = map (fun '(_, x) => fst x) (rev acc) ++ seq i (length nodes).
  Proof.
    induction nodes as [|nid rest IH]; intros acc i.
    - simpl. rewrite app_nil_r. reflexivity.
    - cbn [fold_left length]. rewrite IH.
      cbn [rev]. rewrite map_app. cbn [map]. cbn [seq].
      rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma gsi_idx_nodup (dfg: dfg_state) (nodes: list nid_t):
    NoDup (map (fun '(_, x) => fst x) (get_sizes_and_idx dfg nodes)).
  Proof.
    unfold get_sizes_and_idx. rewrite fold_idx_map. simpl. apply seq_NoDup.
  Qed.

  (* --- flat_map composition helpers --- *)

  Lemma flat_map_flat_map {A B C} (g: B -> list C) (h: A -> list B) (l: list A):
    flat_map g (flat_map h l) = flat_map (fun x => flat_map g (h x)) l.
  Proof.
    induction l as [|a l IH]; simpl; [reflexivity|].
    rewrite flat_map_app, IH. reflexivity.
  Qed.

  Lemma flat_map_map {A B C} (f: B -> list C) (g: A -> B) (l: list A):
    flat_map f (map g l) = flat_map (fun x => f (g x)) l.
  Proof.
    induction l as [|a l IH]; simpl; [reflexivity | rewrite IH; reflexivity].
  Qed.

  Lemma NoDup_map_Some {A} (l: list A): NoDup l -> NoDup (map Some l).
  Proof.
    induction 1 as [|x l Hx Hnd IH]; simpl; constructor; [| exact IH].
    intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Heq Hy]].
    injection Heq as ->. contradiction.
  Qed.

  (* --- the op-tag function used by tfs_ops_no_duplicates --- *)

  Notation OPTAG :=
    (fun op => match op with
       | tf_assign dst _ => [StOp dst]
       | tf_output dst _ => [OutOp dst]
       | _ => []
       end).

  (* --- buffer-op tags --- *)

  Lemma buffers_tags_in (idx: nat) (DFG: dfg_state)
        (BUF: list (nid_t * (nat * sz_t))) t:
    In t (flat_map OPTAG (compile_dfg_buffers idx DFG BUF)) ->
    exists a' n', t = StOp (tf_dfg_b a' n') \/ t = StOp (tf_dfg_v a' n').
  Proof.
    intro Hin. apply in_flat_map in Hin. destruct Hin as [op [Hop Ht]].
    unfold compile_dfg_buffers in Hop.
    destruct (index_of_nat (length buffer_needs) idx) as [a'|]; [| destruct Hop].
    apply in_flat_map in Hop. destruct Hop as [[nid x] [_ Hop]].
    destruct (index_of_nat _ (fst x)) as [n'|]; [| destruct Hop].
    match goal with
    | Hop : In op (let '(_, _) := ?E in _) |- _ =>
        destruct E as [expr valid]
    end.
    simpl in Hop. destruct Hop as [<-|[<-|[]]]; simpl in Ht.
    - destruct Ht as [<-|[]]. exists a', n'. left. reflexivity.
    - destruct Ht as [<-|[]]. exists a', n'. right. reflexivity.
  Qed.

  Lemma buffers_tags_nodup (idx: nat) (DFG: dfg_state)
        (BUF: list (nid_t * (nat * sz_t))):
    NoDup (map (fun '(_, x) => fst x) BUF) ->
    NoDup (flat_map OPTAG (compile_dfg_buffers idx DFG BUF)).
  Proof.
    intro HBUF. unfold compile_dfg_buffers.
    destruct (index_of_nat (length buffer_needs) idx) as [a'|]; [| simpl; constructor].
    rewrite flat_map_flat_map.
    apply NoDup_flat_map_of_key
      with (g := fun '(_, x) => fst x)
           (key := fun t => match t with
                    | StOp (tf_dfg_b _ n) => index_to_nat n
                    | StOp (tf_dfg_v _ n) => index_to_nat n
                    | _ => 0
                    end).
    - exact HBUF.
    - intros [nid x] _.
      destruct (index_of_nat _ (fst x)) as [n'|]; [| simpl; constructor].
      match goal with |- context[let '(_, _) := ?E in _] => destruct E as [expr valid] end.
      simpl. apply NoDup_cons; [simpl; intros [H|[]]; discriminate H|].
      apply NoDup_cons; [simpl; tauto | apply NoDup_nil].
    - intros [nid x] b _ Hb.
      destruct (index_of_nat _ (fst x)) as [n'|] eqn:Hn; [| destruct Hb].
      match goal with
      | Hb : In b (flat_map _ (let '(_, _) := ?E in _)) |- _ =>
          destruct E as [expr valid]
      end.
      simpl in Hb. destruct Hb as [<-|[<-|[]]]; simpl;
        apply index_to_nat_of_nat in Hn; exact Hn.
  Qed.

  (* --- final-op tags --- *)

  Lemma final_tags_in (idx: nat) (DFG: dfg_state)
        (BUF: list (nid_t * (nat * sz_t))) t:
    In t (flat_map OPTAG (compile_dfg_aux idx DFG BUF)) ->
    (exists sv, t = StOp (tf_dfg_s sv)) \/ (exists ov, t = OutOp ov).
  Proof.
    intro Hin. apply in_flat_map in Hin. destruct Hin as [op [Hop Ht]].
    unfold compile_dfg_aux in Hop.
    destruct (index_of_nat (length buffer_needs) idx) as [a'|]; [| destruct Hop].
    apply in_map_iff in Hop. destruct Hop as [[var nid] [Heq _]].
    match goal with
    | Heq : (let '(_, _) := ?E in _) = op |- _ =>
        destruct E as [expr valid]
    end.
    destruct var as [sv|ov]; subst op; simpl in Ht.
    - destruct Ht as [<-|[]]. left. exists sv. reflexivity.
    - destruct Ht as [<-|[]]. right. exists ov. reflexivity.
  Qed.

  Lemma final_tags_nodup (idx: nat) (DFG: dfg_state)
        (BUF: list (nid_t * (nat * sz_t))):
    NoDup (map fst (var_map DFG)) ->
    NoDup (flat_map OPTAG (compile_dfg_aux idx DFG BUF)).
  Proof.
    intro HDFG. unfold compile_dfg_aux.
    destruct (index_of_nat (length buffer_needs) idx) as [a'|]; [| simpl; constructor].
    rewrite flat_map_map.
    apply NoDup_flat_map_of_key
      with (g := fun p => Some (fst p))
           (key := fun t => match t with
                    | StOp (tf_dfg_s sv) => Some (DFG_SVar sv)
                    | OutOp ov => Some (DFG_OVar ov)
                    | _ => None
                    end).
    - rewrite <- (map_map fst Some). apply NoDup_map_Some. exact HDFG.
    - intros [var nid] _.
      match goal with |- context[compile_dfg_expr ?f ?a ?d ?n ?b] =>
        destruct (compile_dfg_expr f a d n b) as [expr valid] end.
      destruct var as [sv|ov]; simpl; apply NoDup_cons; solve [apply NoDup_nil | simpl; tauto].
    - intros [var nid] b _ Hb.
      match goal with
      | Hb : context[compile_dfg_expr ?f ?a ?d ?n ?bf] |- _ =>
          destruct (compile_dfg_expr f a d n bf) as [expr valid]
      end.
      destruct var as [sv|ov]; simpl in Hb; destruct Hb as [<-|[]]; reflexivity.
  Qed.

  (* --- assembly --- *)

  Lemma schedule_no_dup_aux (idx: nat) (DFG: dfg_state)
        (BUF: list (nid_t * (nat * sz_t))):
    NoDup (map fst (var_map DFG)) ->
    NoDup (map (fun '(_, x) => fst x) BUF) ->
    NoDup (flat_map OPTAG
      ((compile_dfg_valid idx DFG BUF :: compile_dfg_buffers idx DFG BUF)
       ++ compile_dfg_aux idx DFG BUF)).
  Proof.
    intros HDFG HBUF.
    assert (Hval: flat_map OPTAG
        (compile_dfg_valid idx DFG BUF :: compile_dfg_buffers idx DFG BUF)
      = StOp tf_dfg_done :: flat_map OPTAG (compile_dfg_buffers idx DFG BUF)).
    { unfold compile_dfg_valid. reflexivity. }
    rewrite flat_map_app, Hval, <- app_comm_cons.
    apply NoDup_cons.
    - rewrite in_app_iff. intros [Hb|Hf].
      + apply buffers_tags_in in Hb. destruct Hb as [a' [n' [Hb|Hb]]]; discriminate Hb.
      + apply final_tags_in in Hf. destruct Hf as [[sv Hf]|[ov Hf]]; discriminate Hf.
    - apply NoDup_app.
      + apply buffers_tags_nodup. exact HBUF.
      + apply final_tags_nodup. exact HDFG.
      + intros x Hxb Hxf.
        apply buffers_tags_in in Hxb. apply final_tags_in in Hxf.
        destruct Hxb as [a' [n' [-> | ->]]];
          destruct Hxf as [[sv Hs]|[ov Ho]]; discriminate.
  Qed.


  Theorem schedule_no_dup: forall a, tfs_ops_no_duplicates (fst (schedule a) ++ snd (schedule a)).
  Proof.
    intros a. unfold tfs_ops_no_duplicates, schedule. cbn [fst snd].
    apply schedule_no_dup_aux.
    - set (i := spec_action_index a).
      destruct (lt_dec i (length (map build_dfg spec_all_actions))) as [Hlt|Hge].
      + pose proof (nth_In (map build_dfg spec_all_actions)
                     {| graph := []; var_map := [] |} Hlt) as HIn.
        apply in_map_iff in HIn. destruct HIn as [a' [Heq _]].
        rewrite <- Heq. apply build_dfg_vm.
      + rewrite nth_overflow by lia. simpl. constructor.
    - set (i := spec_action_index a).
      match goal with
      | |- NoDup (map _ (nth _ ?BUFS _)) =>
        destruct (lt_dec i (length BUFS)) as [Hlt|Hge];
        [ pose proof (nth_In BUFS ([]:list (nid_t * (nat * sz_t))) Hlt) as HIn
        | rewrite nth_overflow by lia; simpl; constructor ]
      end.
      apply in_map_iff in HIn. destruct HIn as [[dfg cm] [Heq _]].
      rewrite <- Heq. apply gsi_idx_nodup.
  Qed.

  Theorem schedule_done_assigned: forall a,    In (StOp done_signal)
       (flat_map (fun op =>
          match op with
          | tf_assign dst _ => [StOp dst]
          | tf_output dst _ => [OutOp dst]
          | _ => []
          end) (fst (schedule a))).
  Proof.
    intros a. unfold schedule, done_signal, compile_dfg_valid. cbn [fst flat_map app].
    left. reflexivity.
  Qed.

  Theorem reset_states_nodup: NoDup reset_states.
  Proof.
    unfold reset_states.
    (* recover the a-index and n-index from an element *)
    pose (a_of := fun v : tf_dfg_states =>
      match v with
      | tf_dfg_b a _ => index_to_nat a
      | tf_dfg_v a _ => index_to_nat a
      | _ => 0
      end).
    pose (n_of := fun v : tf_dfg_states =>
      match v with
      | tf_dfg_b _ n => index_to_nat n
      | tf_dfg_v _ n => index_to_nat n
      | _ => 0
      end).
    apply NoDup_flat_map_key.
    - apply seq_NoDup.
    - (* each outer chunk is NoDup *)
      intros a_idx _.
      destruct (index_of_nat (length buffer_needs) a_idx) as [a'|] eqn:Ha;
        [| constructor].
      apply NoDup_flat_map_key.
      + apply seq_NoDup.
      + (* each inner chunk [b; v] is NoDup *)
        intros n_idx _.
        destruct (index_of_nat _ n_idx) as [n'|] eqn:Hn; [| constructor].
        repeat constructor.
        * simpl. intros [H | []]. discriminate H.
        * simpl. tauto.
      + (* inner disjointness: element recovers its n-index *)
        intros x y b Hx Hy Hbx Hby.
        assert (forall m b0, In b0 (match index_of_nat _ m with
                              | Some n' => [tf_dfg_b a' n'; tf_dfg_v a' n']
                              | None => [] end) -> n_of b0 = m) as Hrec.
        { intros m b0 Hb0. destruct (index_of_nat _ m) as [n'|] eqn:Hm; [| destruct Hb0].
          apply index_to_nat_of_nat in Hm.
          simpl in Hb0. destruct Hb0 as [<- | [<- | []]]; simpl; exact Hm. }
        rewrite <- (Hrec x b Hbx). rewrite <- (Hrec y b Hby). reflexivity.
    - (* outer disjointness: element recovers its a-index *)
      intros x y b Hx Hy Hbx Hby.
      assert (forall m b0, In b0 (match index_of_nat (length buffer_needs) m with
                            | Some a' => flat_map (fun n_idx =>
                                match index_of_nat (length (nth (index_to_nat a') buffer_needs [])) n_idx with
                                | Some n' => [tf_dfg_b a' n'; tf_dfg_v a' n']
                                | None => [] end)
                                (List.seq 0 (length (nth (index_to_nat a') buffer_needs [])))
                            | None => [] end) -> a_of b0 = m) as Hrec.
      { intros m b0 Hb0. destruct (index_of_nat (length buffer_needs) m) as [a'|] eqn:Hm;
          [| destruct Hb0].
        apply index_to_nat_of_nat in Hm.
        apply in_flat_map in Hb0. destruct Hb0 as [n_idx [_ Hb0]].
        destruct (index_of_nat _ n_idx) as [n'|] eqn:Hn; [| destruct Hb0].
        simpl in Hb0. destruct Hb0 as [<- | [<- | []]]; simpl; exact Hm. }
      rewrite <- (Hrec x b Hbx). rewrite <- (Hrec y b Hby). reflexivity.
  Qed.

  Theorem reset_states_init_zero: forall v, In v reset_states -> tf_dfg_states_init v = Bits.zero.
  Proof.
    intros v Hin. unfold reset_states in Hin.
    apply in_flat_map in Hin. destruct Hin as [a_idx [_ Hin]].
    destruct (index_of_nat (length buffer_needs) a_idx) as [a_idx'|]; [|contradiction].
    apply in_flat_map in Hin. destruct Hin as [n_idx [_ Hin]].
    destruct (index_of_nat _ n_idx) as [n_idx'|]; [|contradiction].
    simpl in Hin. destruct Hin as [<-|[<-|[]]]; reflexivity.
  Qed.

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
      tfs_schedule_no_duplicates := schedule_no_dup;
      tfs_done_signal_size := eq_refl;
      tfs_done_signal_assigned_by_always := schedule_done_assigned;
      tfs_reset_states_nodup := reset_states_nodup;
      tfs_reset_states_init_zero := reset_states_init_zero;
    |}.

End VariableScheduler.

(* Keeps every existing use site unchanged while the taint set is computed once
   per top-level call rather than at every phi. *)
Notation compile_dfg_expr ctx cost_limit fuel a_idx dfg n bufs :=
  (compile_dfg_expr_aux ctx cost_limit (get_tainted ctx dfg) (decl_facts ctx dfg) []
     fuel a_idx dfg n bufs).

(* Same, at an explicit path: proofs that recurse into phi branches need it. *)
Notation compile_dfg_expr_at ctx cost_limit pi fuel a_idx dfg n bufs :=
  (compile_dfg_expr_aux ctx cost_limit (get_tainted ctx dfg) (decl_facts ctx dfg) pi
     fuel a_idx dfg n bufs).

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
      tfs_spec_decls := [];
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
      tfs_spec_decls := [];
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
      tfs_spec_decls := [];
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
