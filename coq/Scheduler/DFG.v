(*! Data-flow graph datatypes for the variable scheduler.

    These live below `Contract.v` so that `TFSchedContext` can carry
    declassification rules, which are functions of a `dfg_state_t`.
    They depend only on the three specification variable types, never on
    `TFSchedContext` itself.
!*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.

Require Import Coq.Lists.List.
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
    (* SPIKE (W-b feasibility, 2026-09-09): value passes through from [arg];
       validity lags it.  Nothing emits this yet -- it exists to measure how
       much of the proof development breaks on a node whose validity is NOT the
       conjunction of its arguments' validities.
       SPIKE 2 (2026-09-11): [lat] is the declared latency, in COST units (so
       [lat / cost_limit] cycles).  Cost units rather than cycles only because
       [cost_fn] does not see [cost_limit]; the real design wants cycles, which
       is the ~27-site ripple INSIGHTS #13 describes and absorbs. *)
    | DFG_Stall (lat: nat) (arg: nid_t)
    (* SPIKE 2b (2026-09-11): THE REQUEST SIDE.  [DFG_Drive] puts a port WRITE
       into the graph, so it has a cycle and can be an argument.  [DFG_Sample]
       reads a trusted input through a TOKEN edge, so it stops being a
       [source_op] and acquires a defined sampling cycle.  With [DFG_Stall]
       between them a round trip finally has an edge to sit on -- which is
       precisely what Spike 1.6 found the pipeline could not express. *)
    | DFG_Drive (v: outputs_var) (arg: nid_t)
    | DFG_Sample (v: inputs_var) (tok: nid_t)
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
    (* EXPERIMENT (RESET-PLAN step 1/2): a scheduler-generated register for a
       driven port's write strobe.  The point is the SHAPE -- if the always half
       writes state vars rather than o_vars, [always_ops_no_out] should stay true
       with its existing proof. *)
    | tf_dfg_ov (o: outputs_var)
    .
        
End SchedulerTypes.

(* ===================================================================== *)
(* Declassification: the user's claim that [di_target] is recoverable     *)
(* from [di_sources] whenever every literal in [di_guard] holds.          *)
(* Blackbox is [sources = []] with [guard = []]; an unconditional         *)
(* inverter has [guard = []]; a phi rule carries a guard.                 *)
(* The matching proof obligation is [instance_sound] in                   *)
(* coq/Properties/IPR.v.                                                  *)
(* ===================================================================== *)

Record decl_instance := {
  di_target  : nid_t;
  di_sources : list nid_t;
  di_guard   : list (nid_t * bool);
}.

(* A reusable rule inspects the current DFG and emits instances, so users never
   write node ids by hand. *)
Definition decl_rule (states_var inputs_var outputs_var: Type) :=
  @dfg_state_t states_var inputs_var outputs_var -> list decl_instance.
