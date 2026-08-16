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
  Context {externs_var: Type}.

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
    (* Call to a trusted external function; see Trustformer.Semantics.tf_externs.
       [src] feeds the argument register, [dly] is the end of the delay chain whose
       validity gates the result (campaign extern-calls-mvp, D9). *)
    | DFG_Ext (f: externs_var) (src: nid_t) (dly: nid_t)
    (* Identity, but costed at a full cycle so [require_buffer] buffers its argument:
       this is how a call's latency is realised (campaign extern-calls-mvp, D9). *)
    | DFG_Delay (arg: nid_t)
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
    (* Designated argument / result register of a trusted external function; the call
       itself is issued by the dedicated [rule_ext] (campaign extern-calls-mvp, D8). *)
    | tf_dfg_earg (f: externs_var)
    | tf_dfg_eres (f: externs_var)
    | tf_dfg_b (a_idx: Vect.index (length buffer_needs)) (n_idx: Vect.index (length (nth (index_to_nat a_idx) buffer_needs [])))
    | tf_dfg_v (a_idx: Vect.index (length buffer_needs)) (n_idx: Vect.index (length (nth (index_to_nat a_idx) buffer_needs [])))
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
Definition decl_rule (states_var inputs_var outputs_var externs_var: Type) :=
  @dfg_state_t states_var inputs_var outputs_var externs_var -> list decl_instance.
