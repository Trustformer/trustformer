(*! Data-flow graph datatypes for the variable scheduler.  Below `Contract.v`,
    so `TFSchedContext` can carry declassification rules over a `dfg_state_t`;
    these depend only on the three specification variable types. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.

Require Import Coq.Lists.List.
Import ListNotations.

Section SchedulerTypes.

  Context {states_var: Type}.
  Context {inputs_var: Type}.
  Context {outputs_var: Type}.
  Context {ips_var: Type}.

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
    (* [arg]'s value passes through; its validity lags by [lat] CYCLES, counted
       by the buffer this node gets ([compile_dfg_buffers]). *)
    | DFG_Stall (lat: nat) (arg: nid_t)
    (* A round trip: drive the request, stall, sample the answer.  [en] is the
       call's path condition, SYMBOLIC so a guard materialises no nodes, and a
       drive is a conditional SIDE EFFECT with no [var_map] entry. *)
    | DFG_Drive (p: ips_var) (arg: nid_t) (en: list (nid_t * bool))
    | DFG_Sample (p: ips_var) (tok: nid_t) (en: list (nid_t * bool))
    (* An ORDERING constraint and no value: valid when both arguments are, so a
       second call on an IP waits for the first to answer.  It carries no value,
       hence no relation between its width and its arguments. *)
    | DFG_Join (a: nid_t) (b: nid_t)
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
    (* The scheduler's register for an IP request's {strobe, payload}. *)
    | tf_dfg_ov (p: ips_var)
    .
        
End SchedulerTypes.

(* ===================================================================== *)
(* Declassification: the user's claim that [di_target] is recoverable     *)
(* from [di_sources] whenever every literal in [di_guard] holds.          *)
(* Blackbox is [sources = []] with [guard = []]; an unconditional         *)
(* inverter has [guard = []]; a phi rule carries a guard.                 *)
(* The matching proof obligation is [instance_sound] in                   *)
(* coq/Theorems/IPR.v.                                                  *)
(* ===================================================================== *)

Record decl_instance := {
  di_target  : nid_t;
  di_sources : list nid_t;
  di_guard   : list (nid_t * bool);
  (* HOW to recover it: the target's bits from the sources' bits, in the order
     [di_sources] lists them.  [instance_extracts] is the obligation that this
     agrees with the design, and the relational [instance_sound] follows. *)
  di_extract : list (list bool) -> list bool;
}.

(* A reusable rule inspects the current DFG and emits instances, so users never
   write node ids by hand. *)
Definition decl_rule (states_var inputs_var outputs_var ips_var: Type) :=
  @dfg_state_t states_var inputs_var outputs_var ips_var -> list decl_instance.
