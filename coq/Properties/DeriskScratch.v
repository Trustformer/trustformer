(* ==================================================================== *)
(* TEMPORARY DERISKING SCRATCH — DELETE WHEN DONE.                       *)
(*                                                                      *)
(* Purpose: D1 concrete validation of the buffer_inv / scheduler_done   *)
(* claims on a concrete example (SimpleLockbox).  This file is NOT part *)
(* of the proof development and must be removed before the campaign is  *)
(* considered clean.  Build ONLY this target:                           *)
(*   dune build coq/Properties/DeriskScratch.vo                         *)
(* Never let it flow into SchedulerSimulation.vo.                       *)
(* ==================================================================== *)

Require Import Koika.Frontend.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.
Require Import Trustformer.Examples.SimpleLockbox.
Require Import Trustformer.Examples.ConversionNegator.

(* --- D1 probe 1: does SimpleLockbox's DFG actually exercise buffers? --- *)
(* buffer_needs is a list (over actions) of lists of buffered nodes.
   If every inner list is empty, buffer_inv is vacuous here and this
   example proves nothing about buffer_inv_step. *)

Definition ctx := SimpleLockbox.tfs_ctx.
Definition climit := 10.

(* Length of buffer_needs = number of spec actions. *)
Compute (List.length (buffer_needs ctx climit)).

(* Per-action buffered-node lists (the thing buffer_inv quantifies over). *)
Compute (buffer_needs ctx climit).

(* Per-action DFG graph sizes + cost/cycle maps, to see multi-cycle depth. *)
Compute (List.map (fun a =>
           let d := build_dfg ctx a in
           (List.length (graph d),
            calc_target_cycle climit (calc_backward_cost ctx d)))
        (@finite_elements _ (tfs_spec_action_fin ctx))).

(* Raw backward costs per action (independent of cost_limit). *)
Compute (List.map (fun a => calc_backward_cost ctx (build_dfg ctx a))
        (@finite_elements _ (tfs_spec_action_fin ctx))).

(* Buffering only triggers when cost_limit is small enough to split the DFG
   across cycles.  Probe small limits to find one that actually buffers. *)
Compute (List.map (fun cl => (cl, buffer_needs ctx cl)) [1;2;3;4;5]).

(* --- D5 probe: does a RESIZE node's arg ever get buffered? (eval-convert crux) --- *)
(* List, per action, the graph as (nid, op_tag, sz, args) tuples, so we can spot
   DFG_Resize nodes and check whether their arg nid appears in the buffered set. *)
Definition op_tag {sv iv ov} (o: @dfg_op_t sv iv ov) : nat :=
  match o with
  | DFG_Const _ => 0 | DFG_Input _ => 1 | DFG_Var _ => 2
  | DFG_Unary _ _ => 3 | DFG_Binary _ _ _ => 4 | DFG_Resize _ => 5
  | DFG_Phi _ _ _ => 6 | DFG_Empty => 7
  end.

(* (nid, op_tag, args) per node for each action's DFG. *)
Compute (List.map (fun a =>
           List.map (fun n => (nid n, op_tag (op n), get_args ctx n))
                    (graph (build_dfg ctx a)))
        (@finite_elements _ (tfs_spec_action_fin ctx))).

(* Buffered nids at cost_limit=1 (the buffering instance). *)
Compute (List.map (fun a =>
           require_buffer ctx (build_dfg ctx a)
             (calc_target_cycle 1 (calc_backward_cost ctx (build_dfg ctx a))))
        (@finite_elements _ (tfs_spec_action_fin ctx))).

(* FINDINGS (see PLAN.md DERISK FINDINGS):
   - At cost_limit=10 (examples' default): buffer_needs = [[]; []] — VACUOUS.
   - The buffering instance is cost_limit=1 on fs_act_test: 3 buffered nodes
     [(3,(0,1)); (1,(1,32)); (6,(2,32))], target cycles up to 2 (max_cycle=2).
   - var_map OUTPUT nids = [1;6] (node 1 target cycle 2 = max_cycle, node 6 cycle 1).

   CONCRETE 32-bit vm_compute of the scheduler is INTRACTABLE (even one
   tfs_next_cycle cycle over tf_dfg_states w/ ContextEnv + convert casts hangs).
   Do NOT attempt a numeric run here.  The key soundness question was instead
   settled by ANALYSIS (no computation needed) — see PLAN.md / INSIGHTS.md
   [soundness] buffer_inv_step counterexample. *)

(* --- D6 probe: Resize around a computed value is not semantics-transparent. --- *)
Definition resize_ops (_: ConversionNegator.fs_action)
   : @tf_ops ConversionNegator.fs_states ConversionNegator.fs_inputs
         ConversionNegator.fs_outputs :=
   tf_ops_cons
      (tf_ops_base
         (tf_assign ConversionNegator.fs_st_val (tf_const 16)))
      (tf_ops_base
         (tf_output ConversionNegator.fs_out_val
            (tf_svar ConversionNegator.fs_st_val))).

Definition resize_ctx : TFSchedContext := {|
   tfs_spec_states := ConversionNegator.fs_states;
   tfs_spec_states_fin := _;
   tfs_spec_states_size := ConversionNegator.fs_states_size;
   tfs_spec_states_init := ConversionNegator.fs_states_init;
   tfs_spec_inputs := ConversionNegator.fs_inputs;
   tfs_spec_inputs_fin := _;
   tfs_spec_inputs_size := ConversionNegator.fs_inputs_size;
   tfs_spec_outputs := ConversionNegator.fs_outputs;
   tfs_spec_outputs_fin := _;
   tfs_spec_outputs_size := ConversionNegator.fs_outputs_size;
   tfs_spec_action := ConversionNegator.fs_action;
   tfs_spec_action_fin := _;
   tfs_spec_action_ops := resize_ops
|}.

Definition resize_act := ConversionNegator.fs_act_nop.
Definition resize_dfg := build_dfg resize_ctx resize_act.

Compute (List.map (fun n => (nid n, op_tag (op n), get_args resize_ctx n))
   (graph resize_dfg)).
Compute (var_map resize_dfg).

Definition resize_buffers := nth 0 (buffer_needs resize_ctx 1) [].
Compute (compile_dfg_aux resize_ctx 1 0 resize_dfg resize_buffers).

Definition resize_source_result :=
   tf_ops_run ConversionNegator.fs_states_size
      ConversionNegator.fs_inputs_size ConversionNegator.fs_outputs_size
      (resize_ops resize_act)
      (ContextEnv.(create) ConversionNegator.fs_states_init,
       ContextEnv.(create) (fun _ => Bits.zero))
      (fun _ => Bits.zero).
Compute (ContextEnv.(getenv) (snd resize_source_result)
   ConversionNegator.fs_out_val).
