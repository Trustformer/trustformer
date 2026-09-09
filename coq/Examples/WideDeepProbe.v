Require Import Koika.Frontend.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.
Require Import Trustformer.Examples.WideDeepSpike.
Require Import Coq.Lists.List.
Import ListNotations.

(* SPIKE probe: how deep and how wide did the scheduler actually go? *)
Definition dfg0 := build_dfg tfs_ctx fs_act_mix.
Definition nnodes := Eval vm_compute in (length (graph dfg0)).
Definition bufs := Eval vm_compute in (buffer_needs tfs_ctx 2).
Definition nbufs := Eval vm_compute in (map (@length _) bufs).
Definition bounds := Eval vm_compute in (action_bounds tfs_ctx 2 dfg0).

(* Regression: the spike must stay wide (256-bit buffers) and deep.  If a future
   change collapses this back to a shallow pipeline, these fail loudly. *)
Example probe_nodes : nnodes = 42. Proof. reflexivity. Qed.
Example probe_depth : nbufs = [15]. Proof. reflexivity. Qed.
Example probe_bounds : bounds = (16, 16). Proof. reflexivity. Qed.
