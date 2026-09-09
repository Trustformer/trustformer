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

(* cost_fn ignores width, so the SAME 256-bit chain packs more operators per
   cycle as the limit rises -- the scheduler believes a 256-bit add costs 2,
   exactly as a 1-bit add does. *)
Definition bufs10 := Eval vm_compute in (map (@length _) (buffer_needs tfs_ctx 10)).
Definition bounds10 := Eval vm_compute in (action_bounds tfs_ctx 10 dfg0).
Definition bufs20 := Eval vm_compute in (map (@length _) (buffer_needs tfs_ctx 20)).
Definition bounds20 := Eval vm_compute in (action_bounds tfs_ctx 20 dfg0).
(* Same chain, same widths, three different cost limits.  cost_fn takes [sz] and
   discards it, so these numbers track the LIMIT and not any physical delay: at
   limit 20 the whole ten-operator 256-bit chain sits in ~2 cycles, i.e. five
   chained 256-bit adds in one combinational path.  Experiment on 2026-09-09:
   making add/sub cost [2 + sz/128] rebuilt the ENTIRE development green (only
   these pinned probe values changed, to 26/6/3) and left all eight 32-bit
   examples byte-identical -- so a width-aware cost model is free to adopt; only
   the choice of delay model is open. *)
Example probe_bounds10 : bounds10 = (4, 4). Proof. reflexivity. Qed.
Example probe_bounds20 : bounds20 = (2, 2). Proof. reflexivity. Qed.
