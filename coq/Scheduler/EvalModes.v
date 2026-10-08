(*! Evaluation baselines, outside every theorem: [tfs_schedule] with EVERY phi
    critical (full protection) or NONE (no side-channel protection).  Only the
    taint the code generator reads differs, so they follow the real scheduler. !*)

Require Import Koika.Frontend.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Backend.Lowering.

Require Import Coq.Lists.List.
Import ListNotations.

Inductive crit_mode := AllCritical | NoneCritical.

(* [Codegen.phi_crit] is [mem_nid c tainted && negb (declassified_at dfacts c pi)]:
   every node tainted and no fact makes it true at every phi, no node tainted
   makes it false. *)
Definition tfs_schedule_eval (m: crit_mode) (ctx: TFSchedContext) (cost_limit: nat)
  : TFSchedule :=
  tfs_schedule_bn ctx cost_limit (buffer_needs ctx cost_limit)
    (fun dfg => match m with
                | AllCritical => map nid (graph dfg)
                | NoneCritical => []
                end)
    (fun _ => []).

(* An example's [tf_ctx] rebuilt on the baseline of its own [tfs_schedule ctx
   cost], read off [sched]; fails to elaborate if the example stops being so. *)
Ltac baseline m sched tf name :=
  let s := eval red in sched in
  lazymatch s with
  | tfs_schedule ?ctx ?cost =>
      exact (Interop.Backends.register (Lowering.package {|
        tf_sched_ctx := tfs_schedule_eval m ctx cost;
        tf_action_encoding := tf_action_encoding tf;
        tf_action_encoding_inj := tf_action_encoding_inj tf;
        tf_action_names := tf_action_names tf |} name))
  end.
