(*! The examples under both baselines of Scheduler/EvalModes.v, as
    Example_<name>_{allcrit,nocrit} at each example's own cost, plus the paper's
    lockbox at the paper's: Paper_Lockbox{A,B}, real and both baselines. !*)

Require Import Koika.Frontend.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Scheduler.EvalModes.
Require Import Trustformer.Backend.Lowering.
Require Trustformer.Examples.Lockbox.Spec.
Require Trustformer.Examples.LockboxTries.Spec.
Require Trustformer.Examples.LockboxTries.Taint.
Require Trustformer.Examples.Mars.Spec.
Require Trustformer.Examples.MarsSeq.Spec.
Require Trustformer.Examples.Negator.Spec.
Require Trustformer.Examples.SimpleLockbox.Spec.

(* An example's synthesis context [tf], rebuilt on the schedule [s]. *)
Ltac package_on s tf name :=
  exact (Interop.Backends.register (Lowering.package {|
    tf_sched_ctx := s;
    tf_action_encoding := tf_action_encoding tf;
    tf_action_encoding_inj := tf_action_encoding_inj tf;
    tf_action_names := tf_action_names tf |} name)).

(* [tf] rebuilt on the baseline of its own [tfs_schedule ctx cost]; fails to
   elaborate if an example stops being built that way. *)
Ltac baseline m sched tf name :=
  let s := eval red in sched in
  lazymatch s with
  | tfs_schedule ?ctx ?cost => package_on (tfs_schedule_eval m ctx cost) tf name
  end.

Definition lockbox_allcrit := ltac:(baseline AllCritical
  Lockbox.Spec.tf_schedule Lockbox.Spec.tf_ctx "Example_Lockbox_allcrit").
Definition lockbox_nocrit := ltac:(baseline NoneCritical
  Lockbox.Spec.tf_schedule Lockbox.Spec.tf_ctx "Example_Lockbox_nocrit").
Definition lockboxtries_allcrit := ltac:(baseline AllCritical
  LockboxTries.Spec.tf_schedule LockboxTries.Spec.tf_ctx "Example_LockboxTries_allcrit").
Definition lockboxtries_nocrit := ltac:(baseline NoneCritical
  LockboxTries.Spec.tf_schedule LockboxTries.Spec.tf_ctx "Example_LockboxTries_nocrit").
Definition mars_allcrit := ltac:(baseline AllCritical
  Mars.Spec.tf_schedule Mars.Spec.tf_ctx "Example_Mars_allcrit").
Definition mars_nocrit := ltac:(baseline NoneCritical
  Mars.Spec.tf_schedule Mars.Spec.tf_ctx "Example_Mars_nocrit").
Definition marsseq_allcrit := ltac:(baseline AllCritical
  MarsSeq.Spec.tf_schedule MarsSeq.Spec.tf_ctx "Example_MarsSeq_allcrit").
Definition marsseq_nocrit := ltac:(baseline NoneCritical
  MarsSeq.Spec.tf_schedule MarsSeq.Spec.tf_ctx "Example_MarsSeq_nocrit").
Definition negator_allcrit := ltac:(baseline AllCritical
  Negator.Spec.tf_schedule Negator.Spec.tf_ctx "Example_Negator_allcrit").
Definition negator_nocrit := ltac:(baseline NoneCritical
  Negator.Spec.tf_schedule Negator.Spec.tf_ctx "Example_Negator_nocrit").
Definition simplelockbox_allcrit := ltac:(baseline AllCritical
  SimpleLockbox.Spec.tf_schedule SimpleLockbox.Spec.tf_ctx "Example_SimpleLockbox_allcrit").
Definition simplelockbox_nocrit := ltac:(baseline NoneCritical
  SimpleLockbox.Spec.tf_schedule SimpleLockbox.Spec.tf_ctx "Example_SimpleLockbox_nocrit").

(* THE PAPER'S LOCKBOX, at the cost limit reproducing its figures (one buffer at
   [tries - 1], two cycles; see LockboxTries/Taint.v): A is fig:dfgA5, [tries]
   secret; B is fig:dfgB5, [tries] public with the PhiConst/PhiBranch rules. *)
Definition paper_cost := 4.
Local Notation ctxA := LockboxTries.Spec.tfs_ctx.
Local Notation ctxB := LockboxTries.Taint.ctxB_whitebox.
Local Notation tfL := LockboxTries.Spec.tf_ctx.

Definition paperA := ltac:(package_on
  (tfs_schedule ctxA paper_cost) tfL "Paper_LockboxA").
Definition paperA_allcrit := ltac:(package_on
  (tfs_schedule_eval AllCritical ctxA paper_cost) tfL "Paper_LockboxA_allcrit").
Definition paperA_nocrit := ltac:(package_on
  (tfs_schedule_eval NoneCritical ctxA paper_cost) tfL "Paper_LockboxA_nocrit").
Definition paperB := ltac:(package_on
  (tfs_schedule ctxB paper_cost) tfL "Paper_LockboxB").
Definition paperB_allcrit := ltac:(package_on
  (tfs_schedule_eval AllCritical ctxB paper_cost) tfL "Paper_LockboxB_allcrit").
Definition paperB_nocrit := ltac:(package_on
  (tfs_schedule_eval NoneCritical ctxB paper_cost) tfL "Paper_LockboxB_nocrit").

Set Extraction Output Directory "build".
Extraction "Example_Lockbox_allcrit.ml" lockbox_allcrit.
Extraction "Example_Lockbox_nocrit.ml" lockbox_nocrit.
Extraction "Example_LockboxTries_allcrit.ml" lockboxtries_allcrit.
Extraction "Example_LockboxTries_nocrit.ml" lockboxtries_nocrit.
Extraction "Example_Mars_allcrit.ml" mars_allcrit.
Extraction "Example_Mars_nocrit.ml" mars_nocrit.
Extraction "Example_MarsSeq_allcrit.ml" marsseq_allcrit.
Extraction "Example_MarsSeq_nocrit.ml" marsseq_nocrit.
Extraction "Example_Negator_allcrit.ml" negator_allcrit.
Extraction "Example_Negator_nocrit.ml" negator_nocrit.
Extraction "Example_SimpleLockbox_allcrit.ml" simplelockbox_allcrit.
Extraction "Example_SimpleLockbox_nocrit.ml" simplelockbox_nocrit.
Extraction "Paper_LockboxA.ml" paperA.
Extraction "Paper_LockboxA_allcrit.ml" paperA_allcrit.
Extraction "Paper_LockboxA_nocrit.ml" paperA_nocrit.
Extraction "Paper_LockboxB.ml" paperB.
Extraction "Paper_LockboxB_allcrit.ml" paperB_allcrit.
Extraction "Paper_LockboxB_nocrit.ml" paperB_nocrit.
