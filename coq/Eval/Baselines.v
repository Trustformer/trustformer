(*! The example designs synthesised under both evaluation baselines of
    Scheduler/EvalModes.v, as Example_<name>_allcrit and Example_<name>_nocrit.
    Each reads its context and cost off the example's own [tf_schedule]. !*)

Require Import Koika.Frontend.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Scheduler.EvalModes.
Require Import Trustformer.Backend.Lowering.
Require Trustformer.Examples.Lockbox.Spec.
Require Trustformer.Examples.LockboxTries.Spec.
Require Trustformer.Examples.Mars.Spec.
Require Trustformer.Examples.MarsSeq.Spec.
Require Trustformer.Examples.Negator.Spec.
Require Trustformer.Examples.SimpleLockbox.Spec.

(* [tf] rebuilt on the baseline of its own [tfs_schedule ctx cost]; fails to
   elaborate if an example stops being built that way. *)
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
