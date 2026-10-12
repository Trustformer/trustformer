(*! Every example with EVERY phi critical (Scheduler/EvalModes.v): the full
    protection baseline, extracted as Example_<name>_allcrit at its own cost. !*)

Require Import Koika.Frontend.
Require Import Trustformer.Scheduler.EvalModes.
Require Trustformer.Examples.Lockbox.Spec.
Require Trustformer.Examples.LockboxTries.Spec.
Require Trustformer.Examples.Mars.Spec.
Require Trustformer.Examples.MarsSeq.Spec.
Require Trustformer.Examples.Negator.Spec.
Require Trustformer.Examples.SimpleLockbox.Spec.

Definition lockbox := ltac:(baseline AllCritical
  Lockbox.Spec.tf_schedule Lockbox.Spec.tf_ctx "Example_Lockbox_allcrit").
Definition lockboxtries := ltac:(baseline AllCritical
  LockboxTries.Spec.tf_schedule LockboxTries.Spec.tf_ctx "Example_LockboxTries_allcrit").
Definition mars := ltac:(baseline AllCritical
  Mars.Spec.tf_schedule Mars.Spec.tf_ctx "Example_Mars_allcrit").
Definition marsseq := ltac:(baseline AllCritical
  MarsSeq.Spec.tf_schedule MarsSeq.Spec.tf_ctx "Example_MarsSeq_allcrit").
Definition negator := ltac:(baseline AllCritical
  Negator.Spec.tf_schedule Negator.Spec.tf_ctx "Example_Negator_allcrit").
Definition simplelockbox := ltac:(baseline AllCritical
  SimpleLockbox.Spec.tf_schedule SimpleLockbox.Spec.tf_ctx "Example_SimpleLockbox_allcrit").

Set Extraction Output Directory "build".
Extraction "Example_Lockbox_allcrit.ml" lockbox.
Extraction "Example_LockboxTries_allcrit.ml" lockboxtries.
Extraction "Example_Mars_allcrit.ml" mars.
Extraction "Example_MarsSeq_allcrit.ml" marsseq.
Extraction "Example_Negator_allcrit.ml" negator.
Extraction "Example_SimpleLockbox_allcrit.ml" simplelockbox.
