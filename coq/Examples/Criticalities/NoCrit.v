(*! Every example with NO phi critical (Scheduler/EvalModes.v): the
    no-protection baseline, extracted as Example_<name>_nocrit at its own cost. !*)

Require Import Koika.Frontend.
Require Import Trustformer.Scheduler.EvalModes.
Require Trustformer.Examples.Lockbox.Spec.
Require Trustformer.Examples.LockboxTries.Spec.
Require Trustformer.Examples.Mars.Spec.
Require Trustformer.Examples.MarsSeq.Spec.
Require Trustformer.Examples.Negator.Spec.
Require Trustformer.Examples.SimpleLockbox.Spec.

Definition lockbox := ltac:(baseline NoneCritical
  Lockbox.Spec.tf_schedule Lockbox.Spec.tf_ctx "Example_Lockbox_nocrit").
Definition lockboxtries := ltac:(baseline NoneCritical
  LockboxTries.Spec.tf_schedule LockboxTries.Spec.tf_ctx "Example_LockboxTries_nocrit").
Definition mars := ltac:(baseline NoneCritical
  Mars.Spec.tf_schedule Mars.Spec.tf_ctx "Example_Mars_nocrit").
Definition marsseq := ltac:(baseline NoneCritical
  MarsSeq.Spec.tf_schedule MarsSeq.Spec.tf_ctx "Example_MarsSeq_nocrit").
Definition negator := ltac:(baseline NoneCritical
  Negator.Spec.tf_schedule Negator.Spec.tf_ctx "Example_Negator_nocrit").
Definition simplelockbox := ltac:(baseline NoneCritical
  SimpleLockbox.Spec.tf_schedule SimpleLockbox.Spec.tf_ctx "Example_SimpleLockbox_nocrit").

Set Extraction Output Directory "build".
Extraction "Example_Lockbox_nocrit.ml" lockbox.
Extraction "Example_LockboxTries_nocrit.ml" lockboxtries.
Extraction "Example_Mars_nocrit.ml" mars.
Extraction "Example_MarsSeq_nocrit.ml" marsseq.
Extraction "Example_Negator_nocrit.ml" negator.
Extraction "Example_SimpleLockbox_nocrit.ml" simplelockbox.
