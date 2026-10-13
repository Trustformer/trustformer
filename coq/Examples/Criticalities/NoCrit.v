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
Require Trustformer.Examples.Criticalities.Designs.

Definition lockbox := ltac:(baseline NoneCritical
  Examples.Lockbox.Spec.tf_schedule Examples.Lockbox.Spec.tf_ctx "Example_Lockbox_nocrit").
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
Definition adder := ltac:(baseline NoneCritical
  Designs.adder_sched Knox.Adder.Spec.tf_ctx "Knox_Adder_nocrit").
Definition counter := ltac:(baseline NoneCritical
  Designs.counter_sched Knox.Counter.Spec.tf_ctx "Knox_Counter_nocrit").
Definition fifo := ltac:(baseline NoneCritical
  Designs.fifo_sched Knox.Fifo.Spec.tf_ctx "Knox_Fifo_nocrit").
Definition fifo1 := ltac:(baseline NoneCritical
  Designs.fifo1_sched Knox.Fifo1.Spec.tf_ctx "Knox_Fifo1_nocrit").
Definition fig2backup := ltac:(baseline NoneCritical
  Designs.fig2backup_sched Knox.Fig2Backup.Spec.tf_ctx "Knox_Fig2Backup_nocrit").
Definition knoxlockbox := ltac:(baseline NoneCritical
  Designs.lockbox_sched Knox.Lockbox.Spec.tf_ctx "Knox_Lockbox_nocrit").
Definition multilockbox := ltac:(baseline NoneCritical
  Designs.multilockbox_sched Knox.MultiLockbox.Spec.tf_ctx "Knox_MultiLockbox_nocrit").
Definition otp := ltac:(baseline NoneCritical
  Designs.otp_sched Knox.Otp.Spec.tf_ctx "Knox_Otp_nocrit").
Definition pwhasher := ltac:(baseline NoneCritical
  Designs.pwhasher_sched Knox.PasswordHasher.Spec.tf_ctx "Knox_PwHasher_nocrit").
Definition pinbackup := ltac:(baseline NoneCritical
  Designs.pinbackup_sched Knox.PinBackup.Spec.tf_ctx "Knox_PinBackup_nocrit").
Definition marsv2 := ltac:(baseline NoneCritical
  Designs.marsv2_sched Designs.marsv2_tf "Example_MarsV2_nocrit").
Set Extraction Output Directory "build".
Extraction "Example_Lockbox_nocrit.ml" lockbox.
Extraction "Example_LockboxTries_nocrit.ml" lockboxtries.
Extraction "Example_Mars_nocrit.ml" mars.
Extraction "Example_MarsSeq_nocrit.ml" marsseq.
Extraction "Example_Negator_nocrit.ml" negator.
Extraction "Example_SimpleLockbox_nocrit.ml" simplelockbox.
Extraction "Knox_Adder_nocrit.ml" adder.
Extraction "Knox_Counter_nocrit.ml" counter.
Extraction "Knox_Fifo_nocrit.ml" fifo.
Extraction "Knox_Fifo1_nocrit.ml" fifo1.
Extraction "Knox_Fig2Backup_nocrit.ml" fig2backup.
Extraction "Knox_Lockbox_nocrit.ml" knoxlockbox.
Extraction "Knox_MultiLockbox_nocrit.ml" multilockbox.
Extraction "Knox_Otp_nocrit.ml" otp.
Extraction "Knox_PwHasher_nocrit.ml" pwhasher.
Extraction "Knox_PinBackup_nocrit.ml" pinbackup.
Extraction "Example_MarsV2_nocrit.ml" marsv2.
