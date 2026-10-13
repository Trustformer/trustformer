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
Require Trustformer.Examples.Criticalities.Designs.

Definition lockbox := ltac:(baseline AllCritical
  Examples.Lockbox.Spec.tf_schedule Examples.Lockbox.Spec.tf_ctx "Example_Lockbox_allcrit").
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
Definition adder := ltac:(baseline AllCritical
  Designs.adder_sched Knox.Adder.Spec.tf_ctx "Knox_Adder_allcrit").
Definition counter := ltac:(baseline AllCritical
  Designs.counter_sched Knox.Counter.Spec.tf_ctx "Knox_Counter_allcrit").
Definition fifo := ltac:(baseline AllCritical
  Designs.fifo_sched Knox.Fifo.Spec.tf_ctx "Knox_Fifo_allcrit").
Definition fifo1 := ltac:(baseline AllCritical
  Designs.fifo1_sched Knox.Fifo1.Spec.tf_ctx "Knox_Fifo1_allcrit").
Definition fig2backup := ltac:(baseline AllCritical
  Designs.fig2backup_sched Knox.Fig2Backup.Spec.tf_ctx "Knox_Fig2Backup_allcrit").
Definition knoxlockbox := ltac:(baseline AllCritical
  Designs.lockbox_sched Knox.Lockbox.Spec.tf_ctx "Knox_Lockbox_allcrit").
Definition multilockbox := ltac:(baseline AllCritical
  Designs.multilockbox_sched Knox.MultiLockbox.Spec.tf_ctx "Knox_MultiLockbox_allcrit").
Definition otp := ltac:(baseline AllCritical
  Designs.otp_sched Knox.Otp.Spec.tf_ctx "Knox_Otp_allcrit").
Definition pwhasher := ltac:(baseline AllCritical
  Designs.pwhasher_sched Knox.PasswordHasher.Spec.tf_ctx "Knox_PwHasher_allcrit").
Definition pinbackup := ltac:(baseline AllCritical
  Designs.pinbackup_sched Knox.PinBackup.Spec.tf_ctx "Knox_PinBackup_allcrit").
Definition marsv2 := ltac:(baseline AllCritical
  Designs.marsv2_sched Designs.marsv2_tf "Example_MarsV2_allcrit").
Set Extraction Output Directory "build".
Extraction "Example_Lockbox_allcrit.ml" lockbox.
Extraction "Example_LockboxTries_allcrit.ml" lockboxtries.
Extraction "Example_Mars_allcrit.ml" mars.
Extraction "Example_MarsSeq_allcrit.ml" marsseq.
Extraction "Example_Negator_allcrit.ml" negator.
Extraction "Example_SimpleLockbox_allcrit.ml" simplelockbox.
Extraction "Knox_Adder_allcrit.ml" adder.
Extraction "Knox_Counter_allcrit.ml" counter.
Extraction "Knox_Fifo_allcrit.ml" fifo.
Extraction "Knox_Fifo1_allcrit.ml" fifo1.
Extraction "Knox_Fig2Backup_allcrit.ml" fig2backup.
Extraction "Knox_Lockbox_allcrit.ml" knoxlockbox.
Extraction "Knox_MultiLockbox_allcrit.ml" multilockbox.
Extraction "Knox_Otp_allcrit.ml" otp.
Extraction "Knox_PwHasher_allcrit.ml" pwhasher.
Extraction "Knox_PinBackup_allcrit.ml" pinbackup.
Extraction "Example_MarsV2_allcrit.ml" marsv2.
