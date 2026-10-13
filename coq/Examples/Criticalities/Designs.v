(*! The Knox examples and MarsV2 as [tfs_schedule ctx cost], the shape
    [EvalModes.baseline] reads; MarsV2 with its extraction's placeholder IPs. !*)

Require Import Koika.Frontend.
Require Import Trustformer.Scheduler.Schedule.
Require Trustformer.Examples.Knox.Adder.Spec.
Require Trustformer.Examples.Knox.Counter.Spec.
Require Trustformer.Examples.Knox.Fifo.Spec.
Require Trustformer.Examples.Knox.Fifo1.Spec.
Require Trustformer.Examples.Knox.Fig2Backup.Spec.
Require Trustformer.Examples.Knox.Lockbox.Spec.
Require Trustformer.Examples.Knox.MultiLockbox.Spec.
Require Trustformer.Examples.Knox.Otp.Spec.
Require Trustformer.Examples.Knox.PasswordHasher.Spec.
Require Trustformer.Examples.Knox.PinBackup.Spec.
Require Trustformer.Examples.MarsV2.Spec.
Require Trustformer.Examples.LockboxTries.Spec.
Require Trustformer.Examples.LockboxTries.Taint.

Definition adder_sched := tfs_schedule Knox.Adder.Spec.tfs_ctx Knox.Adder.Spec.CL.
Definition counter_sched := tfs_schedule Knox.Counter.Spec.tfs_ctx Knox.Counter.Spec.CL.
Definition fifo_sched := tfs_schedule Knox.Fifo.Spec.tfs_ctx Knox.Fifo.Spec.CL.
Definition fifo1_sched := tfs_schedule Knox.Fifo1.Spec.tfs_ctx Knox.Fifo1.Spec.CL.
Definition fig2backup_sched := tfs_schedule Knox.Fig2Backup.Spec.tfs_ctx Knox.Fig2Backup.Spec.CL.
Definition lockbox_sched := tfs_schedule Knox.Lockbox.Spec.tfs_ctx Knox.Lockbox.Spec.CL.
Definition multilockbox_sched := tfs_schedule Knox.MultiLockbox.Spec.tfs_ctx Knox.MultiLockbox.Spec.CL.
Definition otp_sched := tfs_schedule Knox.Otp.Spec.tfs_ctx Knox.Otp.Spec.CL.
Definition pwhasher_sched := tfs_schedule Knox.PasswordHasher.Spec.tfs_ctx Knox.PasswordHasher.Spec.CL.
Definition pinbackup_sched := tfs_schedule Knox.PinBackup.Spec.tfs_ctx Knox.PinBackup.Spec.CL.

Definition marsv2_tf :=
  MarsV2.Spec.tf_ctx (@MarsV2.Spec.placeholder_digest _) (@MarsV2.Spec.placeholder_digest _).
Definition marsv2_sched := Eval cbv delta [MarsV2.Spec.tf_schedule] beta in
  MarsV2.Spec.tf_schedule (@MarsV2.Spec.placeholder_digest _) (@MarsV2.Spec.placeholder_digest _).

(* The running example, and its variant with [tries] public (Examples/LockboxTries/Taint.v). *)
Definition lockboxtries_sched := Eval cbv delta [LockboxTries.Spec.tf_schedule] in LockboxTries.Spec.tf_schedule.
Definition lockboxtries_public_sched := tfs_schedule LockboxTries.Taint.ctxB_whitebox 4.
