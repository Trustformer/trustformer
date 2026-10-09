(*! IPR ON THE CIRCUIT, as Athalye et al. define it (vendored in external/ipr/): the
    circuit and the spec, each closed over the same trusted environment, are IPR-
    equivalent through [driver].  Proofs: Internal/. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Backend.Lowering.
Require Export Trustformer.Theorems.IPRDefinitions.
Require Trustformer.Theorems.Internal.IPRBridge.
Require IPR.Definition.

Section Guarantees.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation sched := (tfs_schedule ctx cost_limit).
  Context (enc_sz: nat) (enc: tfs_action sched -> bits_t enc_sz)
          (enc_inj: forall a b, enc a = enc b -> a = b)
          (names: Show (tfs_action sched)).

  (* IPR, AS UPSTREAM DEFINES IT, for any trusted environment: IPs that meet their
     datasheets, and any source on the secure input ports.  With no IP and no
     secure port, the environment drives nothing and every wire is the attacker's. *)
  Theorem ipr (ip: trusted_ip ctx cost_limit enc_sz enc enc_inj names) (src: trusted_source ctx) :
    datasheet ctx cost_limit enc_sz enc enc_inj names ip ->
    IPR.Definition.IPR (closed_circuit ctx cost_limit enc_sz enc enc_inj names ip src)
                       (closed_spec ctx cost_limit src)
                       (driver ctx cost_limit enc_sz enc enc_inj names).
  Proof. exact (IPRBridge.ipr_holds ctx cost_limit enc_sz enc enc_inj names ip src). Qed.

End Guarantees.
