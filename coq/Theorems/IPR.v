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

  Local Notation wires := (forall f, Sig_denote (Sigma (synth ctx cost_limit enc_sz enc enc_inj names) f)).
  Local Notation pub_outputs :=
    (forall o, option (type_denote (tf_outputs_type (tfs_spec_outputs_size ctx) o))).

  (* ONE EMULATOR, chosen before the trusted environment and the start: it works for
     every IP meeting its datasheet, every source, and every start where the circuit
     rests holding the spec's state.  So no secret from either can reach its timing. *)
  Corollary ipr_uniform :
    exists e : IPR.Emulator.emulator (query ctx cost_limit) pub_outputs wires (atk_out ctx),
    forall (ip: trusted_ip ctx cost_limit enc_sz enc enc_inj names) (src: trusted_source ctx),
      datasheet ctx cost_limit enc_sz enc enc_inj names ip ->
      forall c hs sp seen,
        at_rest ctx cost_limit enc_sz enc enc_inj names c sp ->
        IPR.Machine.equivalent
          (IPR.Definition.real_world
             (start_at (closed_circuit ctx cost_limit enc_sz enc enc_inj names ip src) (c, hs, seen))
             (driver ctx cost_limit enc_sz enc enc_inj names))
          (IPR.Definition.ideal_world (start_at (closed_spec ctx cost_limit src) (sp, seen)) e).
  Proof.
    exists (IPRBridge.e_wires ctx cost_limit enc_sz enc enc_inj names).
    intros ip src Hip c hs sp seen Hr.
    exact (IPRBridge.ipr_from ctx cost_limit enc_sz enc enc_inj names ip src Hip
             (c, hs, seen) (sp, seen) (conj Hr eq_refl)).
  Qed.

End Guarantees.
