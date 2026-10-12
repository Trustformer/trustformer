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
Require Import IPR.Common.

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

  Corollary ipr_uniform :
    (* There is one emulator, seeing only the spec's public answers, *)
    exists e : IPR.Emulator.emulator (query ctx cost_limit) pub_outputs wires (atk_out ctx),
    (* such that for any trusted IPs meeting their datasheets and any trusted secret inputs, *)
    forall (ip: trusted_ip ctx cost_limit enc_sz enc enc_inj names) (src: trusted_source ctx),
      datasheet ctx cost_limit enc_sz enc enc_inj names ip ->
      (* and for any state the idle circuit may hold, *)
      forall c hs sp seen,
        at_rest ctx cost_limit enc_sz enc enc_inj names c sp ->
        (* no attacker can tell apart *)
        IPR.Machine.equivalent
          (* the real circuit started in that state *)
          (IPR.Definition.real_world
             (start_at (closed_circuit ctx cost_limit enc_sz enc enc_inj names ip src) (c, hs, seen))
             (driver ctx cost_limit enc_sz enc enc_inj names))
          (* from the spec started in that state, with the emulator playing the wires. *)
          (IPR.Definition.ideal_world
             (start_at (closed_spec ctx cost_limit src) (sp, seen)) e).
  Proof.
    exists (IPRBridge.e_wires ctx cost_limit enc_sz enc enc_inj names).
    intros ip src Hip c hs sp seen Hr.
    exact (IPRBridge.ipr_from ctx cost_limit enc_sz enc enc_inj names ip src Hip
             (c, hs, seen) (sp, seen) (conj Hr eq_refl)).
  Qed.

  Theorem synthesis_correct (ip: trusted_ip ctx cost_limit enc_sz enc enc_inj names)
      (src: trusted_source ctx) :
    (* For any trusted IPs meeting their datasheets and any trusted secret inputs, *)
    datasheet ctx cost_limit enc_sz enc enc_inj names ip ->
    (* whenever the idle circuit holds the same state as the spec, for any command, *)
    forall c hs sp seen (q: query ctx cost_limit),
      at_rest ctx cost_limit enc_sz enc enc_inj names c sp ->
      (* running the command on the circuit always finishes, *)
      (exists o s', IPR.Driver.dexec (IPR.Definition.mux (closed_circuit ctx cost_limit enc_sz enc enc_inj names ip src))
                      _ (driver ctx cost_limit enc_sz enc enc_inj names q) (c, hs, seen) (Result o s'))
      (* and whatever answer it gives, *)
      /\ forall o c' hs' seen',
           IPR.Driver.dexec (IPR.Definition.mux (closed_circuit ctx cost_limit enc_sz enc enc_inj names ip src))
             _ (driver ctx cost_limit enc_sz enc enc_inj names q) (c, hs, seen) (Result o (c', hs', seen')) ->
           (* the spec gives the same answer, *)
           exists sp', IPR.Machine.step (closed_spec ctx cost_limit src) (sp, seen) q (Result o (sp', seen'))
                       (* and the circuit is idle again, holding the spec's new state, secrets included. *)
                       /\ at_rest ctx cost_limit enc_sz enc enc_inj names c' sp'.
  Proof.
    intros Hip c hs sp seen q Hr.
    destruct (IPRBridge.bridge_functional ctx cost_limit enc_sz enc enc_inj names ip src Hip)
      as (_ & Hterm & Hcorrect).
    split.
    - exact (Hterm (c, hs, seen) (sp, seen) q (conj Hr eq_refl)).
    - intros o c' hs' seen' Hd.
      destruct (Hcorrect (c, hs, seen) (sp, seen) q o (c', hs', seen') (conj Hr eq_refl) Hd)
        as ([sp' seen2] & Hs & Hr' & Hseen).
      cbn [fst snd] in Hr', Hseen. subst seen2.
      exists sp'. split; [ exact Hs | exact Hr' ].
  Qed.

End Guarantees.
