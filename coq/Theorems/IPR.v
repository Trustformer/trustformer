(*! NO SECRET LEAKS BY TIMING, ON THE CIRCUIT.  From any state at rest, idle cycles
    included, the Kôika circuit shows what an emulator with only query access to
    the spec shows, and it times each command from public views.  Proof: Internal/. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Backend.Lowering.
Require Export Trustformer.Theorems.Definitions.
Require Trustformer.Theorems.Internal.CircuitProof.

Section IPR.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation sched := (tfs_schedule ctx cost_limit).
  Context (enc_sz: nat) (enc: tfs_action sched -> bits_t enc_sz)
          (enc_inj: forall a b, enc a = enc b -> a = b)
          (names: Show (tfs_action sched)).

  Local Notation synth := (synth ctx cost_limit enc_sz enc enc_inj names).
  Local Notation tsched := (tf_sched_ctx synth).
  Local Notation reg_t :=
    (@_reg_t (tfs_states tsched) (tfs_inputs tsched) (tfs_outputs tsched) (tfs_ips tsched)).
  Hint Extern 0 (FiniteType reg_t) => exact (_reg_t_finite synth) : typeclass_instances.
  Local Notation wires := (forall f, Sig_denote (Sigma synth f)).
  Local Notation input_t :=
    (forall x : tfs_spec_inputs ctx, type_denote (tf_inputs_type (tfs_spec_inputs_size ctx) x)).
  Local Notation command := (tfs_action sched * input_t)%type.
  Local Notation circuit_state := (ContextEnv.(env_t) (R synth)).
  Local Notation src_sys_state :=
    (ContextEnv.(env_t) (tf_states_type (tfs_spec_states_size ctx))
     * ContextEnv.(env_t) (tf_outputs_type (tfs_spec_outputs_size ctx)))%type.

  Local Notation circuit_run := (circuit_run ctx cost_limit enc_sz enc enc_inj names).
  Local Notation at_rest := (at_rest ctx cost_limit enc_sz enc enc_inj names).
  Local Notation presents := (presents ctx cost_limit enc_sz enc enc_inj names).
  Local Notation ip_contract := (ip_contract ctx cost_limit enc_sz enc enc_inj names).
  Local Notation ideal_run := (ideal_run ctx cost_limit).

  (* From any state at rest, with the environment offering [cmds] and every IP
     keeping its datasheet, the circuit shows the ideal world's ready flag and
     outputs at every cycle; the emulator there never reads the spec's state. *)
  Theorem circuit_emulated (c0: circuit_state) (sp0: src_sys_state)
      (env: nat -> wires) (cmds: nat -> option command) :
    at_rest c0 sp0 ->
    (forall k, presents (env k) (cmds k)) ->
    ip_contract c0 env ->
    forall k,
      let e := snd (ideal_run sp0 cmds k) in
      ((circuit_run c0 env k).[tf_ready] = Ob~1 <-> em_ready e = true)
      /\ forall ov, (circuit_run c0 env k).[tf_out ov] = (em_shown e).[ov].
  Proof.
    exact (CircuitProof.circuit_emulated ctx cost_limit enc_sz enc enc_inj names c0 sp0 env cmds).
  Qed.

  (* Reset is at rest, holding the spec's initial state. *)
  Theorem reset_at_rest :
    at_rest (ContextEnv.(create) (r synth))
      (ContextEnv.(create) (tfs_spec_states_init ctx), ContextEnv.(create) (fun _ => Bits.zero)).
  Proof. exact (CircuitProof.reset_at_rest ctx cost_limit enc_sz enc enc_inj names). Qed.

End IPR.
