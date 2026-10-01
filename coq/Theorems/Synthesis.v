(*! THE CIRCUIT COMPUTES THE DESIGN.  One Kôika cycle of the lowered package
    takes a state matching the abstract one to a state matching the abstract
    next cycle, for whichever action the command register selects.  Proved in
    Internal/SynthesisProof.v. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Backend.Lowering.
Require Export Trustformer.Theorems.Definitions.
Require Trustformer.Theorems.Internal.SynthesisProof.

Section SynthesisCorrectness.

  Context (tf_ctx: TFSynthContext).

  Local Notation sched_ctx := (tf_sched_ctx tf_ctx).
  Local Notation spec_action := (tfs_action sched_ctx).
  Local Notation spec_inputs := (tfs_inputs sched_ctx).
  Local Notation spec_inputs_size := (tfs_inputs_size sched_ctx).
  Local Notation st_env  := (ContextEnv.(env_t) (tf_states_type (tfs_states_size sched_ctx))).
  Local Notation out_env := (ContextEnv.(env_t) (tf_outputs_type (tfs_outputs_size sched_ctx))).
  Local Notation sys_state_t := (st_env * out_env)%type.
  Local Notation input_t :=
    (forall x : spec_inputs, type_denote (tf_inputs_type spec_inputs_size x)).
  Local Notation R := (R tf_ctx).
  Local Notation r := (r tf_ctx).
  Local Notation Sigma := (Sigma tf_ctx).
  Local Notation rules := (rules tf_ctx).
  Local Notation system_schedule := (system_schedule tf_ctx).

  Local Notation abstract_init_state := (abstract_init_state tf_ctx).
  Local Notation state_matches := (state_matches tf_ctx).
  Local Notation env_matches := (env_matches tf_ctx).
  Local Notation state_env_matches := (state_env_matches tf_ctx).
  Local Notation input_matches := (input_matches tf_ctx).
  Local Notation live_inputs_match := (live_inputs_match tf_ctx).

  (* The reset state the Kôika package starts in is the design's init state. *)
  Theorem initial_state_matches :
    forall (sys: sys_state_t),
      abstract_init_state sys ->
      state_matches sys ((ContextEnv).(create) r).
  Proof. exact (SynthesisProof.initial_state_matches tf_ctx). Qed.

  (* One cycle of the circuit is one cycle of [tfs_next_cycle]. *)
  Theorem synthesis_correct :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R)
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f)),
      state_matches sys r ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      live_inputs_match input sigma ->
      state_env_matches (tfs_next_cycle sched_ctx act sys input) act input
        (interp_cycle sigma rules system_schedule r).
  Proof. exact (SynthesisProof.synthesis_correct tf_ctx). Qed.

End SynthesisCorrectness.
