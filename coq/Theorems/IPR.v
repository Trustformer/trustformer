(*! NO SECRET LEAKS BY TIMING.  An action finishes on the cycle [L_pub] computes
    from the attacker's view, the outputs at their pre-action values until then
    and post-action ones after; likewise in sequence.  Proofs: Internal/. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Export Trustformer.Theorems.Definitions.
Require Trustformer.Theorems.Internal.IPRChain.

Require Import Coq.Lists.List.
Import ListNotations.

Section IPR.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation sched := (tfs_schedule ctx cost_limit).
  Local Notation s_sz := (tfs_spec_states_size ctx).
  Local Notation i_sz := (tfs_spec_inputs_size ctx).
  Local Notation o_sz := (tfs_spec_outputs_size ctx).
  Local Notation src_sys_state :=
    (ContextEnv.(env_t) (tf_states_type s_sz) * ContextEnv.(env_t) (tf_outputs_type o_sz))%type.
  Local Notation sched_sys_state :=
    (ContextEnv.(env_t) (tf_states_type (tfs_states_size sched))
     * ContextEnv.(env_t) (tf_outputs_type o_sz))%type.
  Local Notation input_t :=
    (forall x : tfs_spec_inputs ctx, type_denote (tf_inputs_type i_sz x)).
  Local Notation resp_val :=
    (forall p : tfs_ips sched, bits_t (ip_resp_sz (tfs_ip sched p))).
  Local Notation spec_run act sp input :=
    (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act)
       sp input).
  Local Notation ss_run := (run_n ctx cost_limit).

  Local Notation first_done := (first_done ctx cost_limit).
  Local Notation emulate := (emulate ctx).
  Local Notation L_pub := (L_pub ctx cost_limit).
  Local Notation observe := (observe ctx).
  Local Notation command := (tfs_action sched * input_t)%type.
  Local Notation queue_run := (queue_run ctx cost_limit).
  Local Notation queue_ip_contract := (queue_ip_contract ctx cost_limit).
  Local Notation spec_outputs_seq := (spec_outputs_seq ctx cost_limit).
  Local Notation emulate_seq := (emulate_seq ctx cost_limit).
  Local Notation emulate_progress := (emulate_progress ctx cost_limit).

  Theorem emulator_correct (act: tfs_action sched)
      (sp0: src_sys_state) (ss0: sched_sys_state)
      (input: input_t) (resp: nat -> resp_val) :
    start_rel ctx cost_limit sp0 ss0 ->
    Definitions.ip_contract ctx cost_limit act input resp ss0 ->
    let pre  := snd sp0 in
    let post := snd (spec_run act sp0 input) in
    let N    := L_pub act (observe input pre post) in
    first_done act input resp ss0 N
    /\ forall k, k <= N -> forall ov,
         (snd (ss_run k act input resp ss0)).[ov] = emulate pre post N k ov.
  Proof. exact (IPRChain.command_emulated ctx cost_limit act sp0 ss0 input resp). Qed.

  (* THE SAME OVER A SEQUENCE run back to back, the IPs keeping their datasheet on
     the actual run: at every cycle the outputs and the commands finished are
     computed from public views, so each command's completion cycle is public. *)
  Theorem emulator_correct_seq (q: list command)
      (sp0: src_sys_state) (ss0: sched_sys_state) (resp: nat -> resp_val) :
    start_rel ctx cost_limit sp0 ss0 ->
    queue_ip_contract q resp ss0 ->
    let obs := spec_outputs_seq q sp0 in
    forall k,
      fst (queue_run k q resp ss0) = skipn (emulate_progress (snd sp0) obs k) q
      /\ forall ov,
           (snd (snd (queue_run k q resp ss0))).[ov] = emulate_seq (snd sp0) obs k ov.
  Proof. exact (IPRChain.queue_emulated ctx cost_limit q sp0 ss0 resp). Qed.

End IPR.
