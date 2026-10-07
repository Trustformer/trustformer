(*! NO SECRET LEAKS BY TIMING, as an observer sees it.  The action finishes on
    the cycle [L_pub] computes from what the attacker sees -- the public inputs,
    and the public outputs before and after -- and up to that cycle the outputs
    stand at their pre-action values, from it at their post-action ones.  The
    proofs are in Internal/IPRProof.v and Declassification/Extract.v. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Export Trustformer.Theorems.Definitions.
Require Trustformer.Declassification.Extract.
Require Trustformer.Theorems.Internal.IPRProof.

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
  Proof.
    intros Hstart Hipc. cbv zeta.
    destruct (Extract.act_slot_exists ctx cost_limit act) as [a_idx Halign].
    rewrite <- (Extract.L_is_public ctx cost_limit act a_idx sp0 ss0 input resp
                  Halign Hstart Hipc).
    split.
    - exact (IPRProof.L_first_done ctx cost_limit act sp0 ss0 input resp Hstart).
    - exact (IPRProof.emulator_correct_L ctx cost_limit act sp0 ss0 input resp
               Hstart Hipc).
  Qed.

End IPR.
