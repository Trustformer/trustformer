(*! NO SECRET LEAKS BY TIMING, as an observer sees it.  An attacker watching the
    outputs learns nothing the specification and its own published data do not
    already give: the outputs stand at the pre-action snapshot until the cycle
    [L_pub] computes, and at the post-action snapshot from there.  [L_pub] reads
    the action, its slot and the values the declassification rules recover --
    never state, never an input, never an IP answer -- so no secret can reach
    the cycle count.  The latency results these rest on, and the proofs of all
    of it, are in Internal/IPRProof.v. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Export Trustformer.Theorems.Definitions.
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
  Local Notation a_index := (Vect.index (length (buffer_needs ctx cost_limit))).
  Local Notation spec_run act sp input :=
    (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act)
       sp input).
  Local Notation ss_run := (run_n ctx cost_limit).

  Local Notation first_done := (first_done ctx cost_limit).
  Local Notation emulate := (emulate ctx).
  Local Notation L_pub := (L_pub ctx cost_limit).
  Local Notation vals_sound := (vals_sound ctx cost_limit).
  Local Notation selectors_extractable := (selectors_extractable ctx cost_limit).
  Local Notation sched_input := (sched_input ctx cost_limit).

  (* THE ATTACKER LEARNS NOTHING FROM THE RUN.  The action completes on the
     cycle [L_pub] computes -- and on no cycle before it -- and up to that cycle
     the outputs are what the emulator says they are: the pre-action snapshot
     until it, the post-action snapshot from it.

     [L_pub] takes the action, its slot in the buffer table, and the values the
     declassification rules recover from the published tables; no state, no
     input and no IP answer appears among its arguments, so no secret can reach
     the cycle count.  The two hypotheses on [vals] are what the rule library
     discharges: it answers with the run's own value wherever a node has
     settled, and it answers at all for the selector of every phi the analysis
     did not call critical.  [Declassification/Extract.v] instantiates both
     from the published tables, leaving a statement over those alone. *)
  Theorem emulator_correct (act: tfs_action sched) (a_idx: a_index)
      (vals: nid_t -> option (list bool))
      (sp0: src_sys_state) (ss0: sched_sys_state)
      (input: input_t) (resp: nat -> resp_val) :
    act_idx_aligned ctx cost_limit act a_idx ->
    start_rel ctx cost_limit sp0 ss0 ->
    Definitions.ip_contract ctx cost_limit act input resp ss0 ->
    (forall k, (forall i, 1 <= i <= k ->
                  ~ done_set ctx cost_limit (ss_run i act input resp ss0)) ->
       selectors_extractable act a_idx vals (ss_run k act input resp ss0)
         (sched_input input (resp k))) ->
    (forall k, (forall i, 1 <= i <= k ->
                  ~ done_set ctx cost_limit (ss_run i act input resp ss0)) ->
       vals_sound act a_idx vals (ss_run k act input resp ss0)
         (sched_input input (resp k))) ->
    first_done act input resp ss0 (L_pub act a_idx vals)
    /\ (forall k, k <= L_pub act a_idx vals ->
          forall ov, (snd (ss_run k act input resp ss0)).[ov]
                   = emulate (snd sp0) (snd (spec_run act sp0 input))
                       (L_pub act a_idx vals) k ov).
  Proof.
    intros Halign Hstart Hipc Hsel Hvals.
    rewrite <- (IPRProof.L_pub_correct ctx cost_limit act a_idx vals input resp
                  ss0 Halign (proj2 (proj2 Hstart)) Hsel Hvals).
    split.
    - exact (IPRProof.L_first_done ctx cost_limit act sp0 ss0 input resp Hstart).
    - exact (IPRProof.emulator_correct_L ctx cost_limit act sp0 ss0 input resp
               Hstart Hipc).
  Qed.

End IPR.
