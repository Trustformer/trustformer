(*! THE SCHEDULER IS CORRECT.  One source step of an action equals iterating the
    scheduled cycle until done, registers mapped back by [maps_from], and it ends
    in a start state for the next action.  Proof: Internal/SchedulerRoundTrip.v. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Export Trustformer.Theorems.Definitions.
Require Trustformer.Theorems.Internal.SchedulerRoundTrip.

Section SchedulerSimulation.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation sched := (tfs_schedule ctx cost_limit).
  Local Notation s_sz := (tfs_spec_states_size ctx).
  Local Notation i_sz := (tfs_spec_inputs_size ctx).
  Local Notation o_sz := (tfs_spec_outputs_size ctx).
  Local Notation bneeds := (buffer_needs ctx cost_limit).
  Local Notation src_sys_state :=
    (ContextEnv.(env_t) (tf_states_type s_sz) * ContextEnv.(env_t) (tf_outputs_type o_sz))%type.
  Local Notation sched_sys_state :=
    (ContextEnv.(env_t) (tf_states_type (tfs_states_size sched))
     * ContextEnv.(env_t) (tf_outputs_type o_sz))%type.
  Local Notation input_t :=
    (forall x : tfs_spec_inputs ctx, type_denote (tf_inputs_type i_sz x)).
  Local Notation resp_val :=
    (forall p : tfs_ips sched, bits_t (ip_resp_sz (tfs_ip sched p))).

  Local Notation start_rel := (start_rel ctx cost_limit).
  Local Notation ip_contract := (ip_contract ctx cost_limit).
  Local Notation done_set := (done_set ctx cost_limit).
  Local Notation run_n := (run_n ctx cost_limit).
  Local Notation first_done := (first_done ctx cost_limit).

  Theorem variable_scheduler_correct :
    forall (act: tfs_action sched) (sp0: src_sys_state)
           (ss0: sched_sys_state) (input: input_t) (resp: nat -> resp_val),
      start_rel sp0 ss0 ->
      ip_contract act input resp ss0 ->
      exists N, 0 < N /\
        (forall k, 0 < k < N -> ~ done_set (run_n k act input resp ss0)) /\
        done_set (run_n N act input resp ss0) /\
        let sp1 := tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act) sp0 input in
        maps_from ctx bneeds (fst (run_n N act input resp ss0)) = fst sp1 /\
        snd (run_n N act input resp ss0) = snd sp1.
  Proof. exact (SchedulerRoundTrip.variable_scheduler_correct ctx cost_limit). Qed.

  (* THE RUN RE-ENTERS A START STATE.  On its done cycle the scheduled state is
     related by [start_rel] to the source state one action later, so every
     per-action theorem applies again to the action that follows. *)
  Theorem start_rel_after_done :
    forall (act: tfs_action sched) (sp0: src_sys_state)
           (ss0: sched_sys_state) (input: input_t) (resp: nat -> resp_val) (N: nat),
      start_rel sp0 ss0 ->
      ip_contract act input resp ss0 ->
      first_done act input resp ss0 N ->
      start_rel (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act) sp0 input)
                (run_n N act input resp ss0).
  Proof.
    intros act sp0 ss0 input resp N Hstart Hipc [HN0 [Hdone Hbefore]].
    exact (SchedulerRoundTrip.start_rel_after_done ctx cost_limit act sp0 ss0 input resp N
             Hstart Hipc HN0 Hbefore Hdone).
  Qed.

End SchedulerSimulation.
