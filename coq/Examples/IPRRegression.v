(*
    Regression example for the IPR / latency-noninterference results.

    The specification is the classic timing side channel: a password check whose
    branch condition depends on a secret register.  The point of the file is to
    pin down, on a concrete context, that

      (a) the taint analysis marks that branch condition as secret-dependent,
      (b) the latency function [L] is genuinely computable, and
      (c) the IPR theorems instantiate at a real context rather than vacuously.

    (c) is the part that catches signature drift: if a hypothesis of any of the
    main theorems is strengthened, the [Definition]s at the foot stop type
    checking.
*)

Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.
Require Import Trustformer.Properties.SchedulerSimulation.
Require Import Trustformer.Properties.IPR.

Require Import Coq.Lists.List.
Import ListNotations.

Section FunctionalSpecification.

  Definition sz := 32.

  Inductive fs_action := fs_check.

  Definition fs_action_encoding (a: fs_action) : bits_t 16 :=
    match a with fs_check => Bits.of_nat 16 1 end.

  Lemma fs_action_encoding_inj :
    forall a1 a2, fs_action_encoding a1 = fs_action_encoding a2 -> a1 = a2.
  Proof. intros a1 a2 _. destruct a1; destruct a2; reflexivity. Qed.

  Inductive fs_states := fs_secret | fs_count.
  Inductive fs_inputs := fs_guess.
  Inductive fs_outputs := fs_ok.

  Definition fs_states_size  (_: fs_states)  : nat := sz.
  Definition fs_inputs_size  (_: fs_inputs)  : nat := sz.
  Definition fs_outputs_size (_: fs_outputs) : nat := sz.

  Definition fs_states_t := tf_states_type fs_states_size.

  Definition fs_states_init (x: fs_states) : fs_states_t x :=
    match x with fs_secret => Bits.zero | fs_count => Bits.zero end.

  (* The branch condition reads [fs_secret], so a naive compilation would take a
     different number of cycles for a correct and an incorrect guess. *)
  Definition fs_transitions (act: fs_action)
      : @tf_ops fs_states fs_inputs fs_outputs :=
    match act with
    | fs_check =>
        {[
          (if $fs_secret ==[sz] $fs_guess then
             let $fs_count := $fs_count + #1;
             let $fs_ok := #1
           else
             let $fs_ok := #0)
        ]}
    end.

End FunctionalSpecification.

Section Context.

  Definition tfs_ctx : TFSchedContext := {|
    tfs_spec_states      := fs_states;
    tfs_spec_states_fin  := _;
    tfs_spec_states_size := fs_states_size;
    tfs_spec_states_init := fs_states_init;

    tfs_spec_inputs      := fs_inputs;
    tfs_spec_inputs_fin  := _;
    tfs_spec_inputs_size := fs_inputs_size;

    tfs_spec_outputs      := fs_outputs;
    tfs_spec_outputs_fin  := _;
    tfs_spec_outputs_size := fs_outputs_size;

    tfs_spec_action     := fs_action;
    tfs_spec_action_fin := _;
    tfs_spec_action_ops := fs_transitions;
    tfs_spec_decls := []
  |}.

  Definition cost := 5.

  Definition check_dfg := build_dfg tfs_ctx fs_check.

End Context.

Section TaintRegression.

  (* The secret reaches the branch, so the roots are not all untainted: a
     latency-noninterference claim here is not free. *)
  Definition tainted_nodes := get_tainted tfs_ctx check_dfg.

  Goal tainted_nodes <> [].
  Proof. vm_compute. discriminate. Qed.

End TaintRegression.

Section TheoremInstantiation.

  Local Notation sched := (tfs_schedule tfs_ctx cost).

  (* [L] is a total function into [nat] rather than a relation, which is what
     lets the paper write [L act input pre post].  It is *not* practically
     reducible: [vm_compute] on this 2-register/32-bit context exceeds 300s,
     because each of the [settle_bound] candidate cycles interprets the whole
     schedule.  Symbolic reasoning via [L_first_done] is the usable route. *)
  Definition check_latency := L tfs_ctx cost.

  (* Signature regression.  Each of these fails to type check if the
     corresponding theorem's hypotheses change. *)

  Definition reg_L_first_done := L_first_done tfs_ctx cost.

  Definition reg_L_public := L_public tfs_ctx cost.

  Definition reg_emulator := emulator_correct_L tfs_ctx cost.

  Definition reg_latency_from_outputs := latency_from_outputs tfs_ctx cost.

  Definition reg_obs_eq_pub_eq := obs_eq_pub_eq tfs_ctx cost.

  (* The headline, fully instantiated: for this context, two runs of [fs_check]
     that agree on the outputs before and after finish on the same cycle, no
     matter what [fs_secret] holds. *)
  Theorem check_latency_is_public :
    forall a_idx input sp0 sp0' ss0 ss0',
      act_idx_aligned tfs_ctx cost fs_check a_idx ->
      start_rel tfs_ctx cost sp0  ss0  ->
      start_rel tfs_ctx cost sp0' ss0' ->
      (forall ov, (snd sp0).[ov] = (snd sp0').[ov]) ->
      (forall ov, (snd (tf_ops_run (tfs_spec_states_size tfs_ctx)
                          (tfs_spec_inputs_size tfs_ctx)
                          (tfs_spec_outputs_size tfs_ctx)
                          (tfs_spec_action_ops tfs_ctx fs_check) sp0 input)).[ov]
                = (snd (tf_ops_run (tfs_spec_states_size tfs_ctx)
                          (tfs_spec_inputs_size tfs_ctx)
                          (tfs_spec_outputs_size tfs_ctx)
                          (tfs_spec_action_ops tfs_ctx fs_check) sp0' input)).[ov]) ->
      check_latency fs_check input ss0 = check_latency fs_check input ss0'.
  Proof.
    intros a_idx input sp0 sp0' ss0 ss0' Halign Hst Hst' Hpre Hpost.
    (* this context supplies no declassification rules *)
    assert (Hdecls : forall act a_idx' input',
              uncond_sound tfs_ctx cost act a_idx' input').
    { intros act a_idx' input' i Hi. cbn in Hi. destruct Hi. }
    exact (L_public tfs_ctx cost Hdecls fs_check a_idx input sp0 sp0' ss0 ss0'
             Halign Hst Hst' Hpre Hpost).
  Qed.

End TheoremInstantiation.

Print Assumptions check_latency_is_public.
