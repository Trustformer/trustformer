(* ==================================================================== *)
(* Variable-scheduler simulation / correctness                          *)
(*                                                                      *)
(* One top-level SOURCE step of an action (tf_ops_run over the whole    *)
(* program) equals iterating the scheduled per-cycle transition         *)
(* (tfs_next_cycle) until the tf_dfg_done flag is set, modulo the state *)
(* mapping maps_to / maps_from.                                         *)
(*                                                                      *)
(* See agents/scheduler-simulation/PLAN.md for the campaign plan.       *)
(* ==================================================================== *)

Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

Section SchedulerSimulation.

  (* The concrete variable scheduler is parameterized by a source scheduling
     context and a per-cycle cost limit. *)
  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  (* The concrete TFSchedule instance built by the variable scheduler. *)
  Local Notation sched := (tfs_schedule ctx cost_limit).

  (* ---- Source (spec) world ---- *)
  Local Notation s_var := (tfs_spec_states ctx).
  Local Notation i_var := (tfs_spec_inputs ctx).
  Local Notation o_var := (tfs_spec_outputs ctx).
  Local Notation s_sz  := (tfs_spec_states_size ctx).
  Local Notation i_sz  := (tfs_spec_inputs_size ctx).
  Local Notation o_sz  := (tfs_spec_outputs_size ctx).

  Hint Extern 0 (FiniteType s_var) => exact (tfs_spec_states_fin ctx)  : typeclass_instances.
  Hint Extern 0 (FiniteType i_var) => exact (tfs_spec_inputs_fin ctx)  : typeclass_instances.
  Hint Extern 0 (FiniteType o_var) => exact (tfs_spec_outputs_fin ctx) : typeclass_instances.

  Local Notation src_st_env  := (ContextEnv.(env_t) (tf_states_type s_sz)).
  Local Notation src_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation src_sys_state := (src_st_env * src_out_env)%type.

  (* ---- Scheduled (target) world ---- *)
  (* Scheduled states are tf_dfg_states; inputs/outputs coincide with the spec's. *)
  Hint Extern 0 (FiniteType (tfs_states sched))  => exact (tfs_states_fin sched)  : typeclass_instances.
  Hint Extern 0 (FiniteType (tfs_outputs sched)) => exact (tfs_outputs_fin sched) : typeclass_instances.

  Local Notation sched_st_env  := (ContextEnv.(env_t) (tf_states_type (tfs_states_size sched))).
  Local Notation sched_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation sched_sys_state := (sched_st_env * sched_out_env)%type.

  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).

  (* ---- One scheduled cycle and its bounded iteration ---- *)
  Definition sched_step (act: tfs_action sched) (ss: sched_sys_state) (input: input_t)
    : sched_sys_state :=
    tfs_next_cycle sched act ss input.

  Fixpoint run_n (n: nat) (act: tfs_action sched) (input: input_t) (ss: sched_sys_state)
    : sched_sys_state :=
    match n with
    | 0 => ss
    | S k => sched_step act (run_n k act input ss) input
    end.

  (* ==================================================================== *)
  (* Phase 1: concrete characterization of ONE scheduled cycle.           *)
  (* ==================================================================== *)

  (* The list of updates a single cycle selects (mirrors the inline `updates`
     let inside tfs_next_cycle): always-updates unconditionally, plus the
     reset+done updates when the done flag fired this cycle. *)
  Definition cycle_updates (act: tfs_action sched) (ss: sched_sys_state) (input: input_t) :=
    let always_updates := tfs_get_updates sched (fst (Contract.tfs_schedule sched act)) ss input in
    let done_updates   := tfs_get_updates sched (snd (Contract.tfs_schedule sched act)) ss input in
    let reset_updates  := tfs_reset_updates sched (tfs_reset_states sched) in
    let done_val := find_st_val sched (tfs_done_signal sched) always_updates ss in
    if beq_dec done_val Bits.zero then always_updates
    else reset_updates ++ done_updates ++ always_updates.

  (* One cycle, expressed as create over find_{st,out}_val of the selected updates. *)
  Lemma sched_step_eq (act: tfs_action sched) (ss: sched_sys_state) (input: input_t) :
    sched_step act ss input =
    ( ContextEnv.(create) (fun x => find_st_val  sched x (cycle_updates act ss input) ss),
      ContextEnv.(create) (fun x => find_out_val sched x (cycle_updates act ss input) ss) ).
  Proof.
    unfold sched_step, tfs_next_cycle, cycle_updates. reflexivity.
  Qed.

  (* Reading a state register after one cycle. *)
  Lemma sched_step_getst (act: tfs_action sched) (ss: sched_sys_state) (input: input_t) x :
    (fst (sched_step act ss input)).[x] =
    find_st_val sched x (cycle_updates act ss input) ss.
  Proof. rewrite sched_step_eq. cbn [fst]. rewrite getenv_create. reflexivity. Qed.

  (* Reading an output register after one cycle. *)
  Lemma sched_step_getout (act: tfs_action sched) (ss: sched_sys_state) (input: input_t) x :
    (snd (sched_step act ss input)).[x] =
    find_out_val sched x (cycle_updates act ss input) ss.
  Proof. rewrite sched_step_eq. cbn [snd]. rewrite getenv_create. reflexivity. Qed.

  (* ---- Generic find_{st,out}_update reductions over tfs_get_updates ---- *)

  Local Notation ss_sz := (tfs_states_size sched).
  Local Notation oo_sz := (tfs_outputs_size sched).
  Local Notation eval_st  dst e ss input :=
    (tf_eval_expr ss_sz i_sz oo_sz (szB := ss_sz dst) e ss input).
  Local Notation eval_out dst e ss input :=
    (tf_eval_expr ss_sz i_sz oo_sz (szB := oo_sz dst) e ss input).

  (* tfs_get_updates is a map, so it peels one op at a time. *)
  Lemma tfs_get_updates_cons (op: @tf_op (tfs_states sched) i_var o_var) ops ss input :
    tfs_get_updates sched (op :: ops) ss input =
    tf_op_step_updates ss_sz i_sz oo_sz op ss input :: tfs_get_updates sched ops ss input.
  Proof. reflexivity. Qed.

  (* A tf_assign to dst at the head resolves find_st_update to its evaluated value. *)
  Lemma find_st_update_assign_head dst e ops ss input :
    find_st_update sched dst
      (tfs_get_updates sched (tf_assign dst e :: ops) ss input)
    = Some (eval_st dst e ss input).
  Proof.
    rewrite tfs_get_updates_cons. cbn [tf_op_step_updates find_st_update].
    destruct (eq_dec dst dst) as [Heq | Hneq]; [| congruence].
    rewrite (Eqdep_dec.UIP_dec eq_dec Heq eq_refl). reflexivity.
  Qed.

  (* find_st_update skips a head update that does not assign the queried state. *)
  Lemma find_st_update_skip_cons x (u: tf_update ss_sz oo_sz) ups :
    (forall v, u <> tf_st_update _ _ x v) ->
    find_st_update sched x (u :: ups) = find_st_update sched x ups.
  Proof.
    intro Hne. destruct u as [| var val | var val]; cbn [find_st_update]; try reflexivity.
    destruct (eq_dec var x) as [Heq | Hneq].
    - exfalso. subst var. eapply Hne. reflexivity.
    - reflexivity.
  Qed.

  (* find_st_update skips a head op that does not assign the queried state. *)
  Lemma find_st_update_skip_head x (op: @tf_op (tfs_states sched) i_var o_var) ops ss input :
    (forall e, op <> tf_assign x e) ->
    find_st_update sched x (tfs_get_updates sched (op :: ops) ss input)
    = find_st_update sched x (tfs_get_updates sched ops ss input).
  Proof.
    intro Hne. rewrite tfs_get_updates_cons. apply find_st_update_skip_cons.
    intro v. destruct op as [| dst e | dst e]; cbn [tf_op_step_updates]; try discriminate.
    intro H. inversion H. subst dst. eapply Hne. reflexivity.
  Qed.

  (* A tf_output to dst at the head resolves find_out_update to its evaluated value. *)
  Lemma find_out_update_output_head dst e ops ss input :
    find_out_update sched dst
      (tfs_get_updates sched (tf_output dst e :: ops) ss input)
    = Some (eval_out dst e ss input).
  Proof.
    rewrite tfs_get_updates_cons. cbn [tf_op_step_updates find_out_update].
    destruct (eq_dec dst dst) as [Heq | Hneq]; [| congruence].
    rewrite (Eqdep_dec.UIP_dec eq_dec Heq eq_refl). reflexivity.
  Qed.

  (* find_out_update skips a head update that does not output the queried var. *)
  Lemma find_out_update_skip_cons x (u: tf_update ss_sz oo_sz) ups :
    (forall v, u <> tf_out_update _ _ x v) ->
    find_out_update sched x (u :: ups) = find_out_update sched x ups.
  Proof.
    intro Hne. destruct u as [| var val | var val]; cbn [find_out_update]; try reflexivity.
    destruct (eq_dec var x) as [Heq | Hneq].
    - exfalso. subst var. eapply Hne. reflexivity.
    - reflexivity.
  Qed.

  (* find_out_update skips a head op that does not output the queried var. *)
  Lemma find_out_update_skip_head x (op: @tf_op (tfs_states sched) i_var o_var) ops ss input :
    (forall e, op <> tf_output x e) ->
    find_out_update sched x (tfs_get_updates sched (op :: ops) ss input)
    = find_out_update sched x (tfs_get_updates sched ops ss input).
  Proof.
    intro Hne. rewrite tfs_get_updates_cons. apply find_out_update_skip_cons.
    intro v. destruct op as [| dst e | dst e]; cbn [tf_op_step_updates]; try discriminate.
    intro H. inversion H. subst dst. eapply Hne. reflexivity.
  Qed.

  (* Predicate: op writes state x. *)
  Definition op_assigns_st (x: tfs_states sched) (op: @tf_op (tfs_states sched) i_var o_var) : Prop :=
    exists e, op = tf_assign x e.
  (* Predicate: op writes output x. *)
  Definition op_writes_out (x: o_var) (op: @tf_op (tfs_states sched) i_var o_var) : Prop :=
    exists e, op = tf_output x e.

  (* If no op in the list assigns x, find_st_update returns None. *)
  Lemma find_st_update_not_in x ops ss input :
    (forall op, In op ops -> ~ op_assigns_st x op) ->
    find_st_update sched x (tfs_get_updates sched ops ss input) = None.
  Proof.
    induction ops as [| op ops IH]; intro Hnone.
    - reflexivity.
    - rewrite find_st_update_skip_head.
      + apply IH. intros op' Hin. apply Hnone. now right.
      + intros e Heq. eapply (Hnone op); [ now left | exists e; exact Heq ].
  Qed.

  (* In an op list with unique destinations, membership of an assignment fixes
     the result returned by find_st_update. *)
  Lemma find_st_update_unique_assign x e ops ss input :
    tfs_ops_no_duplicates ops ->
    In (tf_assign x e) ops ->
    find_st_update sched x (tfs_get_updates sched ops ss input)
    = Some (eval_st x e ss input).
  Proof.
    unfold tfs_ops_no_duplicates.
    induction ops as [| op ops IH]; intros Hnd Hin; [ destruct Hin |].
    cbn [flat_map] in Hnd.
    destruct Hin as [Heq | Hin].
    - subst op. apply find_st_update_assign_head.
    - destruct op as [| dst rhs | dst rhs].
      + apply IH; [ exact Hnd | exact Hin ].
      + inversion Hnd as [| tag tags Hnot Htail]; subst tag tags.
        destruct (eq_dec dst x) as [Hdx | Hdx].
        * subst dst. exfalso. apply Hnot. apply in_flat_map.
          exists (tf_assign x e). split; [ exact Hin |]. cbn [In]. left. reflexivity.
        * rewrite find_st_update_skip_head.
          -- apply IH; [ exact Htail | exact Hin ].
          -- intros rhs' Heq. inversion Heq. contradiction.
      + apply IH.
        * cbn [app] in Hnd. inversion Hnd. assumption.
        * exact Hin.
  Qed.

  Lemma NoDup_app_l {A} (l1 l2: list A) : NoDup (l1 ++ l2) -> NoDup l1.
  Proof.
    induction l1 as [| a l1 IH]; intro Hnd; [ constructor |].
    cbn [app] in Hnd. inversion Hnd as [| ? ? Hnot Htail]; subst.
    constructor.
    - intro Hin. apply Hnot. apply in_or_app. left. exact Hin.
    - apply IH. exact Htail.
  Qed.

  (* If no op in the list writes output x, find_out_update returns None. *)
  Lemma find_out_update_not_in x ops ss input :
    (forall op, In op ops -> ~ op_writes_out x op) ->
    find_out_update sched x (tfs_get_updates sched ops ss input) = None.
  Proof.
    induction ops as [| op ops IH]; intro Hnone.
    - reflexivity.
    - rewrite find_out_update_skip_head.
      + apply IH. intros op' Hin. apply Hnone. now right.
      + intros e Heq. eapply (Hnone op); [ now left | exists e; exact Heq ].
  Qed.

  (* Raw-update version: if no update in the list targets state x, find is None. *)
  Lemma find_st_update_not_in_raw x (ups: list (tf_update ss_sz oo_sz)) :
    (forall u, In u ups -> forall val, u <> tf_st_update ss_sz oo_sz x val) ->
    find_st_update sched x ups = None.
  Proof.
    induction ups as [| u ups IH]; intro Hnone.
    - reflexivity.
    - rewrite find_st_update_skip_cons.
      + apply IH. intros u' Hin. apply Hnone. now right.
      + intro val. eapply Hnone. now left.
  Qed.

  (* ---- Concrete shape of the compiled op lists for the variable scheduler ---- *)

  (* find_st_update over an append: if the prefix has no match, skip it. *)
  Lemma find_st_update_app_None x (ups1 ups2: list (tf_update ss_sz oo_sz)) :
    find_st_update sched x ups1 = None ->
    find_st_update sched x (ups1 ++ ups2) = find_st_update sched x ups2.
  Proof.
    induction ups1 as [| u ups1 IH]; intro Hnone.
    - reflexivity.
    - cbn [app]. destruct u as [| var val | var val]; cbn [find_st_update] in *.
      + apply IH, Hnone.
      + destruct (eq_dec var x) as [Heq | Hneq]; [ discriminate | apply IH, Hnone ].
      + apply IH, Hnone.
  Qed.

  (* The reset states are only buffer/valid registers, never the done flag. *)
  Lemma reset_states_not_done v :
    In v (reset_states ctx cost_limit) -> v <> done_signal ctx cost_limit.
  Proof.
    unfold reset_states, done_signal. rewrite in_flat_map.
    intros [a [_ Ha]].
    destruct (index_of_nat _ a) as [a' |]; [| destruct Ha].
    rewrite in_flat_map in Ha. destruct Ha as [n [_ Hn]].
    destruct (index_of_nat _ n) as [n' |]; [| destruct Hn].
    cbn [In] in Hn. destruct Hn as [Hn | [Hn | []]]; subst v; discriminate.
  Qed.

  (* The reset updates never assign the done flag (they reset buffer/valid regs). *)
  Lemma reset_updates_no_done :
    find_st_update sched (tfs_done_signal sched)
      (tfs_reset_updates sched (tfs_reset_states sched)) = None.
  Proof.
    assert (Hrs: tfs_reset_states sched = reset_states ctx cost_limit) by reflexivity.
    assert (Hds: tfs_done_signal sched = done_signal ctx cost_limit) by reflexivity.
    rewrite Hrs, Hds. unfold tfs_reset_updates.
    apply find_st_update_not_in_raw.
    intros u Hin val. rewrite in_map_iff in Hin.
    destruct Hin as [v [Hu Hv]]. subst u.
    intro Hcontra. inversion Hcontra as [Heq].
    apply (reset_states_not_done v Hv). exact Heq.
  Qed.

  (* The always-ops list of the variable scheduler is exactly the done-flag
     assignment followed by the buffer writes.  Its head assigns tf_dfg_done the
     compiled combined-validity expression over some list of per-node valid exprs. *)
  Lemma always_ops_cons (act: tfs_action sched) :
    exists exprs rest,
      fst (Contract.tfs_schedule sched act)
      = tf_assign (tfs_done_signal sched) (combine_valid_exprs ctx cost_limit exprs) :: rest.
  Proof.
    unfold sched, tfs_schedule, Contract.tfs_schedule, tfs_done_signal, done_signal.
    unfold schedule. cbv zeta. cbn [fst].
    unfold compile_dfg_valid. cbv zeta.
    eexists. eexists. reflexivity.
  Qed.

  (* The done-ops (final state/output writes) never assign the done flag. *)
  Lemma done_ops_no_done (act: tfs_action sched) (ss: sched_sys_state) (input: input_t) :
    find_st_update sched (tfs_done_signal sched)
      (tfs_get_updates sched (snd (Contract.tfs_schedule sched act)) ss input) = None.
  Proof.
    apply find_st_update_not_in. intros op Hin [e He]. subst op.
    revert Hin. unfold sched, tfs_schedule, Contract.tfs_schedule, schedule.
    cbv zeta. cbn [snd]. unfold compile_dfg_aux. cbv zeta.
    destruct (index_of_nat _ _) as [a' |]; [| intros []].
    rewrite in_map_iff. intros [[var nid] [Hop _]].
    destruct (compile_dfg_expr _ _ _ _ _ _ _) as [expr valid].
    destruct var as [sv | ov]; inversion Hop.
  Qed.

  (* The done value produced by one cycle equals the always-list done value,
     regardless of whether the reset/done prefix fired (neither touches done). *)
  Lemma cycle_done_val (act: tfs_action sched) (ss: sched_sys_state) (input: input_t) :
    find_st_val sched (tfs_done_signal sched) (cycle_updates act ss input) ss
    = find_st_val sched (tfs_done_signal sched)
        (tfs_get_updates sched (fst (Contract.tfs_schedule sched act)) ss input) ss.
  Proof.
    unfold cycle_updates. cbv zeta.
    destruct (beq_dec _ _) eqn:Hd.
    - reflexivity.
    - unfold find_st_val.
      rewrite (find_st_update_app_None _ _ _ reset_updates_no_done).
      rewrite (find_st_update_app_None _ _ _ (done_ops_no_done act ss input)).
      reflexivity.
  Qed.

  (* Reading the done flag after one cycle yields exactly the always done value. *)
  Lemma sched_step_done (act: tfs_action sched) (ss: sched_sys_state) (input: input_t) :
    (fst (sched_step act ss input)).[tfs_done_signal sched]
    = find_st_val sched (tfs_done_signal sched)
        (tfs_get_updates sched (fst (Contract.tfs_schedule sched act)) ss input) ss.
  Proof. rewrite sched_step_getst. apply cycle_done_val. Qed.

  (* ---- Semantics of the compiled combined-validity expression ---- *)

  Local Notation eval1 e ss input :=
    (tf_eval_expr ss_sz i_sz oo_sz (szB := 1) e ss input).

  (* The size-1 constant `1` evaluates to the all-ones (single true) bit. *)
  Lemma eval1_const1 (ss: sched_sys_state) (input: input_t) :
    eval1 (tf_const 1) ss input = Bits.ones 1.
  Proof. reflexivity. Qed.

  (* Reading a size-1 validity register through tf_svar is the register itself
     (the convert cast at szA = szB = 1 is the identity). *)
  Lemma eval1_svar_v (ss: sched_sys_state) (input: input_t)
    (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
    (n_idx : Vect.index (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))) :
    eval1 (tf_svar (tf_dfg_v a_idx n_idx)) ss input = (fst ss).[tf_dfg_v a_idx n_idx].
  Proof.
    cbn [tf_eval_expr]. unfold convert.
    destruct (eq_dec (ss_sz (tf_dfg_v a_idx n_idx)) 1) as [e | n].
    - rewrite (Eqdep_dec.UIP_dec eq_dec e eq_refl). reflexivity.
    - exfalso. apply n. reflexivity.
  Qed.

  (* convert at equal source/target size is the identity (the [eq_dec szA szA]
     branch reduces via UIP).  Foundational for size-cast bookkeeping when a
     compiled sub-expression is evaluated at its own register size. *)
  Lemma convert_same {sz} (x: bits_t sz) :
    Semantics.convert (szA := sz) (szB := sz) x = x.
  Proof.
    unfold Semantics.convert.
    destruct (eq_dec sz sz) as [e | ne].
    - rewrite (Eqdep_dec.UIP_dec eq_dec e eq_refl). reflexivity.
    - exfalso. apply ne. reflexivity.
  Qed.

  (* Reading any state register through tf_svar at its OWN size is the register
     itself (convert is the identity when szB = ss_sz v). *)
  Lemma eval_svar_same (v: tfs_states sched) (ss: sched_sys_state) (input: input_t) :
    tf_eval_expr ss_sz i_sz oo_sz (szB := ss_sz v) (tf_svar v) ss input = (fst ss).[v].
  Proof.
    cbn [tf_eval_expr]. apply convert_same.
  Qed.

  (* Eval/convert commute at a state-variable leaf: reading [tf_svar v] at its
     own size and then converting to [szB] equals reading it directly at [szB].
     This is the (star) obligation instance for a buffered DFG_Var node, whose
     declared node size equals the register's natural size [ss_sz v]. *)
  Lemma eval_convert_svar (v: tfs_states sched) (szB: nat)
        (ss: sched_sys_state) (input: input_t) :
    Semantics.convert (szA := ss_sz v) (szB := szB)
      (tf_eval_expr ss_sz i_sz oo_sz (szB := ss_sz v) (tf_svar v) ss input)
    = tf_eval_expr ss_sz i_sz oo_sz (szB := szB) (tf_svar v) ss input.
  Proof.
    rewrite eval_svar_same. reflexivity.
  Qed.

  (* Same commutation for an input leaf [tf_ivar v]. *)
  Lemma eval_convert_ivar (v: i_var) (szB: nat)
        (ss: sched_sys_state) (input: input_t) :
    Semantics.convert (szA := i_sz v) (szB := szB)
      (tf_eval_expr ss_sz i_sz oo_sz (szB := i_sz v) (tf_ivar v) ss input)
    = tf_eval_expr ss_sz i_sz oo_sz (szB := szB) (tf_ivar v) ss input.
  Proof.
    cbn [tf_eval_expr]. rewrite convert_same. reflexivity.
  Qed.

  (* Same commutation for an output leaf [tf_ovar v]. *)
  Lemma eval_convert_ovar (v: o_var) (szB: nat)
        (ss: sched_sys_state) (input: input_t) :
    Semantics.convert (szA := oo_sz v) (szB := szB)
      (tf_eval_expr ss_sz i_sz oo_sz (szB := oo_sz v) (tf_ovar v) ss input)
    = tf_eval_expr ss_sz i_sz oo_sz (szB := szB) (tf_ovar v) ss input.
  Proof.
    cbn [tf_eval_expr]. rewrite convert_same. reflexivity.
  Qed.


  Lemma valid_and_eval
    (e1 e2: @tf_expr (tfs_states sched) i_var o_var) (ss: sched_sys_state) (input: input_t) :
    eval1 (valid_expr_and ctx cost_limit e1 e2) ss input
    = Bits.and (eval1 e1 ss input) (eval1 e2 ss input).
  Proof.
    unfold valid_expr_and.
    destruct e1 as [v1| | | | | |];
      try (destruct e2 as [v2| | | | | |];
           try (destruct v2 as [|[|v2]]);
           cbn [tf_eval_expr];
           change (Bits.of_nat 1 1) with (Bits.ones 1);
           rewrite ?Bits.and_ones_l, ?Bits.and_ones_r; reflexivity).
    (* e1 = tf_const v1 *)
    destruct v1 as [|[|v1]];
      try (destruct e2 as [v2| | | | | |];
           try (destruct v2 as [|[|v2]]);
           cbn [tf_eval_expr];
           change (Bits.of_nat 1 1) with (Bits.ones 1);
           rewrite ?Bits.and_ones_l, ?Bits.and_ones_r; reflexivity).
  Qed.

  (* valid_expr_if evaluates (at size 1) to all-ones whenever BOTH branches do:
     either it collapsed to `tf_const 1`, or it is a runtime `tf_expr_if` whose
     two branches both evaluate to ones (so the selection is irrelevant). *)
  Lemma valid_if_eval
    (cond t e: @tf_expr (tfs_states sched) i_var o_var) (ss: sched_sys_state) (input: input_t) :
    eval1 t ss input = Bits.ones 1 ->
    eval1 e ss input = Bits.ones 1 ->
    eval1 (valid_expr_if ctx cost_limit cond t e) ss input = Bits.ones 1.
  Proof.
    intros Ht He.
    assert (Hcase: valid_expr_if ctx cost_limit cond t e = tf_const 1
                   \/ valid_expr_if ctx cost_limit cond t e = tf_expr_if cond t e).
    { unfold valid_expr_if.
      destruct t as [vt| | | | | |]; try (right; reflexivity).
      destruct vt as [|[|vt]]; try (right; reflexivity).
      destruct e as [ve| | | | | |]; try (right; reflexivity).
      destruct ve as [|[|ve]]; try (right; reflexivity).
      left; reflexivity. }
    destruct Hcase as [Hc | Hc]; rewrite Hc.
    - apply eval1_const1.
    - cbn [tf_eval_expr].
      destruct (beq_dec (tf_eval_expr ss_sz i_sz oo_sz (szB := 1) cond ss input) Bits.zero).
      + exact He.
      + exact Ht.
  Qed.

  (* The compiled combined-validity expression evaluates to the AND-fold of the
     individual validity exprs (base case = all-ones for the empty conjunction). *)
  Lemma combine_valid_eval
    (exprs: list (@tf_expr (tfs_states sched) i_var o_var)) (ss: sched_sys_state) (input: input_t) :
    eval1 (combine_valid_exprs ctx cost_limit exprs) ss input
    = fold_right Bits.and (Bits.ones 1) (map (fun e => eval1 e ss input) exprs).
  Proof.
    induction exprs as [| e rest IH].
    - cbn [combine_valid_exprs map fold_right]. apply eval1_const1.
    - destruct rest as [| e2 rest].
      + cbn [combine_valid_exprs map fold_right].
        rewrite Bits.and_ones_r. reflexivity.
      + cbn [combine_valid_exprs] in *. cbn [map fold_right].
        rewrite valid_and_eval. rewrite IH. reflexivity.
  Qed.

  (* ---- Size-1 AND-fold saturation ---- *)

  (* A size-1 bitvector is either all-ones (true) or zero (false). *)
  Lemma bits1_cases (b: bits_t 1) : b = Bits.ones 1 \/ b = Bits.zero.
  Proof.
    destruct b as [hd tl]. destruct tl. destruct hd.
    - left. reflexivity.
    - right. reflexivity.
  Qed.

  (* At size 1, a value is non-zero iff it is all-ones. *)
  Lemma bits1_nonzero_ones (b: bits_t 1) : b <> Bits.zero <-> b = Bits.ones 1.
  Proof.
    destruct (bits1_cases b) as [H | H]; subst.
    - split; intro; [ reflexivity | intro Hc; discriminate Hc ].
    - split; intro H'; [ exfalso; apply H'; reflexivity | discriminate H' ].
  Qed.

  (* The size-1 AND-fold saturates to all-ones iff every element is all-ones. *)
  Lemma fold_and_ones (l: list (bits_t 1)) :
    fold_right Bits.and (Bits.ones 1) l = Bits.ones 1
    <-> (forall b, In b l -> b = Bits.ones 1).
  Proof.
    induction l as [| b rest IH]; cbn [fold_right In].
    - split; [ intros _ b [] | reflexivity ].
    - split.
      + intro Hand. destruct (bits1_cases b) as [Hb | Hb].
        * subst b. rewrite Bits.and_ones_l in Hand.
          intros b' [Heq | Hin]; [ subst b'; reflexivity | apply IH; auto ].
        * subst b. change Bits.zero with (Bits.zeroes 1) in Hand.
          rewrite Bits.and_zeroes_l in Hand.
          (* zeroes = ones 1 is false *) discriminate Hand.
      + intro Hall. rewrite (Hall b (or_introl eq_refl)).
        rewrite Bits.and_ones_l. apply IH. intros b' Hin. apply Hall; auto.
  Qed.

  (* The done flag's value after computing the always-updates is the AND-fold of the
     per-node validity evals (its assignment is the always-ops head, so the
     first-match find resolves it, and combine_valid_exprs folds to Bits.and). *)
  Lemma done_val_eval (act: tfs_action sched) (ss: sched_sys_state) (input: input_t) :
    exists exprs,
      find_st_val sched (tfs_done_signal sched)
        (tfs_get_updates sched (fst (Contract.tfs_schedule sched act)) ss input) ss
      = fold_right Bits.and (Bits.ones 1) (map (fun e => eval1 e ss input) exprs).
  Proof.
    destruct (always_ops_cons act) as [exprs [rest Heq]].
    exists exprs. unfold find_st_val. rewrite Heq.
    rewrite find_st_update_assign_head. apply combine_valid_eval.
  Qed.

  (* The done flag is set when the tf_dfg_done register is non-zero. *)
  Definition done_set (ss: sched_sys_state) : Prop :=
    (fst ss).[tfs_done_signal sched] <> Bits.zero.

  (* CHARACTERIZATION: one cycle sets the done flag iff every per-node validity
     expression (the same list that the compiled done-signal ANDs together)
     evaluates to true on the pre-cycle state. *)
  Lemma sched_step_done_set (act: tfs_action sched) (ss: sched_sys_state) (input: input_t) :
    exists exprs,
      done_set (sched_step act ss input)
      <-> (forall e, In e exprs -> eval1 e ss input = Bits.ones 1).
  Proof.
    destruct (done_val_eval act ss input) as [exprs Hdv].
    exists exprs. unfold done_set. rewrite sched_step_done, Hdv.
    rewrite bits1_nonzero_ones, fold_and_ones.
    split; intros Hall b Hin.
    - apply Hall, in_map_iff. exists b. auto.
    - rewrite in_map_iff in Hin. destruct Hin as [e [He Hin]]. subst b.
      apply Hall, Hin.
  Qed.

  (* Registers that must start zeroed: the done flag and every validity bit.
     (Buffer value registers tf_dfg_b may hold arbitrary data, since their
     validity bit is 0.) *)
  Definition zeroed_at_start (x: tfs_states sched) : Prop :=
    match x with
    | tf_dfg_v _ _ => True
    | tf_dfg_done  => True
    | _            => False
    end.

  (* Starting relation between a spec state and a scheduled state. *)
  Definition start_rel (sp: src_sys_state) (ss: sched_sys_state) : Prop :=
    snd ss = snd sp                                     (* outputs coincide *)
    /\ maps_from ctx cost_limit (fst ss) = fst sp       (* tf_dfg_s slots = spec state *)
    /\ (forall x, zeroed_at_start x -> (fst ss).[x] = Bits.zero).

  (* ==================================================================== *)
  (* Phase 2 machinery: per-node target cycles + the run's cycle bound.   *)
  (*                                                                      *)
  (* For an action, build_dfg produces the dataflow graph; calc_backward_ *)
  (* cost then calc_target_cycle assign each node the earliest cycle its   *)
  (* value is available (backward cost / cost_limit).  A node's buffer     *)
  (* validity bit flips to 1 once the cycle count reaches its target, so   *)
  (* the whole action is done at the MAX target cycle over its nodes.      *)
  (* ==================================================================== *)

  (* Per-node target-cycle map for an action's DFG. *)
  Local Notation act_cycle_map act :=
    (calc_target_cycle cost_limit (calc_backward_cost ctx (build_dfg ctx act))).

  (* Target cycle of node [n] (0 when absent from the map). *)
  Definition node_cycle (act: tfs_action sched) (n: nat) : nat :=
    match BitsToLists.list_assoc (act_cycle_map act) n with
    | Some c => c
    | None   => 0
    end.

  (* The run's cycle bound: the largest target cycle over the DFG's nodes. *)
  Definition max_cycle (act: tfs_action sched) : nat :=
    fold_left (fun m p => Nat.max m (snd p)) (act_cycle_map act) 0.

  (* ==================================================================== *)
  (* Phase 2: the cross-cycle buffer / validity invariant.                *)
  (*                                                                      *)
  (* Each action's DFG has, per buffered node, a value register tf_dfg_b  *)
  (* and a validity register tf_dfg_v.  Compiling a buffer inlines its     *)
  (* predecessors (compile_dfg_expr with the buffer itself removed), so    *)
  (* the "settled" value a buffer eventually holds is exactly the          *)
  (* fully-inlined, buffer-free reference expression of that node,         *)
  (* evaluated against the (constant, pre-done) tf_dfg_s slots and the     *)
  (* fixed input.  A buffer's validity bit is 1 precisely once the cycle   *)
  (* count reaches the node's target cycle.                                *)
  (* ==================================================================== *)

  (* nid of the DFG node cached by validity/value register (a_idx, n_idx). *)
  Definition vreg_nid
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (n_idx : Vect.index (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])))
    : nat :=
    fst (nth (index_to_nat n_idx)
             (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])
             (0, (0, 0))).

  (* Fully-inlined (buffer-free) reference expression for DFG node n of act. *)
  Definition node_ref_expr
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (n: nat) : @tf_expr (tfs_states sched) i_var o_var :=
    fst (compile_dfg_expr ctx cost_limit
           (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n []).

  (* [a_idx] indexes the SAME action as [act]: buffer_needs is built by mapping
     over spec_all_actions, so length (buffer_needs …) = length spec_all_actions
     and act's slot is finite_index act. *)
  Definition act_idx_aligned
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit))) : Prop :=
    index_to_nat a_idx = @finite_index _ (tfs_action_fin sched) act.

  (* RETRACTED (superseded by [buffers_settled] / [buffers_settled_run]).
     This cycle-ranked invariant is kept only for reference: ranking buffer
     saturation by [node_cycle] is UNSOUND, because [require_buffer] also
     buffers same-cycle nodes, so a buffer chain can be deeper than
     [max_cycle].  Saturation is now ranked by NODE ID instead (args have
     strictly smaller ids, so depth n <= n).  Unused. *)
  Definition buffer_inv
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (ss: sched_sys_state) (input: input_t) (k: nat) : Prop :=
    forall n_idx,
      let n := vreg_nid a_idx n_idx in
      (* validity bit is SET once the node's target cycle has been reached.
         NOTE (soundness): only the SOUND direction [node_cycle <= k -> valid]
         is kept.  The converse [valid -> node_cycle <= k] is FALSE for buffered
         nodes whose compiled validity is data-dependent (an untainted Phi's
         validity is [valid_expr_and cond (valid_expr_if cond then else)], which
         can fire EARLY when the runtime-selected branch settles before the
         static node_cycle = MAX over both branches).  This mirrors the same
         one-directional weakening already applied to the done signal
         ([done_by_max_cycle] replacing the false [done <-> max_cycle <= k]). *)
      ( node_cycle act n <= k -> (fst ss).[tf_dfg_v a_idx n_idx] <> Bits.zero )
      (* and when the target cycle has been reached, the value register holds
         the settled reference value *)
      /\ ( node_cycle act n <= k ->
           (fst ss).[tf_dfg_b a_idx n_idx]
             = eval_st (tf_dfg_b a_idx n_idx) (node_ref_expr act a_idx n) ss input ).

  (* map fst over get_sizes_and_idx recovers the input node list unchanged
     (the indices/sizes it attaches are dropped by fst). *)
  Lemma gsi_map_fst (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var) (outputs_var := o_var))
        (nodes: list nat) :
    map fst (get_sizes_and_idx ctx dfg nodes) = nodes.
  Proof.
    unfold get_sizes_and_idx. rewrite map_rev.
    match goal with
    | |- rev (map fst (fst (fold_left ?f _ _))) = _ =>
        assert (H: forall ns acc idx,
                   map fst (fst (fold_left f ns (acc, idx)))
                   = rev ns ++ map fst acc)
    end.
    { intros ns; induction ns as [| n ns' IH]; intros acc idx; cbn [fold_left].
      - reflexivity.
      - rewrite IH. cbn [map fst rev]. rewrite <- app_assoc. reflexivity. }
    rewrite H. cbn [map]. rewrite app_nil_r. apply rev_involutive.
  Qed.

  (* Length of a buffer slot list = number of buffered nodes. *)
  Lemma gsi_length (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var) (outputs_var := o_var))
        (nodes: list nat) :
    length (get_sizes_and_idx ctx dfg nodes) = length nodes.
  Proof.
    rewrite <- (gsi_map_fst dfg nodes) at 2. rewrite map_length. reflexivity.
  Qed.

  (* The slot stored at position [m] is numbered [m]. *)
  Lemma gsi_idx_at
        (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var) (outputs_var := o_var))
        (nodes: list nat) (m: nat) :
    m < length nodes ->
    fst (snd (nth m (get_sizes_and_idx ctx dfg nodes) (0, (0, 0)))) = m.
  Proof.
    intro Hm.
    replace (fst (snd (nth m (get_sizes_and_idx ctx dfg nodes) (0, (0, 0)))))
      with (nth m (map (fun '(_, x) => fst x) (get_sizes_and_idx ctx dfg nodes)) 0).
    - unfold get_sizes_and_idx. rewrite fold_idx_map. cbn [app map].
      apply seq_nth. exact Hm.
    - assert (Hproj : forall p : nat * (nat * nat),
          fst (snd p) = (let '(_, x) := p in fst x)).
      { intros [n [idx szv]]. reflexivity. }
      rewrite (map_nth (fun '(_, x) => fst x) _ (0, (0, 0)) m).
      symmetry. apply Hproj.
  Qed.

  (* Every slot index attached by get_sizes_and_idx is < the number of nodes:
     the fold assigns running indices start, start+1, …; after rev they range
     over [0, length nodes). *)
  Lemma gsi_idx_bound
        (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var) (outputs_var := o_var))
        (nodes: list nat) (n idx szv: nat) :
    In (n, (idx, szv)) (get_sizes_and_idx ctx dfg nodes) -> idx < length nodes.
  Proof.
    (* generalize the fold over its accumulator + running start index, using the
       EXACT lambda shape of get_sizes_and_idx (so it matches by conversion). *)
    assert (gen: forall (ns: list nat)
                        (acc: list (nat * (nat * nat))) (start: nat),
              (forall n0 i0 s0, In (n0, (i0, s0)) acc -> i0 < start) ->
              In (n, (idx, szv))
                 (fst (fold_left
                    (fun '(acc0, idx0) (nid0: nat) =>
                       ((nid0, (idx0, sz (nth nid0 (graph dfg)
                                           {| nid := 0; op := DFG_Empty; sz := 0 |})))
                          :: acc0, S idx0))
                    ns (acc, start))) ->
              idx < start + length ns).
    { intros ns. induction ns as [| a ns IH]; intros acc start Hacc Hin;
        cbn [fold_left length] in *.
      - rewrite Nat.add_0_r. exact (Hacc _ _ _ Hin).
      - specialize (IH ((a, (start, sz (nth a (graph dfg)
                          {| nid := 0; op := DFG_Empty; sz := 0 |}))) :: acc) (S start)).
        replace (start + S (length ns)) with (S start + length ns) by lia.
        apply IH; [ | exact Hin ].
        intros n0 i0 s0 [Heq | Hin0].
        + injection Heq as _ Hi0 _. subst i0. apply Nat.lt_succ_diag_r.
        + apply Nat.lt_lt_succ_r. exact (Hacc _ _ _ Hin0). }
    unfold get_sizes_and_idx. rewrite <- in_rev.
    intro Hin.
    specialize (gen nodes [] 0 ltac:(intros ? ? ? []) Hin).
    rewrite Nat.add_0_l in gen. exact gen.
  Qed.

  (* Zip of two maps over the same list is the map of the paired function. *)
  Lemma combine_map2 {A B C} (l: list A) (f: A -> B) (g: A -> C) :
    combine (map f l) (map g l) = map (fun x => (f x, g x)) l.
  Proof.
    induction l as [| a l IH]; cbn [map combine]; [ reflexivity |].
    rewrite IH. reflexivity.
  Qed.

  (* The size attached by get_sizes_and_idx to a buffered node [n] is exactly the
     [sz] field of that node in the graph (the fold reads [sz node] verbatim).
     This pins the buffer register size b(n) to the DFG node's declared size. *)
  Lemma gsi_size
        (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var) (outputs_var := o_var))
        (nodes: list nat) (n idx szv: nat) :
    In (n, (idx, szv)) (get_sizes_and_idx ctx dfg nodes) ->
    szv = sz (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}).
  Proof.
    assert (gen: forall (ns: list nat)
                        (acc: list (nat * (nat * nat))) (start: nat),
              (forall n0 i0 s0, In (n0, (i0, s0)) acc ->
                 s0 = sz (nth n0 (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |})) ->
              In (n, (idx, szv))
                 (fst (fold_left
                    (fun '(acc0, idx0) (nid0: nat) =>
                       ((nid0, (idx0, sz (nth nid0 (graph dfg)
                                           {| nid := 0; op := DFG_Empty; sz := 0 |})))
                          :: acc0, S idx0))
                    ns (acc, start))) ->
              szv = sz (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |})).
    { intros ns. induction ns as [| a ns IH]; intros acc start Hacc Hin;
        cbn [fold_left] in *.
      - exact (Hacc _ _ _ Hin).
      - apply (IH ((a, (start, sz (nth a (graph dfg)
                     {| nid := 0; op := DFG_Empty; sz := 0 |}))) :: acc) (S start));
          [ | exact Hin ].
        intros n0 i0 s0 [Heq | Hin0].
        + injection Heq as Hn0 _ Hs0. subst n0 s0. reflexivity.
        + exact (Hacc _ _ _ Hin0). }
    unfold get_sizes_and_idx. rewrite <- in_rev.
    intro Hin. exact (gen nodes [] 0 ltac:(intros ? ? ? []) Hin).
  Qed.

  (* An entry carrying slot index [m] sits at position [m] of the slot list
     (each entry is numbered by its own position, so membership pins it). *)
  Lemma gsi_entry_at
        (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var) (outputs_var := o_var))
        (nodes: list nat) (n m szv: nat) :
    In (n, (m, szv)) (get_sizes_and_idx ctx dfg nodes) ->
    nth m (get_sizes_and_idx ctx dfg nodes) (0, (0, 0)) = (n, (m, szv)).
  Proof.
    intro Hin.
    destruct (In_nth _ _ (0, (0, 0)) Hin) as [p [Hp Hnth]].
    assert (Hm : m = p).
    { assert (Hf := f_equal (fun x => fst (snd x)) Hnth). cbn [fst snd] in Hf.
      rewrite <- Hf. apply gsi_idx_at.
      rewrite <- (gsi_length dfg nodes). exact Hp. }
    subst m. exact Hnth.
  Qed.

  (* buffer_needs is (up to defeq) a single map over the finite action list. *)
  Lemma buffer_needs_eq :
    buffer_needs ctx cost_limit
    = map (fun a => get_sizes_and_idx ctx (build_dfg ctx a)
                      (require_buffer ctx (build_dfg ctx a)
                         (calc_target_cycle cost_limit
                            (calc_backward_cost ctx (build_dfg ctx a)))))
          (@finite_elements _ (tfs_action_fin sched)).
  Proof.
    unfold buffer_needs. rewrite !map_map, combine_map2, map_map. reflexivity.
  Qed.

  (* The buffer slot for the aligned action is exactly get_sizes_and_idx over
     its require_buffer list (structural: buffer_needs = map over
     spec_all_actions, and a_idx aligns with finite_index act). *)
  Lemma buffer_slot_eq :
    forall (act: tfs_action sched) a_idx,
      act_idx_aligned act a_idx ->
      nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []
      = get_sizes_and_idx ctx (build_dfg ctx act)
          (require_buffer ctx (build_dfg ctx act)
             (calc_target_cycle cost_limit
                (calc_backward_cost ctx (build_dfg ctx act)))).
  Proof.
    intros act a_idx Halign.
    unfold act_idx_aligned in Halign.
    rewrite Halign, buffer_needs_eq.
    set (F := fun a => get_sizes_and_idx ctx (build_dfg ctx a)
                         (require_buffer ctx (build_dfg ctx a)
                            (calc_target_cycle cost_limit
                               (calc_backward_cost ctx (build_dfg ctx a))))).
    (* nth_error (map F finite_elements) (finite_index act) = Some (F act) *)
    assert (Hne : nth_error (map F (@finite_elements _ (tfs_action_fin sched)))
                    (@finite_index _ (tfs_action_fin sched) act) = Some (F act))
      by (apply map_nth_error, (@finite_surjective _ (tfs_action_fin sched) act)).
    (* F act is definitionally the RHS get_sizes_and_idx term *)
    apply (nth_error_nth _ _ _ Hne).
  Qed.

  (* A dependent buffer index selects an entry carrying that same plain index. *)
  Lemma buffer_entry_at
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
        (n_idx : Vect.index
          (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))) :
    act_idx_aligned act a_idx ->
    let entry := nth (index_to_nat n_idx)
                  (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])
                  (0, (0, 0)) in
    In (fst entry, (index_to_nat n_idx, snd (snd entry)))
       (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []).
  Proof.
    intro Halign. cbv zeta.
    pose proof (index_to_nat_bounded n_idx) as Hbound.
    generalize dependent Hbound.
    generalize (index_to_nat n_idx). intros m Hbound.
    rewrite (buffer_slot_eq act a_idx Halign) in Hbound |- *.
    rewrite gsi_length in Hbound.
    set (nodes := require_buffer ctx (build_dfg ctx act)
                    (calc_target_cycle cost_limit
                       (calc_backward_cost ctx (build_dfg ctx act)))) in *.
    assert (Hbound_gsi : m < length (get_sizes_and_idx ctx (build_dfg ctx act) nodes)).
    { rewrite gsi_length. exact Hbound. }
    pose proof (nth_In (get_sizes_and_idx ctx (build_dfg ctx act) nodes)
            (0, (0, 0)) Hbound_gsi) as Hin.
    pose proof (gsi_idx_at (build_dfg ctx act) nodes
                  m Hbound) as Hidx.
    destruct (nth m
                (get_sizes_and_idx ctx (build_dfg ctx act) nodes) (0, (0, 0)))
      as [n [idx szv]] eqn:Hentry.
    cbn [fst snd] in Hin, Hidx |- *.
    subst idx. exact Hin.
  Qed.

  Lemma buffer_register_node_size
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
        (n_idx : Vect.index
          (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))) :
    act_idx_aligned act a_idx ->
    ss_sz (tf_dfg_b a_idx n_idx)
    = sz (nth (vreg_nid a_idx n_idx) (graph (build_dfg ctx act))
            {| nid := 0; op := DFG_Empty; sz := 0 |}).
  Proof.
    intro Halign.
    pose proof (buffer_entry_at act a_idx n_idx Halign) as Hentry.
    pose proof (gsi_size (build_dfg ctx act)
      (require_buffer ctx (build_dfg ctx act) (act_cycle_map act))
      (vreg_nid a_idx n_idx) (index_to_nat n_idx)
      (snd (snd (nth (index_to_nat n_idx)
        (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])
        (0, (0, 0))))) ) as Hsize.
    rewrite <- (buffer_slot_eq act a_idx Halign) in Hsize.
    specialize (Hsize Hentry).
    exact Hsize.
  Qed.

  (* The selected entry emits its value/validity assignment pair. *)
  Lemma compile_dfg_buffers_entry
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
        (n_idx : Vect.index
          (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))) :
    act_idx_aligned act a_idx ->
    let buffers := nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [] in
    let entry := nth (index_to_nat n_idx) buffers (0, (0, 0)) in
    let n := fst entry in
    let buffers' := filter (fun '(b_nid, _) => negb (Nat.eqb b_nid n)) buffers in
    let compiled := compile_dfg_expr ctx cost_limit
                      (length (graph (build_dfg ctx act))) a_idx
                      (build_dfg ctx act) n buffers' in
    In (tf_assign (tf_dfg_b a_idx n_idx) (fst compiled))
       (compile_dfg_buffers ctx cost_limit (index_to_nat a_idx)
          (build_dfg ctx act) buffers)
    /\
    In (tf_assign (tf_dfg_v a_idx n_idx) (snd compiled))
       (compile_dfg_buffers ctx cost_limit (index_to_nat a_idx)
          (build_dfg ctx act) buffers).
  Proof.
    intro Halign. cbv zeta.
    pose proof (buffer_entry_at act a_idx n_idx Halign) as Hentry.
    unfold compile_dfg_buffers. rewrite index_of_nat_to_nat.
    split; apply in_flat_map;
      exists (vreg_nid a_idx n_idx,
        (index_to_nat n_idx,
         snd (snd (nth (index_to_nat n_idx)
           (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])
           (0, (0, 0))))));
      split.
    - exact Hentry.
    - cbn [fst]. rewrite index_of_nat_to_nat.
      unfold vreg_nid.
      match goal with
      | |- In _ (let '(_, _) := ?run in _) => destruct run as [expr valid]
      end.
      cbn [In fst]. left. reflexivity.
    - exact Hentry.
    - cbn [fst]. rewrite index_of_nat_to_nat.
      unfold vreg_nid.
      match goal with
      | |- In _ (let '(_, _) := ?run in _) => destruct run as [expr valid]
      end.
      cbn [In snd]. right. left. reflexivity.
  Qed.

  (* The nid cached in a buffer register is a member of that action's
     require_buffer list. *)
  Lemma vreg_nid_in_require_buffer :
    forall (act: tfs_action sched) a_idx n_idx,
      act_idx_aligned act a_idx ->
      In (vreg_nid a_idx n_idx)
         (require_buffer ctx (build_dfg ctx act)
            (calc_target_cycle cost_limit
               (calc_backward_cost ctx (build_dfg ctx act)))).
  Proof.
    intros act a_idx n_idx Halign.
    pose proof (index_to_nat_bounded n_idx) as Hb.
    unfold vreg_nid.
    (* generalize the dependent index to a plain nat so we can rewrite the slot *)
    generalize dependent Hb.
    generalize (index_to_nat n_idx); intros m Hb.
    rewrite (buffer_slot_eq act a_idx Halign) in Hb |- *.
    rewrite gsi_length in Hb.
    set (rb := require_buffer ctx (build_dfg ctx act)
                 (calc_target_cycle cost_limit
                    (calc_backward_cost ctx (build_dfg ctx act)))) in *.
    replace (fst (nth m (get_sizes_and_idx ctx (build_dfg ctx act) rb) (0, (0, 0))))
      with (nth m (map fst (get_sizes_and_idx ctx (build_dfg ctx act) rb)) 0).
    - rewrite gsi_map_fst. apply nth_In. exact Hb.
    - rewrite (map_nth fst _ (0, (0, 0)) m). reflexivity.
  Qed.

  (* Membership in a left-fold that prepends f-images: the accumulator starts
     empty, so an element is in the result iff some list item contributes it. *)
  Lemma fold_left_prepend_In {A B} (f: B -> list A) (L: list B) (a: A) :
    In a (fold_left (fun cm node => f node ++ cm) L []) <->
    exists node, In node L /\ In a (f node).
  Proof.
    assert (gen: forall L0 acc,
              In a (fold_left (fun cm node => f node ++ cm) L0 acc)
              <-> In a acc \/ exists node, In node L0 /\ In a (f node)).
    { intros L0; induction L0 as [| b L0 IH]; intros acc; cbn [fold_left].
      - split; [ intro H; left; exact H
               | intros [H | [node [[] _]]]; exact H ].
      - rewrite IH, in_app_iff. split.
        + intros [[H|H] | [node [Hin Ha]]].
          * right. exists b. split; [ left; reflexivity | exact H ].
          * left. exact H.
          * right. exists node. split; [ right; exact Hin | exact Ha ].
        + intros [H | [node [[Hb|Hin] Ha]]].
          * left. right. exact H.
          * subst b. left. left. exact Ha.
          * right. exists node. split; [ exact Hin | exact Ha ]. }
    rewrite gen. split.
    - intros [H | H]; [ destruct H | exact H ].
    - intros H. right. exact H.
  Qed.

  (* list_assoc commutes with the value-only remapping done by calc_target_cycle:
     the keys are preserved, so a lookup just divides the found cost. *)
  Lemma list_assoc_calc_target_cycle :
    forall cm n,
      BitsToLists.list_assoc (calc_target_cycle cost_limit cm) n
      = option_map (fun c => c / cost_limit) (BitsToLists.list_assoc cm n).
  Proof.
    intros cm n. unfold calc_target_cycle.
    induction cm as [| [k c] cm IH]; cbn [map BitsToLists.list_assoc].
    - reflexivity.
    - destruct (eq_dec n k).
      + reflexivity.
      + exact IH.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Numeric core of backward-cost monotonicity.                       *)
  (*                                                                   *)
  (* calc_backward_cost dfg = fold_left aux (rev (graph dfg)) [] where  *)
  (* aux sets nid node :: get_args node all to the SAME running-max     *)
  (* value.  We prove monotonicity (arg cost >= consumer cost) from a   *)
  (* single structural well-formedness fact about build_dfg: once a     *)
  (* node is processed, no later-processed node touches its cost key    *)
  (* (topological ordering + unique nids).                              *)
  (* ---------------------------------------------------------------- *)

  (* cost lookup with 0 default *)
  Local Definition getn (l: list (nid_t * nat)) (k: nid_t) : nat :=
    match BitsToLists.list_assoc l k with Some c => c | None => 0 end.

  (* single list_assoc_set: value at the set key / at another key *)
  Lemma la_set_get_eq (l: list (nid_t*nat)) (k: nid_t) (v: nat) :
    getn (BitsToLists.list_assoc_set l k v) k = v.
  Proof.
    unfold getn. induction l as [| [k1 v1] l IH];
      cbn [BitsToLists.list_assoc BitsToLists.list_assoc_set].
    - destruct (eq_dec k k) as [_|n]; [reflexivity|congruence].
    - destruct (eq_dec k k1); cbn [BitsToLists.list_assoc].
      + destruct (eq_dec k k1) as [_|n]; [reflexivity|congruence].
      + destruct (eq_dec k k1) as [e|_]; [congruence|exact IH].
  Qed.

  Lemma la_set_get_neq (l: list (nid_t*nat)) (k j: nid_t) (v: nat) :
    j <> k -> getn (BitsToLists.list_assoc_set l k v) j = getn l j.
  Proof.
    intro Hjk. unfold getn. induction l as [| [k1 v1] l IH];
      cbn [BitsToLists.list_assoc BitsToLists.list_assoc_set].
    - destruct (eq_dec j k) as [e|_]; [congruence|reflexivity].
    - destruct (eq_dec k k1) as [e|ne]; cbn [BitsToLists.list_assoc].
      + subst k1. destruct (eq_dec j k) as [e2|_]; [congruence|reflexivity].
      + destruct (eq_dec j k1) as [e2|_]; [reflexivity|exact IH].
  Qed.

  (* one running-max step of list_assoc_set_all_max *)
  Local Definition sam_step (l: list (nid_t*nat)) (v: nat) (a: nid_t)
    : list (nid_t*nat) :=
    if Nat.leb (getn l a) v then BitsToLists.list_assoc_set l a v else l.

  Lemma step_mono l v a j : getn l j <= getn (sam_step l v a) j.
  Proof.
    unfold sam_step. destruct (Nat.leb (getn l a) v) eqn:H.
    - destruct (eq_dec j a) as [->|Hne].
      + rewrite la_set_get_eq. apply Nat.leb_le in H. exact H.
      + rewrite (la_set_get_neq l a j v Hne). apply Nat.le_refl.
    - apply Nat.le_refl.
  Qed.

  Lemma step_untouched l v a j : j <> a -> getn (sam_step l v a) j = getn l j.
  Proof.
    intro Hne. unfold sam_step. destruct (Nat.leb (getn l a) v).
    - rewrite (la_set_get_neq l a j v Hne). reflexivity.
    - reflexivity.
  Qed.

  Lemma step_ge l v a : v <= getn (sam_step l v a) a.
  Proof.
    unfold sam_step. destruct (Nat.leb (getn l a) v) eqn:H.
    - rewrite la_set_get_eq. apply Nat.le_refl.
    - apply Nat.leb_gt in H. apply Nat.lt_le_incl. exact H.
  Qed.

  Lemma step_upper l v a j : getn (sam_step l v a) j <= Nat.max (getn l j) v.
  Proof.
    unfold sam_step. destruct (Nat.leb (getn l a) v).
    - destruct (eq_dec j a) as [->|Hne].
      + rewrite la_set_get_eq. apply Nat.le_max_r.
      + rewrite (la_set_get_neq l a j v Hne). apply Nat.le_max_l.
    - apply Nat.le_max_l.
  Qed.

  (* cons-unfolding of list_assoc_set_all_max as a sam_step fold *)
  Lemma sam_cons l v a keys :
    list_assoc_set_all_max l (a::keys) v
    = list_assoc_set_all_max (sam_step l v a) keys v.
  Proof. reflexivity. Qed.

  Lemma sam_mono keys : forall l v j,
    getn l j <= getn (list_assoc_set_all_max l keys v) j.
  Proof.
    induction keys as [| a keys IH]; intros l v j.
    - apply Nat.le_refl.
    - rewrite sam_cons. eapply Nat.le_trans; [ apply step_mono | apply IH ].
  Qed.

  Lemma sam_untouched keys : forall l v j,
    ~ In j keys -> getn (list_assoc_set_all_max l keys v) j = getn l j.
  Proof.
    induction keys as [| a keys IH]; intros l v j Hnin.
    - reflexivity.
    - rewrite sam_cons.
      assert (Hne : j <> a) by (intro Heq; apply Hnin; left; symmetry; exact Heq).
      assert (Hk : ~ In j keys) by (intro; apply Hnin; right; assumption).
      rewrite (IH (sam_step l v a) v j Hk).
      apply step_untouched. exact Hne.
  Qed.

  Lemma sam_in_ge keys : forall l v j,
    In j keys -> v <= getn (list_assoc_set_all_max l keys v) j.
  Proof.
    induction keys as [| a keys IH]; intros l v j Hin.
    - destruct Hin.
    - rewrite sam_cons. destruct Hin as [->|Hin].
      + eapply Nat.le_trans; [ apply step_ge | apply sam_mono ].
      + apply IH. exact Hin.
  Qed.

  Lemma sam_upper keys : forall l v j,
    getn (list_assoc_set_all_max l keys v) j <= Nat.max (getn l j) v.
  Proof.
    induction keys as [| a keys IH]; intros l v j.
    - apply Nat.le_max_l.
    - rewrite sam_cons. eapply Nat.le_trans; [ apply IH |].
      apply Nat.max_lub; [ apply step_upper | apply Nat.le_max_r ].
  Qed.

  (* the aux of calc_backward_cost, named *)
  Local Definition bc_aux (cost_map : list (nid_t * nat)) node
    : list (nid_t * nat) :=
    list_assoc_set_all_max cost_map (nid node :: get_args ctx node)
      (getn cost_map (nid node) + cost_fn ctx (op node) (sz node)).

  Lemma calc_backward_cost_fold dfg :
    calc_backward_cost ctx dfg = fold_left bc_aux (rev (graph dfg)) [].
  Proof. unfold calc_backward_cost, bc_aux, getn. reflexivity. Qed.

  (* Frozen-key propagation: if key (nid N) is never in the key-set of any
     node processed later, then the inequality getn x >= getn (nid N) is
     preserved through the rest of the fold. *)
  Lemma cost_ge_after_fold :
    forall (suf: list (@dfg_node_t s_var i_var o_var)) acc
           (N: @dfg_node_t s_var i_var o_var) x,
      getn acc (nid N) <= getn acc x ->
      (forall M, In M suf -> ~ In (nid N) (nid M :: get_args ctx M)) ->
      getn (fold_left bc_aux suf acc) (nid N)
      <= getn (fold_left bc_aux suf acc) x.
  Proof.
    induction suf as [| M suf IH]; cbn [fold_left]; intros acc N x Hge Hfr.
    - exact Hge.
    - apply IH.
      + assert (Hnotin : ~ In (nid N) (nid M :: get_args ctx M))
          by (apply Hfr; left; reflexivity).
        unfold bc_aux.
        rewrite (sam_untouched _ _ _ _ Hnotin).
        eapply Nat.le_trans; [ exact Hge | apply sam_mono ].
      + intros M' HM'. apply Hfr. right. exact HM'.
  Qed.

  (* --- Structural well-formedness of the built DFG --- *)

  (* Along the fold order [rev (graph (build_dfg …))] the node ids are strictly
     decreasing (each node was emitted with a strictly larger id than every node
     appearing later in this order). *)
  Definition ids_desc (L : list (@dfg_node_t s_var i_var o_var)) : Prop :=
    forall pre a rest, L = pre ++ a :: rest ->
      forall M, In M rest -> nid M < nid a.

  (* Every node's args reference strictly-earlier (lower) ids. *)
  Definition args_lt (L : list (@dfg_node_t s_var i_var o_var)) : Prop :=
    forall a, In a L -> forall x, In x (get_args ctx a) -> x < nid a.

  (* ===================================================================== *)
  (* build_dfg_wf : the builder emits nodes with strictly increasing ids   *)
  (* and every node's args reference already-emitted (lower) ids.          *)
  (* Proved by a state-monad invariant [winv] threaded through the builder.*)
  (* ===================================================================== *)

  Local Notation wst := (@dfg_state_t s_var i_var o_var).

  (* --- list / seq arithmetic helpers --- *)

  Lemma revseq_S n : rev (seq 0 (S n)) = n :: rev (seq 0 n).
  Proof.
    rewrite seq_S, rev_app_distr. simpl. reflexivity.
  Qed.

  Lemma revseq_split_lt :
    forall n P b R, rev (seq 0 n) = P ++ b :: R -> forall m, In m R -> m < b.
  Proof.
    induction n as [|n IH]; intros P b R Hsplit m Hm.
    - simpl in Hsplit. destruct P; simpl in Hsplit; discriminate.
    - rewrite revseq_S in Hsplit. destruct P as [|p P'].
      + simpl in Hsplit. injection Hsplit as <- <-.
        apply in_rev in Hm. apply in_seq in Hm. lia.
      + simpl in Hsplit. injection Hsplit as <- Hsplit.
        eapply IH; eauto.
  Qed.

  (* --- the state invariant --- *)

  Definition nid_seq (s: wst) : Prop :=
    map nid (graph s) = rev (seq 0 (length (graph s))).

  Definition wvmg (s: wst) : Prop :=
    forall k id, In (k, id) (var_map s) ->
      exists node, In node (graph s) /\ nid node = id.

  Definition wnidwf (s: wst) (id: nid_t) : Prop :=
    exists node, In node (graph s) /\ nid node = id.

  Definition winv (s: wst) : Prop :=
    wvmg s /\ nid_seq s /\ args_lt (graph s).

  Definition wgmono (s s': wst) : Prop :=
    forall node, In node (graph s) -> In node (graph s').

  Lemma wgmono_refl s : wgmono s s. Proof. intros n H; exact H. Qed.
  Lemma wgmono_trans s1 s2 s3 : wgmono s1 s2 -> wgmono s2 s3 -> wgmono s1 s3.
  Proof. intros H1 H2 n H. apply H2, H1, H. Qed.

  Lemma wnidwf_gmono s s' id : wnidwf s id -> wgmono s s' -> wnidwf s' id.
  Proof. intros [node [Hin Hnid]] Hg. exists node. split;[apply Hg; exact Hin|exact Hnid]. Qed.

  Lemma wla_in {K} `{EqDec K} {A} (l: list (K * A)) k v :
    BitsToLists.list_assoc l k = Some v -> In (k, v) l.
  Proof.
    induction l as [|[k0 v0] l IH]; simpl; [ discriminate | ].
    destruct (eq_dec k k0) as [->|Hne].
    - intro Heq. injection Heq as <-. left; reflexivity.
    - intro Heq. right; apply IH; exact Heq.
  Qed.

  Lemma nid_seq_bound s node : nid_seq s -> In node (graph s) -> nid node < length (graph s).
  Proof.
    unfold nid_seq. intros Hns Hin.
    assert (H: In (nid node) (rev (seq 0 (length (graph s))))).
    { rewrite <- Hns. apply in_map; exact Hin. }
    apply in_rev in H. apply in_seq in H. lia.
  Qed.

  Lemma wnidwf_bound s id : nid_seq s -> wnidwf s id -> id < length (graph s).
  Proof. intros Hns [node [Hin Hnid]]. subst id. eapply nid_seq_bound; eauto. Qed.

  Lemma nid_seq_ids_desc s : nid_seq s -> ids_desc (graph s).
  Proof.
    unfold nid_seq, ids_desc. intros Hns P a R Hsplit M HM.
    rewrite Hsplit in Hns. rewrite map_app in Hns. simpl in Hns.
    eapply revseq_split_lt.
    - exact (eq_sym Hns).
    - apply in_map; exact HM.
  Qed.

  (* --- monad reductions --- *)

  Lemma emit_red op sz (s: wst) :
    emit ctx op sz s =
      (length (graph s),
       {| graph := {| nid := length (graph s); op := op; sz := sz |} :: graph s;
          var_map := var_map s |}).
  Proof. unfold emit, bind, get_state, put_state, ret. reflexivity. Qed.

  Lemma bind_red {A B} (m: M ctx A) (f: A -> M ctx B) (s: wst) x s1 :
    m s = (x, s1) -> bind ctx m f s = f x s1.
  Proof. intro H. unfold bind. rewrite H. reflexivity. Qed.

  Lemma get_state_red (s: wst) : get_state ctx s = (s, s).
  Proof. reflexivity. Qed.

  Lemma put_state_red (s0 s: wst) : put_state ctx s0 s = (tt, s0).
  Proof. reflexivity. Qed.

  (* --- per-primitive invariant lemmas --- *)

  Lemma emit_full op sz (s: wst) :
    winv s ->
    (forall x, In x (get_args ctx {| nid := length (graph s); op := op; sz := sz |}) -> wnidwf s x) ->
    let (id, s') := emit ctx op sz s in wgmono s s' /\ wnidwf s' id /\ winv s'.
  Proof.
    intros [Hv [Hns Hab]] Hargs.
    rewrite emit_red.
    split; [ intros n Hn; right; exact Hn | ].
    split.
    - exists {| nid := length (graph s); op := op; sz := sz |}.
      split; [ left; reflexivity | reflexivity ].
    - split; [ | split ].
      + intros k id Hin. simpl in Hin.
        destruct (Hv k id Hin) as [node [Hn2 Hnid]].
        exists node. split; [ right; exact Hn2 | exact Hnid ].
      + unfold nid_seq. cbn [graph map length nid]. rewrite revseq_S. f_equal. exact Hns.
      + intros a Ha x Hx. simpl in Ha. destruct Ha as [<-|Ha].
        * simpl in Hx. specialize (Hargs x Hx).
          apply (wnidwf_bound s x Hns) in Hargs. exact Hargs.
        * apply Hab; assumption.
  Qed.

  Lemma ensure_var_graph v (s: wst) id s' :
    ensure_var ctx v s = (id, s') ->
    graph s' = {| nid := length (graph s); op := DFG_Var v; sz := dfg_var_size ctx v |} :: graph s
    /\ id = length (graph s).
  Proof.
    unfold ensure_var, emit, bind, get_state, put_state, ret. simpl. intro H.
    injection H as <- <-. split; reflexivity.
  Qed.

  Lemma ensure_var_full v (s: wst) :
    winv s ->
    let (id, s') := ensure_var ctx v s in wgmono s s' /\ wnidwf s' id /\ winv s'.
  Proof.
    intros Hinv. destruct Hinv as [Hv [Hns Hab]].
    destruct (ensure_var ctx v s) as [id s'] eqn:Ev.
    pose proof (ensure_var_graph v s id s' Ev) as [Hg Hid].
    (* gmono *)
    assert (Hg' : wgmono s s') by (intros n Hn; rewrite Hg; right; exact Hn).
    split; [ exact Hg' | ].
    (* nidwf *)
    split.
    - exists {| nid := length (graph s); op := DFG_Var v; sz := dfg_var_size ctx v |}.
      split; [ rewrite Hg; left; reflexivity | rewrite Hid; reflexivity ].
    - split; [ | split ].
      + (* wvmg s' : var_map s' = (v,id) :: filter ... (var_map s) *)
        unfold ensure_var, emit, bind, get_state, put_state, ret in Ev. simpl in Ev.
        injection Ev as HidE HsE. subst id.
        intros k id0 Hin. rewrite <- HsE in Hin. simpl in Hin.
        destruct Hin as [Heq|Hin].
        * injection Heq as <- <-.
          exists {| nid := length (graph s); op := DFG_Var v; sz := dfg_var_size ctx v |}.
          split; [ rewrite Hg; left; reflexivity | reflexivity ].
        * apply filter_In in Hin. destruct Hin as [Hin _].
          destruct (Hv k id0 Hin) as [node [Hn Hnid]].
          exists node. split; [ apply Hg'; exact Hn | exact Hnid ].
      + unfold nid_seq. rewrite Hg. cbn [map length nid]. rewrite revseq_S. f_equal. exact Hns.
      + intros a Ha x Hx. rewrite Hg in Ha. simpl in Ha. destruct Ha as [<-|Ha].
        * simpl in Hx. destruct Hx.
        * apply Hab; assumption.
  Qed.

  Lemma set_var_full v id (s: wst) :
    winv s -> wnidwf s id ->
    let (u, s') := set_var ctx v id s in wgmono s s' /\ winv s'.
  Proof.
    intros [Hv [Hns Hab]] Hnw.
    unfold set_var, bind, get_state, put_state. simpl.
    split.
    - intros n Hn; exact Hn.
    - split; [ | split ].
      + intros k id0 Hin. simpl in Hin. destruct Hin as [Heq|Hin].
        * injection Heq as <- <-. exact Hnw.
        * apply filter_In in Hin. destruct Hin as [Hin _].
          destruct (Hv k id0 Hin) as [node [Hn Hnid]].
          exists node. split; [ exact Hn | exact Hnid ].
      + exact Hns.
      + exact Hab.
  Qed.

  Lemma get_var_full v (s: wst) :
    winv s ->
    let (id, s') := get_var ctx v s in wgmono s s' /\ wnidwf s' id /\ winv s'.
  Proof.
    intros Hinv. unfold get_var, bind, get_state.
    destruct (BitsToLists.list_assoc (var_map s) v) as [id|] eqn:E.
    - unfold ret. split; [ apply wgmono_refl | split ].
      + destruct Hinv as [Hv _]. apply wla_in in E.
        destruct (Hv v id E) as [node [Hn Hnid]]. exists node; split; assumption.
      + exact Hinv.
    - apply ensure_var_full; exact Hinv.
  Qed.

  Lemma ret_full id (s: wst) :
    wnidwf s id -> winv s ->
    let (i, s') := ret ctx id s in wgmono s s' /\ wnidwf s' i /\ winv s'.
  Proof. intros Hn Hp. unfold ret. split; [ apply wgmono_refl | split; assumption ]. Qed.

  Lemma seq_full (m: M ctx nid_t) (f: nid_t -> M ctx nid_t) (s: wst) :
    (winv s -> let (id, s1) := m s in wgmono s s1 /\ wnidwf s1 id /\ winv s1) ->
    (forall id s1, wgmono s s1 -> wnidwf s1 id -> winv s1 ->
       let (id2, s2) := f id s1 in wgmono s1 s2 /\ wnidwf s2 id2 /\ winv s2) ->
    winv s ->
    let (id2, s2) := bind ctx m f s in wgmono s s2 /\ wnidwf s2 id2 /\ winv s2.
  Proof.
    intros H1 H2 Hinv. specialize (H1 Hinv).
    unfold bind. destruct (m s) as [id s1] eqn:Em.
    destruct H1 as [g1 [n1 p1]].
    specialize (H2 id s1 g1 n1 p1).
    destruct (f id s1) as [id2 s2]. destruct H2 as [g2 [n2 p2]].
    split; [ eapply wgmono_trans; eauto | split; assumption ].
  Qed.

  (* --- expression compiler --- *)

  Lemma dataflow_expr_full :
    forall e sz (s: wst), winv s ->
      let (id, s') := dataflow_expr ctx e sz s in wgmono s s' /\ wnidwf s' id /\ winv s'.
  Proof.
    induction e; intros sz s Hinv.
    - (* tf_const *)
      simpl. apply emit_full; [ exact Hinv | intros x Hx; simpl in Hx; destruct Hx ].
    - (* tf_svar *)
      simpl. apply seq_full.
      + apply get_var_full.
      + intros id s1 Hg Hn Hp1. cbn beta.
        destruct (Nat.eqb _ sz).
        * apply ret_full; assumption.
        * apply emit_full; [ exact Hp1 | intros x Hx; simpl in Hx; destruct Hx as [<-|[]]; exact Hn ].
      + exact Hinv.
    - (* tf_ivar *)
      simpl. apply seq_full.
      + intro Hp. apply emit_full; [ exact Hp | intros x Hx; simpl in Hx; destruct Hx ].
      + intros id s1 Hg Hn Hp1. cbn beta.
        destruct (Nat.eqb _ sz).
        * apply ret_full; assumption.
        * apply emit_full; [ exact Hp1 | intros x Hx; simpl in Hx; destruct Hx as [<-|[]]; exact Hn ].
      + exact Hinv.
    - (* tf_ovar *)
      simpl. apply seq_full.
      + apply get_var_full.
      + intros id s1 Hg Hn Hp1. cbn beta.
        destruct (Nat.eqb _ sz).
        * apply ret_full; assumption.
        * apply emit_full; [ exact Hp1 | intros x Hx; simpl in Hx; destruct Hx as [<-|[]]; exact Hn ].
      + exact Hinv.
    - (* tf_op1 *)
      simpl. destruct op as [| source_size].
      + apply seq_full.
        * apply IHe.
        * intros id1 s1 Hg1 Hn1 Hp1. apply emit_full;
            [ exact Hp1 | intros x Hx; simpl in Hx; destruct Hx as [<-|[]]; exact Hn1 ].
        * exact Hinv.
      + apply seq_full.
        * apply IHe.
        * intros id1 s1 Hg1 Hn1 Hp1. apply emit_full;
            [ exact Hp1 | intros x Hx; simpl in Hx; destruct Hx as [<-|[]]; exact Hn1 ].
        * exact Hinv.
    - (* tf_op2 *)
      simpl. destruct op;
        ( apply seq_full;
          [ apply IHe1
          | intros id1 s1 Hg1 Hn1 Hp1; apply seq_full;
            [ apply IHe2
            | intros id2 s2 Hg2 Hn2 Hp2; apply emit_full;
              [ exact Hp2
              | intros x Hx; simpl in Hx;
                destruct Hx as [<-|[<-|[]]];
                [ eapply wnidwf_gmono; [ exact Hn1 | exact Hg2 ] | exact Hn2 ] ]
            | exact Hp1 ]
          | exact Hinv ]).
    - (* tf_expr_if *)
      simpl. apply seq_full.
      + apply IHe1.
      + intros idc s1 Hgc Hnc Hpc. apply seq_full.
        * apply IHe2.
        * intros idt s2 Hgt Hnt Hpt. apply seq_full.
          -- apply IHe3.
          -- intros ide s3 Hge Hne Hpe. apply emit_full.
             ++ exact Hpe.
             ++ intros x Hx. simpl in Hx.
                destruct Hx as [<-|[<-|[<-|[]]]].
                ** eapply wnidwf_gmono; [ exact Hnc | eapply wgmono_trans; [ exact Hgt | exact Hge ] ].
                ** eapply wnidwf_gmono; [ exact Hnt | exact Hge ].
                ** exact Hne.
          -- exact Hpt.
        * exact Hpc.
      + exact Hinv.
  Qed.

  (* ===================================================================== *)
  (* STI-1: dataflow_expr returns a node whose [sz] equals the DEMANDED     *)
  (* size.  Supported by [wvsz]: every var_map entry maps to a node whose   *)
  (* [sz] is the variable's natural [dfg_var_size].  Threaded together      *)
  (* through dataflow_expr (var_map only grows via ensure_var here).        *)
  (* ===================================================================== *)

  Definition wsz (s: wst) (id: nid_t) (size: sz_t) : Prop :=
    exists node, In node (graph s) /\ nid node = id /\ sz node = size.

  Definition wvsz (s: wst) : Prop :=
    forall v id, In (v, id) (var_map s) -> wsz s id (dfg_var_size ctx v).

  Lemma wsz_gmono s s' id size : wsz s id size -> wgmono s s' -> wsz s' id size.
  Proof.
    intros [node [Hin [Hnid Hsz]]] Hg.
    exists node. split; [ apply Hg; exact Hin | split; assumption ].
  Qed.

  Lemma emit_sz op size (s: wst) :
    winv s -> wvsz s ->
    (forall x, In x (get_args ctx {| nid := length (graph s); op := op; sz := size |}) -> wnidwf s x) ->
    let (id, s') := emit ctx op size s in
    wgmono s s' /\ wnidwf s' id /\ winv s' /\ wvsz s' /\ wsz s' id size.
  Proof.
    intros Hinv Hvsz Hargs.
    pose proof (emit_full op size s Hinv Hargs) as Hf.
    rewrite emit_red in Hf |- *.
    destruct Hf as [Hg [Hn Hw]].
    split; [ exact Hg | split; [ exact Hn | split; [ exact Hw | split ] ] ].
    - intros v id Hin. cbn [var_map] in Hin.
      apply (wsz_gmono s); [ apply Hvsz; exact Hin | exact Hg ].
    - exists {| nid := length (graph s); op := op; sz := size |}.
      cbn [graph nid sz]. split; [ left; reflexivity | split; reflexivity ].
  Qed.

  Lemma ensure_var_sz v (s: wst) :
    winv s -> wvsz s ->
    let (id, s') := ensure_var ctx v s in
    wgmono s s' /\ wnidwf s' id /\ winv s' /\ wvsz s' /\ wsz s' id (dfg_var_size ctx v).
  Proof.
    intros Hinv Hvsz.
    destruct (ensure_var ctx v s) as [id s'] eqn:Ev.
    pose proof (ensure_var_full v s Hinv) as Hf. rewrite Ev in Hf.
    destruct Hf as [Hg [Hn Hw]].
    pose proof (ensure_var_graph v s id s' Ev) as [Hgr Hid].
    assert (Hvm : exists f, var_map s' = (v, id) :: filter f (var_map s)).
    { revert Ev. unfold ensure_var, emit, bind, get_state, put_state, ret. simpl.
      intro H. injection H as <- <-. eexists. reflexivity. }
    destruct Hvm as [f Hvm].
    split; [ exact Hg | split; [ exact Hn | split; [ exact Hw | split ] ] ].
    - intros v0 id0 Hin. rewrite Hvm in Hin. cbn [In] in Hin. destruct Hin as [Heq|Hin].
      + injection Heq as <- <-. exists {| nid := length (graph s); op := DFG_Var v; sz := dfg_var_size ctx v |}.
        rewrite Hgr. cbn [graph nid sz]. split; [ left; reflexivity | split; [ symmetry; exact Hid | reflexivity ] ].
      + apply filter_In in Hin. destruct Hin as [Hin _].
        apply (wsz_gmono s); [ apply Hvsz; exact Hin | exact Hg ].
    - exists {| nid := length (graph s); op := DFG_Var v; sz := dfg_var_size ctx v |}.
      rewrite Hgr. cbn [graph nid sz]. split; [ left; reflexivity | split; [ symmetry; exact Hid | reflexivity ] ].
  Qed.

  Lemma get_var_sz v (s: wst) :
    winv s -> wvsz s ->
    let (id, s') := get_var ctx v s in
    wgmono s s' /\ wnidwf s' id /\ winv s' /\ wvsz s' /\ wsz s' id (dfg_var_size ctx v).
  Proof.
    intros Hinv Hvsz. unfold get_var, bind, get_state.
    destruct (BitsToLists.list_assoc (var_map s) v) as [id|] eqn:E.
    - unfold ret.
      split; [ apply wgmono_refl | split; [ | split; [ exact Hinv | split; [ exact Hvsz | ] ] ] ].
      + destruct Hinv as [Hv _]. apply wla_in in E.
        destruct (Hv v id E) as [node [Hn Hnid]]. exists node; split; assumption.
      + apply wla_in in E. apply Hvsz. exact E.
    - apply ensure_var_sz; assumption.
  Qed.

  (* weaken the 5-tuple result to the 4-tuple premise seq_sz expects for [m]. *)
  Lemma sz_weaken (g n w v Q: Prop) :
    (g /\ n /\ w /\ v /\ Q) -> (g /\ n /\ w /\ v).
  Proof. intros [a [b [c [d _]]]]. tauto. Qed.

  (* threading combinator for the sz-augmented invariant *)
  Lemma seq_sz (m: M ctx nid_t) (f: nid_t -> M ctx nid_t) (s: wst) (size: sz_t) :
    (winv s -> wvsz s ->
       let (id, s1) := m s in wgmono s s1 /\ wnidwf s1 id /\ winv s1 /\ wvsz s1) ->
    (forall id s1, wgmono s s1 -> wnidwf s1 id -> winv s1 -> wvsz s1 ->
       let (id2, s2) := f id s1 in
       wgmono s1 s2 /\ wnidwf s2 id2 /\ winv s2 /\ wvsz s2 /\ wsz s2 id2 size) ->
    winv s -> wvsz s ->
    let (id2, s2) := bind ctx m f s in
    wgmono s s2 /\ wnidwf s2 id2 /\ winv s2 /\ wvsz s2 /\ wsz s2 id2 size.
  Proof.
    intros H1 H2 Hinv Hvsz. specialize (H1 Hinv Hvsz).
    unfold bind. destruct (m s) as [id s1] eqn:Em.
    destruct H1 as [g1 [n1 [p1 q1]]].
    specialize (H2 id s1 g1 n1 p1 q1).
    destruct (f id s1) as [id2 s2]. destruct H2 as [g2 [n2 [p2 [q2 r2]]]].
    split; [ eapply wgmono_trans; eauto | split; [ exact n2 | split; [ exact p2 | split; [ exact q2 | exact r2 ] ] ] ].
  Qed.

  (* var-read case: get_var then optional resize, returns node at demanded size. *)
  Lemma dataflow_var_sz (dv: @dfg_vars_t s_var o_var)
        (size: sz_t) (s: wst) :
    winv s -> wvsz s ->
    let (id, s') :=
      (bind ctx (get_var ctx dv)
        (fun src_id =>
          if Nat.eqb (dfg_var_size ctx dv) size then ret ctx src_id
          else emit ctx (DFG_Resize src_id) size)) s in
    wgmono s s' /\ wnidwf s' id /\ winv s' /\ wvsz s' /\ wsz s' id size.
  Proof.
    intros Hinv Hvsz. unfold bind.
    pose proof (get_var_sz dv s Hinv Hvsz) as Hgv.
    destruct (get_var ctx dv s) as [id s1].
    destruct Hgv as [Hg1 [Hn1 [Hp1 [Hq1 Hs1]]]].
    destruct (Nat.eqb (dfg_var_size ctx dv) size) eqn:Eb.
    - apply Nat.eqb_eq in Eb. unfold ret.
      split; [ exact Hg1 | split; [ exact Hn1 | split; [ exact Hp1 | split; [ exact Hq1 | ] ] ] ].
      rewrite <- Eb. exact Hs1.
    - assert (Hargs : forall x, In x (get_args ctx {| nid := length (graph s1); op := DFG_Resize id; sz := size |}) -> wnidwf s1 x).
      { intros x Hx. simpl in Hx. destruct Hx as [<-|[]]. exact Hn1. }
      pose proof (emit_sz (DFG_Resize id) size s1 Hp1 Hq1 Hargs) as He.
      destruct (emit ctx (DFG_Resize id) size s1) as [id2 s2].
      destruct He as [Hg2 [Hn2 [Hp2 [Hq2 Hs2]]]].
      split; [ eapply wgmono_trans; eauto | split; [ exact Hn2 | split; [ exact Hp2 | split; [ exact Hq2 | exact Hs2 ] ] ] ].
  Qed.

  Lemma dataflow_expr_sz :
    forall e size (s: wst), winv s -> wvsz s ->
      let (id, s') := dataflow_expr ctx e size s in
      wgmono s s' /\ wnidwf s' id /\ winv s' /\ wvsz s' /\ wsz s' id size.
  Proof.
    induction e; intros size s Hinv Hvsz.
    - (* tf_const *)
      simpl. apply emit_sz; [ exact Hinv | exact Hvsz | intros x Hx; simpl in Hx; destruct Hx ].
    - (* tf_svar *)
      simpl. apply dataflow_var_sz; assumption.
    - (* tf_ivar *)
      simpl. unfold bind.
      assert (Hargs0 : forall x, In x (get_args ctx {| nid := length (graph s); op := DFG_Input v; sz := size |}) -> wnidwf s x).
      { intros x Hx. simpl in Hx. destruct Hx. }
      pose proof (emit_sz (DFG_Input v) size s Hinv Hvsz Hargs0) as He.
      destruct (emit ctx (DFG_Input v) size s) as [id s1].
      destruct He as [Hg1 [Hn1 [Hp1 [Hq1 Hs1]]]].
      destruct (Nat.eqb _ size) eqn:Eb.
      + unfold ret.
        split; [ exact Hg1 | split; [ exact Hn1 | split; [ exact Hp1 | split; [ exact Hq1 | exact Hs1 ] ] ] ].
      + assert (Hargs : forall x, In x (get_args ctx {| nid := length (graph s1); op := DFG_Resize id; sz := size |}) -> wnidwf s1 x).
        { intros x Hx. simpl in Hx. destruct Hx as [<-|[]]. exact Hn1. }
        pose proof (emit_sz (DFG_Resize id) size s1 Hp1 Hq1 Hargs) as He2.
        destruct (emit ctx (DFG_Resize id) size s1) as [id2 s2].
        destruct He2 as [Hg2 [Hn2 [Hp2 [Hq2 Hs2]]]].
        split; [ eapply wgmono_trans; eauto | split; [ exact Hn2 | split; [ exact Hp2 | split; [ exact Hq2 | exact Hs2 ] ] ] ].
    - (* tf_ovar *)
      simpl. apply dataflow_var_sz; assumption.
    - (* tf_op1 *)
      simpl. destruct op as [| source_size].
      + apply (seq_sz _ _ _ size).
        * intros Hi Hv. pose proof (IHe size s Hi Hv) as H.
          destruct (dataflow_expr ctx e size s) as [id s1]. exact (sz_weaken _ _ _ _ _ H).
        * intros id s1 Hg Hn Hp Hq. apply emit_sz;
            [ exact Hp | exact Hq | intros x Hx; simpl in Hx; destruct Hx as [<-|[]]; exact Hn ].
        * exact Hinv.
        * exact Hvsz.
      + unfold bind. cbv beta.
        destruct (dataflow_expr ctx e source_size s) as [id s1] eqn:Erun.
        pose proof (IHe source_size s Hinv Hvsz) as H. rewrite Erun in H.
        cbv beta iota.
        destruct H as [Hg1 [Hn1 [Hp1 [Hq1 Hs1]]]].
        assert (Hargs : forall x,
            In x (get_args ctx
              {| nid := length (graph s1); op := DFG_Unary (tf_resize source_size) id; sz := size |}) ->
            wnidwf s1 x).
        { intros x Hx. simpl in Hx. destruct Hx as [<-|[]]. exact Hn1. }
        pose proof (emit_sz (DFG_Unary (tf_resize source_size) id) size s1 Hp1 Hq1 Hargs) as He.
        destruct (emit ctx (DFG_Unary (tf_resize source_size) id) size s1) as [id2 s2].
        destruct He as [Hg2 [Hn2 [Hp2 [Hq2 Hs2]]]].
        split; [ eapply wgmono_trans; eauto
               | split; [ exact Hn2 | split; [ exact Hp2 | split; [ exact Hq2 | exact Hs2 ] ] ] ].
    - (* tf_op2 *)
      simpl. destruct op;
        try (apply (seq_sz _ _ _ size);
          [ intros Hi Hv;
            match goal with |- context[dataflow_expr ctx e1 ?z _] =>
              pose proof (IHe1 z s Hi Hv) as H; destruct (dataflow_expr ctx e1 z s) as [id1 s1] end;
            exact (sz_weaken _ _ _ _ _ H)
          | intros id1 s1 Hg1 Hn1 Hp1 Hq1; apply (seq_sz _ _ _ size);
            [ intros Hi Hv;
              match goal with |- context[dataflow_expr ctx e2 ?z _] =>
                pose proof (IHe2 z s1 Hi Hv) as H; destruct (dataflow_expr ctx e2 z s1) as [id2 s2] end;
              exact (sz_weaken _ _ _ _ _ H)
            | intros id2 s2 Hg2 Hn2 Hp2 Hq2; apply emit_sz;
              [ exact Hp2 | exact Hq2
              | intros x Hx; simpl in Hx; destruct Hx as [<-|[<-|[]]];
                [ eapply wnidwf_gmono; [ exact Hn1 | exact Hg2 ] | exact Hn2 ] ]
            | exact Hp1 | exact Hq1 ]
          | exact Hinv | exact Hvsz ]).
    - (* tf_expr_if *)
      simpl. apply (seq_sz _ _ _ size).
      + intros Hi Hv. pose proof (IHe1 1 s Hi Hv) as H.
        destruct (dataflow_expr ctx e1 1 s) as [idc s1]. exact (sz_weaken _ _ _ _ _ H).
      + intros idc s1 Hgc Hnc Hpc Hqc. apply (seq_sz _ _ _ size).
        * intros Hi Hv. pose proof (IHe2 size s1 Hi Hv) as H.
          destruct (dataflow_expr ctx e2 size s1) as [idt s2]. exact (sz_weaken _ _ _ _ _ H).
        * intros idt s2 Hgt Hnt Hpt Hqt. apply (seq_sz _ _ _ size).
          -- intros Hi Hv. pose proof (IHe3 size s2 Hi Hv) as H.
             destruct (dataflow_expr ctx e3 size s2) as [ide s3]. exact (sz_weaken _ _ _ _ _ H).
          -- intros ide s3 Hge Hne Hpe Hqe. apply emit_sz;
               [ exact Hpe | exact Hqe
               | intros x Hx; simpl in Hx; destruct Hx as [<-|[<-|[<-|[]]]];
                 [ eapply wnidwf_gmono; [ exact Hnc | eapply wgmono_trans; [ exact Hgt | exact Hge ] ]
                 | eapply wnidwf_gmono; [ exact Hnt | exact Hge ] | exact Hne ] ].
          -- exact Hpt.
          -- exact Hqt.
        * exact Hpc.
        * exact Hqc.
      + exact Hinv.
      + exact Hvsz.
  Qed.

  (* ===================================================================== *)
  (* STI-2 (wfg): every node's args are recorded at the size the node's op  *)
  (* demands of them (which the eval of compile_dfg_expr pushes down).      *)
  (*  - Unary not a         : a has sz = node.sz                            *)
  (*  - Unary resize n a    : a has sz = n                                  *)
  (*  - Binary (cmp szC) a b : a,b have sz = szC                            *)
  (*  - Binary other  a b    : a,b have sz = node.sz                        *)
  (*  - Phi c t e            : c has sz 1, t,e have sz = node.sz            *)
  (*  - DFG_Resize / leaves  : no constraint (handled by op-split in subst) *)
  (* Threaded through dataflow_expr; each emit establishes the new node's   *)
  (* constraint from the args' [wsz] returned by the recursive calls.       *)
  (* ===================================================================== *)

  Definition node_args_sz (s: wst) (node: @dfg_node_t s_var i_var o_var) : Prop :=
    match op node with
    | DFG_Unary uop a =>
        match uop with
        | tf_not => wsz s a (sz node)
        | tf_resize source_size => wsz s a source_size
        end
    | DFG_Binary bop a1 a2 =>
        match bop with
        | tf_cmp szC _ => wsz s a1 szC /\ wsz s a2 szC
        | _ => wsz s a1 (sz node) /\ wsz s a2 (sz node)
        end
    | DFG_Phi c t e => wsz s c 1 /\ wsz s t (sz node) /\ wsz s e (sz node)
    | _ => True
    end.

  Definition wfg (s: wst) : Prop :=
    forall node, In node (graph s) -> node_args_sz s node.

  Lemma node_args_sz_gmono s s' node :
    node_args_sz s node -> wgmono s s' -> node_args_sz s' node.
  Proof.
    unfold node_args_sz. intros H Hg.
    destruct (op node) as [c|v|v|uop a|bop a1 a2|a|cd t e|];
      [ exact I | exact I | exact I | | | exact I | | exact I ].
    - destruct uop; eapply wsz_gmono; eauto.
    - destruct bop; destruct H as [H1 H2]; split; eapply wsz_gmono; eauto.
    - destruct H as [H1 [H2 H3]]; repeat split; eapply wsz_gmono; eauto.
  Qed.

  Lemma emit_fg op size (s: wst) :
    winv s -> wvsz s -> wfg s ->
    (forall x, In x (get_args ctx {| nid := length (graph s); op := op; sz := size |}) -> wnidwf s x) ->
    node_args_sz s {| nid := length (graph s); op := op; sz := size |} ->
    let (id, s') := emit ctx op size s in
    wgmono s s' /\ wnidwf s' id /\ winv s' /\ wvsz s' /\ wsz s' id size /\ wfg s'.
  Proof.
    intros Hinv Hvsz Hfg Hargs Hnode.
    pose proof (emit_sz op size s Hinv Hvsz Hargs) as Hsz.
    rewrite emit_red in Hsz |- *.
    destruct Hsz as [Hg [Hn [Hw [Hvs Hs]]]].
    split; [ exact Hg | split; [ exact Hn | split; [ exact Hw | split; [ exact Hvs | split; [ exact Hs | ] ] ] ] ].
    intros node Hin. cbn [graph] in Hin. destruct Hin as [<-|Hin].
    - eapply node_args_sz_gmono; [ exact Hnode | exact Hg ].
    - eapply node_args_sz_gmono; [ apply Hfg; exact Hin | exact Hg ].
  Qed.

  Lemma ensure_var_fg v (s: wst) :
    winv s -> wvsz s -> wfg s ->
    let (id, s') := ensure_var ctx v s in
    wgmono s s' /\ wnidwf s' id /\ winv s' /\ wvsz s' /\ wsz s' id (dfg_var_size ctx v) /\ wfg s'.
  Proof.
    intros Hinv Hvsz Hfg.
    destruct (ensure_var ctx v s) as [id s'] eqn:Ev.
    pose proof (ensure_var_sz v s Hinv Hvsz) as Hsz. rewrite Ev in Hsz.
    destruct Hsz as [Hg [Hn [Hw [Hvs Hs]]]].
    pose proof (ensure_var_graph v s id s' Ev) as [Hgr Hid].
    split; [ exact Hg | split; [ exact Hn | split; [ exact Hw | split; [ exact Hvs | split; [ exact Hs | ] ] ] ] ].
    intros node Hin. rewrite Hgr in Hin. cbn [In] in Hin. destruct Hin as [<-|Hin].
    - unfold node_args_sz. cbn [op]. exact I.
    - eapply node_args_sz_gmono; [ apply Hfg; exact Hin | exact Hg ].
  Qed.

  Lemma get_var_fg v (s: wst) :
    winv s -> wvsz s -> wfg s ->
    let (id, s') := get_var ctx v s in
    wgmono s s' /\ wnidwf s' id /\ winv s' /\ wvsz s' /\ wsz s' id (dfg_var_size ctx v) /\ wfg s'.
  Proof.
    intros Hinv Hvsz Hfg. unfold get_var, bind, get_state.
    destruct (BitsToLists.list_assoc (var_map s) v) as [id|] eqn:E.
    - unfold ret.
      split; [ apply wgmono_refl | split; [ | split; [ exact Hinv | split; [ exact Hvsz | split; [ | exact Hfg ] ] ] ] ].
      + destruct Hinv as [Hv _]. apply wla_in in E.
        destruct (Hv v id E) as [node [Hn Hnid]]. exists node; split; assumption.
      + apply wla_in in E. apply Hvsz. exact E.
    - apply ensure_var_fg; assumption.
  Qed.

  Lemma dataflow_var_fg (dv: @dfg_vars_t s_var o_var) (size: sz_t) (s: wst) :
    winv s -> wvsz s -> wfg s ->
    let (id, s') :=
      (bind ctx (get_var ctx dv)
        (fun src_id =>
          if Nat.eqb (dfg_var_size ctx dv) size then ret ctx src_id
          else emit ctx (DFG_Resize src_id) size)) s in
    wgmono s s' /\ wnidwf s' id /\ winv s' /\ wvsz s' /\ wsz s' id size /\ wfg s'.
  Proof.
    intros Hinv Hvsz Hfg. unfold bind.
    pose proof (get_var_fg dv s Hinv Hvsz Hfg) as Hgv.
    destruct (get_var ctx dv s) as [id s1].
    destruct Hgv as [Hg1 [Hn1 [Hp1 [Hq1 [Hs1 Hf1]]]]].
    destruct (Nat.eqb (dfg_var_size ctx dv) size) eqn:Eb.
    - apply Nat.eqb_eq in Eb. unfold ret.
      split; [ exact Hg1 | split; [ exact Hn1 | split; [ exact Hp1 | split; [ exact Hq1 | split; [ | exact Hf1 ] ] ] ] ].
      rewrite <- Eb. exact Hs1.
    - assert (Hargs : forall x, In x (get_args ctx {| nid := length (graph s1); op := DFG_Resize id; sz := size |}) -> wnidwf s1 x).
      { intros x Hx. simpl in Hx. destruct Hx as [<-|[]]. exact Hn1. }
      assert (Hnode : node_args_sz s1 {| nid := length (graph s1); op := DFG_Resize id; sz := size |})
        by (unfold node_args_sz; cbn [op]; exact I).
      pose proof (emit_fg (DFG_Resize id) size s1 Hp1 Hq1 Hf1 Hargs Hnode) as He.
      destruct (emit ctx (DFG_Resize id) size s1) as [id2 s2].
      destruct He as [Hg2 [Hn2 [Hp2 [Hq2 [Hs2 Hf2]]]]].
      split; [ eapply wgmono_trans; eauto | split; [ exact Hn2 | split; [ exact Hp2 | split; [ exact Hq2 | split; [ exact Hs2 | exact Hf2 ] ] ] ] ].
  Qed.

  Lemma dataflow_expr_fg :
    forall e size (s: wst), winv s -> wvsz s -> wfg s ->
      let (id, s') := dataflow_expr ctx e size s in
      wgmono s s' /\ wnidwf s' id /\ winv s' /\ wvsz s' /\ wsz s' id size /\ wfg s'.
  Proof.
    induction e; intros size s Hinv Hvsz Hfg.
    - (* tf_const *)
      simpl. apply emit_fg; [ exact Hinv | exact Hvsz | exact Hfg
        | intros x Hx; simpl in Hx; destruct Hx
        | unfold node_args_sz; cbn [op]; exact I ].
    - (* tf_svar *)
      simpl. apply dataflow_var_fg; assumption.
    - (* tf_ivar *)
      cbn [dataflow_expr]. unfold bind.
      assert (Hargs0 : forall x, In x (get_args ctx {| nid := length (graph s); op := DFG_Input v; sz := size |}) -> wnidwf s x)
        by (intros x Hx; simpl in Hx; destruct Hx).
      assert (Hnode0 : node_args_sz s {| nid := length (graph s); op := DFG_Input v; sz := size |})
        by (unfold node_args_sz; cbn [op]; exact I).
      pose proof (emit_fg (DFG_Input v) size s Hinv Hvsz Hfg Hargs0 Hnode0) as He.
      destruct (emit ctx (DFG_Input v) size s) as [id s1].
      destruct He as [Hg1 [Hn1 [Hp1 [Hq1 [Hs1 Hf1]]]]].
      destruct (Nat.eqb _ size) eqn:Eb.
      + unfold ret.
        split; [ exact Hg1 | split; [ exact Hn1 | split; [ exact Hp1 | split; [ exact Hq1 | split; [ exact Hs1 | exact Hf1 ] ] ] ] ].
      + assert (Hargs : forall x, In x (get_args ctx {| nid := length (graph s1); op := DFG_Resize id; sz := size |}) -> wnidwf s1 x)
          by (intros x Hx; simpl in Hx; destruct Hx as [<-|[]]; exact Hn1).
        assert (Hnode : node_args_sz s1 {| nid := length (graph s1); op := DFG_Resize id; sz := size |})
          by (unfold node_args_sz; cbn [op]; exact I).
        pose proof (emit_fg (DFG_Resize id) size s1 Hp1 Hq1 Hf1 Hargs Hnode) as He2.
        destruct (emit ctx (DFG_Resize id) size s1) as [id2 s2].
        destruct He2 as [Hg2 [Hn2 [Hp2 [Hq2 [Hs2 Hf2]]]]].
        split; [ eapply wgmono_trans; eauto | split; [ exact Hn2 | split; [ exact Hp2 | split; [ exact Hq2 | split; [ exact Hs2 | exact Hf2 ] ] ] ] ].
    - (* tf_ovar *)
      simpl. apply dataflow_var_fg; assumption.
    - (* tf_op1 *)
      rename op into uop.
      cbn [dataflow_expr]. destruct uop as [| source_size].
      + unfold bind.
        pose proof (IHe size s Hinv Hvsz Hfg) as H1.
        destruct (dataflow_expr ctx e size s) as [id1 s1].
        destruct H1 as [Hg1 [Hn1 [Hw1 [Hv1 [Hs1 Hf1]]]]].
        assert (Hargs : forall x, In x (get_args ctx {| nid := length (graph s1); op := DFG_Unary tf_not id1; sz := size |}) -> wnidwf s1 x)
          by (intros x Hx; simpl in Hx; destruct Hx as [<-|[]]; exact Hn1).
        assert (Hnode : node_args_sz s1 {| nid := length (graph s1); op := DFG_Unary tf_not id1; sz := size |})
          by (unfold node_args_sz; cbn [op sz]; exact Hs1).
        pose proof (emit_fg (DFG_Unary tf_not id1) size s1 Hw1 Hv1 Hf1 Hargs Hnode) as He.
        destruct (emit ctx (DFG_Unary tf_not id1) size s1) as [id2 s2].
        destruct He as [Hg2 [Hn2 [Hp2 [Hq2 [Hs2 Hf2]]]]].
        split; [ eapply wgmono_trans; [ exact Hg1 | exact Hg2 ]
               | split; [ exact Hn2 | split; [ exact Hp2 | split; [ exact Hq2 | split; [ exact Hs2 | exact Hf2 ] ] ] ] ].
      + unfold bind. cbv beta.
        destruct (dataflow_expr ctx e source_size s) as [id1 s1] eqn:Erun.
        pose proof (IHe source_size s Hinv Hvsz Hfg) as H1. rewrite Erun in H1.
        cbv beta iota. destruct H1 as [Hg1 [Hn1 [Hw1 [Hv1 [Hs1 Hf1]]]]].
        assert (Hargs : forall x,
            In x (get_args ctx
              {| nid := length (graph s1); op := DFG_Unary (tf_resize source_size) id1; sz := size |}) ->
            wnidwf s1 x)
          by (intros x Hx; simpl in Hx; destruct Hx as [<-|[]]; exact Hn1).
        assert (Hnode : node_args_sz s1
            {| nid := length (graph s1); op := DFG_Unary (tf_resize source_size) id1; sz := size |})
          by (unfold node_args_sz; cbn [op]; exact Hs1).
        pose proof (emit_fg (DFG_Unary (tf_resize source_size) id1) size s1
          Hw1 Hv1 Hf1 Hargs Hnode) as He.
        destruct (emit ctx (DFG_Unary (tf_resize source_size) id1) size s1) as [id2 s2].
        destruct He as [Hg2 [Hn2 [Hp2 [Hq2 [Hs2 Hf2]]]]].
        split; [ eapply wgmono_trans; [ exact Hg1 | exact Hg2 ]
               | split; [ exact Hn2 | split; [ exact Hp2 | split; [ exact Hq2 | split; [ exact Hs2 | exact Hf2 ] ] ] ] ].
    - (* tf_op2 *)
      rename op into bop0.
      cbn [dataflow_expr]. destruct bop0;
        (unfold bind;
         match goal with
         | |- context[dataflow_expr ctx e1 ?z s] =>
            pose proof (IHe1 z s Hinv Hvsz Hfg) as H1;
            destruct (dataflow_expr ctx e1 z s) as [id1 s1];
            destruct H1 as [Hg1 [Hn1 [Hw1 [Hv1 [Hs1 Hf1]]]]];
            pose proof (IHe2 z s1 Hw1 Hv1 Hf1) as H2;
            destruct (dataflow_expr ctx e2 z s1) as [id2 s2];
            destruct H2 as [Hg2 [Hn2 [Hw2 [Hv2 [Hs2 Hf2]]]]]
         end;
         match goal with
         | |- context[emit ctx ?opn ?szn ?sst] =>
            assert (Hargs : forall x, In x (get_args ctx {| nid := length (graph sst); op := opn; sz := szn |}) -> wnidwf sst x)
              by (intros x Hx; simpl in Hx; destruct Hx as [<-|[<-|[]]];
                  [ eapply wnidwf_gmono; [ exact Hn1 | exact Hg2 ] | exact Hn2 ]);
            assert (Hnode : node_args_sz sst {| nid := length (graph sst); op := opn; sz := szn |})
              by (unfold node_args_sz; cbn [op sz];
                  split; [ eapply wsz_gmono; [ exact Hs1 | exact Hg2 ] | exact Hs2 ]);
            pose proof (emit_fg opn szn sst Hw2 Hv2 Hf2 Hargs Hnode) as He;
            destruct (emit ctx opn szn sst) as [id3 s3];
            destruct He as [Hg3 [Hn3 [Hp3 [Hq3 [Hs3 Hf3]]]]]
         end;
         split; [ eapply wgmono_trans; [ exact Hg1 | eapply wgmono_trans; [ exact Hg2 | exact Hg3 ] ]
                | split; [ exact Hn3 | split; [ exact Hp3 | split; [ exact Hq3 | split; [ exact Hs3 | exact Hf3 ] ] ] ] ]).
    - (* tf_expr_if *)
      cbn [dataflow_expr]. unfold bind.
      pose proof (IHe1 1 s Hinv Hvsz Hfg) as H1.
      destruct (dataflow_expr ctx e1 1 s) as [idc s1].
      destruct H1 as [Hgc [Hnc [Hwc [Hvc [Hsc Hfc]]]]].
      pose proof (IHe2 size s1 Hwc Hvc Hfc) as H2.
      destruct (dataflow_expr ctx e2 size s1) as [idt s2].
      destruct H2 as [Hgt [Hnt [Hwt [Hvt [Hst Hft]]]]].
      pose proof (IHe3 size s2 Hwt Hvt Hft) as H3.
      destruct (dataflow_expr ctx e3 size s2) as [ide s3].
      destruct H3 as [Hge [Hne [Hwe [Hve [Hse Hfe]]]]].
      assert (Hargs : forall x, In x (get_args ctx {| nid := length (graph s3); op := DFG_Phi idc idt ide; sz := size |}) -> wnidwf s3 x)
        by (intros x Hx; simpl in Hx; destruct Hx as [<-|[<-|[<-|[]]]];
            [ eapply wnidwf_gmono; [ exact Hnc | eapply wgmono_trans; [ exact Hgt | exact Hge ] ]
            | eapply wnidwf_gmono; [ exact Hnt | exact Hge ] | exact Hne ]).
      assert (Hnode : node_args_sz s3 {| nid := length (graph s3); op := DFG_Phi idc idt ide; sz := size |})
        by (unfold node_args_sz; cbn [op sz];
            split; [ eapply wsz_gmono; [ exact Hsc | eapply wgmono_trans; [ exact Hgt | exact Hge ] ]
                   | split; [ eapply wsz_gmono; [ exact Hst | exact Hge ] | exact Hse ] ]).
      pose proof (emit_fg (DFG_Phi idc idt ide) size s3 Hwe Hve Hfe Hargs Hnode) as He.
      destruct (emit ctx (DFG_Phi idc idt ide) size s3) as [idp s4].
      destruct He as [Hg4 [Hn4 [Hp4 [Hq4 [Hs4 Hf4]]]]].
      split; [ eapply wgmono_trans; [ exact Hgc | eapply wgmono_trans; [ exact Hgt | eapply wgmono_trans; [ exact Hge | exact Hg4 ] ] ]
             | split; [ exact Hn4 | split; [ exact Hp4 | split; [ exact Hq4 | split; [ exact Hs4 | exact Hf4 ] ] ] ] ].
  Qed.

  (* --- map merger --- *)

  Lemma merge_key_full cond_id k vt_opt ve_opt (s: wst) res s' :
    merge_key ctx cond_id k vt_opt ve_opt s = (res, s') ->
    winv s -> wnidwf s cond_id ->
    (forall vt, vt_opt = Some vt -> wnidwf s vt) ->
    (forall ve, ve_opt = Some ve -> wnidwf s ve) ->
    wgmono s s' /\ winv s' /\ (forall fid, res = Some fid -> wnidwf s' fid).
  Proof.
    intros Hrun Hinv Hcond Hvt Hve. unfold merge_key in Hrun.
    destruct vt_opt as [vt|]; destruct ve_opt as [ve|].
    - (* Some/Some *)
      destruct (eq_dec vt ve) as [Heq|Hne].
      + unfold ret in Hrun. injection Hrun as <- <-.
        split; [ apply wgmono_refl | split; [ exact Hinv | ] ].
        intros fid Hf. injection Hf as <-. apply Hvt; reflexivity.
      + assert (Harg : forall x,
          In x (get_args ctx {| nid := length (graph s); op := DFG_Phi cond_id vt ve; sz := dfg_var_size ctx k |}) -> wnidwf s x).
        { intros x Hx. simpl in Hx. destruct Hx as [<-|[<-|[<-|[]]]].
          - exact Hcond. - apply Hvt; reflexivity. - apply Hve; reflexivity. }
        pose proof (emit_full (DFG_Phi cond_id vt ve) (dfg_var_size ctx k) s Hinv Harg) as He.
        destruct (emit ctx (DFG_Phi cond_id vt ve) (dfg_var_size ctx k) s) as [phi s1] eqn:Ee.
        destruct He as [Ge [Ne Pe]].
        rewrite (bind_red (emit ctx (DFG_Phi cond_id vt ve) (dfg_var_size ctx k)) _ s _ _ Ee) in Hrun.
        unfold ret in Hrun. injection Hrun as <- <-.
        split; [ exact Ge | split; [ exact Pe | ] ].
        intros fid Hf. injection Hf as <-. exact Ne.
    - (* Some/None *)
      destruct (ensure_var ctx k s) as [ve0 s1] eqn:Ev.
      pose proof (ensure_var_full k s Hinv) as Hev. rewrite Ev in Hev.
      destruct Hev as [Gv [Nv Pv]].
      rewrite (bind_red (ensure_var ctx k) _ s _ _ Ev) in Hrun.
      assert (Harg : forall x,
        In x (get_args ctx {| nid := length (graph s1); op := DFG_Phi cond_id vt ve0; sz := dfg_var_size ctx k |}) -> wnidwf s1 x).
      { intros x Hx. simpl in Hx. destruct Hx as [<-|[<-|[<-|[]]]].
        - eapply wnidwf_gmono; [ exact Hcond | exact Gv ].
        - eapply wnidwf_gmono; [ apply Hvt; reflexivity | exact Gv ].
        - exact Nv. }
      pose proof (emit_full (DFG_Phi cond_id vt ve0) (dfg_var_size ctx k) s1 Pv Harg) as He.
      destruct (emit ctx (DFG_Phi cond_id vt ve0) (dfg_var_size ctx k) s1) as [phi s2] eqn:Ee.
      destruct He as [Ge [Ne Pe]].
      rewrite (bind_red (emit ctx (DFG_Phi cond_id vt ve0) (dfg_var_size ctx k)) _ s1 _ _ Ee) in Hrun.
      unfold ret in Hrun. injection Hrun as <- <-.
      split; [ eapply wgmono_trans; eauto | split; [ exact Pe | ] ].
      intros fid Hf. injection Hf as <-. exact Ne.
    - (* None/Some *)
      destruct (ensure_var ctx k s) as [vt0 s1] eqn:Ev.
      pose proof (ensure_var_full k s Hinv) as Hev. rewrite Ev in Hev.
      destruct Hev as [Gv [Nv Pv]].
      rewrite (bind_red (ensure_var ctx k) _ s _ _ Ev) in Hrun.
      assert (Harg : forall x,
        In x (get_args ctx {| nid := length (graph s1); op := DFG_Phi cond_id vt0 ve; sz := dfg_var_size ctx k |}) -> wnidwf s1 x).
      { intros x Hx. simpl in Hx. destruct Hx as [<-|[<-|[<-|[]]]].
        - eapply wnidwf_gmono; [ exact Hcond | exact Gv ].
        - exact Nv.
        - eapply wnidwf_gmono; [ apply Hve; reflexivity | exact Gv ]. }
      pose proof (emit_full (DFG_Phi cond_id vt0 ve) (dfg_var_size ctx k) s1 Pv Harg) as He.
      destruct (emit ctx (DFG_Phi cond_id vt0 ve) (dfg_var_size ctx k) s1) as [phi s2] eqn:Ee.
      destruct He as [Ge [Ne Pe]].
      rewrite (bind_red (emit ctx (DFG_Phi cond_id vt0 ve) (dfg_var_size ctx k)) _ s1 _ _ Ee) in Hrun.
      unfold ret in Hrun. injection Hrun as <- <-.
      split; [ eapply wgmono_trans; eauto | split; [ exact Pe | ] ].
      intros fid Hf. injection Hf as <-. exact Ne.
    - (* None/None *)
      unfold ret in Hrun. injection Hrun as <- <-.
      split; [ apply wgmono_refl | split; [ exact Hinv | ] ].
      intros fid Hf. discriminate.
  Qed.

  Lemma merge_loop_full cond_id mt me :
    forall keys acc (s: wst) fin s',
      merge_loop ctx cond_id mt me keys acc s = (fin, s') ->
      winv s -> wnidwf s cond_id ->
      (forall k id, In (k, id) mt -> wnidwf s id) ->
      (forall k id, In (k, id) me -> wnidwf s id) ->
      (forall k id, In (k, id) acc -> wnidwf s id) ->
      wgmono s s' /\ winv s' /\ (forall k id, In (k, id) fin -> wnidwf s' id).
  Proof.
    induction keys as [|[k kv] rest IH]; intros acc s fin s' Hrun Hinv Hcond Hmt Hme Hacc.
    - simpl in Hrun. unfold ret in Hrun. injection Hrun as <- <-.
      split; [ apply wgmono_refl | split; [ exact Hinv | exact Hacc ] ].
    - simpl in Hrun.
      destruct (BitsToLists.list_assoc acc k) as [existing|] eqn:Ek.
      + eapply IH; eauto.
      + unfold bind in Hrun. cbv beta in Hrun.
        destruct (merge_key ctx cond_id k (BitsToLists.list_assoc mt k) (BitsToLists.list_assoc me k) s)
          as [res_opt s1] eqn:Emk.
        cbv beta iota in Hrun.
        pose proof (merge_key_full cond_id k _ _ s res_opt s1 Emk Hinv Hcond
                      (fun vt Hvt => Hmt k vt (wla_in mt k vt Hvt))
                      (fun ve Hve => Hme k ve (wla_in me k ve Hve))) as Hmk.
        destruct Hmk as [gk [pk nk]].
        assert (Hcond1 : wnidwf s1 cond_id) by (eapply wnidwf_gmono; eauto).
        assert (Hmt1 : forall k0 id, In (k0, id) mt -> wnidwf s1 id)
          by (intros k0 id Hin; eapply wnidwf_gmono; [ eapply Hmt; eauto | exact gk ]).
        assert (Hme1 : forall k0 id, In (k0, id) me -> wnidwf s1 id)
          by (intros k0 id Hin; eapply wnidwf_gmono; [ eapply Hme; eauto | exact gk ]).
        destruct res_opt as [final_id|].
        * assert (Hacc1 : forall k0 id, In (k0, id) ((k, final_id) :: acc) -> wnidwf s1 id).
          { intros k0 id Hin. simpl in Hin. destruct Hin as [Heq|Hin].
            - injection Heq as <- <-. apply nk; reflexivity.
            - eapply wnidwf_gmono; [ eapply Hacc; eauto | exact gk ]. }
          specialize (IH ((k, final_id) :: acc) s1 fin s' Hrun pk Hcond1 Hmt1 Hme1 Hacc1).
          destruct IH as [g' [p' n']].
          split; [ eapply wgmono_trans; eauto | split; [ exact p' | exact n' ] ].
        * assert (Hacc1 : forall k0 id, In (k0, id) acc -> wnidwf s1 id)
            by (intros k0 id Hin; eapply wnidwf_gmono; [ eapply Hacc; eauto | exact gk ]).
          specialize (IH acc s1 fin s' Hrun pk Hcond1 Hmt1 Hme1 Hacc1).
          destruct IH as [g' [p' n']].
          split; [ eapply wgmono_trans; eauto | split; [ exact p' | exact n' ] ].
  Qed.

  Lemma merge_maps_full cond_id mo mt me (s: wst) :
    winv s -> wnidwf s cond_id ->
    (forall k id, In (k, id) mt -> wnidwf s id) ->
    (forall k id, In (k, id) me -> wnidwf s id) ->
    let (fin, s') := merge_maps ctx cond_id mo mt me s in
    wgmono s s' /\ winv s' /\ (forall k id, In (k, id) fin -> wnidwf s' id).
  Proof.
    intros Hinv Hcond Hmt Hme. unfold merge_maps.
    destruct (merge_loop ctx cond_id mt me (mt ++ me) [] s) as [fin s'] eqn:Er.
    eapply merge_loop_full;
      [ exact Er | exact Hinv | exact Hcond | exact Hmt | exact Hme
      | intros k id Hin; destruct Hin ].
  Qed.

  (* --- operations compiler --- *)

  Lemma dataflow_ops_full :
    forall ops (s: wst), winv s ->
      let (u, s') := dataflow_ops ctx ops s in wgmono s s' /\ winv s'.
  Proof.
    induction ops as [op | op1 IHops1 op2 IHops2 | cond op1 IHops1 op2 IHops2];
      intros s Hinv.
    - (* base *)
      destruct op.
      + (* nop *) simpl. unfold ret. split; [ apply wgmono_refl | exact Hinv ].
      + (* assign dst expr *)
        simpl.
        pose proof (dataflow_expr_full expr (dfg_var_size ctx (DFG_SVar dst)) s Hinv) as He.
        destruct (dataflow_expr ctx expr (dfg_var_size ctx (DFG_SVar dst)) s) as [res_id s1] eqn:Ee.
        destruct He as [Ge [Ne Pe]].
        rewrite (bind_red (dataflow_expr ctx expr (dfg_var_size ctx (DFG_SVar dst))) _ s _ _ Ee).
        pose proof (set_var_full (DFG_SVar dst) res_id s1 Pe Ne) as Hs.
        destruct (set_var ctx (DFG_SVar dst) res_id s1) as [u s'] eqn:Es.
        destruct Hs as [Gs Ps].
        split; [ eapply wgmono_trans; eauto | exact Ps ].
      + (* output dst expr *)
        simpl.
        pose proof (dataflow_expr_full expr (dfg_var_size ctx (DFG_OVar dst)) s Hinv) as He.
        destruct (dataflow_expr ctx expr (dfg_var_size ctx (DFG_OVar dst)) s) as [res_id s1] eqn:Ee.
        destruct He as [Ge [Ne Pe]].
        rewrite (bind_red (dataflow_expr ctx expr (dfg_var_size ctx (DFG_OVar dst))) _ s _ _ Ee).
        pose proof (set_var_full (DFG_OVar dst) res_id s1 Pe Ne) as Hs.
        destruct (set_var ctx (DFG_OVar dst) res_id s1) as [u s'] eqn:Es.
        destruct Hs as [Gs Ps].
        split; [ eapply wgmono_trans; eauto | exact Ps ].
    - (* cons *)
      simpl.
      pose proof (IHops1 s Hinv) as H1.
      destruct (dataflow_ops ctx op1 s) as [u1 s1] eqn:E1.
      destruct H1 as [G1 P1].
      rewrite (bind_red (dataflow_ops ctx op1) _ s _ _ E1).
      pose proof (IHops2 s1 P1) as H2.
      destruct (dataflow_ops ctx op2 s1) as [u2 s2] eqn:E2.
      destruct H2 as [G2 P2].
      split; [ eapply wgmono_trans; eauto | exact P2 ].
    - (* if *)
      simpl.
      (* cond *)
      pose proof (dataflow_expr_full cond 1 s Hinv) as Hc.
      destruct (dataflow_expr ctx cond 1 s) as [cond_id s1] eqn:Ec.
      destruct Hc as [Gc [Nc Pc]].
      rewrite (bind_red (dataflow_expr ctx cond 1) _ s _ _ Ec).
      (* get_state -> s_orig = s1 *)
      rewrite (bind_red (get_state ctx) _ s1 _ _ (get_state_red s1)).
      (* then branch *)
      pose proof (IHops1 s1 Pc) as Hthen.
      destruct (dataflow_ops ctx op1 s1) as [ut s_then] eqn:Et.
      destruct Hthen as [Gthen Pthen].
      rewrite (bind_red (dataflow_ops ctx op1) _ s1 _ _ Et).
      (* get_state -> s_then *)
      rewrite (bind_red (get_state ctx) _ s_then _ _ (get_state_red s_then)).
      (* restore put_state *)
      set (sR := {| graph := graph s_then; var_map := var_map s1 |} : wst).
      rewrite (bind_red (put_state ctx sR) _ s_then _ _ (put_state_red sR s_then)).
      (* sR->s_then graph identity gmono *)
      assert (Gthen_sR : wgmono s_then sR) by (intros n Hn; unfold sR; simpl; exact Hn).
      assert (GsR_then : wgmono sR s_then) by (intros n Hn; unfold sR in Hn; simpl in Hn; exact Hn).
      (* winv sR *)
      assert (PsR : winv sR).
      { destruct Pc as [Hv1 [Hns1 Hab1]]. destruct Pthen as [Hvt [Hnst Habt]].
        split; [ | split ].
        - intros k id Hin. unfold sR in Hin; simpl in Hin.
          destruct (Hv1 k id Hin) as [node [Hn Hnid]].
          exists node. split; [ unfold sR; simpl; apply Gthen; exact Hn | exact Hnid ].
        - unfold nid_seq, sR; simpl. exact Hnst.
        - unfold sR; simpl. exact Habt. }
      (* else branch on sR *)
      pose proof (IHops2 sR PsR) as Helse.
      destruct (dataflow_ops ctx op2 sR) as [ue s_else] eqn:Ee.
      destruct Helse as [Gelse Pelse].
      rewrite (bind_red (dataflow_ops ctx op2) _ sR _ _ Ee).
      (* get_state -> s_else *)
      rewrite (bind_red (get_state ctx) _ s_else _ _ (get_state_red s_else)).
      (* compose gmono s1 -> s_else *)
      assert (Gs1_selse : wgmono s1 s_else)
        by (eapply wgmono_trans; [ exact Gthen | eapply wgmono_trans; [ exact Gthen_sR | exact Gelse ] ]).
      assert (Ncond : wnidwf s_else cond_id) by (eapply wnidwf_gmono; [ exact Nc | exact Gs1_selse ]).
      assert (Hmt : forall k id, In (k, id) (var_map s_then) -> wnidwf s_else id).
      { intros k id Hin. destruct Pthen as [Hvt _]. destruct (Hvt k id Hin) as [node [Hn Hnid]].
        exists node. split;
          [ apply (wgmono_trans s_then sR s_else Gthen_sR Gelse); exact Hn | exact Hnid ]. }
      assert (Hme : forall k id, In (k, id) (var_map s_else) -> wnidwf s_else id).
      { intros k id Hin. destruct Pelse as [Hve _]. exact (Hve k id Hin). }
      pose proof (merge_maps_full cond_id (var_map s1) (var_map s_then) (var_map s_else) s_else
                    Pelse Ncond Hmt Hme) as Hmerge.
      destruct (merge_maps ctx cond_id (var_map s1) (var_map s_then) (var_map s_else) s_else)
        as [final_vars s_final] eqn:Em.
      destruct Hmerge as [Gmerge [Pfinal Nfinal]].
      rewrite (bind_red (merge_maps ctx cond_id (var_map s1) (var_map s_then) (var_map s_else)) _ s_else _ _ Em).
      (* get_state -> s_final *)
      rewrite (bind_red (get_state ctx) _ s_final _ _ (get_state_red s_final)).
      (* final put_state *)
      set (sF := {| graph := graph s_final; var_map := final_vars |} : wst).
      rewrite (put_state_red sF s_final).
      split.
      + (* gmono s sF *)
        intros n Hn. unfold sF; simpl.
        apply Gmerge. apply Gs1_selse. apply Gc. exact Hn.
      + (* winv sF *)
        destruct Pfinal as [Hvf [Hnsf Habf]]. split; [ | split ].
        * intros k id Hin. unfold sF in Hin; simpl in Hin.
          destruct (Nfinal k id Hin) as [node [Hn Hnid]].
          exists node. split; [ unfold sF; simpl; exact Hn | exact Hnid ].
        * unfold nid_seq, sF; simpl. exact Hnsf.
        * unfold sF; simpl. exact Habf.
  Qed.

  (* ===================================================================== *)
  (* STI-2 lifting: thread [wvsz] and [wfg] through the whole operations    *)
  (* compiler, including the control-flow merge (Phi emission).  Mirrors    *)
  (* the [_full] chain but additionally carries the size invariants.        *)
  (* ===================================================================== *)

  Lemma set_var_fg v id (s: wst) :
    winv s -> wvsz s -> wfg s -> wnidwf s id -> wsz s id (dfg_var_size ctx v) ->
    let (u, s') := set_var ctx v id s in
    wgmono s s' /\ winv s' /\ wvsz s' /\ wfg s'.
  Proof.
    intros Hinv Hvsz Hfg Hnw Hsz.
    pose proof (set_var_full v id s Hinv Hnw) as Hf.
    unfold set_var, bind, get_state, put_state in Hf |- *. simpl in Hf |- *.
    destruct Hf as [Gs Ps].
    split; [ exact Gs | split; [ exact Ps | split ] ].
    - intros v0 id0 Hin. simpl in Hin. destruct Hin as [Heq|Hin].
      + injection Heq as <- <-. eapply wsz_gmono; [ exact Hsz | exact Gs ].
      + apply filter_In in Hin. destruct Hin as [Hin _].
        eapply wsz_gmono; [ apply Hvsz; exact Hin | exact Gs ].
    - intros node Hin. simpl in Hin.
      eapply node_args_sz_gmono; [ apply Hfg; exact Hin | exact Gs ].
  Qed.

  Lemma merge_key_fg cond_id k vt_opt ve_opt (s: wst) res s' :
    merge_key ctx cond_id k vt_opt ve_opt s = (res, s') ->
    winv s -> wvsz s -> wfg s ->
    wnidwf s cond_id -> wsz s cond_id 1 ->
    (forall vt, vt_opt = Some vt -> wnidwf s vt) ->
    (forall ve, ve_opt = Some ve -> wnidwf s ve) ->
    (forall vt, vt_opt = Some vt -> wsz s vt (dfg_var_size ctx k)) ->
    (forall ve, ve_opt = Some ve -> wsz s ve (dfg_var_size ctx k)) ->
    wgmono s s' /\ winv s' /\ wvsz s' /\ wfg s' /\
    (forall fid, res = Some fid -> wnidwf s' fid) /\
    (forall fid, res = Some fid -> wsz s' fid (dfg_var_size ctx k)).
  Proof.
    intros Hrun Hinv Hvsz Hfg Hcondn Hconds Hvtn Hven Hvts Hves.
    unfold merge_key in Hrun.
    destruct vt_opt as [vt|]; destruct ve_opt as [ve|].
    - (* Some/Some *)
      destruct (eq_dec vt ve) as [Heq|Hne].
      + unfold ret in Hrun. injection Hrun as <- <-.
        split; [ apply wgmono_refl | split; [ exact Hinv | split; [ exact Hvsz | split; [ exact Hfg | split ] ] ] ].
        * intros fid Hf. injection Hf as <-. apply Hvtn; reflexivity.
        * intros fid Hf. injection Hf as <-. apply Hvts; reflexivity.
      + assert (Harg : forall x,
          In x (get_args ctx {| nid := length (graph s); op := DFG_Phi cond_id vt ve; sz := dfg_var_size ctx k |}) -> wnidwf s x).
        { intros x Hx. simpl in Hx. destruct Hx as [<-|[<-|[<-|[]]]].
          - exact Hcondn. - apply Hvtn; reflexivity. - apply Hven; reflexivity. }
        assert (Hnode : node_args_sz s {| nid := length (graph s); op := DFG_Phi cond_id vt ve; sz := dfg_var_size ctx k |}).
        { unfold node_args_sz. cbn [op sz].
          split; [ exact Hconds | split; [ apply Hvts; reflexivity | apply Hves; reflexivity ] ]. }
        pose proof (emit_fg (DFG_Phi cond_id vt ve) (dfg_var_size ctx k) s Hinv Hvsz Hfg Harg Hnode) as He.
        destruct (emit ctx (DFG_Phi cond_id vt ve) (dfg_var_size ctx k) s) as [phi s1] eqn:Ee.
        destruct He as [Ge [Ne [Pe [Qe [Se Fe]]]]].
        rewrite (bind_red (emit ctx (DFG_Phi cond_id vt ve) (dfg_var_size ctx k)) _ s _ _ Ee) in Hrun.
        unfold ret in Hrun. injection Hrun as <- <-.
        split; [ exact Ge | split; [ exact Pe | split; [ exact Qe | split; [ exact Fe | split ] ] ] ].
        * intros fid Hf. injection Hf as <-. exact Ne.
        * intros fid Hf. injection Hf as <-. exact Se.
    - (* Some/None *)
      destruct (ensure_var ctx k s) as [ve0 s1] eqn:Ev.
      pose proof (ensure_var_fg k s Hinv Hvsz Hfg) as Hev. rewrite Ev in Hev.
      destruct Hev as [Gv [Nv [Pv [Qv [Sv Fv]]]]].
      rewrite (bind_red (ensure_var ctx k) _ s _ _ Ev) in Hrun.
      assert (Harg : forall x,
        In x (get_args ctx {| nid := length (graph s1); op := DFG_Phi cond_id vt ve0; sz := dfg_var_size ctx k |}) -> wnidwf s1 x).
      { intros x Hx. simpl in Hx. destruct Hx as [<-|[<-|[<-|[]]]].
        - eapply wnidwf_gmono; [ exact Hcondn | exact Gv ].
        - eapply wnidwf_gmono; [ apply Hvtn; reflexivity | exact Gv ].
        - exact Nv. }
      assert (Hnode : node_args_sz s1 {| nid := length (graph s1); op := DFG_Phi cond_id vt ve0; sz := dfg_var_size ctx k |}).
      { unfold node_args_sz. cbn [op sz].
        split; [ eapply wsz_gmono; [ exact Hconds | exact Gv ]
               | split; [ eapply wsz_gmono; [ apply Hvts; reflexivity | exact Gv ] | exact Sv ] ]. }
      pose proof (emit_fg (DFG_Phi cond_id vt ve0) (dfg_var_size ctx k) s1 Pv Qv Fv Harg Hnode) as He.
      destruct (emit ctx (DFG_Phi cond_id vt ve0) (dfg_var_size ctx k) s1) as [phi s2] eqn:Ee.
      destruct He as [Ge [Ne [Pe [Qe [Se Fe]]]]].
      rewrite (bind_red (emit ctx (DFG_Phi cond_id vt ve0) (dfg_var_size ctx k)) _ s1 _ _ Ee) in Hrun.
      unfold ret in Hrun. injection Hrun as <- <-.
      split; [ eapply wgmono_trans; eauto | split; [ exact Pe | split; [ exact Qe | split; [ exact Fe | split ] ] ] ].
      * intros fid Hf. injection Hf as <-. exact Ne.
      * intros fid Hf. injection Hf as <-. exact Se.
    - (* None/Some *)
      destruct (ensure_var ctx k s) as [vt0 s1] eqn:Ev.
      pose proof (ensure_var_fg k s Hinv Hvsz Hfg) as Hev. rewrite Ev in Hev.
      destruct Hev as [Gv [Nv [Pv [Qv [Sv Fv]]]]].
      rewrite (bind_red (ensure_var ctx k) _ s _ _ Ev) in Hrun.
      assert (Harg : forall x,
        In x (get_args ctx {| nid := length (graph s1); op := DFG_Phi cond_id vt0 ve; sz := dfg_var_size ctx k |}) -> wnidwf s1 x).
      { intros x Hx. simpl in Hx. destruct Hx as [<-|[<-|[<-|[]]]].
        - eapply wnidwf_gmono; [ exact Hcondn | exact Gv ].
        - exact Nv.
        - eapply wnidwf_gmono; [ apply Hven; reflexivity | exact Gv ]. }
      assert (Hnode : node_args_sz s1 {| nid := length (graph s1); op := DFG_Phi cond_id vt0 ve; sz := dfg_var_size ctx k |}).
      { unfold node_args_sz. cbn [op sz].
        split; [ eapply wsz_gmono; [ exact Hconds | exact Gv ]
               | split; [ exact Sv | eapply wsz_gmono; [ apply Hves; reflexivity | exact Gv ] ] ]. }
      pose proof (emit_fg (DFG_Phi cond_id vt0 ve) (dfg_var_size ctx k) s1 Pv Qv Fv Harg Hnode) as He.
      destruct (emit ctx (DFG_Phi cond_id vt0 ve) (dfg_var_size ctx k) s1) as [phi s2] eqn:Ee.
      destruct He as [Ge [Ne [Pe [Qe [Se Fe]]]]].
      rewrite (bind_red (emit ctx (DFG_Phi cond_id vt0 ve) (dfg_var_size ctx k)) _ s1 _ _ Ee) in Hrun.
      unfold ret in Hrun. injection Hrun as <- <-.
      split; [ eapply wgmono_trans; eauto | split; [ exact Pe | split; [ exact Qe | split; [ exact Fe | split ] ] ] ].
      * intros fid Hf. injection Hf as <-. exact Ne.
      * intros fid Hf. injection Hf as <-. exact Se.
    - (* None/None *)
      unfold ret in Hrun. injection Hrun as <- <-.
      split; [ apply wgmono_refl | split; [ exact Hinv | split; [ exact Hvsz | split; [ exact Hfg | split ] ] ] ].
      * intros fid Hf. discriminate.
      * intros fid Hf. discriminate.
  Qed.

  Lemma merge_loop_fg cond_id mt me :
    forall keys acc (s: wst) fin s',
      merge_loop ctx cond_id mt me keys acc s = (fin, s') ->
      winv s -> wvsz s -> wfg s ->
      wnidwf s cond_id -> wsz s cond_id 1 ->
      (forall k id, In (k, id) mt -> wnidwf s id) ->
      (forall k id, In (k, id) me -> wnidwf s id) ->
      (forall k id, In (k, id) mt -> wsz s id (dfg_var_size ctx k)) ->
      (forall k id, In (k, id) me -> wsz s id (dfg_var_size ctx k)) ->
      (forall k id, In (k, id) acc -> wnidwf s id) ->
      (forall k id, In (k, id) acc -> wsz s id (dfg_var_size ctx k)) ->
      wgmono s s' /\ winv s' /\ wvsz s' /\ wfg s' /\
      (forall k id, In (k, id) fin -> wnidwf s' id) /\
      (forall k id, In (k, id) fin -> wsz s' id (dfg_var_size ctx k)).
  Proof.
    induction keys as [|[k kv] rest IH];
      intros acc s fin s' Hrun Hinv Hvsz Hfg Hcondn Hconds Hmtn Hmen Hmts Hmes Haccn Haccs.
    - simpl in Hrun. unfold ret in Hrun. injection Hrun as <- <-.
      split; [ apply wgmono_refl | split; [ exact Hinv | split; [ exact Hvsz | split; [ exact Hfg | split; [ exact Haccn | exact Haccs ] ] ] ] ].
    - simpl in Hrun.
      destruct (BitsToLists.list_assoc acc k) as [existing|] eqn:Ek.
      + eapply IH; eauto.
      + unfold bind in Hrun. cbv beta in Hrun.
        destruct (merge_key ctx cond_id k (BitsToLists.list_assoc mt k) (BitsToLists.list_assoc me k) s)
          as [res_opt s1] eqn:Emk.
        cbv beta iota in Hrun.
        pose proof (merge_key_fg cond_id k _ _ s res_opt s1 Emk Hinv Hvsz Hfg Hcondn Hconds
                      (fun vt Hvt => Hmtn k vt (wla_in mt k vt Hvt))
                      (fun ve Hve => Hmen k ve (wla_in me k ve Hve))
                      (fun vt Hvt => Hmts k vt (wla_in mt k vt Hvt))
                      (fun ve Hve => Hmes k ve (wla_in me k ve Hve))) as Hmk.
        destruct Hmk as [gk [pk [qk [fk [nk sk]]]]].
        assert (Hcondn1 : wnidwf s1 cond_id) by (eapply wnidwf_gmono; eauto).
        assert (Hconds1 : wsz s1 cond_id 1) by (eapply wsz_gmono; eauto).
        assert (Hmtn1 : forall k0 id, In (k0, id) mt -> wnidwf s1 id)
          by (intros k0 id Hin; eapply wnidwf_gmono; [ eapply Hmtn; eauto | exact gk ]).
        assert (Hmen1 : forall k0 id, In (k0, id) me -> wnidwf s1 id)
          by (intros k0 id Hin; eapply wnidwf_gmono; [ eapply Hmen; eauto | exact gk ]).
        assert (Hmts1 : forall k0 id, In (k0, id) mt -> wsz s1 id (dfg_var_size ctx k0))
          by (intros k0 id Hin; eapply wsz_gmono; [ eapply Hmts; eauto | exact gk ]).
        assert (Hmes1 : forall k0 id, In (k0, id) me -> wsz s1 id (dfg_var_size ctx k0))
          by (intros k0 id Hin; eapply wsz_gmono; [ eapply Hmes; eauto | exact gk ]).
        destruct res_opt as [final_id|].
        * assert (Haccn1 : forall k0 id, In (k0, id) ((k, final_id) :: acc) -> wnidwf s1 id).
          { intros k0 id Hin. simpl in Hin. destruct Hin as [Heq|Hin].
            - injection Heq as <- <-. apply nk; reflexivity.
            - eapply wnidwf_gmono; [ eapply Haccn; eauto | exact gk ]. }
          assert (Haccs1 : forall k0 id, In (k0, id) ((k, final_id) :: acc) -> wsz s1 id (dfg_var_size ctx k0)).
          { intros k0 id Hin. simpl in Hin. destruct Hin as [Heq|Hin].
            - injection Heq as <- <-. apply sk; reflexivity.
            - eapply wsz_gmono; [ eapply Haccs; eauto | exact gk ]. }
          specialize (IH ((k, final_id) :: acc) s1 fin s' Hrun pk qk fk Hcondn1 Hconds1 Hmtn1 Hmen1 Hmts1 Hmes1 Haccn1 Haccs1).
          destruct IH as [g' [p' [q' [f' [n' s'']]]]].
          split; [ eapply wgmono_trans; eauto | split; [ exact p' | split; [ exact q' | split; [ exact f' | split; [ exact n' | exact s'' ] ] ] ] ].
        * assert (Haccn1 : forall k0 id, In (k0, id) acc -> wnidwf s1 id)
            by (intros k0 id Hin; eapply wnidwf_gmono; [ eapply Haccn; eauto | exact gk ]).
          assert (Haccs1 : forall k0 id, In (k0, id) acc -> wsz s1 id (dfg_var_size ctx k0))
            by (intros k0 id Hin; eapply wsz_gmono; [ eapply Haccs; eauto | exact gk ]).
          specialize (IH acc s1 fin s' Hrun pk qk fk Hcondn1 Hconds1 Hmtn1 Hmen1 Hmts1 Hmes1 Haccn1 Haccs1).
          destruct IH as [g' [p' [q' [f' [n' s'']]]]].
          split; [ eapply wgmono_trans; eauto | split; [ exact p' | split; [ exact q' | split; [ exact f' | split; [ exact n' | exact s'' ] ] ] ] ].
  Qed.

  Lemma merge_maps_fg cond_id mo mt me (s: wst) :
    winv s -> wvsz s -> wfg s ->
    wnidwf s cond_id -> wsz s cond_id 1 ->
    (forall k id, In (k, id) mt -> wnidwf s id) ->
    (forall k id, In (k, id) me -> wnidwf s id) ->
    (forall k id, In (k, id) mt -> wsz s id (dfg_var_size ctx k)) ->
    (forall k id, In (k, id) me -> wsz s id (dfg_var_size ctx k)) ->
    let (fin, s') := merge_maps ctx cond_id mo mt me s in
    wgmono s s' /\ winv s' /\ wvsz s' /\ wfg s' /\
    (forall k id, In (k, id) fin -> wnidwf s' id) /\
    (forall k id, In (k, id) fin -> wsz s' id (dfg_var_size ctx k)).
  Proof.
    intros Hinv Hvsz Hfg Hcondn Hconds Hmtn Hmen Hmts Hmes. unfold merge_maps.
    destruct (merge_loop ctx cond_id mt me (mt ++ me) [] s) as [fin s'] eqn:Er.
    eapply merge_loop_fg;
      [ exact Er | exact Hinv | exact Hvsz | exact Hfg | exact Hcondn | exact Hconds
      | exact Hmtn | exact Hmen | exact Hmts | exact Hmes
      | intros k id Hin; destruct Hin | intros k id Hin; destruct Hin ].
  Qed.

  Lemma dataflow_ops_fg :
    forall ops (s: wst), winv s -> wvsz s -> wfg s ->
      let (u, s') := dataflow_ops ctx ops s in wgmono s s' /\ winv s' /\ wvsz s' /\ wfg s'.
  Proof.
    induction ops as [op | op1 IHops1 op2 IHops2 | cond op1 IHops1 op2 IHops2];
      intros s Hinv Hvsz Hfg.
    - (* base *)
      destruct op.
      + (* nop *) simpl. unfold ret. split; [ apply wgmono_refl | split; [ exact Hinv | split; [ exact Hvsz | exact Hfg ] ] ].
      + (* assign dst expr *)
        simpl.
        pose proof (dataflow_expr_fg expr (dfg_var_size ctx (DFG_SVar dst)) s Hinv Hvsz Hfg) as He.
        destruct (dataflow_expr ctx expr (dfg_var_size ctx (DFG_SVar dst)) s) as [res_id s1] eqn:Ee.
        destruct He as [Ge [Ne [Pe [Qe [Se Fe]]]]].
        rewrite (bind_red (dataflow_expr ctx expr (dfg_var_size ctx (DFG_SVar dst))) _ s _ _ Ee).
        pose proof (set_var_fg (DFG_SVar dst) res_id s1 Pe Qe Fe Ne Se) as Hs.
        destruct (set_var ctx (DFG_SVar dst) res_id s1) as [u s'] eqn:Es.
        destruct Hs as [Gs [Ps [Qs Fs]]].
        split; [ eapply wgmono_trans; eauto | split; [ exact Ps | split; [ exact Qs | exact Fs ] ] ].
      + (* output dst expr *)
        simpl.
        pose proof (dataflow_expr_fg expr (dfg_var_size ctx (DFG_OVar dst)) s Hinv Hvsz Hfg) as He.
        destruct (dataflow_expr ctx expr (dfg_var_size ctx (DFG_OVar dst)) s) as [res_id s1] eqn:Ee.
        destruct He as [Ge [Ne [Pe [Qe [Se Fe]]]]].
        rewrite (bind_red (dataflow_expr ctx expr (dfg_var_size ctx (DFG_OVar dst))) _ s _ _ Ee).
        pose proof (set_var_fg (DFG_OVar dst) res_id s1 Pe Qe Fe Ne Se) as Hs.
        destruct (set_var ctx (DFG_OVar dst) res_id s1) as [u s'] eqn:Es.
        destruct Hs as [Gs [Ps [Qs Fs]]].
        split; [ eapply wgmono_trans; eauto | split; [ exact Ps | split; [ exact Qs | exact Fs ] ] ].
    - (* cons *)
      simpl.
      pose proof (IHops1 s Hinv Hvsz Hfg) as H1.
      destruct (dataflow_ops ctx op1 s) as [u1 s1] eqn:E1.
      destruct H1 as [G1 [P1 [Q1 F1]]].
      rewrite (bind_red (dataflow_ops ctx op1) _ s _ _ E1).
      pose proof (IHops2 s1 P1 Q1 F1) as H2.
      destruct (dataflow_ops ctx op2 s1) as [u2 s2] eqn:E2.
      destruct H2 as [G2 [P2 [Q2 F2]]].
      split; [ eapply wgmono_trans; eauto | split; [ exact P2 | split; [ exact Q2 | exact F2 ] ] ].
    - (* if *)
      simpl.
      (* cond *)
      pose proof (dataflow_expr_fg cond 1 s Hinv Hvsz Hfg) as Hc.
      destruct (dataflow_expr ctx cond 1 s) as [cond_id s1] eqn:Ec.
      destruct Hc as [Gc [Nc [Pc [Qc [Sc Fc]]]]].
      rewrite (bind_red (dataflow_expr ctx cond 1) _ s _ _ Ec).
      rewrite (bind_red (get_state ctx) _ s1 _ _ (get_state_red s1)).
      (* then branch *)
      pose proof (IHops1 s1 Pc Qc Fc) as Hthen.
      destruct (dataflow_ops ctx op1 s1) as [ut s_then] eqn:Et.
      destruct Hthen as [Gthen [Pthen [Qthen Fthen]]].
      rewrite (bind_red (dataflow_ops ctx op1) _ s1 _ _ Et).
      rewrite (bind_red (get_state ctx) _ s_then _ _ (get_state_red s_then)).
      (* restore put_state *)
      set (sR := {| graph := graph s_then; var_map := var_map s1 |} : wst).
      rewrite (bind_red (put_state ctx sR) _ s_then _ _ (put_state_red sR s_then)).
      assert (Gthen_sR : wgmono s_then sR) by (intros n Hn; unfold sR; simpl; exact Hn).
      assert (GsR_then : wgmono sR s_then) by (intros n Hn; unfold sR in Hn; simpl in Hn; exact Hn).
      (* winv sR *)
      assert (PsR : winv sR).
      { destruct Pc as [Hv1 [Hns1 Hab1]]. destruct Pthen as [Hvt [Hnst Habt]].
        split; [ | split ].
        - intros k id Hin. unfold sR in Hin; simpl in Hin.
          destruct (Hv1 k id Hin) as [node [Hn Hnid]].
          exists node. split; [ unfold sR; simpl; apply Gthen; exact Hn | exact Hnid ].
        - unfold nid_seq, sR; simpl. exact Hnst.
        - unfold sR; simpl. exact Habt. }
      (* wvsz sR : var_map sR = var_map s1, sized in s1, lifted to sR graph (= graph s_then) *)
      assert (QsR : wvsz sR).
      { intros v id Hin. unfold sR in Hin; simpl in Hin.
        eapply wsz_gmono; [ apply Qc; exact Hin | ].
        intros n Hn; unfold sR; simpl; apply Gthen; exact Hn. }
      (* wfg sR : graph sR = graph s_then, so node_args_sz from Fthen *)
      assert (FsR : wfg sR).
      { intros node Hin. unfold sR in Hin; simpl in Hin.
        eapply node_args_sz_gmono; [ apply Fthen; exact Hin | exact GsR_then ]. }
      (* else branch on sR *)
      pose proof (IHops2 sR PsR QsR FsR) as Helse.
      destruct (dataflow_ops ctx op2 sR) as [ue s_else] eqn:Ee.
      destruct Helse as [Gelse [Pelse [Qelse Felse]]].
      rewrite (bind_red (dataflow_ops ctx op2) _ sR _ _ Ee).
      rewrite (bind_red (get_state ctx) _ s_else _ _ (get_state_red s_else)).
      assert (Gs1_selse : wgmono s1 s_else)
        by (eapply wgmono_trans; [ exact Gthen | eapply wgmono_trans; [ exact Gthen_sR | exact Gelse ] ]).
      assert (Ncond : wnidwf s_else cond_id) by (eapply wnidwf_gmono; [ exact Nc | exact Gs1_selse ]).
      assert (Scond : wsz s_else cond_id 1) by (eapply wsz_gmono; [ exact Sc | exact Gs1_selse ]).
      assert (Gthen_selse : wgmono s_then s_else)
        by (eapply wgmono_trans; [ exact Gthen_sR | exact Gelse ]).
      assert (Hmtn : forall k id, In (k, id) (var_map s_then) -> wnidwf s_else id).
      { intros k id Hin. destruct Pthen as [Hvt _]. destruct (Hvt k id Hin) as [node [Hn Hnid]].
        exists node. split; [ apply Gthen_selse; exact Hn | exact Hnid ]. }
      assert (Hmen : forall k id, In (k, id) (var_map s_else) -> wnidwf s_else id).
      { intros k id Hin. destruct Pelse as [Hve _]. exact (Hve k id Hin). }
      assert (Hmts : forall k id, In (k, id) (var_map s_then) -> wsz s_else id (dfg_var_size ctx k)).
      { intros k id Hin. eapply wsz_gmono; [ apply Qthen; exact Hin | exact Gthen_selse ]. }
      assert (Hmes : forall k id, In (k, id) (var_map s_else) -> wsz s_else id (dfg_var_size ctx k)).
      { intros k id Hin. apply Qelse; exact Hin. }
      pose proof (merge_maps_fg cond_id (var_map s1) (var_map s_then) (var_map s_else) s_else
                    Pelse Qelse Felse Ncond Scond Hmtn Hmen Hmts Hmes) as Hmerge.
      destruct (merge_maps ctx cond_id (var_map s1) (var_map s_then) (var_map s_else) s_else)
        as [final_vars s_final] eqn:Em.
      destruct Hmerge as [Gmerge [Pfinal [Qfinal [Ffinal [Nfinal Sfinal]]]]].
      rewrite (bind_red (merge_maps ctx cond_id (var_map s1) (var_map s_then) (var_map s_else)) _ s_else _ _ Em).
      rewrite (bind_red (get_state ctx) _ s_final _ _ (get_state_red s_final)).
      set (sF := {| graph := graph s_final; var_map := final_vars |} : wst).
      rewrite (put_state_red sF s_final).
      assert (GsF : wgmono s_final sF) by (intros n Hn; unfold sF; simpl; exact Hn).
      assert (GsF_rev : wgmono sF s_final) by (intros n Hn; unfold sF in Hn; simpl in Hn; exact Hn).
      split.
      + intros n Hn. unfold sF; simpl.
        apply Gmerge. apply Gs1_selse. apply Gc. exact Hn.
      + split; [ | split ].
        * (* winv sF *)
          destruct Pfinal as [Hvf [Hnsf Habf]]. split; [ | split ].
          -- intros k id Hin. unfold sF in Hin; simpl in Hin.
             destruct (Nfinal k id Hin) as [node [Hn Hnid]].
             exists node. split; [ unfold sF; simpl; exact Hn | exact Hnid ].
          -- unfold nid_seq, sF; simpl. exact Hnsf.
          -- unfold sF; simpl. exact Habf.
        * (* wvsz sF *)
          intros v id Hin. unfold sF in Hin; simpl in Hin.
          eapply wsz_gmono; [ apply Sfinal; exact Hin | exact GsF ].
        * (* wfg sF *)
          intros node Hin. unfold sF in Hin; simpl in Hin.
          eapply node_args_sz_gmono; [ apply Ffinal; exact Hin | exact GsF ].
  Qed.



  Definition gpos (s: wst) : Prop :=
    1 <= length (graph s)
    /\ (forall k id, In (k, id) (var_map s) -> 1 <= id)
    /\ (forall node, In node (graph s) -> forall x, In x (get_args ctx node) -> 1 <= x)
    /\ (forall node, In node (graph s) -> op node = DFG_Empty -> nid node = 0).

  Lemma ensure_var_vmap v (s: wst) id s' :
    ensure_var ctx v s = (id, s') ->
    exists f, var_map s' = (v, id) :: filter f (var_map s).
  Proof.
    unfold ensure_var, emit, bind, get_state, put_state, ret. intro H.
    injection H as <- <-. eexists. reflexivity.
  Qed.

  Lemma emit_pos op sz (s: wst) :
    gpos s -> op <> DFG_Empty ->
    (forall x, In x (get_args ctx {| nid := length (graph s); op := op; sz := sz |}) -> 1 <= x) ->
    let (id, s') := emit ctx op sz s in 1 <= id /\ gpos s'.
  Proof.
    intros [Hlen [Hvm [Hargs Hemp]]] Hne Hnew.
    rewrite emit_red.
    split; [ exact Hlen | ].
    split; [ | split; [ | split ] ].
    - cbn [graph length]. lia.
    - cbn [var_map]. exact Hvm.
    - cbn [graph]. intros node Hin x Hx. destruct Hin as [<-|Hin].
      + exact (Hnew x Hx).
      + exact (Hargs node Hin x Hx).
    - cbn [graph]. intros node Hin He. destruct Hin as [<-|Hin].
      + cbn in He. exfalso. apply Hne. exact He.
      + exact (Hemp node Hin He).
  Qed.

  Lemma ensure_var_pos v (s: wst) :
    gpos s ->
    let (id, s') := ensure_var ctx v s in 1 <= id /\ gpos s'.
  Proof.
    intros Hp.
    destruct (ensure_var ctx v s) as [id s'] eqn:Ev.
    pose proof (ensure_var_graph v s id s' Ev) as [Hg Hid].
    pose proof (ensure_var_vmap v s id s' Ev) as [f Hvm'].
    destruct Hp as [Hlen [Hvm [Hargs Hemp]]].
    split; [ rewrite Hid; exact Hlen | ].
    split; [ | split; [ | split ] ].
    - rewrite Hg. cbn [graph length]. lia.
    - rewrite Hvm'. intros k id0 Hin. destruct Hin as [Heq|Hin].
      + injection Heq as <- <-. rewrite Hid; exact Hlen.
      + apply filter_In in Hin. destruct Hin as [Hin _]. exact (Hvm k id0 Hin).
    - rewrite Hg. cbn [graph]. intros node Hin x Hx. destruct Hin as [<-|Hin].
      + cbn in Hx. destruct Hx.
      + exact (Hargs node Hin x Hx).
    - rewrite Hg. cbn [graph]. intros node Hin He. destruct Hin as [<-|Hin].
      + cbn in He. discriminate He.
      + exact (Hemp node Hin He).
  Qed.

  Lemma set_var_pos v id (s: wst) :
    gpos s -> 1 <= id ->
    let (u, s') := set_var ctx v id s in gpos s'.
  Proof.
    intros [Hlen [Hvm [Hargs Hemp]]] Hi.
    unfold set_var, bind, get_state, put_state. simpl.
    split; [ | split; [ | split ] ].
    - cbn [graph length]. exact Hlen.
    - cbn [var_map]. intros k id0 Hin. destruct Hin as [Heq|Hin].
      + injection Heq as <- <-. exact Hi.
      + apply filter_In in Hin. destruct Hin as [Hin _]. exact (Hvm k id0 Hin).
    - cbn [graph]. exact Hargs.
    - cbn [graph]. exact Hemp.
  Qed.

  Lemma get_var_pos v (s: wst) :
    gpos s ->
    let (id, s') := get_var ctx v s in 1 <= id /\ gpos s'.
  Proof.
    intros Hp. unfold get_var, bind, get_state.
    destruct (BitsToLists.list_assoc (var_map s) v) as [id|] eqn:E.
    - unfold ret. split; [ | exact Hp ].
      destruct Hp as [_ [Hvm _]]. apply wla_in in E. exact (Hvm v id E).
    - apply ensure_var_pos; exact Hp.
  Qed.

  Lemma ret_pos id (s: wst) :
    1 <= id -> gpos s -> let (i, s') := ret ctx id s in 1 <= i /\ gpos s'.
  Proof. intros Hi Hp. unfold ret. split; assumption. Qed.

  Lemma seq_pos (m: M ctx nid_t) (f: nid_t -> M ctx nid_t) (s: wst) :
    (gpos s -> let (id, s1) := m s in 1 <= id /\ gpos s1) ->
    (forall id s1, 1 <= id -> gpos s1 ->
       let (id2, s2) := f id s1 in 1 <= id2 /\ gpos s2) ->
    gpos s ->
    let (id2, s2) := bind ctx m f s in 1 <= id2 /\ gpos s2.
  Proof.
    intros H1 H2 Hp. specialize (H1 Hp).
    unfold bind. destruct (m s) as [id s1] eqn:Em.
    destruct H1 as [n1 p1]. specialize (H2 id s1 n1 p1).
    destruct (f id s1) as [id2 s2]. exact H2.
  Qed.

  Lemma dataflow_expr_pos :
    forall e sz (s: wst), gpos s ->
      let (id, s') := dataflow_expr ctx e sz s in 1 <= id /\ gpos s'.
  Proof.
    induction e; intros sz s Hp.
    - simpl. apply emit_pos; [ exact Hp | discriminate | intros x Hx; simpl in Hx; destruct Hx ].
    - simpl. apply seq_pos.
      + apply get_var_pos.
      + intros id s1 Hid Hp1. cbn beta. destruct (Nat.eqb _ sz).
        * apply ret_pos; assumption.
        * apply emit_pos; [ exact Hp1 | discriminate | intros x Hx; simpl in Hx; destruct Hx as [<-|[]]; exact Hid ].
      + exact Hp.
    - simpl. apply seq_pos.
      + intro Hp0. apply emit_pos; [ exact Hp0 | discriminate | intros x Hx; simpl in Hx; destruct Hx ].
      + intros id s1 Hid Hp1. cbn beta. destruct (Nat.eqb _ sz).
        * apply ret_pos; assumption.
        * apply emit_pos; [ exact Hp1 | discriminate | intros x Hx; simpl in Hx; destruct Hx as [<-|[]]; exact Hid ].
      + exact Hp.
    - simpl. apply seq_pos.
      + apply get_var_pos.
      + intros id s1 Hid Hp1. cbn beta. destruct (Nat.eqb _ sz).
        * apply ret_pos; assumption.
        * apply emit_pos; [ exact Hp1 | discriminate | intros x Hx; simpl in Hx; destruct Hx as [<-|[]]; exact Hid ].
      + exact Hp.
    - simpl. destruct op as [| source_size].
      + apply seq_pos.
        * apply IHe.
        * intros id1 s1 Hid1 Hp1. apply emit_pos;
            [ exact Hp1 | discriminate | intros x Hx; simpl in Hx; destruct Hx as [<-|[]]; exact Hid1 ].
        * exact Hp.
      + apply seq_pos.
        * apply IHe.
        * intros id1 s1 Hid1 Hp1. apply emit_pos;
            [ exact Hp1 | discriminate
            | intros x Hx; simpl in Hx; destruct Hx as [<-|[]]; exact Hid1 ].
        * exact Hp.
    - simpl. destruct op;
        ( apply seq_pos;
          [ apply IHe1
          | intros id1 s1 Hid1 Hp1; apply seq_pos;
            [ apply IHe2
            | intros id2 s2 Hid2 Hp2; apply emit_pos;
              [ exact Hp2 | discriminate
              | intros x Hx; simpl in Hx; destruct Hx as [<-|[<-|[]]]; [ exact Hid1 | exact Hid2 ] ]
            | exact Hp1 ]
          | exact Hp ]).
    - simpl. apply seq_pos.
      + apply IHe1.
      + intros idc s1 Hidc Hpc. apply seq_pos.
        * apply IHe2.
        * intros idt s2 Hidt Hpt. apply seq_pos.
          -- apply IHe3.
          -- intros ide s3 Hide Hpe. apply emit_pos.
             ++ exact Hpe.
             ++ discriminate.
             ++ intros x Hx; simpl in Hx; destruct Hx as [<-|[<-|[<-|[]]]];
                  [ exact Hidc | exact Hidt | exact Hide ].
          -- exact Hpt.
        * exact Hpc.
      + exact Hp.
  Qed.

  Lemma merge_key_pos cond_id k vt_opt ve_opt (s: wst) res s' :
    merge_key ctx cond_id k vt_opt ve_opt s = (res, s') ->
    gpos s -> 1 <= cond_id ->
    (forall vt, vt_opt = Some vt -> 1 <= vt) ->
    (forall ve, ve_opt = Some ve -> 1 <= ve) ->
    gpos s' /\ (forall fid, res = Some fid -> 1 <= fid).
  Proof.
    intros Hrun Hp Hcond Hvt Hve. unfold merge_key in Hrun.
    destruct vt_opt as [vt|]; destruct ve_opt as [ve|].
    - destruct (eq_dec vt ve) as [Heq|Hne].
      + unfold ret in Hrun. injection Hrun as <- <-.
        split; [ exact Hp | intros fid Hf; injection Hf as <-; apply Hvt; reflexivity ].
      + assert (Harg : forall x,
          In x (get_args ctx {| nid := length (graph s); op := DFG_Phi cond_id vt ve; sz := dfg_var_size ctx k |}) -> 1 <= x).
        { intros x Hx. simpl in Hx. destruct Hx as [<-|[<-|[<-|[]]]].
          - exact Hcond. - apply Hvt; reflexivity. - apply Hve; reflexivity. }
        pose proof (emit_pos (DFG_Phi cond_id vt ve) (dfg_var_size ctx k) s Hp ltac:(discriminate) Harg) as He.
        destruct (emit ctx (DFG_Phi cond_id vt ve) (dfg_var_size ctx k) s) as [phi s1] eqn:Ee.
        destruct He as [Ne Pe].
        rewrite (bind_red (emit ctx (DFG_Phi cond_id vt ve) (dfg_var_size ctx k)) _ s _ _ Ee) in Hrun.
        unfold ret in Hrun. injection Hrun as <- <-.
        split; [ exact Pe | intros fid Hf; injection Hf as <-; exact Ne ].
    - destruct (ensure_var ctx k s) as [ve0 s1] eqn:Ev.
      pose proof (ensure_var_pos k s Hp) as Hev. rewrite Ev in Hev. destruct Hev as [Nv Pv].
      rewrite (bind_red (ensure_var ctx k) _ s _ _ Ev) in Hrun.
      assert (Harg : forall x,
        In x (get_args ctx {| nid := length (graph s1); op := DFG_Phi cond_id vt ve0; sz := dfg_var_size ctx k |}) -> 1 <= x).
      { intros x Hx. simpl in Hx. destruct Hx as [<-|[<-|[<-|[]]]].
        - exact Hcond. - apply Hvt; reflexivity. - exact Nv. }
      pose proof (emit_pos (DFG_Phi cond_id vt ve0) (dfg_var_size ctx k) s1 Pv ltac:(discriminate) Harg) as He.
      destruct (emit ctx (DFG_Phi cond_id vt ve0) (dfg_var_size ctx k) s1) as [phi s2] eqn:Ee.
      destruct He as [Ne Pe].
      rewrite (bind_red (emit ctx (DFG_Phi cond_id vt ve0) (dfg_var_size ctx k)) _ s1 _ _ Ee) in Hrun.
      unfold ret in Hrun. injection Hrun as <- <-.
      split; [ exact Pe | intros fid Hf; injection Hf as <-; exact Ne ].
    - destruct (ensure_var ctx k s) as [vt0 s1] eqn:Ev.
      pose proof (ensure_var_pos k s Hp) as Hev. rewrite Ev in Hev. destruct Hev as [Nv Pv].
      rewrite (bind_red (ensure_var ctx k) _ s _ _ Ev) in Hrun.
      assert (Harg : forall x,
        In x (get_args ctx {| nid := length (graph s1); op := DFG_Phi cond_id vt0 ve; sz := dfg_var_size ctx k |}) -> 1 <= x).
      { intros x Hx. simpl in Hx. destruct Hx as [<-|[<-|[<-|[]]]].
        - exact Hcond. - exact Nv. - apply Hve; reflexivity. }
      pose proof (emit_pos (DFG_Phi cond_id vt0 ve) (dfg_var_size ctx k) s1 Pv ltac:(discriminate) Harg) as He.
      destruct (emit ctx (DFG_Phi cond_id vt0 ve) (dfg_var_size ctx k) s1) as [phi s2] eqn:Ee.
      destruct He as [Ne Pe].
      rewrite (bind_red (emit ctx (DFG_Phi cond_id vt0 ve) (dfg_var_size ctx k)) _ s1 _ _ Ee) in Hrun.
      unfold ret in Hrun. injection Hrun as <- <-.
      split; [ exact Pe | intros fid Hf; injection Hf as <-; exact Ne ].
    - unfold ret in Hrun. injection Hrun as <- <-.
      split; [ exact Hp | intros fid Hf; discriminate ].
  Qed.

  Lemma merge_loop_pos cond_id mt me :
    forall keys acc (s: wst) fin s',
      merge_loop ctx cond_id mt me keys acc s = (fin, s') ->
      gpos s -> 1 <= cond_id ->
      (forall k id, In (k, id) mt -> 1 <= id) ->
      (forall k id, In (k, id) me -> 1 <= id) ->
      (forall k id, In (k, id) acc -> 1 <= id) ->
      gpos s' /\ (forall k id, In (k, id) fin -> 1 <= id).
  Proof.
    induction keys as [|[k kv] rest IH]; intros acc s fin s' Hrun Hp Hcond Hmt Hme Hacc.
    - simpl in Hrun. unfold ret in Hrun. injection Hrun as <- <-.
      split; [ exact Hp | exact Hacc ].
    - simpl in Hrun.
      destruct (BitsToLists.list_assoc acc k) as [existing|] eqn:Ek.
      + eapply IH; eauto.
      + unfold bind in Hrun. cbv beta in Hrun.
        destruct (merge_key ctx cond_id k (BitsToLists.list_assoc mt k) (BitsToLists.list_assoc me k) s)
          as [res_opt s1] eqn:Emk.
        cbv beta iota in Hrun.
        pose proof (merge_key_pos cond_id k _ _ s res_opt s1 Emk Hp Hcond
                      (fun vt Hvt => Hmt k vt (wla_in mt k vt Hvt))
                      (fun ve Hve => Hme k ve (wla_in me k ve Hve))) as Hmk.
        destruct Hmk as [pk nk].
        destruct res_opt as [final_id|].
        * assert (Hacc1 : forall k0 id, In (k0, id) ((k, final_id) :: acc) -> 1 <= id).
          { intros k0 id Hin. simpl in Hin. destruct Hin as [Heq|Hin].
            - injection Heq as <- <-. apply nk; reflexivity.
            - eapply Hacc; eauto. }
          specialize (IH ((k, final_id) :: acc) s1 fin s' Hrun pk Hcond Hmt Hme Hacc1).
          exact IH.
        * assert (Hacc1 : forall k0 id, In (k0, id) acc -> 1 <= id)
            by (intros k0 id Hin; eapply Hacc; eauto).
          specialize (IH acc s1 fin s' Hrun pk Hcond Hmt Hme Hacc1).
          exact IH.
  Qed.

  Lemma merge_maps_pos cond_id mo mt me (s: wst) fin s' :
    merge_maps ctx cond_id mo mt me s = (fin, s') ->
    gpos s -> 1 <= cond_id ->
    (forall k id, In (k, id) mt -> 1 <= id) ->
    (forall k id, In (k, id) me -> 1 <= id) ->
    gpos s' /\ (forall k id, In (k, id) fin -> 1 <= id).
  Proof.
    intros Hrun Hp Hcond Hmt Hme. unfold merge_maps in Hrun.
    eapply merge_loop_pos;
      [ exact Hrun | exact Hp | exact Hcond | exact Hmt | exact Hme
      | intros k id Hin; destruct Hin ].
  Qed.

  Lemma dataflow_ops_pos :
    forall ops (s: wst), gpos s ->
      let (u, s') := dataflow_ops ctx ops s in gpos s'.
  Proof.
    induction ops as [op | op1 IHops1 op2 IHops2 | cond op1 IHops1 op2 IHops2];
      intros s Hp.
    - destruct op.
      + simpl. unfold ret. exact Hp.
      + simpl.
        pose proof (dataflow_expr_pos expr (dfg_var_size ctx (DFG_SVar dst)) s Hp) as He.
        destruct (dataflow_expr ctx expr (dfg_var_size ctx (DFG_SVar dst)) s) as [res_id s1] eqn:Ee.
        destruct He as [Ne Pe].
        rewrite (bind_red (dataflow_expr ctx expr (dfg_var_size ctx (DFG_SVar dst))) _ s _ _ Ee).
        pose proof (set_var_pos (DFG_SVar dst) res_id s1 Pe Ne) as Hs.
        destruct (set_var ctx (DFG_SVar dst) res_id s1) as [u s'] eqn:Es.
        exact Hs.
      + simpl.
        pose proof (dataflow_expr_pos expr (dfg_var_size ctx (DFG_OVar dst)) s Hp) as He.
        destruct (dataflow_expr ctx expr (dfg_var_size ctx (DFG_OVar dst)) s) as [res_id s1] eqn:Ee.
        destruct He as [Ne Pe].
        rewrite (bind_red (dataflow_expr ctx expr (dfg_var_size ctx (DFG_OVar dst))) _ s _ _ Ee).
        pose proof (set_var_pos (DFG_OVar dst) res_id s1 Pe Ne) as Hs.
        destruct (set_var ctx (DFG_OVar dst) res_id s1) as [u s'] eqn:Es.
        exact Hs.
    - simpl.
      pose proof (IHops1 s Hp) as H1.
      destruct (dataflow_ops ctx op1 s) as [u1 s1] eqn:E1.
      rewrite (bind_red (dataflow_ops ctx op1) _ s _ _ E1).
      pose proof (IHops2 s1 H1) as H2.
      destruct (dataflow_ops ctx op2 s1) as [u2 s2] eqn:E2.
      exact H2.
    - simpl.
      pose proof (dataflow_expr_pos cond 1 s Hp) as Hc.
      destruct (dataflow_expr ctx cond 1 s) as [cond_id s1] eqn:Ec.
      destruct Hc as [Nc Pc].
      rewrite (bind_red (dataflow_expr ctx cond 1) _ s _ _ Ec).
      rewrite (bind_red (get_state ctx) _ s1 _ _ (get_state_red s1)).
      pose proof (IHops1 s1 Pc) as Hthen.
      destruct (dataflow_ops ctx op1 s1) as [ut s_then] eqn:Et.
      rewrite (bind_red (dataflow_ops ctx op1) _ s1 _ _ Et).
      rewrite (bind_red (get_state ctx) _ s_then _ _ (get_state_red s_then)).
      set (sR := {| graph := graph s_then; var_map := var_map s1 |} : wst).
      rewrite (bind_red (put_state ctx sR) _ s_then _ _ (put_state_red sR s_then)).
      assert (PsR : gpos sR).
      { destruct Pc as [_ [Hvm1 _]]. destruct Hthen as [Hlt [_ [Habt Hempt]]].
        split; [ | split; [ | split ] ].
        - unfold sR; cbn [graph]. exact Hlt.
        - unfold sR; cbn [var_map]. exact Hvm1.
        - unfold sR; cbn [graph]. exact Habt.
        - unfold sR; cbn [graph]. exact Hempt. }
      pose proof (IHops2 sR PsR) as Helse.
      destruct (dataflow_ops ctx op2 sR) as [ue s_else] eqn:Ee.
      rewrite (bind_red (dataflow_ops ctx op2) _ sR _ _ Ee).
      rewrite (bind_red (get_state ctx) _ s_else _ _ (get_state_red s_else)).
      assert (Hmt : forall k id, In (k, id) (var_map s_then) -> 1 <= id).
      { intros k id Hin. destruct Hthen as [_ [Hvmt _]]. exact (Hvmt k id Hin). }
      assert (Hme : forall k id, In (k, id) (var_map s_else) -> 1 <= id).
      { intros k id Hin. destruct Helse as [_ [Hvme _]]. exact (Hvme k id Hin). }
      destruct (merge_maps ctx cond_id (var_map s1) (var_map s_then) (var_map s_else) s_else)
        as [final_vars s_final] eqn:Em.
      pose proof (merge_maps_pos cond_id (var_map s1) (var_map s_then) (var_map s_else) s_else
                    final_vars s_final Em Helse Nc Hmt Hme) as Hmerge.
      destruct Hmerge as [Pfinal Nfinal].
      rewrite (bind_red (merge_maps ctx cond_id (var_map s1) (var_map s_then) (var_map s_else)) _ s_else _ _ Em).
      rewrite (bind_red (get_state ctx) _ s_final _ _ (get_state_red s_final)).
      set (sF := {| graph := graph s_final; var_map := final_vars |} : wst).
      rewrite (put_state_red sF s_final).
      destruct Pfinal as [Hlf [_ [Habf Hempf]]].
      split; [ | split; [ | split ] ].
      + unfold sF; cbn [graph]. exact Hlf.
      + unfold sF; cbn [var_map]. exact Nfinal.
      + unfold sF; cbn [graph]. exact Habf.
      + unfold sF; cbn [graph]. exact Hempf.
  Qed.

  (* Forward-graph corollary: in build_dfg's exported graph, no arg and no
     var_map value is 0 (the DFG_Empty placeholder at position 0). *)
  Lemma build_dfg_args_pos :
    forall (act: tfs_action sched),
      (forall k id, In (k, id) (var_map (build_dfg ctx act)) -> 1 <= id)
      /\ (forall node, In node (graph (build_dfg ctx act)) ->
            forall x, In x (get_args ctx node) -> 1 <= x)
      /\ (forall node, In node (graph (build_dfg ctx act)) ->
            op node = DFG_Empty -> nid node = 0).
  Proof.
    intro act.
    assert (Hempty : gpos {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |}).
    { split; [ | split; [ | split ] ].
      - cbn. lia.
      - intros k id Hin. destruct Hin.
      - intros node Hin x Hx. cbn in Hin. destruct Hin as [<-|[]]. cbn in Hx. destruct Hx.
      - intros node Hin He. cbn in Hin. destruct Hin as [<-|[]]. cbn. reflexivity. }
    unfold build_dfg.
    pose proof (dataflow_ops_pos (tfs_spec_action_ops ctx act)
                  {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |} Hempty) as Hop.
    destruct (dataflow_ops ctx (tfs_spec_action_ops ctx act)
                {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |})
      as [u final] eqn:Ed.
    destruct Hop as [_ [Hvm [Hargs Hemp]]].
    cbn [graph var_map]. split; [ | split ].
    - exact Hvm.
    - intros node Hin x Hx. apply in_rev in Hin. exact (Hargs node Hin x Hx).
    - intros node Hin He. apply in_rev in Hin. exact (Hemp node Hin He).
  Qed.

  (* --- the theorem --- *)

  Lemma build_dfg_wf :
    forall (act: tfs_action sched),
      ids_desc (rev (graph (build_dfg ctx act)))
      /\ args_lt (rev (graph (build_dfg ctx act))).
  Proof.
    intro act.
    assert (Hempty : winv {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |}).
    { split; [ | split ].
      - intros k id Hin. destruct Hin.
      - unfold nid_seq. reflexivity.
      - intros a Ha x Hx. simpl in Ha. destruct Ha as [<-|[]]. simpl in Hx. destruct Hx. }
    unfold build_dfg.
    pose proof (dataflow_ops_full (tfs_spec_action_ops ctx act)
                  {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |} Hempty) as Hop.
    destruct (dataflow_ops ctx (tfs_spec_action_ops ctx act)
                {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |})
      as [u final] eqn:Ed.
    destruct Hop as [_ [Hvmg [Hns Hargs]]].
    simpl. rewrite rev_involutive.
    split.
    - apply nid_seq_ids_desc; exact Hns.
    - exact Hargs.
  Qed.

  (* STI-2 capstone: the exported forward graph satisfies [wfg] — every node's
     args are recorded at the size the node's op demands.  [node_args_sz] uses
     only [In], so it survives the [rev] wrapper in [build_dfg]. *)
  Lemma wfg_build_dfg :
    forall (act: tfs_action sched), wfg (build_dfg ctx act).
  Proof.
    intro act.
    assert (Hempty : winv {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |}).
    { split; [ | split ].
      - intros k id Hin. destruct Hin.
      - unfold nid_seq. reflexivity.
      - intros a Ha x Hx. simpl in Ha. destruct Ha as [<-|[]]. simpl in Hx. destruct Hx. }
    assert (Hemvsz : wvsz {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |}).
    { intros v id Hin. destruct Hin. }
    assert (Hemfg : wfg {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |}).
    { intros node Hin. simpl in Hin. destruct Hin as [<-|[]].
      unfold node_args_sz. cbn [op]. exact I. }
    unfold build_dfg.
    pose proof (dataflow_ops_fg (tfs_spec_action_ops ctx act)
                  {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |}
                  Hempty Hemvsz Hemfg) as Hop.
    destruct (dataflow_ops ctx (tfs_spec_action_ops ctx act)
                {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |})
      as [u final] eqn:Ed.
    destruct Hop as [_ [_ [_ Ffinal]]].
    intros node Hin. cbn [graph] in Hin. rewrite <- in_rev in Hin.
    specialize (Ffinal node Hin).
    eapply node_args_sz_gmono; [ exact Ffinal | ].
    intros n Hn. cbn [graph]. rewrite <- in_rev. exact Hn.
  Qed.

  (* The forward (exported) graph has ids exactly 0,1,…,len-1: build_dfg reverses
     the internally-built (descending-id) graph, so positions match ids. *)
  Lemma build_dfg_nids :
    forall (act: tfs_action sched),
      map nid (graph (build_dfg ctx act))
      = seq 0 (length (graph (build_dfg ctx act))).
  Proof.
    intro act.
    assert (Hempty : winv {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |}).
    { split; [ | split ].
      - intros k id Hin. destruct Hin.
      - unfold nid_seq. reflexivity.
      - intros a Ha x Hx. simpl in Ha. destruct Ha as [<-|[]]. simpl in Hx. destruct Hx. }
    unfold build_dfg.
    pose proof (dataflow_ops_full (tfs_spec_action_ops ctx act)
                  {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |} Hempty) as Hop.
    destruct (dataflow_ops ctx (tfs_spec_action_ops ctx act)
                {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |})
      as [u final] eqn:Ed.
    destruct Hop as [_ [_ [Hns _]]].
    unfold nid_seq in Hns. cbn [graph].
    rewrite map_rev, Hns, rev_involutive, rev_length. reflexivity.
  Qed.

  (* Consequently the node at position [n] (n < len) has [nid] field = n. *)
  Lemma node_nid_at :
    forall (act: tfs_action sched) n,
      n < length (graph (build_dfg ctx act)) ->
      nid (nth n (graph (build_dfg ctx act)) {| nid := 0; op := DFG_Empty; sz := 0 |}) = n.
  Proof.
    intros act n Hn.
    rewrite <- (map_nth nid (graph (build_dfg ctx act))
                  {| nid := 0; op := DFG_Empty; sz := 0 |} n).
    rewrite build_dfg_nids, seq_nth; [ reflexivity | exact Hn ].
  Qed.

  (* No real node (position >= 1) carries the DFG_Empty placeholder op:
     the only Empty is the placeholder at forward position 0 (nid 0). *)
  Lemma node_op_not_empty (act: tfs_action sched) (n: nat) :
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    op (nth n (graph (build_dfg ctx act)) {| nid := 0; op := DFG_Empty; sz := 0 |}) <> DFG_Empty.
  Proof.
    intros Hn Hlt He.
    pose proof (build_dfg_args_pos act) as [_ [_ Hemp]].
    assert (Hin : In (nth n (graph (build_dfg ctx act)) {| nid := 0; op := DFG_Empty; sz := 0 |})
                     (graph (build_dfg ctx act)))
      by (apply nth_In; exact Hlt).
    pose proof (Hemp _ Hin He) as Hnid0.
    pose proof (node_nid_at act n Hlt) as Hnidn.
    rewrite Hnidn in Hnid0. lia.
  Qed.

  (* A [wsz] fact about the exported graph pins the node sitting at that
     position: ids are exactly the positions, so the witness node IS the node
     at position [n], and its declared size is the recorded one. *)
  Lemma wsz_node_sz (act: tfs_action sched) (n size: nat) :
    wsz (build_dfg ctx act) n size ->
    n < length (graph (build_dfg ctx act))
    /\ sz (nth n (graph (build_dfg ctx act))
             {| nid := 0; op := DFG_Empty; sz := 0 |}) = size.
  Proof.
    intros [node [Hin [Hnid Hsz]]].
    destruct (In_nth _ _ {| nid := 0; op := DFG_Empty; sz := 0 |} Hin)
      as [p [Hp Hnth]].
    assert (Hpn : p = n).
    { pose proof (node_nid_at act p Hp) as Hp_nid.
      rewrite Hnth in Hp_nid. congruence. }
    rewrite <- Hpn.
    split; [ exact Hp | rewrite Hnth; exact Hsz ].
  Qed.

  (* args_lt holds on the forward graph too (it is permutation-invariant). *)
  Lemma args_lt_fwd :
    forall (act: tfs_action sched),
      args_lt (graph (build_dfg ctx act)).
  Proof.
    intros act a Ha x Hx.
    pose proof (build_dfg_wf act) as [_ Hargs].
    apply (Hargs a); [ apply in_rev in Ha; exact Ha | exact Hx ].
  Qed.

  (* Once a node is processed in the fold order, its id is frozen: no node
     appearing later has that id as its own nid or among its args.  Derived
     from build_dfg_wf (strictly-decreasing ids + args-below-nid). *)
  Lemma build_dfg_suffix_frozen :
    forall (act: tfs_action sched) pre node rest,
      rev (graph (build_dfg ctx act)) = pre ++ node :: rest ->
      forall M, In M rest -> ~ In (nid node) (nid M :: get_args ctx M).
  Proof.
    intros act pre node rest Hsplit M HM Hin.
    destruct (build_dfg_wf act) as [Hdesc Hargs].
    pose proof (Hdesc pre node rest Hsplit M HM) as HltM. (* nid M < nid node *)
    cbn [In] in Hin. destruct Hin as [Heq | Harg].
    - (* nid node = nid M contradicts nid M < nid node *)
      rewrite Heq in HltM. exact (Nat.lt_irrefl _ HltM).
    - (* nid node in get_args M ⇒ nid node < nid M, contradicts nid M < nid node *)
      assert (HinM : In M (rev (graph (build_dfg ctx act)))).
      { rewrite Hsplit. apply in_or_app. right. right. exact HM. }
      pose proof (Hargs M HinM (nid node) Harg) as Hlt2. (* nid node < nid M *)
      exact (Nat.lt_irrefl _ (Nat.lt_trans _ _ _ Hlt2 HltM)).
  Qed.

  (* Raw backward-cost monotonicity: an argument's accumulated backward cost is
     >= that of its consuming node. *)
  Lemma backward_cost_monotone :
    forall (act: tfs_action sched) node x,
      In node (graph (build_dfg ctx act)) ->
      In x (get_args ctx node) ->
      (match BitsToLists.list_assoc
               (calc_backward_cost ctx (build_dfg ctx act)) (nid node) with
       | Some c => c | None => 0 end)
      <= (match BitsToLists.list_assoc
               (calc_backward_cost ctx (build_dfg ctx act)) x with
          | Some c => c | None => 0 end).
  Proof.
    intros act node x Hnode Hx.
    change (getn (calc_backward_cost ctx (build_dfg ctx act)) (nid node)
            <= getn (calc_backward_cost ctx (build_dfg ctx act)) x).
    rewrite calc_backward_cost_fold.
    (* split the processing list at [node] *)
    pose proof Hnode as HinL. apply in_rev in HinL.
    apply in_split in HinL. destruct HinL as [pre [rest Hsplit]].
    rewrite Hsplit, fold_left_app. cbn [fold_left].
    set (acc0 := fold_left bc_aux pre []).
    (* base inequality after processing [node] itself *)
    apply cost_ge_after_fold.
    - unfold bc_aux.
      set (w := getn acc0 (nid node) + cost_fn ctx (op node) (sz node)).
      eapply Nat.le_trans.
      + (* getn (sam ..) (nid node) <= w *)
        eapply Nat.le_trans; [ apply sam_upper |].
        apply Nat.max_lub; [ apply Nat.le_add_r | apply Nat.le_refl ].
      + (* w <= getn (sam ..) x *)
        apply sam_in_ge. right. exact Hx.
    - (* frozen: no node after [node] touches key (nid node) *)
      apply (build_dfg_suffix_frozen act pre node rest Hsplit).
  Qed.

  (* Backward-cost monotonicity (at cycle granularity): a node's target cycle is
     <= that of any of its DFG arguments — reduces to backward_cost_monotone since
     dividing by cost_limit preserves the order. *)
  Lemma backward_cycle_monotone :
    forall (act: tfs_action sched) node x,
      In node (graph (build_dfg ctx act)) ->
      In x (get_args ctx node) ->
      node_cycle act (nid node) <= node_cycle act x.
  Proof.
    intros act node x Hnode Hx. unfold node_cycle.
    rewrite !list_assoc_calc_target_cycle.
    pose proof (backward_cost_monotone act node x Hnode Hx) as Hm.
    destruct (BitsToLists.list_assoc
                (calc_backward_cost ctx (build_dfg ctx act)) (nid node)) as [c1|];
    destruct (BitsToLists.list_assoc
                (calc_backward_cost ctx (build_dfg ctx act)) x) as [c2|];
    cbn [option_map].
    - apply Nat.Div0.div_le_mono. exact Hm.
    - apply Nat.le_0_r in Hm. rewrite Hm, Nat.Div0.div_0_l. apply Nat.le_0_l.
    - apply Nat.le_0_l.
    - apply Nat.le_0_l.
  Qed.

  (* --- list_assoc presence machinery (for cost-entry existence) --- *)

  (* Setting key k gives k a value. *)
  Lemma list_assoc_set_same {K V} {eqK: EqDec K} (l: list (K * V)) (k: K) (v: V) :
    BitsToLists.list_assoc (BitsToLists.list_assoc_set l k v) k = Some v.
  Proof.
    induction l as [| [k1 v1] l IH]; cbn.
    - destruct (eq_dec k k) as [_|n]; [ reflexivity | congruence ].
    - destruct (eq_dec k k1); cbn.
      + destruct (eq_dec k k1) as [_|n]; [ reflexivity | congruence ].
      + destruct (eq_dec k k1) as [e|_]; [ congruence | exact IH ].
  Qed.

  (* Setting a key preserves presence of any already-present key. *)
  Lemma list_assoc_set_pres {K V} {eqK: EqDec K} (l: list (K * V)) (k: K) (v: V) :
    forall j, BitsToLists.list_assoc l j <> None ->
              BitsToLists.list_assoc (BitsToLists.list_assoc_set l k v) j <> None.
  Proof.
    induction l as [| [k1 v1] l IH]; cbn; intros j H.
    - congruence.
    - destruct (eq_dec k k1); cbn in *.
      + destruct (eq_dec j k1); [ discriminate | exact H ].
      + destruct (eq_dec j k1); [ discriminate | apply IH; exact H ].
  Qed.

  (* list_assoc_set_all_max preserves presence. *)
  Lemma set_all_max_pres {K} {eqK: EqDec K} (keys: list K) (v: nat) :
    forall (l: list (K * nat)) j,
      BitsToLists.list_assoc l j <> None ->
      BitsToLists.list_assoc (list_assoc_set_all_max l keys v) j <> None.
  Proof.
    unfold list_assoc_set_all_max.
    induction keys as [| a keys IH]; cbn; intros l j H.
    - exact H.
    - apply IH.
      destruct (Nat.leb _ v).
      + apply list_assoc_set_pres; exact H.
      + exact H.
  Qed.

  (* Any key in the key list ends up present after list_assoc_set_all_max
     (if it was absent the running-max condition Nat.leb 0 v holds and sets it). *)
  Lemma set_all_max_mem {K} {eqK: EqDec K} (keys: list K) (v: nat) :
    forall (l: list (K * nat)) j,
      In j keys ->
      BitsToLists.list_assoc (list_assoc_set_all_max l keys v) j <> None.
  Proof.
    unfold list_assoc_set_all_max.
    induction keys as [| a keys IH]; cbn; intros l j Hin.
    - destruct Hin.
    - destruct Hin as [-> | Hin].
      + apply set_all_max_pres.
        destruct (Nat.leb (match BitsToLists.list_assoc l j with
                           | Some e => e | None => 0 end) v) eqn:Hleb.
        * rewrite list_assoc_set_same. discriminate.
        * destruct (BitsToLists.list_assoc l j) eqn:Hla.
          -- discriminate.
          -- cbn in Hleb. discriminate.
      + apply IH; exact Hin.
  Qed.

  (* Generic fold membership: if F preserves presence and always sets key (keyf a),
     then folding F over a list containing a leaves keyf a present. *)
  Lemma fold_pres_mem {A K V} {eqK: EqDec K}
        (keyf: A -> K) (F: list (K * V) -> A -> list (K * V))
        (Hpres: forall acc a j, BitsToLists.list_assoc acc j <> None ->
                                BitsToLists.list_assoc (F acc a) j <> None)
        (Hset: forall acc a, BitsToLists.list_assoc (F acc a) (keyf a) <> None) :
    forall (g: list A) acc a,
      In a g -> BitsToLists.list_assoc (fold_left F g acc) (keyf a) <> None.
  Proof.
    assert (fold_pres: forall g acc j,
               BitsToLists.list_assoc acc j <> None ->
               BitsToLists.list_assoc (fold_left F g acc) j <> None).
    { induction g as [| b g IH]; cbn; intros acc j H.
      - exact H.
      - apply IH. apply Hpres. exact H. }
    induction g as [| b g IH]; cbn; intros acc a Hin.
    - destruct Hin.
    - destruct Hin as [-> | Hin].
      + apply fold_pres. apply Hset.
      + apply IH; exact Hin.
  Qed.

  (* Every graph node's nid has a cost entry in calc_backward_cost. *)
  Lemma graph_nid_has_cost :
    forall (act: tfs_action sched) node,
      In node (graph (build_dfg ctx act)) ->
      BitsToLists.list_assoc
        (calc_backward_cost ctx (build_dfg ctx act)) (nid node) <> None.
  Proof.
    intros act node Hin. unfold calc_backward_cost.
    apply in_rev in Hin.
    apply (fold_pres_mem (fun n => nid n)
             (fun cost_map n =>
                     list_assoc_set_all_max cost_map
                       (nid n :: get_args ctx n)
                       (match BitsToLists.list_assoc cost_map (nid n) with
                        | Some c => c | None => 0 end
                        + cost_fn ctx (op n) (sz n)))).
    - intros acc a j H. apply set_all_max_pres. exact H.
    - intros acc a. apply set_all_max_mem. left. reflexivity.
    - exact Hin.
  Qed.

  Lemma graph_position_has_target_cycle :
    forall (act: tfs_action sched) n,
      n < length (graph (build_dfg ctx act)) ->
      BitsToLists.list_assoc (act_cycle_map act) n <> None.
  Proof.
    intros act n Hn.
    rewrite list_assoc_calc_target_cycle.
    set (node := nth n (graph (build_dfg ctx act))
                  {| nid := 0; op := DFG_Empty; sz := 0 |}).
    assert (Hin : In node (graph (build_dfg ctx act)))
      by (unfold node; apply nth_In; exact Hn).
    pose proof (graph_nid_has_cost act node Hin) as Hcost.
    pose proof (node_nid_at act n Hn) as Hnid. fold node in Hnid.
    rewrite Hnid in Hcost.
    destruct (BitsToLists.list_assoc
      (calc_backward_cost ctx (build_dfg ctx act)) n); cbn [option_map]; congruence.
  Qed.

  (* Every edge either remains within one target cycle or crosses a cycle
     boundary, in which case require_buffer contains the argument. *)
  Lemma arg_same_cycle_or_buffer :
    forall (act: tfs_action sched) node x,
      In node (graph (build_dfg ctx act)) ->
      In x (get_args ctx node) ->
      node_cycle act x = node_cycle act (nid node)
      \/ In x (require_buffer ctx (build_dfg ctx act) (act_cycle_map act)).
  Proof.
    intros act node x Hnode Hx.
    destruct (Nat.eq_dec (node_cycle act x) (node_cycle act (nid node))) as [Heq | Hneq].
    - left. exact Heq.
    - right. unfold require_buffer. apply nodup_In. apply in_app_iff. left.
      apply fold_left_prepend_In. exists node. split; [ exact Hnode |].
      apply filter_In. split; [ exact Hx |].
      assert (Hnid_bound : nid node < length (graph (build_dfg ctx act))).
      { pose proof (in_map nid _ _ Hnode) as Hmap.
        rewrite build_dfg_nids, in_seq in Hmap. lia. }
      pose proof (args_lt_fwd act node Hnode x Hx) as Hxlt.
      assert (Hx_bound : x < length (graph (build_dfg ctx act))) by lia.
      pose proof (graph_position_has_target_cycle act x Hx_bound) as Htx.
      pose proof (graph_position_has_target_cycle act (nid node) Hnid_bound) as Htn.
      unfold node_cycle in Hneq.
      destruct (BitsToLists.list_assoc (act_cycle_map act) x) as [cx|] eqn:Ex;
      destruct (BitsToLists.list_assoc (act_cycle_map act) (nid node)) as [cn|] eqn:En;
        try congruence.
      cbn. apply negb_true_iff, Nat.eqb_neq. exact Hneq.
  Qed.

  Lemma arg_buffer_cycle_gt :
    forall (act: tfs_action sched) node x,
      In node (graph (build_dfg ctx act)) ->
      In x (get_args ctx node) ->
      node_cycle act x <> node_cycle act (nid node) ->
      node_cycle act (nid node) < node_cycle act x.
  Proof.
    intros act node x Hnode Hx Hneq.
    pose proof (backward_cycle_monotone act node x Hnode Hx) as Hle.
    lia.
  Qed.

  (* Structural well-formedness of build_dfg (no cost reasoning): every var_map
     output nid is the nid of some graph node.  Isolated as the sole assumption
     underneath var_map_output_has_cost. *)

  (* The build_dfg monad invariant: every var_map entry's nid names a graph node.
     Holds vacuously of the empty start state and is preserved by dataflow_ops;
     the preservation step (over emit/set_var/ensure_var/merge_maps + the two
     compiler Fixpoints) is the sole remaining assumption here. *)
  Definition vmg (s : dfg_state_t (states_var:=s_var)(inputs_var:=i_var)(outputs_var:=o_var)) : Prop :=
    forall k id, In (k, id) (var_map s) ->
                 exists node, In node (graph s) /\ nid node = id.

  Local Notation dstate :=
    (dfg_state_t (states_var:=s_var)(inputs_var:=i_var)(outputs_var:=o_var)).

  (* graph only grows (node-preserving) *)
  Definition gmono (s s': dstate) : Prop :=
    forall node, In node (graph s) -> In node (graph s').
  (* id names an existing graph node *)
  Definition nidwf (s: dstate) (id: nid_t) : Prop :=
    exists node, In node (graph s) /\ nid node = id.
  (* spec of an nid-returning compiler step *)
  Definition espec (s: dstate) (id: nid_t) (s': dstate) : Prop :=
    gmono s s' /\ (vmg s -> nidwf s' id /\ vmg s').
  (* spec of a unit-returning compiler step *)
  Definition ospec (s s': dstate) : Prop :=
    gmono s s' /\ (vmg s -> vmg s').

  Lemma gmono_refl s : gmono s s. Proof. intros n H; exact H. Qed.
  Lemma gmono_trans s1 s2 s3 : gmono s1 s2 -> gmono s2 s3 -> gmono s1 s3.
  Proof. intros H1 H2 n H; apply H2, H1, H. Qed.

  Lemma espec_trans s id1 s1 id2 s2 :
    espec s id1 s1 -> espec s1 id2 s2 -> espec s id2 s2.
  Proof.
    intros [g1 v1] [g2 v2]. split.
    - eapply gmono_trans; eauto.
    - intro Hv. destruct (v1 Hv) as [_ Hv1]. exact (v2 Hv1).
  Qed.

  Lemma espec_ospec s id s' : espec s id s' -> ospec s s'.
  Proof. intros [g v]. split; [ exact g | intro Hv; apply (proj2 (v Hv)) ]. Qed.

  Lemma ospec_trans s1 s2 s3 : ospec s1 s2 -> ospec s2 s3 -> ospec s1 s3.
  Proof.
    intros [g1 v1] [g2 v2]. split.
    - eapply gmono_trans; eauto.
    - intro Hv; apply v2, v1, Hv.
  Qed.

  (* --- monad-primitive eval lemmas --- *)

  Lemma emit_eval op sz (s: dstate) :
    emit ctx op sz s =
    (length (graph s),
     {| graph := {| nid := length (graph s); op := op; sz := sz |} :: graph s;
        var_map := var_map s |}).
  Proof. unfold emit, bind, get_state, put_state, ret. reflexivity. Qed.

  (* emit adds a fresh node; grows graph, keeps var_map, returns a valid nid *)
  Lemma emit_spec op sz (s: dstate) :
    let (id, s') := emit ctx op sz s in
    espec s id s' /\ var_map s' = var_map s.
  Proof.
    rewrite emit_eval. split; [ split | reflexivity ].
    - intros n H; right; exact H.
    - intro Hv. split.
      + exists {| nid := length (graph s); op := op; sz := sz |}.
        split; [ left; reflexivity | reflexivity ].
      + intros k id Hin. cbn in Hin.
        destruct (Hv k id Hin) as [node [Hn Hnid]].
        exists node. split; [ right; exact Hn | exact Hnid ].
  Qed.

  (* set_var keeps the graph; preserves vmg provided the stored id is valid *)
  Lemma set_var_spec dfg_v id (s: dstate) :
    nidwf s id ->
    let (_, s') := set_var ctx dfg_v id s in ospec s s' /\ graph s' = graph s.
  Proof.
    intro Hid. unfold set_var, bind, get_state, put_state. cbn.
    split; [ split | reflexivity ].
    - intros n H; exact H.
    - intro Hv. intros k id0 Hin. cbn in Hin.
      destruct Hin as [Heq | Hin].
      + inversion Heq; subst. exact Hid.
      + apply filter_In in Hin. destruct Hin as [Hin _].
        exact (Hv k id0 Hin).
  Qed.

  (* ensure_var emits a fresh Var node and binds it; preserves vmg *)
  Lemma ensure_var_spec dfg_v (s: dstate) :
    let (id, s') := ensure_var ctx dfg_v s in espec s id s'.
  Proof.
    unfold ensure_var, emit, bind, get_state, put_state, ret. cbn. split.
    - intros n H; right; exact H.
    - intro Hv. split.
      + exists {| nid := length (graph s); op := DFG_Var dfg_v;
                  sz := dfg_var_size ctx dfg_v |}.
        split; [ left; reflexivity | reflexivity ].
      + intros k id0 Hin. cbn in Hin.
        destruct Hin as [Heq | Hin].
        * injection Heq as Ek Eid; subst id0.
          exists {| nid := length (graph s); op := DFG_Var dfg_v;
                    sz := dfg_var_size ctx dfg_v |}.
          split; [ left; reflexivity | reflexivity ].
        * apply filter_In in Hin. destruct Hin as [Hin _].
          destruct (Hv k id0 Hin) as [node [Hn Hnid]].
          exists node. split; [ right; exact Hn | exact Hnid ].
  Qed.

  (* get_var either finds an existing (valid, under vmg) binding without
     changing state, or falls through to ensure_var *)
  Lemma get_var_spec dfg_v (s: dstate) :
    let (id, s') := get_var ctx dfg_v s in espec s id s'.
  Proof.
    unfold get_var, bind, get_state.
    destruct (BitsToLists.list_assoc (var_map s) dfg_v) as [id|] eqn:E.
    - split.
      + apply gmono_refl.
      + intro Hv. split; [ | exact Hv ].
        (* list_assoc found (dfg_v, id) in var_map s *)
        assert (In (dfg_v, id) (var_map s)) as Hin.
        { clear -E. induction (var_map s) as [| [k v] l IH];
            cbn [BitsToLists.list_assoc] in E.
          - discriminate.
          - destruct (eq_dec dfg_v k) as [->|Hneq].
            + inversion E; subst. left; reflexivity.
            + right; apply IH; exact E. }
        exact (Hv dfg_v id Hin).
    - apply ensure_var_spec.
  Qed.

  (* combined forward spec (assuming vmg on entry) *)
  Definition fspec (s: dstate) (id: nid_t) (s': dstate) : Prop :=
    gmono s s' /\ nidwf s' id /\ vmg s'.

  Lemma emit_fspec op sz (s: dstate) :
    vmg s -> let (id, s') := emit ctx op sz s in fspec s id s'.
  Proof.
    intro Hv. pose proof (emit_spec op sz s) as H.
    destruct (emit ctx op sz s) as [id s']. destruct H as [[g v] _].
    destruct (v Hv) as [n vs]. split; [ exact g | split; [ exact n | exact vs ] ].
  Qed.

  Lemma get_var_fspec dfg_v (s: dstate) :
    vmg s -> let (id, s') := get_var ctx dfg_v s in fspec s id s'.
  Proof.
    intro Hv. pose proof (get_var_spec dfg_v s) as H.
    destruct (get_var ctx dfg_v s) as [id s']. destruct H as [g v].
    destruct (v Hv) as [n vs]. split; [ exact g | split; [ exact n | exact vs ] ].
  Qed.

  (* sequential composition of two compiler steps under vmg *)
  Lemma fspec_seq (m: M ctx nid_t) (f: nid_t -> M ctx nid_t) (s: dstate) :
    (vmg s -> let (id, s1) := m s in fspec s id s1) ->
    (forall id s1, gmono s s1 -> nidwf s1 id -> vmg s1 ->
       let (id2, s2) := f id s1 in fspec s1 id2 s2) ->
    vmg s -> let (id2, s2) := bind ctx m f s in fspec s id2 s2.
  Proof.
    intros H1 H2 Hv. specialize (H1 Hv).
    unfold bind. destruct (m s) as [id s1] eqn:Em.
    destruct H1 as [g1 [n1 v1]].
    specialize (H2 id s1 g1 n1 v1).
    destruct (f id s1) as [id2 s2]. destruct H2 as [g2 [n2 v2]].
    split; [ eapply gmono_trans; eauto | split; [ exact n2 | exact v2 ] ].
  Qed.

  (* ret keeps state; valid provided the returned id is already valid *)
  Lemma ret_fspec (id: nid_t) (s1: dstate) :
    nidwf s1 id -> vmg s1 -> let (i, s2) := ret ctx id s1 in fspec s1 i s2.
  Proof.
    intros Hn Hv. unfold ret. split; [ apply gmono_refl | split; assumption ].
  Qed.

  (* The expression compiler grows the graph, returns a valid nid, preserves vmg *)
  Lemma dataflow_expr_spec :
    forall e sz s, vmg s ->
      let (id, s') := dataflow_expr ctx e sz s in fspec s id s'.
  Proof.
    induction e; intros sz s.
    - (* tf_const *) apply emit_fspec.
    - (* tf_svar *)
      cbn [dataflow_expr]. apply fspec_seq.
      + apply get_var_fspec.
      + intros id s1 Hg Hn Hv1.
        destruct (Nat.eqb (dfg_var_size ctx (DFG_SVar v)) sz).
        * apply ret_fspec; assumption.
        * apply emit_fspec; assumption.
    - (* tf_ivar *)
      cbn [dataflow_expr]. apply fspec_seq.
      + apply emit_fspec.
      + intros id s1 Hg Hn Hv1.
        destruct (Nat.eqb _ sz).
        * apply ret_fspec; assumption.
        * apply emit_fspec; assumption.
    - (* tf_ovar *)
      cbn [dataflow_expr]. apply fspec_seq.
      + apply get_var_fspec.
      + intros id s1 Hg Hn Hv1.
        destruct (Nat.eqb (dfg_var_size ctx (DFG_OVar v)) sz).
        * apply ret_fspec; assumption.
        * apply emit_fspec; assumption.
    - (* tf_op1 *)
      cbn [dataflow_expr]. destruct op as [| source_size].
      + apply fspec_seq.
        * apply IHe.
        * intros id s1 Hg Hn Hv1. apply emit_fspec; assumption.
      + apply fspec_seq.
        * apply IHe.
        * intros id s1 Hg Hn Hv1. apply emit_fspec; assumption.
    - (* tf_op2 *)
      cbn [dataflow_expr]. destruct op;
        ( apply fspec_seq;
          [ apply IHe1
          | intros id1 s1 Hg1 Hn1; apply fspec_seq;
            [ apply IHe2
            | intros id2 s2 Hg2 Hn2; apply emit_fspec ] ] ).
    - (* tf_expr_if *)
      cbn [dataflow_expr]. apply fspec_seq.
      + apply IHe1.
      + intros idc s1 Hgc Hnc. apply fspec_seq.
        * apply IHe2.
        * intros idt s2 Hgt Hnt. apply fspec_seq.
          -- apply IHe3.
          -- intros ide s3 Hge Hne. apply emit_fspec.
  Qed.

  (* unit-returning forward spec (assuming vmg on entry) *)
  Definition ospecv (s s': dstate) : Prop := gmono s s' /\ vmg s'.

  Lemma set_var_ospecv dfg_v id (s: dstate) :
    nidwf s id -> vmg s ->
    let (u, s') := set_var ctx dfg_v id s in ospecv s s'.
  Proof.
    intros Hn Hv. pose proof (set_var_spec dfg_v id s Hn) as H.
    destruct (set_var ctx dfg_v id s) as [u s']. destruct H as [[g vi] _].
    split; [ exact g | apply vi; exact Hv ].
  Qed.

  (* The genuine control-flow-merge core: if every then/else binding names a
     node in the current graph, then after merge_maps the graph grows and every
     resulting binding names a node in the new graph.  merge_maps emits Phi
     nodes and otherwise forwards then/else nids.  This is the sole remaining
     assumption underneath dataflow_ops_preserves_vmg. *)

  Lemma nidwf_gmono (s s': dstate) id :
    nidwf s id -> gmono s s' -> nidwf s' id.
  Proof.
    intros [node [Hn Hid]] g. exists node. split; [ apply g; exact Hn | exact Hid ].
  Qed.

  Lemma la_in {K} `{EqDec K} {A} (l: list (K * A)) k v :
    BitsToLists.list_assoc l k = Some v -> In (k, v) l.
  Proof.
    induction l as [| [k1 v1] l IH]; cbn [BitsToLists.list_assoc]; intro Hla.
    - discriminate.
    - destruct (eq_dec k k1) as [->|Hne].
      + injection Hla as <-. left; reflexivity.
      + right; apply IH; exact Hla.
  Qed.

  (* bind reduction as an equation (rewrite works under nested lets) *)
  Lemma bind_pair {A B} (m: M ctx A) (f: A -> M ctx B) (s: dstate) x s1 :
    m s = (x, s1) -> bind ctx m f s = f x s1.
  Proof. intro H. unfold bind. rewrite H. reflexivity. Qed.

  (* emit adds a fresh node; the returned id names it (unconditionally) *)
  Lemma emit_eq op sz (s: dstate) id s1 :
    emit ctx op sz s = (id, s1) ->
    gmono s s1 /\ nidwf s1 id /\ var_map s1 = var_map s.
  Proof.
    rewrite emit_eval. intro H. injection H as <- <-. split; [| split].
    - intros n Hn; right; exact Hn.
    - exists {| nid := length (graph s); op := op; sz := sz |}.
      split; [ left; reflexivity | reflexivity ].
    - reflexivity.
  Qed.

  (* ensure_var emits a fresh Var node; the returned id names it *)
  Lemma ensure_var_eq dfg_v (s: dstate) id s1 :
    ensure_var ctx dfg_v s = (id, s1) -> gmono s s1 /\ nidwf s1 id.
  Proof.
    unfold ensure_var, emit, bind, get_state, put_state, ret. cbn. intro H.
    injection H as <- <-. split.
    - intros n Hn; right; exact Hn.
    - exists {| nid := length (graph s); op := DFG_Var dfg_v;
                sz := dfg_var_size ctx dfg_v |}.
      split; [ left; reflexivity | reflexivity ].
  Qed.

  (* merge_key: if the then/else source nids (when present) name graph nodes,
     the graph grows and any produced nid names a node in the new graph *)
  Lemma merge_key_spec cond_id k vt_opt ve_opt (s: dstate) res s' :
    merge_key ctx cond_id k vt_opt ve_opt s = (res, s') ->
    (forall vt, vt_opt = Some vt -> nidwf s vt) ->
    (forall ve, ve_opt = Some ve -> nidwf s ve) ->
    gmono s s' /\ (forall fid, res = Some fid -> nidwf s' fid).
  Proof.
    intros Hrun Hvt Hve. unfold merge_key in Hrun.
    destruct vt_opt as [vt|]; destruct ve_opt as [ve|].
    - (* Some / Some *)
      destruct (eq_dec vt ve) as [Heq|Hne].
      + unfold ret in Hrun. injection Hrun as <- <-.
        split; [ apply gmono_refl
               | intros fid Hf; injection Hf as <-; apply Hvt; reflexivity ].
      + destruct (emit ctx (DFG_Phi cond_id vt ve) (dfg_var_size ctx k) s)
          as [phi s1] eqn:Ee.
        pose proof Ee as Ee'; apply emit_eq in Ee'; destruct Ee' as [g [n _]].
        rewrite (bind_pair (emit ctx (DFG_Phi cond_id vt ve) (dfg_var_size ctx k))
                   _ s _ _ Ee) in Hrun. unfold ret in Hrun.
        injection Hrun as <- <-.
        split; [ exact g | intros fid Hf; injection Hf as <-; exact n ].
    - (* Some / None *)
      destruct (ensure_var ctx k s) as [ve s1] eqn:Ev.
      pose proof Ev as Ev'; apply ensure_var_eq in Ev'; destruct Ev' as [g1 n1].
      rewrite (bind_pair (ensure_var ctx k) _ s _ _ Ev) in Hrun.
      destruct (emit ctx (DFG_Phi cond_id vt ve) (dfg_var_size ctx k) s1)
        as [phi s2] eqn:Ee.
      pose proof Ee as Ee'; apply emit_eq in Ee'; destruct Ee' as [g2 [n2 _]].
      rewrite (bind_pair (emit ctx (DFG_Phi cond_id vt ve) (dfg_var_size ctx k))
                 _ s1 _ _ Ee) in Hrun. unfold ret in Hrun.
      injection Hrun as <- <-.
      split; [ eapply gmono_trans; eauto
             | intros fid Hf; injection Hf as <-; exact n2 ].
    - (* None / Some *)
      destruct (ensure_var ctx k s) as [vt s1] eqn:Ev.
      pose proof Ev as Ev'; apply ensure_var_eq in Ev'; destruct Ev' as [g1 n1].
      rewrite (bind_pair (ensure_var ctx k) _ s _ _ Ev) in Hrun.
      destruct (emit ctx (DFG_Phi cond_id vt ve) (dfg_var_size ctx k) s1)
        as [phi s2] eqn:Ee.
      pose proof Ee as Ee'; apply emit_eq in Ee'; destruct Ee' as [g2 [n2 _]].
      rewrite (bind_pair (emit ctx (DFG_Phi cond_id vt ve) (dfg_var_size ctx k))
                 _ s1 _ _ Ee) in Hrun. unfold ret in Hrun.
      injection Hrun as <- <-.
      split; [ eapply gmono_trans; eauto
             | intros fid Hf; injection Hf as <-; exact n2 ].
    - (* None / None *)
      unfold ret in Hrun. injection Hrun as <- <-.
      split; [ apply gmono_refl | intros fid Hf; discriminate ].
  Qed.

  (* merge_loop preserves graph monotonicity and the "every binding names a
     graph node" invariant across the accumulator.  Stated equationally to keep
     reduction inside a hypothesis (avoids nested-let destruct blockage). *)
  Lemma merge_loop_spec cond_id mt me :
    forall keys acc (s: dstate) fin s',
      merge_loop ctx cond_id mt me keys acc s = (fin, s') ->
      (forall k id, In (k, id) mt -> nidwf s id) ->
      (forall k id, In (k, id) me -> nidwf s id) ->
      (forall k id, In (k, id) acc -> nidwf s id) ->
      gmono s s' /\ (forall k id, In (k, id) fin -> nidwf s' id).
  Proof.
    induction keys as [| [k kv] rest IH]; intros acc s fin s' Hrun Hmt Hme Hacc.
    - (* [] *) cbn [merge_loop] in Hrun. unfold ret in Hrun.
      injection Hrun as <- <-. split; [ apply gmono_refl | exact Hacc ].
    - (* (k,_) :: rest *)
      cbn [merge_loop] in Hrun.
      destruct (BitsToLists.list_assoc acc k) as [existing|] eqn:Ek.
      + (* already present: skip, state unchanged *)
        eapply IH; eauto.
      + (* not present: run merge_key then recurse *)
        unfold bind in Hrun. cbv beta in Hrun.
        destruct (merge_key ctx cond_id k (BitsToLists.list_assoc mt k)
                    (BitsToLists.list_assoc me k) s) as [res_opt s1] eqn:Emk.
        cbv beta iota in Hrun.
        pose proof (merge_key_spec cond_id k _ _ s res_opt s1 Emk
                      (fun vt Hvt => Hmt k vt (la_in mt k vt Hvt))
                      (fun ve Hve => Hme k ve (la_in me k ve Hve))) as Hmk.
        destruct Hmk as [gk nk].
        assert (Hmt1: forall kk id, In (kk, id) mt -> nidwf s1 id).
        { intros kk id Hin. eapply nidwf_gmono; [ eapply Hmt; exact Hin | exact gk ]. }
        assert (Hme1: forall kk id, In (kk, id) me -> nidwf s1 id).
        { intros kk id Hin. eapply nidwf_gmono; [ eapply Hme; exact Hin | exact gk ]. }
        destruct res_opt as [final_id|].
        * (* Some: recurse with (k, final_id) :: acc *)
          assert (Hacc1: forall kk id, In (kk, id) ((k, final_id) :: acc) -> nidwf s1 id).
          { intros kk id Hin. destruct Hin as [Heq|Hin].
            - injection Heq as <- <-. apply nk; reflexivity.
            - eapply nidwf_gmono; [ eapply Hacc; exact Hin | exact gk ]. }
          specialize (IH ((k, final_id) :: acc) s1 fin s' Hrun Hmt1 Hme1 Hacc1).
          destruct IH as [g' n'].
          split; [ eapply gmono_trans; eauto | exact n' ].
        * (* None: recurse with acc unchanged *)
          assert (Hacc1: forall kk id, In (kk, id) acc -> nidwf s1 id).
          { intros kk id Hin. eapply nidwf_gmono; [ eapply Hacc; exact Hin | exact gk ]. }
          specialize (IH acc s1 fin s' Hrun Hmt1 Hme1 Hacc1).
          destruct IH as [g' n'].
          split; [ eapply gmono_trans; eauto | exact n' ].
  Qed.

  Lemma merge_maps_spec cond_id mo mt me (s: dstate) :
    (forall k id, In (k, id) mt -> nidwf s id) ->
    (forall k id, In (k, id) me -> nidwf s id) ->
    let (fin, s') := merge_maps ctx cond_id mo mt me s in
    gmono s s' /\ (forall k id, In (k, id) fin -> nidwf s' id).
  Proof.
    intros Hmt Hme. unfold merge_maps.
    destruct (merge_loop ctx cond_id mt me (mt ++ me) [] s) as [fin s'] eqn:Er.
    eapply merge_loop_spec.
    - exact Er.
    - exact Hmt.
    - exact Hme.
    - intros k id Hin; destruct Hin.
  Qed.

  Lemma dataflow_ops_spec :
    forall ops s, vmg s ->
      let (u, s') := dataflow_ops ctx ops s in ospecv s s'.
  Proof.
    induction ops as [ op | op1 IH1 op2 IH2 | cond then_ops IHthen else_ops IHelse ];
      intros s Hv.
    - (* tf_ops_base *)
      destruct op as [ | dst expr | dst expr ]; cbn [dataflow_ops].
      + (* tf_nop *) unfold ret. split; [ apply gmono_refl | exact Hv ].
      + (* tf_assign *)
        unfold bind.
        pose proof (dataflow_expr_spec expr (dfg_var_size ctx (DFG_SVar dst)) s Hv) as He.
        destruct (dataflow_expr ctx expr (dfg_var_size ctx (DFG_SVar dst)) s)
          as [res_id s1]. destruct He as [g1 [n1 v1]].
        pose proof (set_var_ospecv (DFG_SVar dst) res_id s1 n1 v1) as Hs.
        destruct (set_var ctx (DFG_SVar dst) res_id s1) as [u s2].
        destruct Hs as [g2 v2]. split; [ eapply gmono_trans; eauto | exact v2 ].
      + (* tf_output *)
        unfold bind.
        pose proof (dataflow_expr_spec expr (dfg_var_size ctx (DFG_OVar dst)) s Hv) as He.
        destruct (dataflow_expr ctx expr (dfg_var_size ctx (DFG_OVar dst)) s)
          as [res_id s1]. destruct He as [g1 [n1 v1]].
        pose proof (set_var_ospecv (DFG_OVar dst) res_id s1 n1 v1) as Hs.
        destruct (set_var ctx (DFG_OVar dst) res_id s1) as [u s2].
        destruct Hs as [g2 v2]. split; [ eapply gmono_trans; eauto | exact v2 ].
    - (* tf_ops_cons *)
      cbn [dataflow_ops]. unfold bind.
      specialize (IH1 s Hv).
      destruct (dataflow_ops ctx op1 s) as [u1 s1]. destruct IH1 as [g1 v1].
      specialize (IH2 s1 v1).
      destruct (dataflow_ops ctx op2 s1) as [u2 s2]. destruct IH2 as [g2 v2].
      split; [ eapply gmono_trans; eauto | exact v2 ].
    - (* tf_ops_if *)
      unfold ospecv. cbn [dataflow_ops]. unfold bind, get_state, put_state.
      (* cond *)
      pose proof (dataflow_expr_spec cond 1 s Hv) as Hc.
      destruct (dataflow_expr ctx cond 1 s) as [cond_id s0].
      destruct Hc as [g0 [n0 v0]].
      (* then branch on s0 *)
      specialize (IHthen s0 v0).
      destruct (dataflow_ops ctx then_ops s0) as [ut s1].
      destruct IHthen as [g1 v1].
      (* else branch on sp = {graph:=graph s1; var_map:=var_map s0} *)
      assert (Hvsp : vmg {| graph := graph s1; var_map := var_map s0 |}).
      { unfold vmg; cbn. intros k id Hin.
        destruct (v0 k id Hin) as [node [Hn Hnid]].
        exists node. split; [ apply g1; exact Hn | exact Hnid ]. }
      specialize (IHelse _ Hvsp).
      destruct (dataflow_ops ctx else_ops {| graph := graph s1; var_map := var_map s0 |})
        as [ue s2].
      destruct IHelse as [g2 v2].
      (* merge *)
      assert (Hmt : forall k id, In (k, id) (var_map s1) -> nidwf s2 id).
      { intros k id Hin. destruct (v1 k id Hin) as [node [Hn Hnid]].
        exists node. split; [ apply g2; cbn; exact Hn | exact Hnid ]. }
      assert (Hme : forall k id, In (k, id) (var_map s2) -> nidwf s2 id).
      { intros k id Hin. exact (v2 k id Hin). }
      pose proof (merge_maps_spec cond_id (var_map s0) (var_map s1) (var_map s2)
                    s2 Hmt Hme) as Hm.
      destruct (merge_maps ctx cond_id (var_map s0) (var_map s1) (var_map s2) s2)
        as [final_vars s3].
      destruct Hm as [g3 nf].
      (* final state = {graph := graph s3; var_map := final_vars} *)
      cbn. split.
      + (* gmono s (graph s3) *)
        intros node Hn. cbn.
        apply g3. apply g2. cbn. apply g1. apply g0. exact Hn.
      + (* vmg final *)
        unfold vmg; cbn. intros k id Hin. exact (nf k id Hin).
  Qed.

  Lemma dataflow_ops_preserves_vmg :
    forall ops s, vmg s -> vmg (snd (dataflow_ops ctx ops s)).
  Proof.
    intros ops s Hv. pose proof (dataflow_ops_spec ops s Hv) as H.
    destruct (dataflow_ops ctx ops s) as [u s']. cbn. apply (proj2 H).
  Qed.

  (* Structural well-formedness of build_dfg (no cost reasoning): every var_map
     output nid is the nid of some graph node.  The rev/empty-state wrapper is
     fully proved; only dataflow_ops_preserves_vmg remains assumed. *)
  Lemma var_map_snd_is_graph_nid :
    forall (act: tfs_action sched) n,
      In n (map snd (var_map (build_dfg ctx act))) ->
      exists node, In node (graph (build_dfg ctx act)) /\ nid node = n.
  Proof.
    intros act n Hn.
    apply in_map_iff in Hn. destruct Hn as [[k id] [Hsnd Hin]]. cbn in Hsnd. subst n.
    unfold build_dfg in *.
    destruct (dataflow_ops ctx (tfs_spec_action_ops ctx act)
                {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0 |} ]; var_map := [] |})
      as [u final] eqn:E.
    cbn in Hin |- *.
    assert (Hv : vmg final).
    { pose proof (dataflow_ops_preserves_vmg (tfs_spec_action_ops ctx act)
                    {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0 |} ]; var_map := [] |}) as HP.
      rewrite E in HP. cbn in HP. apply HP.
      unfold vmg. intros k0 id0 HI. cbn in HI. destruct HI. }
    destruct (Hv k id Hin) as [node [Hng Hnn]].
    exists node. split; [ rewrite <- in_rev; exact Hng | exact Hnn ].
  Qed.

  (* Well-formedness of build_dfg: every var_map output node has a cost entry
     (it appears in the graph, so calc_backward_cost assigns it a cost).  The
     cost-existence reasoning is now fully proved; only the purely structural
     var_map_snd_is_graph_nid remains assumed. *)
  Lemma var_map_output_has_cost :
    forall (act: tfs_action sched) n,
      In n (map snd (var_map (build_dfg ctx act))) ->
      BitsToLists.list_assoc
        (calc_target_cycle cost_limit
           (calc_backward_cost ctx (build_dfg ctx act))) n <> None.
  Proof.
    intros act n Hn.
    rewrite list_assoc_calc_target_cycle.
    destruct (var_map_snd_is_graph_nid act n Hn) as [node [Hnode Hnid]].
    subst n.
    pose proof (graph_nid_has_cost act node Hnode) as Hc.
    destruct (BitsToLists.list_assoc
                (calc_backward_cost ctx (build_dfg ctx act)) (nid node)) as [c|].
    - cbn [option_map]. discriminate.
    - congruence.
  Qed.

  (* Every buffered nid has a strictly positive target cycle: require_buffer
     only buffers (a) a node's args that live in a DIFFERENT cycle — and since
     backward cost is non-increasing along edges, an arg's target cycle is >=
     the node's, and being buffered it differs, so it is > 0 — or (b) a var_map
     output whose target cycle is explicitly > 0. *)
  Lemma require_buffer_cycle_pos :
    forall (act: tfs_action sched) n,
      In n (require_buffer ctx (build_dfg ctx act)
              (calc_target_cycle cost_limit
                 (calc_backward_cost ctx (build_dfg ctx act)))) ->
      node_cycle act n <> 0.
  Proof.
    intros act n Hin.
    unfold require_buffer in Hin.
    apply nodup_In, in_app_iff in Hin.
    set (cc := calc_target_cycle cost_limit
                 (calc_backward_cost ctx (build_dfg ctx act))) in *.
    destruct Hin as [HA | HB].
    - (* arg-part: n is a buffered argument of some node *)
      apply fold_left_prepend_In in HA.
      destruct HA as [node [Hnode Hn]].
      apply filter_In in Hn. destruct Hn as [Hn Hpred].
      unfold node_cycle. fold cc.
      destruct (BitsToLists.list_assoc cc n) as [c|] eqn:Hc; [| discriminate Hpred].
      pose proof (backward_cycle_monotone act node n Hnode Hn) as Hmono.
      unfold node_cycle in Hmono. fold cc in Hmono. rewrite Hc in Hmono.
      destruct (BitsToLists.list_assoc cc (nid node)) as [cn|] eqn:Hcn.
      + (* Hpred: c <> cn; Hmono: cn <= c ⇒ c > cn ≥ 0 ⇒ c <> 0 *)
        apply negb_true_iff, Nat.eqb_neq in Hpred.
        intro Hc0. subst c. apply Nat.le_0_r in Hmono. apply Hpred. symmetry. exact Hmono.
      + (* n_cycle defaults to 0; Hpred: c <> 0 directly *)
        apply negb_true_iff, Nat.eqb_neq in Hpred. exact Hpred.
    - (* out-part: n is a var_map output with nonzero target cycle *)
      apply filter_In in HB. destruct HB as [Hmem Hpred].
      pose proof (var_map_output_has_cost act n Hmem) as Hne. fold cc in Hne.
      unfold node_cycle. fold cc.
      destruct (BitsToLists.list_assoc cc n) as [c|] eqn:Hc;
        [| exfalso; apply Hne; reflexivity ].
      destruct c as [| c']; [ discriminate Hpred | ].
      intro H; discriminate H.
  Qed.

  (* Every buffered nid is a REAL node of the forward graph.  The arg-part of
     require_buffer holds args of graph nodes (positive, below their consumer);
     the out-part holds var_map values (positive by build_dfg_args_pos, and a
     graph nid by var_map_snd_is_graph_nid). *)
  Lemma require_buffer_node_range :
    forall (act: tfs_action sched) n,
      In n (require_buffer ctx (build_dfg ctx act)
              (calc_target_cycle cost_limit
                 (calc_backward_cost ctx (build_dfg ctx act)))) ->
      1 <= n /\ n < length (graph (build_dfg ctx act)).
  Proof.
    intros act n Hin.
    assert (Hnid_lt : forall node, In node (graph (build_dfg ctx act)) ->
              nid node < length (graph (build_dfg ctx act))).
    { intros node Hnode.
      destruct (In_nth _ _ {| nid := 0; op := DFG_Empty; sz := 0 |} Hnode)
        as [p [Hp Hnth]].
      pose proof (node_nid_at act p Hp) as Hp_nid.
      rewrite Hnth in Hp_nid. rewrite Hp_nid. exact Hp. }
    unfold require_buffer in Hin.
    apply nodup_In, in_app_iff in Hin.
    destruct Hin as [HA | HB].
    - apply fold_left_prepend_In in HA.
      destruct HA as [node [Hnode Hn]].
      apply filter_In in Hn. destruct Hn as [Hn _].
      pose proof (build_dfg_args_pos act) as [_ [Hargpos _]].
      split; [ exact (Hargpos node Hnode n Hn) | ].
      pose proof (args_lt_fwd act node Hnode n Hn) as Hlt.
      pose proof (Hnid_lt node Hnode). lia.
    - apply filter_In in HB. destruct HB as [Hmem _].
      split.
      + apply in_map_iff in Hmem. destruct Hmem as [[k id] [Hsnd Hkin]].
        cbn in Hsnd. subst id.
        pose proof (build_dfg_args_pos act) as [Hvm _]. exact (Hvm k n Hkin).
      + destruct (var_map_snd_is_graph_nid act n Hmem) as [node [Hnode Hnid]].
        rewrite <- Hnid. exact (Hnid_lt node Hnode).
  Qed.

  Lemma vreg_nid_node_range :
    forall (act: tfs_action sched) a_idx n_idx,
      act_idx_aligned act a_idx ->
      1 <= vreg_nid a_idx n_idx
      /\ vreg_nid a_idx n_idx < length (graph (build_dfg ctx act)).
  Proof.
    intros act a_idx n_idx Halign.
    apply require_buffer_node_range.
    apply vreg_nid_in_require_buffer. exact Halign.
  Qed.

  (* Hence every register nid has node_cycle >= 1, so its validity bit
     starts (correctly) at 0. *)  Lemma buffered_node_cycle_pos :
    forall (act: tfs_action sched) a_idx n_idx,
      act_idx_aligned act a_idx ->
      node_cycle act (vreg_nid a_idx n_idx) <> 0.
  Proof.
    intros act a_idx n_idx Halign.
    apply require_buffer_cycle_pos.
    apply vreg_nid_in_require_buffer. exact Halign.
  Qed.


  (* I(0) for the RETRACTED cycle-ranked [buffer_inv]: established by start_rel
     (all validity bits zero at the start; only nodes with target cycle 0 are
     immediately valid).  Unused; see the note on [buffer_inv]. *)
  Lemma buffer_inv_init :
    forall (act: tfs_action sched) a_idx (sp0: src_sys_state)
           (ss0: sched_sys_state) (input: input_t),
      act_idx_aligned act a_idx ->
      start_rel sp0 ss0 ->
      buffer_inv act a_idx ss0 input 0.
  Proof.
    intros act a_idx sp0 ss0 input Halign [_ [_ Hzero]] n_idx.
    (* validity bit is zero at the start *)
    assert (Hv : (fst ss0).[tf_dfg_v a_idx n_idx] = Bits.zero)
      by (apply Hzero; exact I).
    (* buffered nodes have a positive target cycle *)
    pose proof (buffered_node_cycle_pos act a_idx n_idx Halign) as Hpos.
    split.
    - intros Hle. exfalso. apply Hpos. apply Nat.le_0_r. exact Hle.
    - intros Hle. exfalso. apply Hpos. apply Nat.le_0_r. exact Hle.
  Qed.

  (* When a cycle does NOT fire the done flag, tfs_next_cycle takes the ALWAYS
     branch: cycle_updates reduces to just the always-updates (no reset/done
     prefix).  This is the entry point for pre-done buffer reasoning. *)
  Lemma cycle_updates_not_done (act: tfs_action sched) (ss: sched_sys_state) (input: input_t) :
    ~ done_set (sched_step act ss input) ->
    cycle_updates act ss input
    = tfs_get_updates sched (fst (Contract.tfs_schedule sched act)) ss input.
  Proof.
    intro Hnd.
    (* ~done_set gives the always-list done value = zero *)
    assert (Hdz : find_st_val sched (tfs_done_signal sched)
                    (tfs_get_updates sched (fst (Contract.tfs_schedule sched act)) ss input) ss
                  = Bits.zero).
    { unfold done_set in Hnd. rewrite sched_step_done in Hnd.
      destruct (bits1_cases
                  (find_st_val sched (tfs_done_signal sched)
                     (tfs_get_updates sched (fst (Contract.tfs_schedule sched act)) ss input) ss))
        as [Hone | Hz].
      - exfalso. apply Hnd. rewrite Hone. discriminate.
      - exact Hz. }
    unfold cycle_updates. cbv zeta. rewrite Hdz.
    rewrite beq_dec_refl. reflexivity.
  Qed.

  (* Every op emitted by compile_dfg_buffers is a tf_assign to a tf_dfg_b or
     tf_dfg_v register — never a base state var tf_dfg_s (nor the done flag). *)
  Lemma compile_dfg_buffers_no_svar
    (a_idx: nat)
    (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var) (outputs_var := o_var))
    (buffers: list (nat * (nat * nat))) (s: s_var)
    (op: @tf_op (tfs_states sched) i_var o_var) :
    In op (compile_dfg_buffers ctx cost_limit a_idx dfg buffers) ->
    ~ op_assigns_st (tf_dfg_s s) op.
  Proof.
    unfold compile_dfg_buffers.
    destruct (index_of_nat _ a_idx) as [a' |]; [| intros []].
    intro Hin. apply in_flat_map in Hin.
    destruct Hin as [[bnid x] [_ Hop]].
    destruct (index_of_nat _ (fst x)) as [n' |]; [| destruct Hop].
    destruct (compile_dfg_expr _ _ _ _ _ _ _) as [expr valid].
    cbn [In] in Hop.
    destruct Hop as [Heq | [Heq | []]]; subst op; intros [e He]; discriminate He.
  Qed.

  (* No op in the always-ops list assigns a base state var tf_dfg_s: the head is
     the done-flag assignment (tf_dfg_done) and the tail is compile_dfg_buffers
     (only tf_dfg_b / tf_dfg_v writes). *)
  Lemma always_ops_no_svar (act: tfs_action sched) (s: s_var)
    (op: @tf_op (tfs_states sched) i_var o_var) :
    In op (fst (Contract.tfs_schedule sched act)) ->
    ~ op_assigns_st (tf_dfg_s s) op.
  Proof.
    unfold sched, tfs_schedule, Contract.tfs_schedule, schedule. cbv zeta. cbn [fst].
    intro Hin. cbn [In] in Hin. destruct Hin as [Heq | Hin].
    - subst op. unfold compile_dfg_valid. cbv zeta.
      intros [e He]. discriminate He.
    - exact (compile_dfg_buffers_no_svar _ _ _ s op Hin).
  Qed.

  (* A non-done cycle leaves every base state var tf_dfg_s unchanged: the always-
     ops never assign tf_dfg_s, so find_st_update returns None and the value
     falls through to the pre-cycle register. *)
  Lemma sched_step_preserves_svar (act: tfs_action sched) (ss: sched_sys_state)
    (input: input_t) (s: s_var) :
    ~ done_set (sched_step act ss input) ->
    (fst (sched_step act ss input)).[tf_dfg_s s] = (fst ss).[tf_dfg_s s].
  Proof.
    intro Hnd. rewrite sched_step_getst. rewrite (cycle_updates_not_done _ _ _ Hnd).
    unfold find_st_val.
    rewrite (find_st_update_not_in (tf_dfg_s s) _ ss input
               (fun op Hin => always_ops_no_svar act s op Hin)).
    reflexivity.
  Qed.

  (* Every op emitted by compile_dfg_buffers is a tf_assign, never a tf_output. *)
  Lemma compile_dfg_buffers_no_out
    (a_idx: nat)
    (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var) (outputs_var := o_var))
    (buffers: list (nat * (nat * nat))) (o: o_var)
    (op: @tf_op (tfs_states sched) i_var o_var) :
    In op (compile_dfg_buffers ctx cost_limit a_idx dfg buffers) ->
    ~ op_writes_out o op.
  Proof.
    unfold compile_dfg_buffers.
    destruct (index_of_nat _ a_idx) as [a' |]; [| intros []].
    intro Hin. apply in_flat_map in Hin.
    destruct Hin as [[bnid x] [_ Hop]].
    destruct (index_of_nat _ (fst x)) as [n' |]; [| destruct Hop].
    destruct (compile_dfg_expr _ _ _ _ _ _ _) as [expr valid].
    cbn [In] in Hop.
    destruct Hop as [Heq | [Heq | []]]; subst op; intros [e He]; discriminate He.
  Qed.

  (* No op in the always-ops list writes an output: the head assigns the done
     flag and the tail is compile_dfg_buffers (only tf_dfg_b / tf_dfg_v writes).
     Outputs are produced exclusively by the DONE branch of tfs_next_cycle. *)
  Lemma always_ops_no_out (act: tfs_action sched) (o: o_var)
    (op: @tf_op (tfs_states sched) i_var o_var) :
    In op (fst (Contract.tfs_schedule sched act)) ->
    ~ op_writes_out o op.
  Proof.
    unfold sched, tfs_schedule, Contract.tfs_schedule, schedule. cbv zeta. cbn [fst].
    intro Hin. cbn [In] in Hin. destruct Hin as [Heq | Hin].
    - subst op. unfold compile_dfg_valid. cbv zeta.
      intros [e He]. discriminate He.
    - exact (compile_dfg_buffers_no_out _ _ _ o op Hin).
  Qed.

  (* A non-done cycle leaves every output unchanged. *)
  Lemma sched_step_preserves_ovar (act: tfs_action sched) (ss: sched_sys_state)
    (input: input_t) (o: o_var) :
    ~ done_set (sched_step act ss input) ->
    (snd (sched_step act ss input)).[o] = (snd ss).[o].
  Proof.
    intro Hnd. rewrite sched_step_getout. rewrite (cycle_updates_not_done _ _ _ Hnd).
    unfold find_out_val.
    rewrite (find_out_update_not_in o _ ss input
               (fun op Hin => always_ops_no_out act o op Hin)).
    reflexivity.
  Qed.

  (* A BUFFER-FREE compiled expression reads only base state vars (tf_dfg_s),
     outputs and the input, so its value only depends on those.  This is what
     makes a settled value stable across further pre-done cycles. *)
  Lemma compile_nobuf_state_indep
        (act: tfs_action sched) a_idx (input: input_t) (ss1 ss2: sched_sys_state) :
    (forall s, (fst ss1).[tf_dfg_s s] = (fst ss2).[tf_dfg_s s]) ->
    (forall o, (snd ss1).[o] = (snd ss2).[o]) ->
    forall fuel n szB,
      tf_eval_expr ss_sz i_sz oo_sz (szB := szB)
        (fst (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act) n []))
        ss1 input
      = tf_eval_expr ss_sz i_sz oo_sz (szB := szB)
        (fst (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act) n []))
        ss2 input.
  Proof.
    intros Hs Ho fuel.
    induction fuel as [| fuel IH]; intros n szB; [ reflexivity | ].
    cbn [compile_dfg_expr BitsToLists.list_assoc]. cbv beta iota.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | op1 arg | op1 arg1 arg2 | arg | cnd tid eid | ].
    - reflexivity.
    - reflexivity.
    - destruct v; cbn [fst tf_eval_expr]; [ rewrite Hs | rewrite Ho ]; reflexivity.
    - destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                  arg []) as [ae ve] eqn:E1.
      cbn [fst]. destruct op1 as [| src];
        cbn [tf_eval_expr];
        [ specialize (IH arg szB) | specialize (IH arg src) ];
        rewrite E1 in IH; cbn [fst] in IH; rewrite IH; reflexivity.
    - destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                  arg1 []) as [a1e v1e] eqn:E1.
      destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                  arg2 []) as [a2e v2e] eqn:E2.
      cbn [fst].
      pose proof (IH arg1 szB) as Hc1. pose proof (IH arg2 szB) as Hc2.
      rewrite E1 in Hc1. rewrite E2 in Hc2. cbn [fst] in Hc1, Hc2.
      destruct op1 as [ | | | | | | szC cop ];
        cbn [tf_eval_expr]; try (rewrite Hc1, Hc2; reflexivity).
      pose proof (IH arg1 szC) as Hd1. pose proof (IH arg2 szC) as Hd2.
      rewrite E1 in Hd1. rewrite E2 in Hd2. cbn [fst] in Hd1, Hd2.
      rewrite Hd1, Hd2. destruct cop; reflexivity.
    - destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                  arg []) as [ae ve] eqn:E1.
      cbn [fst tf_eval_expr].
      specialize (IH arg (sz (nth arg (graph (build_dfg ctx act))
                                {| nid := 0; op := DFG_Empty; sz := 0 |}))).
      rewrite E1 in IH. cbn [fst] in IH. rewrite IH. reflexivity.
    - destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                  cnd []) as [ce cv] eqn:Ec.
      destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                  tid []) as [te tv] eqn:Et.
      destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                  eid []) as [ee ev] eqn:Ee.
      cbn [fst tf_eval_expr].
      pose proof (IH cnd 1) as Hcc.
      pose proof (IH tid szB) as Hct.
      pose proof (IH eid szB) as Hce.
      rewrite Ec in Hcc. rewrite Et in Hct. rewrite Ee in Hce.
      cbn [fst] in Hcc, Hct, Hce.
      rewrite Hcc, Hct, Hce. reflexivity.
    - reflexivity.
  Qed.

  (* Specialisation: a buffer-free compiled expression is unchanged by a pre-done
     cycle (which touches neither tf_dfg_s nor the outputs). *)
  Lemma compile_nobuf_step_stable
        (act: tfs_action sched) a_idx (ss: sched_sys_state) (input: input_t) :
    ~ done_set (sched_step act ss input) ->
    forall fuel n szB,
      tf_eval_expr ss_sz i_sz oo_sz (szB := szB)
        (fst (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act) n []))
        (sched_step act ss input) input
      = tf_eval_expr ss_sz i_sz oo_sz (szB := szB)
        (fst (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act) n []))
        ss input.
  Proof.
    intro Hnd.
    apply compile_nobuf_state_indep.
    - intro s. exact (sched_step_preserves_svar act ss input s Hnd).
    - intro o. exact (sched_step_preserves_ovar act ss input o Hnd).
  Qed.

  (* compile_dfg_expr is fuel-invariant above the structural bound: for the
     forward build_dfg graph, any two fuels strictly above a node's position
     produce the same compiled (expr, valid) pair.  The recursion only descends
     into strictly-smaller arg positions, so fuel beyond [n] is never consumed.
     This lets us canonicalize node_ref_expr / compile calls to a single fuel. *)
  Lemma compile_fuel_irrel (act: tfs_action sched) a_idx buffers :
    forall n,
      1 <= n ->
      n < length (graph (build_dfg ctx act)) ->
      forall f1 f2,
        n < f1 -> n < f2 ->
        compile_dfg_expr ctx cost_limit f1 a_idx (build_dfg ctx act) n buffers
        = compile_dfg_expr ctx cost_limit f2 a_idx (build_dfg ctx act) n buffers.
  Proof.
    intros n. induction n as [n IH] using (well_founded_induction lt_wf).
    intros Hn1 Hnlen f1 f2 Hf1 Hf2.
    destruct f1 as [| f1']; [ lia | ].
    destruct f2 as [| f2']; [ lia | ].
    set (dfg := build_dfg ctx act) in *.
    cbn [compile_dfg_expr].
    destruct (BitsToLists.list_assoc buffers n) as [[n_idx n_sz] |] eqn:Hla.
    - reflexivity.
    - set (node := nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}) in *.
      assert (Hnode_in : In node (graph dfg)) by (unfold node; apply nth_In; exact Hnlen).
      pose proof (build_dfg_args_pos act) as [_ [Hargpos _]].
      pose proof (node_nid_at act n Hnlen) as Hnid. fold dfg in Hnid. fold node in Hnid.
      assert (Harg : forall x, In x (get_args ctx node) -> 1 <= x /\ x < n).
      { intros x Hx. split.
        - exact (Hargpos node Hnode_in x Hx).
        - pose proof (args_lt_fwd act node) as Hlt2. fold dfg in Hlt2.
          specialize (Hlt2 Hnode_in x Hx). rewrite Hnid in Hlt2. exact Hlt2. }
      assert (Hrec : forall x, In x (get_args ctx node) ->
                compile_dfg_expr ctx cost_limit f1' a_idx dfg x buffers
                = compile_dfg_expr ctx cost_limit f2' a_idx dfg x buffers).
      { intros x Hx. destruct (Harg x Hx) as [Hx1 Hx2].
        apply (IH x Hx2 Hx1 (Nat.lt_trans _ _ _ Hx2 Hnlen)); lia. }
      destruct (op node) as [c | v | v | op1 arg | op1 arg1 arg2 | arg | cnd tid eid | ] eqn:Hop.
      + reflexivity.
      + reflexivity.
      + destruct v; reflexivity.
      + assert (Hain : In arg (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        rewrite (Hrec arg Hain). reflexivity.
      + assert (Ha1 : In arg1 (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        assert (Ha2 : In arg2 (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; left; reflexivity).
        rewrite (Hrec arg1 Ha1), (Hrec arg2 Ha2). reflexivity.
      + assert (Hain : In arg (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        rewrite (Hrec arg Hain). reflexivity.
      + assert (Hcin : In cnd (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        assert (Htin : In tid (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; left; reflexivity).
        assert (Hein : In eid (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; right; left; reflexivity).
        rewrite (Hrec cnd Hcin), (Hrec tid Htin), (Hrec eid Hein). reflexivity.
      + exfalso. apply (node_op_not_empty act n Hn1 Hnlen). exact Hop.
  Qed.

  (* Every buffer register of [act]'s slot whose cached node id is BELOW [bound]
     holds its SETTLED value, i.e. the fully-inlined buffer-free reference
     expression of the node it caches.  This is the guard-free form of
     buffer_inv's value conjunct, relativized by NODE ID: a buffer's compiled
     expression only ever reaches strictly smaller node ids, so the id is the
     rank along which saturation is proved (the target cycle is NOT a valid
     rank — [require_buffer] also buffers same-cycle nodes). *)
  Definition buffers_settled
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (ss: sched_sys_state) (input: input_t) (bound: nat) : Prop :=
    forall n_idx,
      vreg_nid a_idx n_idx < bound ->
      (fst ss).[tf_dfg_b a_idx n_idx]
      = eval_st (tf_dfg_b a_idx n_idx)
          (node_ref_expr act a_idx (vreg_nid a_idx n_idx)) ss input.

  (* SUBSTITUTION (2b).  Once every buffer register holds its settled value,
     compiling a node WITH buffers evaluates exactly like compiling it
     buffer-free: each buffered leaf reads a register that, by hypothesis,
     already equals the inlined expression it replaced.

     SIZE DISCIPLINE.  The only hypothesis needed on the demanded size is
     [szB = sz node]: every operand slot of a compiled expression demands its
     argument at that argument's OWN declared size — [tf_not]/binary/Phi via
     [wfg_build_dfg], [tf_cmp szC] via the operator's own width (which [wfg]
     also pins on the args), and [DFG_Resize] definitionally (the compiler emits
     [tf_resize (sz arg_node)]).  At a buffered leaf the register width matches
     by [buffer_register_node_size], so the [convert] cast is the identity.

     BOUND DISCIPLINE.  Settledness is only assumed for buffers caching a node
     id below [bound].  The recursion descends to strictly smaller ids, so a
     child of a node [n <= bound] satisfies [x < bound]; the TOP-level caller
     (compiling buffer [n] itself, whose entry [compile_dfg_buffers] removed
     from the slot) instead supplies the left disjunct [list_assoc bufs n = None]
     and therefore need not assume that [n]'s own register is already settled. *)
  Lemma compile_subst
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
        (ss: sched_sys_state) (input: input_t) :
    act_idx_aligned act a_idx ->
    forall bound,
    buffers_settled act a_idx ss input bound ->
    forall bufs,
      (forall e, In e bufs ->
         In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
      forall fuel n szB,
        1 <= n ->
        n < length (graph (build_dfg ctx act)) ->
        n < fuel ->
        n <= bound ->
        (BitsToLists.list_assoc bufs n = None \/ n < bound) ->
        szB = sz (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}) ->
        tf_eval_expr ss_sz i_sz oo_sz (szB := szB)
          (fst (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act) n bufs))
          ss input
        = tf_eval_expr ss_sz i_sz oo_sz (szB := szB)
          (fst (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act) n []))
          ss input.
  Proof.
    intros Halign bound Hsettled bufs Hsub fuel.
    induction fuel as [| fuel IH];
      intros n szB Hn1 Hnlen Hnfuel Hnb Hself HszB; [ lia | ].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:Hla.
    - (* buffered leaf: the register already holds the inlined value *)
      assert (Hnlt : n < bound)
        by (destruct Hself as [Hnone | Hlt']; [ congruence | exact Hlt' ]).
      (* canonicalize the buffer-free side to node_ref_expr's fuel *)
      rewrite (compile_fuel_irrel act a_idx [] n Hn1 Hnlen (S fuel)
                 (length (graph (build_dfg ctx act))) Hnfuel Hnlen).
      cbn [compile_dfg_expr]. rewrite Hla. cbv beta iota.
      assert (Hin_slot : In (n, (m, msz))
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))
        by (apply Hsub, wla_in, Hla).
      assert (Hin_gsi : In (n, (m, msz))
                (get_sizes_and_idx ctx (build_dfg ctx act)
                   (require_buffer ctx (build_dfg ctx act)
                      (calc_target_cycle cost_limit
                         (calc_backward_cost ctx (build_dfg ctx act))))))
        by (rewrite <- (buffer_slot_eq act a_idx Halign); exact Hin_slot).
      assert (Hlt : m < length
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])).
      { rewrite (buffer_slot_eq act a_idx Halign), gsi_length.
        exact (gsi_idx_bound _ _ n m msz Hin_gsi). }
      destruct (index_of_nat_bounded Hlt) as [n_idx' Hn_idx'].
      rewrite Hn_idx'. cbv beta iota. cbn [fst].
      assert (Hmi : index_to_nat n_idx' = m)
        by (apply index_to_nat_of_nat; exact Hn_idx').
      assert (Hvn : vreg_nid a_idx n_idx' = n).
      { unfold vreg_nid. rewrite Hmi, (buffer_slot_eq act a_idx Halign).
        rewrite (gsi_entry_at _ _ n m msz Hin_gsi). reflexivity. }
      assert (Hsz : ss_sz (tf_dfg_b a_idx n_idx') = szB).
      { rewrite (buffer_register_node_size act a_idx n_idx' Halign), Hvn.
        symmetry; exact HszB. }
      assert (Hset := Hsettled n_idx' ltac:(rewrite Hvn; exact Hnlt)).
      rewrite <- Hsz, eval_svar_same, Hset, Hvn.
      unfold node_ref_expr. reflexivity.
    - (* not buffered: both sides take the same op branch *)
      cbn [compile_dfg_expr BitsToLists.list_assoc].
      rewrite Hla. cbv beta iota.
      set (node := nth n (graph (build_dfg ctx act))
                     {| nid := 0; op := DFG_Empty; sz := 0 |}) in *.
      subst szB.
      assert (Hnode_in : In node (graph (build_dfg ctx act)))
        by (unfold node; apply nth_In; exact Hnlen).
      pose proof (build_dfg_args_pos act) as [_ [Hargpos _]].
      pose proof (node_nid_at act n Hnlen) as Hnid. fold node in Hnid.
      assert (Harg : forall x, In x (get_args ctx node) -> 1 <= x /\ x < n).
      { intros x Hx. split.
        - exact (Hargpos node Hnode_in x Hx).
        - pose proof (args_lt_fwd act node) as Hlt2.
          specialize (Hlt2 Hnode_in x Hx). rewrite Hnid in Hlt2. exact Hlt2. }
      (* recursion at a child, demanded at a size pinned by [wsz] *)
      assert (Hchild : forall x sx, In x (get_args ctx node) ->
                wsz (build_dfg ctx act) x sx ->
                tf_eval_expr ss_sz i_sz oo_sz (szB := sx)
                  (fst (compile_dfg_expr ctx cost_limit fuel a_idx
                          (build_dfg ctx act) x bufs)) ss input
                = tf_eval_expr ss_sz i_sz oo_sz (szB := sx)
                  (fst (compile_dfg_expr ctx cost_limit fuel a_idx
                          (build_dfg ctx act) x [])) ss input).
      { intros x sx Hx Hwsz.
        destruct (Harg x Hx) as [Hx1 Hx2].
        destruct (wsz_node_sz act x sx Hwsz) as [Hxlen Hxsz].
        apply (IH x sx Hx1 Hxlen);
          [ lia | lia | right; lia | symmetry; exact Hxsz ]. }
      pose proof (wfg_build_dfg act node Hnode_in) as Hfg.
      destruct (op node) as [c | v | v | op1 arg | op1 arg1 arg2 | arg | cnd tid eid | ]
        eqn:Hop.
      + (* Const *) reflexivity.
      + (* Input *) reflexivity.
      + (* Var *) destruct v; reflexivity.
      + (* Unary *)
        assert (Hain : In arg (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    arg bufs) as [ae ve] eqn:E1.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    arg []) as [ae' ve'] eqn:E2.
        cbn [fst].
        unfold node_args_sz in Hfg. rewrite Hop in Hfg.
        destruct op1 as [| src].
        * (* tf_not: child demanded at the node's own size *)
          pose proof (Hchild arg (sz node) Hain Hfg) as Hc.
          rewrite E1, E2 in Hc. cbn [fst] in Hc.
          cbn [tf_eval_expr]. rewrite Hc. reflexivity.
        * (* tf_resize src: child demanded at [src], which [wfg] pins *)
          pose proof (Hchild arg src Hain Hfg) as Hc.
          rewrite E1, E2 in Hc. cbn [fst] in Hc.
          cbn [tf_eval_expr]. rewrite Hc. reflexivity.
      + (* Binary *)
        assert (Ha1in : In arg1 (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        assert (Ha2in : In arg2 (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; left; reflexivity).
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    arg1 bufs) as [a1e v1e] eqn:E1.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    arg2 bufs) as [a2e v2e] eqn:E2.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    arg1 []) as [a1e' v1e'] eqn:E3.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    arg2 []) as [a2e' v2e'] eqn:E4.
        cbn [fst].
        unfold node_args_sz in Hfg. rewrite Hop in Hfg.
        destruct op1 as [ | | | | | | szC cop ];
          [ destruct Hfg as [Hf1 Hf2];
            pose proof (Hchild arg1 (sz node) Ha1in Hf1) as Hc1;
            pose proof (Hchild arg2 (sz node) Ha2in Hf2) as Hc2;
            rewrite E1, E3 in Hc1; rewrite E2, E4 in Hc2;
            cbn [fst] in Hc1, Hc2;
            cbn [tf_eval_expr]; rewrite Hc1, Hc2; reflexivity .. | ].
        destruct Hfg as [Hf1 Hf2].
        pose proof (Hchild arg1 szC Ha1in Hf1) as Hc1.
        pose proof (Hchild arg2 szC Ha2in Hf2) as Hc2.
        rewrite E1, E3 in Hc1. rewrite E2, E4 in Hc2.
        cbn [fst] in Hc1, Hc2.
        cbn [tf_eval_expr]. rewrite Hc1, Hc2. reflexivity.
      + (* Resize: the demanded size is the arg node's own size, definitionally *)
        assert (Hain : In arg (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    arg bufs) as [ae ve] eqn:E1.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    arg []) as [ae' ve'] eqn:E2.
        cbn [fst].
        destruct (Harg arg Hain) as [Hx1 Hx2].
        assert (Hself' : BitsToLists.list_assoc bufs arg = None \/ arg < bound)
          by (right; lia).
        pose proof (IH arg (sz (nth arg (graph (build_dfg ctx act))
                                  {| nid := 0; op := DFG_Empty; sz := 0 |}))
                      Hx1 (Nat.lt_trans _ _ _ Hx2 Hnlen)
                      ltac:(lia) ltac:(lia) Hself' eq_refl) as Hc.
        rewrite E1, E2 in Hc. cbn [fst] in Hc.
        cbn [tf_eval_expr]. rewrite Hc. reflexivity.
      + (* Phi *)
        assert (Hcin : In cnd (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        assert (Htin : In tid (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; left; reflexivity).
        assert (Hein : In eid (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; right; left; reflexivity).
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    cnd bufs) as [ce cv] eqn:Ec.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    tid bufs) as [te tv] eqn:Et.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    eid bufs) as [ee ev] eqn:Ee.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    cnd []) as [ce' cv'] eqn:Ec'.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    tid []) as [te' tv'] eqn:Et'.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    eid []) as [ee' ev'] eqn:Ee'.
        cbn [fst].
        unfold node_args_sz in Hfg. rewrite Hop in Hfg.
        destruct Hfg as [Hf1 [Hf2 Hf3]].
        pose proof (Hchild cnd 1 Hcin Hf1) as Hcc.
        pose proof (Hchild tid (sz node) Htin Hf2) as Hct.
        pose proof (Hchild eid (sz node) Hein Hf3) as Hce.
        rewrite Ec, Ec' in Hcc. rewrite Et, Et' in Hct. rewrite Ee, Ee' in Hce.
        cbn [fst] in Hcc, Hct, Hce.
        cbn [tf_eval_expr]. rewrite Hcc, Hct, Hce. reflexivity.
      + (* Empty: impossible for a real node *)
        exfalso. apply (node_op_not_empty act n Hn1 Hnlen).
        unfold node in Hop. exact Hop.
  Qed.

  (* ==================================================================== *)
  (* Phase 3b: the VALID => SETTLED invariant.                            *)
  (*                                                                      *)
  (* Saturation by cycle count is the wrong tool for correctness: a done   *)
  (* cycle may fire EARLY (an untainted Phi validates as soon as the       *)
  (* runtime-selected branch is ready).  What actually holds of every      *)
  (* reachable state is that a buffer whose validity bit is set holds its  *)
  (* settled value -- and the done flag is exactly the conjunction of the  *)
  (* output nodes' validity bits.                                         *)
  (* ==================================================================== *)

  Definition valid_settled
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (ss: sched_sys_state) (input: input_t) : Prop :=
    forall n_idx,
      (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
      (fst ss).[tf_dfg_b a_idx n_idx]
      = eval_st (tf_dfg_b a_idx n_idx)
          (node_ref_expr act a_idx (vreg_nid a_idx n_idx)) ss input.

  Lemma ones1_neq_zero : Bits.ones 1 <> Bits.zero.
  Proof. apply (proj2 (bits1_nonzero_ones (Bits.ones 1))). reflexivity. Qed.

  Lemma bits1_and_split (a b: bits_t 1) :
    Bits.and a b = Bits.ones 1 -> a = Bits.ones 1 /\ b = Bits.ones 1.
  Proof.
    intro H.
    destruct (bits1_cases a) as [Ha | Ha]; destruct (bits1_cases b) as [Hb | Hb];
      subst; try (split; reflexivity); exfalso; vm_compute in H; discriminate.
  Qed.

  (* Converse of valid_if_eval: a valid_expr_if that fires tells us the
     SELECTED branch is valid (and if it collapsed to [tf_const 1], both
     branches were literally [tf_const 1], hence valid). *)
  Lemma valid_if_eval_inv
    (cond t e: @tf_expr (tfs_states sched) i_var o_var) (ss: sched_sys_state) (input: input_t) :
    eval1 (valid_expr_if ctx cost_limit cond t e) ss input = Bits.ones 1 ->
    (eval1 cond ss input <> Bits.zero -> eval1 t ss input = Bits.ones 1) /\
    (eval1 cond ss input = Bits.zero -> eval1 e ss input = Bits.ones 1).
  Proof.
    intro H.
    assert (Hcase: (t = tf_const 1 /\ e = tf_const 1)
                   \/ valid_expr_if ctx cost_limit cond t e = tf_expr_if cond t e).
    { unfold valid_expr_if.
      destruct t as [vt| | | | | |]; try (right; reflexivity).
      destruct vt as [|[|vt]]; try (right; reflexivity).
      destruct e as [ve| | | | | |]; try (right; reflexivity).
      destruct ve as [|[|ve]]; try (right; reflexivity).
      left; split; reflexivity. }
    destruct Hcase as [[Ht He] | Hc].
    - subst t e. split; intros _; apply eval1_const1.
    - rewrite Hc in H. cbn [tf_eval_expr] in H.
      destruct (beq_dec (eval1 cond ss input) Bits.zero) eqn:Hb.
      + apply beq_dec_iff in Hb.
        split; intro Hcz; [ contradiction | exact H ].
      + split; intro Hcz; [ exact H |].
        exfalso. rewrite Hcz, beq_dec_refl in Hb. discriminate.
  Qed.

  (* SUBSTITUTION, gated by VALIDITY.  Wherever a node's compiled validity
     expression fires, its compiled value expression agrees with the buffer-free
     one.  The recursion is justified by the validity conjunctions: a binary
     node's validity is the AND of its children's, and an untainted Phi's is
     [and cond (if cond then_valid else_valid)] -- which validates exactly the
     branch that [tf_expr_if] selects, so the unselected (possibly unsettled)
     branch is never read. *)
  Lemma compile_subst_valid
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
        (ss: sched_sys_state) (input: input_t) :
    act_idx_aligned act a_idx ->
    valid_settled act a_idx ss input ->
    forall bufs,
      (forall e, In e bufs ->
         In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
      forall fuel n szB,
        1 <= n ->
        n < length (graph (build_dfg ctx act)) ->
        n < fuel ->
        szB = sz (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}) ->
        eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                      n bufs)) ss input = Bits.ones 1 ->
        tf_eval_expr ss_sz i_sz oo_sz (szB := szB)
          (fst (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act) n bufs))
          ss input
        = tf_eval_expr ss_sz i_sz oo_sz (szB := szB)
          (fst (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act) n []))
          ss input.
  Proof.
    intros Halign Hinv bufs Hsub fuel.
    induction fuel as [| fuel IH];
      intros n szB Hn1 Hnlen Hnfuel HszB Hval; [ lia | ].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:Hla.
    - (* buffered leaf: its validity bit is the one that fired *)
      rewrite (compile_fuel_irrel act a_idx [] n Hn1 Hnlen (S fuel)
                 (length (graph (build_dfg ctx act))) Hnfuel Hnlen).
      cbn [compile_dfg_expr] in Hval |- *. rewrite Hla in Hval |- *.
      cbv beta iota in Hval |- *.
      assert (Hin_slot : In (n, (m, msz))
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))
        by (apply Hsub, wla_in, Hla).
      assert (Hin_gsi : In (n, (m, msz))
                (get_sizes_and_idx ctx (build_dfg ctx act)
                   (require_buffer ctx (build_dfg ctx act)
                      (calc_target_cycle cost_limit
                         (calc_backward_cost ctx (build_dfg ctx act))))))
        by (rewrite <- (buffer_slot_eq act a_idx Halign); exact Hin_slot).
      assert (Hlt : m < length
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])).
      { rewrite (buffer_slot_eq act a_idx Halign), gsi_length.
        exact (gsi_idx_bound _ _ n m msz Hin_gsi). }
      destruct (index_of_nat_bounded Hlt) as [n_idx' Hn_idx'].
      rewrite Hn_idx' in Hval |- *. cbv beta iota in Hval |- *.
      cbn [fst]. cbn [snd] in Hval.
      assert (Hmi : index_to_nat n_idx' = m)
        by (apply index_to_nat_of_nat; exact Hn_idx').
      assert (Hvn : vreg_nid a_idx n_idx' = n).
      { unfold vreg_nid. rewrite Hmi, (buffer_slot_eq act a_idx Halign).
        rewrite (gsi_entry_at _ _ n m msz Hin_gsi). reflexivity. }
      assert (Hsz : ss_sz (tf_dfg_b a_idx n_idx') = szB).
      { rewrite (buffer_register_node_size act a_idx n_idx' Halign), Hvn.
        symmetry; exact HszB. }
      rewrite eval1_svar_v in Hval.
      assert (Hset := Hinv n_idx' Hval).
      rewrite <- Hsz, eval_svar_same, Hset, Hvn.
      unfold node_ref_expr. reflexivity.
    - (* not buffered: split the validity along the op's structure *)
      cbn [compile_dfg_expr BitsToLists.list_assoc] in Hval |- *.
      rewrite Hla in Hval |- *. cbv beta iota in Hval |- *.
      set (node := nth n (graph (build_dfg ctx act))
                     {| nid := 0; op := DFG_Empty; sz := 0 |}) in *.
      subst szB.
      assert (Hnode_in : In node (graph (build_dfg ctx act)))
        by (unfold node; apply nth_In; exact Hnlen).
      pose proof (build_dfg_args_pos act) as [_ [Hargpos _]].
      pose proof (node_nid_at act n Hnlen) as Hnid. fold node in Hnid.
      assert (Harg : forall x, In x (get_args ctx node) -> 1 <= x /\ x < n).
      { intros x Hx. split.
        - exact (Hargpos node Hnode_in x Hx).
        - pose proof (args_lt_fwd act node) as Hlt2.
          specialize (Hlt2 Hnode_in x Hx). rewrite Hnid in Hlt2. exact Hlt2. }
      assert (Hchild : forall x sx, In x (get_args ctx node) ->
                wsz (build_dfg ctx act) x sx ->
                eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx
                              (build_dfg ctx act) x bufs)) ss input = Bits.ones 1 ->
                tf_eval_expr ss_sz i_sz oo_sz (szB := sx)
                  (fst (compile_dfg_expr ctx cost_limit fuel a_idx
                          (build_dfg ctx act) x bufs)) ss input
                = tf_eval_expr ss_sz i_sz oo_sz (szB := sx)
                  (fst (compile_dfg_expr ctx cost_limit fuel a_idx
                          (build_dfg ctx act) x [])) ss input).
      { intros x sx Hx Hwsz Hxv.
        destruct (Harg x Hx) as [Hx1 Hx2].
        destruct (wsz_node_sz act x sx Hwsz) as [Hxlen Hxsz].
        apply (IH x sx Hx1 Hxlen ltac:(lia) (eq_sym Hxsz) Hxv). }
      pose proof (wfg_build_dfg act node Hnode_in) as Hfg.
      destruct (op node) as [c | v | v | op1 arg | op1 arg1 arg2 | arg | cnd tid eid | ]
        eqn:Hop.
      + (* Const *) reflexivity.
      + (* Input *) reflexivity.
      + (* Var *) destruct v; reflexivity.
      + (* Unary: validity passes through *)
        assert (Hain : In arg (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    arg bufs) as [ae ve] eqn:E1.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    arg []) as [ae' ve'] eqn:E2.
        cbn [fst]. cbn [snd] in Hval.
        unfold node_args_sz in Hfg. rewrite Hop in Hfg.
        assert (Hav : eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx
                                    (build_dfg ctx act) arg bufs)) ss input
                      = Bits.ones 1) by (rewrite E1; cbn [snd]; exact Hval).
        destruct op1 as [| src].
        * pose proof (Hchild arg (sz node) Hain Hfg Hav) as Hc.
          rewrite E1, E2 in Hc. cbn [fst] in Hc.
          cbn [tf_eval_expr]. rewrite Hc. reflexivity.
        * pose proof (Hchild arg src Hain Hfg Hav) as Hc.
          rewrite E1, E2 in Hc. cbn [fst] in Hc.
          cbn [tf_eval_expr]. rewrite Hc. reflexivity.
      + (* Binary: validity is the AND of the two children's *)
        assert (Ha1in : In arg1 (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        assert (Ha2in : In arg2 (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; left; reflexivity).
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    arg1 bufs) as [a1e v1e] eqn:E1.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    arg2 bufs) as [a2e v2e] eqn:E2.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    arg1 []) as [a1e' v1e'] eqn:E3.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    arg2 []) as [a2e' v2e'] eqn:E4.
        cbn [fst]. cbn [snd] in Hval.
        rewrite valid_and_eval in Hval.
        destruct (bits1_and_split _ _ Hval) as [Hv1 Hv2].
        assert (Hav1 : eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx
                                     (build_dfg ctx act) arg1 bufs)) ss input
                       = Bits.ones 1) by (rewrite E1; cbn [snd]; exact Hv1).
        assert (Hav2 : eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx
                                     (build_dfg ctx act) arg2 bufs)) ss input
                       = Bits.ones 1) by (rewrite E2; cbn [snd]; exact Hv2).
        unfold node_args_sz in Hfg. rewrite Hop in Hfg.
        destruct op1 as [ | | | | | | szC cop ];
          [ destruct Hfg as [Hf1 Hf2];
            pose proof (Hchild arg1 (sz node) Ha1in Hf1 Hav1) as Hc1;
            pose proof (Hchild arg2 (sz node) Ha2in Hf2 Hav2) as Hc2;
            rewrite E1, E3 in Hc1; rewrite E2, E4 in Hc2;
            cbn [fst] in Hc1, Hc2;
            cbn [tf_eval_expr]; rewrite Hc1, Hc2; reflexivity .. | ].
        destruct Hfg as [Hf1 Hf2].
        pose proof (Hchild arg1 szC Ha1in Hf1 Hav1) as Hc1.
        pose proof (Hchild arg2 szC Ha2in Hf2 Hav2) as Hc2.
        rewrite E1, E3 in Hc1. rewrite E2, E4 in Hc2.
        cbn [fst] in Hc1, Hc2.
        cbn [tf_eval_expr]. rewrite Hc1, Hc2. reflexivity.
      + (* Resize: validity passes through *)
        assert (Hain : In arg (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    arg bufs) as [ae ve] eqn:E1.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    arg []) as [ae' ve'] eqn:E2.
        cbn [fst]. cbn [snd] in Hval.
        destruct (Harg arg Hain) as [Hx1 Hx2].
        assert (Hav : eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx
                                    (build_dfg ctx act) arg bufs)) ss input
                      = Bits.ones 1) by (rewrite E1; cbn [snd]; exact Hval).
        pose proof (IH arg (sz (nth arg (graph (build_dfg ctx act))
                                  {| nid := 0; op := DFG_Empty; sz := 0 |}))
                      Hx1 (Nat.lt_trans _ _ _ Hx2 Hnlen)
                      ltac:(lia) eq_refl Hav) as Hc.
        rewrite E1, E2 in Hc. cbn [fst] in Hc.
        cbn [tf_eval_expr]. rewrite Hc. reflexivity.
      + (* Phi: the validity fires only for the branch the value selects *)
        assert (Hcin : In cnd (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        assert (Htin : In tid (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; left; reflexivity).
        assert (Hein : In eid (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; right; left; reflexivity).
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    cnd bufs) as [ce cv] eqn:Ec.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    tid bufs) as [te tv] eqn:Et.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    eid bufs) as [ee ev] eqn:Ee.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    cnd []) as [ce' cv'] eqn:Ec'.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    tid []) as [te' tv'] eqn:Et'.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    eid []) as [ee' ev'] eqn:Ee'.
        cbn [fst]. cbn [snd] in Hval.
        unfold node_args_sz in Hfg. rewrite Hop in Hfg.
        destruct Hfg as [Hf1 [Hf2 Hf3]].
        destruct (mem cnd (get_tainted ctx (build_dfg ctx act))).
        * (* tainted: all three children are valid *)
          rewrite valid_and_eval, valid_and_eval in Hval.
          destruct (bits1_and_split _ _ Hval) as [Hte Hcv].
          destruct (bits1_and_split _ _ Hte) as [Htv Hev].
          assert (Hac : eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx
                                      (build_dfg ctx act) cnd bufs)) ss input
                        = Bits.ones 1) by (rewrite Ec; cbn [snd]; exact Hcv).
          assert (Hat : eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx
                                      (build_dfg ctx act) tid bufs)) ss input
                        = Bits.ones 1) by (rewrite Et; cbn [snd]; exact Htv).
          assert (Hae : eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx
                                      (build_dfg ctx act) eid bufs)) ss input
                        = Bits.ones 1) by (rewrite Ee; cbn [snd]; exact Hev).
          pose proof (Hchild cnd 1 Hcin Hf1 Hac) as Hcc.
          pose proof (Hchild tid (sz node) Htin Hf2 Hat) as Hct.
          pose proof (Hchild eid (sz node) Hein Hf3 Hae) as Hce.
          rewrite Ec, Ec' in Hcc. rewrite Et, Et' in Hct. rewrite Ee, Ee' in Hce.
          cbn [fst] in Hcc, Hct, Hce.
          cbn [tf_eval_expr]. rewrite Hcc, Hct, Hce. reflexivity.
        * (* untainted: only the selected branch is known valid *)
          rewrite valid_and_eval in Hval.
          destruct (bits1_and_split _ _ Hval) as [Hcv Hif].
          assert (Hac : eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx
                                      (build_dfg ctx act) cnd bufs)) ss input
                        = Bits.ones 1) by (rewrite Ec; cbn [snd]; exact Hcv).
          pose proof (Hchild cnd 1 Hcin Hf1 Hac) as Hcc.
          rewrite Ec, Ec' in Hcc. cbn [fst] in Hcc.
          destruct (valid_if_eval_inv ce tv ev ss input Hif) as [Hthen Helse].
          cbn [tf_eval_expr]. rewrite Hcc.
          destruct (beq_dec (eval1 ce' ss input) Bits.zero) eqn:Hb.
          -- apply beq_dec_iff in Hb.
             assert (Hcz : eval1 ce ss input = Bits.zero) by (rewrite Hcc; exact Hb).
             assert (Hae : eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx
                                         (build_dfg ctx act) eid bufs)) ss input
                           = Bits.ones 1)
               by (rewrite Ee; cbn [snd]; exact (Helse Hcz)).
             pose proof (Hchild eid (sz node) Hein Hf3 Hae) as Hce.
             rewrite Ee, Ee' in Hce. cbn [fst] in Hce. exact Hce.
          -- assert (Hcnz : eval1 ce ss input <> Bits.zero).
             { rewrite Hcc. intro Hz. rewrite Hz, beq_dec_refl in Hb. discriminate. }
             assert (Hat : eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx
                                         (build_dfg ctx act) tid bufs)) ss input
                           = Bits.ones 1)
               by (rewrite Et; cbn [snd]; exact (Hthen Hcnz)).
             pose proof (Hchild tid (sz node) Htin Hf2 Hat) as Hct.
             rewrite Et, Et' in Hct. cbn [fst] in Hct. exact Hct.
      + (* Empty: impossible for a real node *)
        exfalso. apply (node_op_not_empty act n Hn1 Hnlen).
        unfold node in Hop. exact Hop.
  Qed.

  (* A key filtered OUT of an association list is absent from it.  This is what
     lets a buffer's own compiled expression avoid depending on its own
     register: compile_dfg_buffers removes the entry before compiling it. *)
  Lemma list_assoc_filter_out (l: list (nat * (nat * nat))) (n: nat) :
    BitsToLists.list_assoc
      (filter (fun '(b_nid, _) => negb (Nat.eqb b_nid n)) l) n = None.
  Proof.
    induction l as [| [b x] l IH]; cbn [filter]; [ reflexivity | ].
    destruct (Nat.eqb b n) eqn:Hb; cbn [negb].
    - exact IH.
    - cbn [BitsToLists.list_assoc].
      destruct (eq_dec n b) as [He | Hne].
      + subst b. rewrite Nat.eqb_refl in Hb. discriminate.
      + exact IH.
  Qed.

  (* SETTLE BOUND.  Buffers are ranked by NODE ID, not by target cycle: a
     buffer's compiled expression only reaches strictly smaller ids
     (args_lt_fwd), so a buffer caching node [n] settles by cycle [n].  Note the
     target cycle is NOT a valid rank — require_buffer's out-part buffers every
     var_map output with a nonzero cycle, so a buffer can read another buffer at
     the SAME target cycle (see agents/scheduler-simulation for the
     counterexample), which is why the whole run is bounded by the graph size. *)
  Definition settle_bound (act: tfs_action sched) : nat :=
    length (graph (build_dfg ctx act)).

  (* ==================================================================== *)
  (* Phase 2/3 decomposition of the top-level theorem.                    *)
  (*                                                                      *)
  (* The monolithic correctness statement splits into two obligations:    *)
  (*  - PROGRESS (Phase 2): from start_rel, the scheduled run reaches a    *)
  (*    FIRST done cycle N; N is bounded by S (max target cycle), and is   *)
  (*    obtained as the LEAST cycle at which the done flag fires, so       *)
  (*    "not done before N" holds by construction (well-ordering).         *)
  (*  - CORRECTNESS-AT-DONE (Phase 3): at that done cycle the mapped final *)
  (*    states + outputs equal the one-shot source evaluation, because     *)
  (*    every buffer then holds the settled DFG value = tf_eval_expr of    *)
  (*    the source sub-expression under the fixed input.                   *)
  (*                                                                      *)
  (* NOTE (soundness): an earlier attempt characterized done exactly as    *)
  (* [done_set (run_n k) <-> max_cycle <= k].  That biconditional is FALSE *)
  (* for DFGs with non-secret conditionals: an untainted Phi's compiled    *)
  (* validity is a data-dependent [if cond then then_val else else_val]    *)
  (* (see compile_dfg_expr / valid_expr_if), so a Phi can validate EARLY   *)
  (* when the runtime-selected branch is ready, even though its static     *)
  (* node_cycle (backward cost / cost_limit, a MAX over both branches) is  *)
  (* later.  Hence the [validity set -> node_cycle <= k] direction fails.  *)
  (* We therefore keep only the SOUND one-directional fact                 *)
  (* [done_by_settle_bound] (all leaves are valid once every buffer has    *)
  (* saturated) and recover the "first done" witness by well-ordering,     *)
  (* which needs no sharp lower bound.                                     *)
  (*                                                                      *)
  (* NOTE (soundness, 2nd): the saturation bound is NOT [max_cycle].       *)
  (* [require_buffer] buffers cycle-crossing args AND every var_map output *)
  (* with a non-zero target cycle, and [compile_dfg_buffers] removes only  *)
  (* the buffer ITSELF from its slot, so a buffer may read same-cycle      *)
  (* buffers and the resulting chain can be deeper than [max_cycle].       *)
  (* Saturation is therefore ranked by NODE ID (args are strictly smaller, *)
  (* [args_lt_fwd]), giving the bound [settle_bound = |graph|].            *)
  (* ==================================================================== *)

  (* --- well-ordering: a decidable predicate true at some bound B has a
         least witness N <= B. --- *)

  Lemma bounded_dec (P: nat -> Prop) (dec: forall n, {P n} + {~ P n}) :
    forall B, {exists n, n <= B /\ P n} + {forall n, n <= B -> ~ P n}.
  Proof.
    induction B as [| B IH].
    - destruct (dec 0) as [H0 | H0].
      + left. exists 0. split; [ apply Nat.le_refl | exact H0 ].
      + right. intros n Hn. apply Nat.le_0_r in Hn. subst n. exact H0.
    - destruct IH as [Hex | Hno].
      + left. destruct Hex as [n [Hn HP]]. exists n. split; [ lia | exact HP ].
      + destruct (dec (S B)) as [Hs | Hs].
        * left. exists (S B). split; [ apply Nat.le_refl | exact Hs ].
        * right. intros n Hn. destruct (Nat.eq_dec n (S B)) as [-> | Hne].
          -- exact Hs.
          -- apply Hno. lia.
  Qed.

  Lemma least_witness (P: nat -> Prop) (dec: forall n, {P n} + {~ P n}) :
    forall B, (exists n, n <= B /\ P n) ->
      exists N, P N /\ (forall k, k < N -> ~ P k).
  Proof.
    induction B as [| B IH]; intros [n [Hn HP]].
    - apply Nat.le_0_r in Hn. subst n. exists 0. split; [ exact HP | intros k Hk; lia ].
    - destruct (bounded_dec P dec B) as [Hex | Hno].
      + apply IH. exact Hex.
      + (* nothing true in [0,B], so the least witness is the boundary *)
        exists (S B). split.
        * (* n <= S B and ~ P m for m <= B forces n = S B *)
          destruct (Nat.eq_dec n (S B)) as [-> | Hne].
          -- exact HP.
          -- exfalso. apply (Hno n); [ lia | exact HP ].
        * intros k Hk. apply Hno. lia.
  Qed.

  (* done_set is decidable (a size-1 register is zero or all-ones). *)
  Lemma done_set_dec (ss: sched_sys_state) : {done_set ss} + {~ done_set ss}.
  Proof.
    unfold done_set.
    destruct (eq_dec ((fst ss).[tfs_done_signal sched]) Bits.zero) as [H | H].
    - right. intro Hc. apply Hc. exact H.
    - left. exact H.
  Qed.

  (* --- pure list lemma: every node's target cycle is <= max_cycle. --- *)

  Lemma fold_max_ge_start (l: list (nat * nat)) :
    forall acc, acc <= fold_left (fun m p => Nat.max m (snd p)) l acc.
  Proof.
    induction l as [| p l IH]; intro acc; cbn [fold_left].
    - apply Nat.le_refl.
    - eapply Nat.le_trans; [ apply Nat.le_max_l | apply IH ].
  Qed.

  Lemma fold_max_ge_elem (l: list (nat * nat)) :
    forall acc n c, In (n, c) l -> c <= fold_left (fun m p => Nat.max m (snd p)) l acc.
  Proof.
    induction l as [| p l IH]; intros acc n c Hin; cbn [fold_left].
    - destruct Hin.
    - destruct Hin as [Heq | Hin].
      + subst p. cbn [snd].
        eapply Nat.le_trans; [ apply Nat.le_max_r | apply fold_max_ge_start ].
      + eapply IH; exact Hin.
  Qed.

  Lemma node_cycle_le_max_cycle (act: tfs_action sched) (n: nat) :
    node_cycle act n <= max_cycle act.
  Proof.
    unfold node_cycle, max_cycle.
    destruct (BitsToLists.list_assoc
                (calc_target_cycle cost_limit (calc_backward_cost ctx (build_dfg ctx act))) n)
      as [c |] eqn:Hc.
    - apply wla_in in Hc. eapply fold_max_ge_elem; exact Hc.
    - apply Nat.le_0_l.
  Qed.

  (* Every action has an aligned index into buffer_needs (its finite_index,
     which is < length buffer_needs because buffer_needs maps over the finite
     action list). *)
  Lemma exists_act_idx (act: tfs_action sched) :
    exists a_idx, act_idx_aligned act a_idx.
  Proof.
    assert (Hlt : @finite_index _ (tfs_action_fin sched) act
                  < length (buffer_needs ctx cost_limit)).
    { pose proof (@finite_surjective _ (tfs_action_fin sched) act) as Hs.
      assert (Hne : nth_error (@finite_elements _ (tfs_action_fin sched))
                      (@finite_index _ (tfs_action_fin sched) act) <> None)
        by (rewrite Hs; discriminate).
      apply nth_error_Some in Hne.
      rewrite buffer_needs_eq, map_length. exact Hne. }
    destruct (index_of_nat_bounded Hlt) as [a_idx Hidx].
    exists a_idx. unfold act_idx_aligned.
    apply index_to_nat_of_nat. exact Hidx.
  Qed.

  (* GATEWAY: the compiled done signal is the tf_dfg_done assignment of the
     combined validity over EXACTLY the concrete per-output validity exprs
     (snd of compile_dfg_expr for each nodup var_map output nid), evaluated with
     the aligned action's DFG, full fuel, and its require_buffer slot list. *)
  Lemma done_exprs_concrete (act: tfs_action sched) a_idx :
    act_idx_aligned act a_idx ->
    exists rest,
      fst (Contract.tfs_schedule sched act)
      = tf_assign (tfs_done_signal sched)
          (combine_valid_exprs ctx cost_limit
             (map (fun nid =>
                     snd (compile_dfg_expr ctx cost_limit
                            (length (graph (build_dfg ctx act)))
                            a_idx (build_dfg ctx act) nid
                            (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])))
                  (nodup Nat.eq_dec (map snd (var_map (build_dfg ctx act))))))
        :: rest.
  Proof.
    intros Halign.
    (* alignment equation in the ctx-form the unfolded schedule exposes *)
    assert (Halign2 : @finite_index (tfs_spec_action ctx) (tfs_spec_action_fin ctx) act
                      = index_to_nat a_idx)
      by (unfold act_idx_aligned in Halign; exact (eq_sym Halign)).
    (* nth (finite_index act) dfgs default = build_dfg act *)
    assert (Hnth_dfg :
      nth (index_to_nat a_idx)
          (map (build_dfg ctx)
             (@finite_elements (tfs_spec_action ctx) (tfs_spec_action_fin ctx)))
          {| graph := []; var_map := [] |}
      = build_dfg ctx act).
    { rewrite <- Halign2.
      assert (Hne : nth_error
                      (map (build_dfg ctx)
                         (@finite_elements (tfs_spec_action ctx) (tfs_spec_action_fin ctx)))
                      (@finite_index (tfs_spec_action ctx) (tfs_spec_action_fin ctx) act)
                    = Some (build_dfg ctx act))
        by (apply map_nth_error,
              (@finite_surjective (tfs_spec_action ctx) (tfs_spec_action_fin ctx) act)).
      apply (nth_error_nth _ _ _ Hne). }
    unfold sched, tfs_schedule, Contract.tfs_schedule, tfs_done_signal, done_signal.
    unfold schedule. cbv zeta. cbn [fst].
    unfold compile_dfg_valid. cbv zeta.
    rewrite Halign2.
    rewrite index_of_nat_to_nat.
    rewrite Hnth_dfg.
    eexists. reflexivity.
  Qed.

  (* Structural exposure of the buffer-write tail of the always-ops list: after
     the done-flag head, the remaining ops are exactly compile_dfg_buffers over
     the aligned action's DFG (full fuel) and its require_buffer slot list. *)
  Lemma buffer_ops_concrete (act: tfs_action sched) a_idx :
    act_idx_aligned act a_idx ->
    exists done_e,
      fst (Contract.tfs_schedule sched act)
      = done_e ::
        compile_dfg_buffers ctx cost_limit (index_to_nat a_idx) (build_dfg ctx act)
          (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []).
  Proof.
    intros Halign.
    assert (Halign2 : @finite_index (tfs_spec_action ctx) (tfs_spec_action_fin ctx) act
                      = index_to_nat a_idx)
      by (unfold act_idx_aligned in Halign; exact (eq_sym Halign)).
    assert (Hnth_dfg :
      nth (index_to_nat a_idx)
          (map (build_dfg ctx)
             (@finite_elements (tfs_spec_action ctx) (tfs_spec_action_fin ctx)))
          {| graph := []; var_map := [] |}
      = build_dfg ctx act).
    { rewrite <- Halign2.
      assert (Hne : nth_error
                      (map (build_dfg ctx)
                         (@finite_elements (tfs_spec_action ctx) (tfs_spec_action_fin ctx)))
                      (@finite_index (tfs_spec_action ctx) (tfs_spec_action_fin ctx) act)
                    = Some (build_dfg ctx act))
        by (apply map_nth_error,
              (@finite_surjective (tfs_spec_action ctx) (tfs_spec_action_fin ctx) act)).
      apply (nth_error_nth _ _ _ Hne). }
    unfold sched, tfs_schedule, Contract.tfs_schedule.
    unfold schedule. cbv zeta. cbn [fst].
    rewrite Halign2.
    rewrite Hnth_dfg.
    eexists. reflexivity.
  Qed.

  (* On a pre-done cycle, each buffer pair reads exactly the expressions emitted
     for its entry by compile_dfg_buffers. *)
  Lemma buffer_after_cycle
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
        (n_idx : Vect.index
          (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])))
        (ss: sched_sys_state) (input: input_t) :
    act_idx_aligned act a_idx ->
    ~ done_set (sched_step act ss input) ->
    let buffers := nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [] in
    let entry := nth (index_to_nat n_idx) buffers (0, (0, 0)) in
    let n := fst entry in
    let buffers' := filter (fun '(b_nid, _) => negb (Nat.eqb b_nid n)) buffers in
    let compiled := compile_dfg_expr ctx cost_limit
                      (length (graph (build_dfg ctx act))) a_idx
                      (build_dfg ctx act) n buffers' in
    (fst (sched_step act ss input)).[tf_dfg_b a_idx n_idx]
      = eval_st (tf_dfg_b a_idx n_idx) (fst compiled) ss input
    /\
    (fst (sched_step act ss input)).[tf_dfg_v a_idx n_idx]
      = eval_st (tf_dfg_v a_idx n_idx) (snd compiled) ss input.
  Proof.
    intros Halign Hnd. cbv zeta.
    pose proof (compile_dfg_buffers_entry act a_idx n_idx Halign) as Hmem.
    cbv zeta in Hmem.
    match goal with
    | |- _ = eval_st _ (fst ?compiled) _ _ /\
           _ = eval_st _ (snd ?compiled) _ _ =>
        destruct compiled as [expr valid] eqn:Hcompiled
    end.
    destruct Hmem as [Hvalue Hvalid].
      unfold vreg_nid in Hvalue, Hvalid.
    cbn [fst snd] in Hvalue, Hvalid |- *.
    destruct (buffer_ops_concrete act a_idx Halign) as [done_e Hops].
    assert (Hnd_always : tfs_ops_no_duplicates
              (fst (Contract.tfs_schedule sched act))).
    { pose proof (tfs_schedule_no_duplicates sched act) as Hnd_all.
      unfold tfs_ops_no_duplicates in *. rewrite flat_map_app in Hnd_all.
      apply (NoDup_app_l _ _ Hnd_all). }
    assert (Hvalue_ops : In (tf_assign (tf_dfg_b a_idx n_idx) expr)
              (fst (Contract.tfs_schedule sched act))).
    { rewrite Hops. right. exact Hvalue. }
    assert (Hvalid_ops : In (tf_assign (tf_dfg_v a_idx n_idx) valid)
              (fst (Contract.tfs_schedule sched act))).
    { rewrite Hops. right. exact Hvalid. }
    split; rewrite sched_step_getst, (cycle_updates_not_done act ss input Hnd);
      unfold find_st_val.
    - rewrite (find_st_update_unique_assign _ _ _ _ _ Hnd_always Hvalue_ops).
      reflexivity.
    - rewrite (find_st_update_unique_assign _ _ _ _ _ Hnd_always Hvalid_ops).
      reflexivity.
  Qed.

  (* SATURATION (value).  After k cycles without a done flag, every buffer
     caching a node id BELOW k holds its settled (buffer-free) value.  Induction
     on k: the cycle recomputes the buffer from its slot minus itself, all the
     buffers it can read cache strictly smaller ids and are settled by the IH
     (compile_subst), and a pre-done cycle does not disturb the settled value
     itself (compile_nobuf_step_stable). *)
  Lemma buffers_settled_run :
    forall (act: tfs_action sched) a_idx (input: input_t)
           (ss0: sched_sys_state) (k: nat),
      act_idx_aligned act a_idx ->
      (forall i, 1 <= i <= k -> ~ done_set (run_n i act input ss0)) ->
      buffers_settled act a_idx (run_n k act input ss0) input k.
  Proof.
    intros act a_idx input ss0 k Halign.
    induction k as [| k IH]; intros Hnd n_idx Hlt; [ lia | ].
    assert (Hndk : forall i, 1 <= i <= k -> ~ done_set (run_n i act input ss0))
      by (intros i Hi; apply Hnd; lia).
    specialize (IH Hndk).
    set (ssk := run_n k act input ss0) in *.
    assert (Hstep : ~ done_set (sched_step act ssk input))
      by (apply (Hnd (S k)); lia).
    destruct (vreg_nid_node_range act a_idx n_idx Halign) as [Hn1 Hnlen].
    pose proof (buffer_after_cycle act a_idx n_idx ssk input Halign Hstep) as Hba.
    cbv zeta in Hba. destruct Hba as [Hval _].
    unfold vreg_nid in Hlt, Hn1, Hnlen.
    change (run_n (S k) act input ss0) with (sched_step act ssk input).
    unfold vreg_nid. rewrite Hval. unfold node_ref_expr.
    rewrite (compile_nobuf_step_stable act a_idx ssk input Hstep).
    apply (compile_subst act a_idx ssk input Halign k IH).
    - intros e He. exact (proj1 (proj1 (filter_In _ e _) He)).
    - exact Hn1.
    - exact Hnlen.
    - exact Hnlen.
    - lia.
    - left. apply list_assoc_filter_out.
    - apply buffer_register_node_size. exact Halign.
  Qed.

  (* VALIDITY substitution: if every buffer register caching an id below [bound]
     reads all-ones, then so does the compiled validity expression of any node
     at or below [bound].  Same rank discipline as compile_subst. *)
  Lemma compile_valid_ones
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
        (ss: sched_sys_state) (input: input_t) :
    act_idx_aligned act a_idx ->
    forall bound,
    (forall n_idx, vreg_nid a_idx n_idx < bound ->
       (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1) ->
    forall bufs,
      (forall e, In e bufs ->
         In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
      forall fuel n,
        1 <= n ->
        n < length (graph (build_dfg ctx act)) ->
        n < fuel ->
        n <= bound ->
        (BitsToLists.list_assoc bufs n = None \/ n < bound) ->
        eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                      n bufs)) ss input = Bits.ones 1.
  Proof.
    intros Halign bound Hvalid bufs Hsub fuel.
    induction fuel as [| fuel IH]; intros n Hn1 Hnlen Hnfuel Hnb Hself; [ lia | ].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:Hla.
    - (* buffered leaf: read the validity register, valid by hypothesis *)
      assert (Hnlt : n < bound)
        by (destruct Hself as [Hnone | Hlt']; [ congruence | exact Hlt' ]).
      cbn [compile_dfg_expr]. rewrite Hla. cbv beta iota.
      assert (Hin_slot : In (n, (m, msz))
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))
        by (apply Hsub, wla_in, Hla).
      assert (Hin_gsi : In (n, (m, msz))
                (get_sizes_and_idx ctx (build_dfg ctx act)
                   (require_buffer ctx (build_dfg ctx act)
                      (calc_target_cycle cost_limit
                         (calc_backward_cost ctx (build_dfg ctx act))))))
        by (rewrite <- (buffer_slot_eq act a_idx Halign); exact Hin_slot).
      assert (Hlt : m < length
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])).
      { rewrite (buffer_slot_eq act a_idx Halign), gsi_length.
        exact (gsi_idx_bound _ _ n m msz Hin_gsi). }
      destruct (index_of_nat_bounded Hlt) as [n_idx' Hn_idx'].
      rewrite Hn_idx'. cbv beta iota. cbn [snd].
      assert (Hmi : index_to_nat n_idx' = m)
        by (apply index_to_nat_of_nat; exact Hn_idx').
      assert (Hvn : vreg_nid a_idx n_idx' = n).
      { unfold vreg_nid. rewrite Hmi, (buffer_slot_eq act a_idx Halign).
        rewrite (gsi_entry_at _ _ n m msz Hin_gsi). reflexivity. }
      rewrite eval1_svar_v. apply Hvalid. rewrite Hvn. exact Hnlt.
    - (* not buffered: the validity is built from the args' validities *)
      cbn [compile_dfg_expr]. rewrite Hla. cbv beta iota.
      set (node := nth n (graph (build_dfg ctx act))
                     {| nid := 0; op := DFG_Empty; sz := 0 |}) in *.
      assert (Hnode_in : In node (graph (build_dfg ctx act)))
        by (unfold node; apply nth_In; exact Hnlen).
      pose proof (build_dfg_args_pos act) as [_ [Hargpos _]].
      pose proof (node_nid_at act n Hnlen) as Hnid. fold node in Hnid.
      assert (Harg : forall x, In x (get_args ctx node) -> 1 <= x /\ x < n).
      { intros x Hx. split.
        - exact (Hargpos node Hnode_in x Hx).
        - pose proof (args_lt_fwd act node) as Hlt2.
          specialize (Hlt2 Hnode_in x Hx). rewrite Hnid in Hlt2. exact Hlt2. }
      assert (Hchild : forall x, In x (get_args ctx node) ->
                eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx
                              (build_dfg ctx act) x bufs)) ss input = Bits.ones 1).
      { intros x Hx. destruct (Harg x Hx) as [Hx1 Hx2].
        apply (IH x Hx1 (Nat.lt_trans _ _ _ Hx2 Hnlen));
          [ lia | lia | right; lia ]. }
      destruct (op node) as [c | v | v | op1 arg | op1 arg1 arg2 | arg | cnd tid eid | ]
        eqn:Hop.
      + cbn [snd]. apply eval1_const1.
      + cbn [snd]. apply eval1_const1.
      + destruct v; cbn [snd]; apply eval1_const1.
      + assert (Hain : In arg (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        pose proof (Hchild arg Hain) as Ha.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    arg bufs) as [ae ve] eqn:E1.
        cbn [snd] in Ha |- *. exact Ha.
      + assert (Ha1in : In arg1 (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        assert (Ha2in : In arg2 (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; left; reflexivity).
        pose proof (Hchild arg1 Ha1in) as Hv1.
        pose proof (Hchild arg2 Ha2in) as Hv2.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    arg1 bufs) as [a1e v1e] eqn:E1.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    arg2 bufs) as [a2e v2e] eqn:E2.
        cbn [snd] in Hv1, Hv2 |- *.
        rewrite valid_and_eval, Hv1, Hv2. apply Bits.and_ones_l.
      + assert (Hain : In arg (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        pose proof (Hchild arg Hain) as Ha.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    arg bufs) as [ae ve] eqn:E1.
        cbn [snd] in Ha |- *. exact Ha.
      + assert (Hcin : In cnd (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        assert (Htin : In tid (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; left; reflexivity).
        assert (Hein : In eid (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; right; left; reflexivity).
        pose proof (Hchild cnd Hcin) as Hcv.
        pose proof (Hchild tid Htin) as Htv.
        pose proof (Hchild eid Hein) as Hev.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    cnd bufs) as [ce cv] eqn:Ec.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    tid bufs) as [te tv] eqn:Et.
        destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                    eid bufs) as [ee ev] eqn:Ee.
        cbn [snd] in Hcv, Htv, Hev |- *.
        destruct (mem cnd (get_tainted ctx (build_dfg ctx act))).
        * rewrite valid_and_eval, valid_and_eval, Htv, Hev, Hcv.
          rewrite Bits.and_ones_l. apply Bits.and_ones_l.
        * rewrite valid_and_eval, Hcv, Bits.and_ones_l.
          apply (valid_if_eval ce tv ev _ input Htv Hev).
      + exfalso. apply (node_op_not_empty act n Hn1 Hnlen).
        unfold node in Hop. exact Hop.
  Qed.

  (* SATURATION (validity).  After k pre-done cycles, every buffer caching a
     node id below k reads all-ones. *)
  Lemma valids_ones_run :
    forall (act: tfs_action sched) a_idx (input: input_t)
           (ss0: sched_sys_state) (k: nat),
      act_idx_aligned act a_idx ->
      (forall i, 1 <= i <= k -> ~ done_set (run_n i act input ss0)) ->
      forall n_idx,
        vreg_nid a_idx n_idx < k ->
        (fst (run_n k act input ss0)).[tf_dfg_v a_idx n_idx] = Bits.ones 1.
  Proof.
    intros act a_idx input ss0 k Halign.
    induction k as [| k IH]; intros Hnd n_idx Hlt; [ lia | ].
    assert (Hndk : forall i, 1 <= i <= k -> ~ done_set (run_n i act input ss0))
      by (intros i Hi; apply Hnd; lia).
    specialize (IH Hndk).
    set (ssk := run_n k act input ss0) in *.
    assert (Hstep : ~ done_set (sched_step act ssk input))
      by (apply (Hnd (S k)); lia).
    destruct (vreg_nid_node_range act a_idx n_idx Halign) as [Hn1 Hnlen].
    pose proof (buffer_after_cycle act a_idx n_idx ssk input Halign Hstep) as Hba.
    cbv zeta in Hba. destruct Hba as [_ Hval].
    unfold vreg_nid in Hlt, Hn1, Hnlen.
    change (run_n (S k) act input ss0) with (sched_step act ssk input).
    rewrite Hval.
    apply (compile_valid_ones act a_idx ssk input Halign k IH).
    - intros e He. exact (proj1 (proj1 (filter_In _ e _) He)).
    - exact Hn1.
    - exact Hnlen.
    - exact Hnlen.
    - lia.
    - left. apply list_assoc_filter_out.
  Qed.


  (* SOUND semantic core (Phase 2): a done cycle exists no later than
     S (settle_bound).  Either the done flag already fired at some cycle <=
     settle_bound (early done — harmless, yields an earlier witness), or it did
     not, in which case every buffer has settled and validated by cycle
     settle_bound (its node id is < settle_bound = the graph size), so the
     combined validity — hence the done flag — fires at S (settle_bound). *)
  Lemma done_by_settle_bound :
    forall (act: tfs_action sched) (sp0: src_sys_state)
           (ss0: sched_sys_state) (input: input_t),
      start_rel sp0 ss0 ->
      exists N, N <= S (settle_bound act) /\ done_set (run_n N act input ss0).
  Proof.
    intros act sp0 ss0 input Hstart.
    destruct (bounded_dec (fun k => done_set (run_n k act input ss0))
                (fun k => done_set_dec _) (settle_bound act)) as [Hearly | Hno].
    - destruct Hearly as [j [Hjle Hjdone]]. exists j. split; [ lia | exact Hjdone ].
    - exists (S (settle_bound act)). split; [ apply Nat.le_refl | ].
      destruct (exists_act_idx act) as [a_idx Halign].
      unfold done_set. cbn [run_n]. rewrite sched_step_done.
      destruct (done_exprs_concrete act a_idx Halign) as [rest Hsched].
      unfold find_st_val. rewrite Hsched.
      rewrite find_st_update_assign_head.
      (* eval_st done (combine ...) = eval1 (combine ...) since ss_sz done = 1 *)
      match goal with
      | |- context[eval_st ?d ?e ?s ?i] =>
          replace (eval_st d e s i) with (eval1 e s i) by reflexivity
      end.
      rewrite combine_valid_eval.
      rewrite bits1_nonzero_ones. apply fold_and_ones.
      intros b Hb.
      rewrite in_map_iff in Hb. destruct Hb as [e [Hbe He_in]]. subst b.
      rewrite in_map_iff in He_in. destruct He_in as [nd [He_nd Hnd_in]]. subst e.
      apply nodup_In in Hnd_in.
      (* nd is a var_map output nid: 1 <= nd and nd < length graph *)
      assert (Hnd1 : 1 <= nd).
      { rewrite in_map_iff in Hnd_in. destruct Hnd_in as [[k id] [Hsnd Hin]].
        cbn in Hsnd. subst id.
        pose proof (build_dfg_args_pos act) as [Hvm _]. exact (Hvm k nd Hin). }
      assert (Hndlt : nd < length (graph (build_dfg ctx act))).
      { destruct (var_map_snd_is_graph_nid act nd Hnd_in) as [node [Hin Hnid]].
        pose proof (build_dfg_nids act) as Hseq.
        assert (Hinm : In (nid node) (map nid (graph (build_dfg ctx act))))
          by (apply in_map; exact Hin).
        rewrite Hseq in Hinm. rewrite in_seq in Hinm. rewrite Hnid in Hinm. lia. }
      apply (compile_valid_ones act a_idx _ input Halign (settle_bound act)
               (valids_ones_run act a_idx input ss0 (settle_bound act) Halign
                  (fun i Hi => Hno i (proj2 Hi)))
               _ (fun e He => He)
               (length (graph (build_dfg ctx act))) nd Hnd1 Hndlt Hndlt);
        [ unfold settle_bound; lia | right; unfold settle_bound; lia ].
  Qed.

  (* PHASE 2 (progress): a FIRST done cycle exists.  Obtained as the least
     cycle N <= S (settle_bound act) at which the done flag fires (well-ordering
     over the decidable predicate [done_set (run_n k …)]), so "not done before
     N" holds by construction. *)
  Lemma scheduler_reaches_done :
    forall (act: tfs_action sched) (sp0: src_sys_state)
           (ss0: sched_sys_state) (input: input_t),
      start_rel sp0 ss0 ->
      exists N,
        (forall k, k < N -> ~ done_set (run_n k act input ss0)) /\
        done_set (run_n N act input ss0).
  Proof.
    intros act sp0 ss0 input Hstart.
    destruct (least_witness (fun k => done_set (run_n k act input ss0))
                (fun k => done_set_dec _) (S (settle_bound act)))
      as [N [Hdone Hbefore]].
    - apply (done_by_settle_bound act sp0 ss0 input Hstart).
    - exists N. split; [ exact Hbefore | exact Hdone ].
  Qed.

  (* ==================================================================== *)
  (* Phase 3a: what a DONE cycle writes.                                  *)
  (*                                                                      *)
  (* On the done cycle tfs_next_cycle takes the reset ++ done ++ always   *)
  (* branch.  Neither the reset updates nor the always-ops touch a base   *)
  (* state var or an output, so a tf_dfg_s / output register is resolved  *)
  (* by the DONE ops, i.e. by compile_dfg_aux over the action's var_map.  *)
  (* ==================================================================== *)

  Lemma cycle_updates_done (act: tfs_action sched) (ss: sched_sys_state) (input: input_t) :
    done_set (sched_step act ss input) ->
    cycle_updates act ss input
    = tfs_reset_updates sched (tfs_reset_states sched)
      ++ tfs_get_updates sched (snd (Contract.tfs_schedule sched act)) ss input
      ++ tfs_get_updates sched (fst (Contract.tfs_schedule sched act)) ss input.
  Proof.
    intro Hd. unfold done_set in Hd. rewrite sched_step_done in Hd.
    unfold cycle_updates. cbv zeta.
    destruct (beq_dec _ _) eqn:Hb; [| reflexivity ].
    exfalso. apply Hd. apply beq_dec_iff in Hb. exact Hb.
  Qed.

  (* --- find over an append whose SUFFIX has no match --- *)

  Lemma find_st_update_app_r_None x (ups1 ups2: list (tf_update ss_sz oo_sz)) :
    find_st_update sched x ups2 = None ->
    find_st_update sched x (ups1 ++ ups2) = find_st_update sched x ups1.
  Proof.
    induction ups1 as [| u ups1 IH]; intro Hnone; [ exact Hnone |].
    cbn [app]. destruct u as [| var val | var val]; cbn [find_st_update] in *.
    - apply IH, Hnone.
    - destruct (eq_dec var x); [ reflexivity | apply IH, Hnone ].
    - apply IH, Hnone.
  Qed.

  Lemma find_out_update_app_None x (ups1 ups2: list (tf_update ss_sz oo_sz)) :
    find_out_update sched x ups1 = None ->
    find_out_update sched x (ups1 ++ ups2) = find_out_update sched x ups2.
  Proof.
    induction ups1 as [| u ups1 IH]; intro Hnone; [ reflexivity |].
    cbn [app]. destruct u as [| var val | var val]; cbn [find_out_update] in *.
    - apply IH, Hnone.
    - apply IH, Hnone.
    - destruct (eq_dec var x); [ discriminate | apply IH, Hnone ].
  Qed.

  Lemma find_out_update_app_r_None x (ups1 ups2: list (tf_update ss_sz oo_sz)) :
    find_out_update sched x ups2 = None ->
    find_out_update sched x (ups1 ++ ups2) = find_out_update sched x ups1.
  Proof.
    induction ups1 as [| u ups1 IH]; intro Hnone; [ exact Hnone |].
    cbn [app]. destruct u as [| var val | var val]; cbn [find_out_update] in *.
    - apply IH, Hnone.
    - apply IH, Hnone.
    - destruct (eq_dec var x); [ reflexivity | apply IH, Hnone ].
  Qed.

  Lemma find_out_update_not_in_raw x (ups: list (tf_update ss_sz oo_sz)) :
    (forall u, In u ups -> forall val, u <> tf_out_update ss_sz oo_sz x val) ->
    find_out_update sched x ups = None.
  Proof.
    induction ups as [| u ups IH]; intro Hnone; [ reflexivity |].
    rewrite find_out_update_skip_cons.
    - apply IH. intros u' Hin. apply Hnone. now right.
    - intro val. eapply Hnone. now left.
  Qed.

  (* --- the reset updates touch neither base state vars nor outputs --- *)

  Lemma reset_states_not_svar (s: s_var) v :
    In v (reset_states ctx cost_limit) -> v <> tf_dfg_s s.
  Proof.
    unfold reset_states. rewrite in_flat_map.
    intros [a [_ Ha]].
    destruct (index_of_nat _ a) as [a' |]; [| destruct Ha].
    rewrite in_flat_map in Ha. destruct Ha as [n [_ Hn]].
    destruct (index_of_nat _ n) as [n' |]; [| destruct Hn].
    cbn [In] in Hn. destruct Hn as [Hn | [Hn | []]]; subst v; discriminate.
  Qed.

  Lemma reset_updates_no_svar (s: s_var) :
    find_st_update sched (tf_dfg_s s)
      (tfs_reset_updates sched (tfs_reset_states sched)) = None.
  Proof.
    assert (Hrs: tfs_reset_states sched = reset_states ctx cost_limit) by reflexivity.
    rewrite Hrs. unfold tfs_reset_updates.
    apply find_st_update_not_in_raw.
    intros u Hin val. rewrite in_map_iff in Hin.
    destruct Hin as [v [Hu Hv]]. subst u.
    intro Hcontra. inversion Hcontra as [Heq].
    apply (reset_states_not_svar s v Hv). exact Heq.
  Qed.

  Lemma reset_updates_no_out (o: o_var) :
    find_out_update sched o
      (tfs_reset_updates sched (tfs_reset_states sched)) = None.
  Proof.
    unfold tfs_reset_updates. apply find_out_update_not_in_raw.
    intros u Hin val. rewrite in_map_iff in Hin.
    destruct Hin as [v [Hu _]]. subst u. discriminate.
  Qed.

  (* --- uniqueness of the done-branch writes --- *)

  Lemma NoDup_app_r {A} (l1 l2: list A) : NoDup (l1 ++ l2) -> NoDup l2.
  Proof.
    induction l1 as [| a l1 IH]; intro Hnd; [ exact Hnd |].
    cbn [app] in Hnd. inversion Hnd; subst. apply IH. assumption.
  Qed.

  Lemma done_ops_no_dup (act: tfs_action sched) :
    tfs_ops_no_duplicates (snd (Contract.tfs_schedule sched act)).
  Proof.
    pose proof (tfs_schedule_no_duplicates sched act) as H.
    unfold tfs_ops_no_duplicates in *. rewrite flat_map_app in H.
    exact (NoDup_app_r _ _ H).
  Qed.

  Lemma find_out_update_unique_output x e ops ss input :
    tfs_ops_no_duplicates ops ->
    In (tf_output x e) ops ->
    find_out_update sched x (tfs_get_updates sched ops ss input)
    = Some (eval_out x e ss input).
  Proof.
    unfold tfs_ops_no_duplicates.
    induction ops as [| op ops IH]; intros Hnd Hin; [ destruct Hin |].
    cbn [flat_map] in Hnd.
    destruct Hin as [Heq | Hin].
    - subst op. apply find_out_update_output_head.
    - destruct op as [| dst rhs | dst rhs].
      + apply IH; [ exact Hnd | exact Hin ].
      + apply IH; [ cbn [app] in Hnd; inversion Hnd; assumption | exact Hin ].
      + inversion Hnd as [| tag tags Hnot Htail]; subst tag tags.
        destruct (eq_dec dst x) as [Hdx | Hdx].
        * subst dst. exfalso. apply Hnot. apply in_flat_map.
          exists (tf_output x e). split; [ exact Hin |]. cbn [In]. left. reflexivity.
        * rewrite find_out_update_skip_head.
          -- apply IH; [ exact Htail | exact Hin ].
          -- intros rhs' Heq. inversion Heq. contradiction.
  Qed.

  (* --- concrete shape of the done-branch op list --- *)

  Lemma final_ops_concrete (act: tfs_action sched) a_idx :
    act_idx_aligned act a_idx ->
    snd (Contract.tfs_schedule sched act)
    = map (fun '(var, n) =>
             let '(expr, _) := compile_dfg_expr ctx cost_limit
                    (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n
                    (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) in
             match var with
             | DFG_SVar sv => tf_assign (tf_dfg_s sv) expr
             | DFG_OVar ov => tf_output ov expr
             end)
          (var_map (build_dfg ctx act)).
  Proof.
    intros Halign.
    assert (Halign2 : @finite_index (tfs_spec_action ctx) (tfs_spec_action_fin ctx) act
                      = index_to_nat a_idx)
      by (unfold act_idx_aligned in Halign; exact (eq_sym Halign)).
    assert (Hnth_dfg :
      nth (index_to_nat a_idx)
          (map (build_dfg ctx)
             (@finite_elements (tfs_spec_action ctx) (tfs_spec_action_fin ctx)))
          {| graph := []; var_map := [] |}
      = build_dfg ctx act).
    { rewrite <- Halign2.
      assert (Hne : nth_error
                      (map (build_dfg ctx)
                         (@finite_elements (tfs_spec_action ctx) (tfs_spec_action_fin ctx)))
                      (@finite_index (tfs_spec_action ctx) (tfs_spec_action_fin ctx) act)
                    = Some (build_dfg ctx act))
        by (apply map_nth_error,
              (@finite_surjective (tfs_spec_action ctx) (tfs_spec_action_fin ctx) act)).
      apply (nth_error_nth _ _ _ Hne). }
    unfold sched, tfs_schedule, Contract.tfs_schedule. unfold schedule.
    cbv zeta. cbn [snd]. unfold compile_dfg_aux. cbv zeta.
    rewrite Halign2, index_of_nat_to_nat, Hnth_dfg. reflexivity.
  Qed.

  Local Notation act_slot a_idx :=
    (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []).

  (* The compiled expression the done branch writes for a var_map entry. *)
  Local Notation vm_expr act a_idx n :=
    (fst (compile_dfg_expr ctx cost_limit (length (graph (build_dfg ctx act)))
            a_idx (build_dfg ctx act) n
            (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))).

  Lemma final_ops_svar_in (act: tfs_action sched) a_idx (sv: s_var) (n: nat) :
    act_idx_aligned act a_idx ->
    In (DFG_SVar sv, n) (var_map (build_dfg ctx act)) ->
    In (tf_assign (tf_dfg_s sv) (vm_expr act a_idx n))
       (snd (Contract.tfs_schedule sched act)).
  Proof.
    intros Halign Hin. rewrite (final_ops_concrete act a_idx Halign).
    apply in_map_iff. exists (DFG_SVar sv, n). split; [| exact Hin ].
    destruct (compile_dfg_expr _ _ _ _ _ _ _) as [expr valid]. reflexivity.
  Qed.

  Lemma final_ops_ovar_in (act: tfs_action sched) a_idx (ov: o_var) (n: nat) :
    act_idx_aligned act a_idx ->
    In (DFG_OVar ov, n) (var_map (build_dfg ctx act)) ->
    In (tf_output ov (vm_expr act a_idx n))
       (snd (Contract.tfs_schedule sched act)).
  Proof.
    intros Halign Hin. rewrite (final_ops_concrete act a_idx Halign).
    apply in_map_iff. exists (DFG_OVar ov, n). split; [| exact Hin ].
    destruct (compile_dfg_expr _ _ _ _ _ _ _) as [expr valid]. reflexivity.
  Qed.

  (* A state var with no var_map entry is never assigned by the done branch. *)
  Lemma final_ops_no_svar (act: tfs_action sched) a_idx (sv: s_var) :
    act_idx_aligned act a_idx ->
    (forall n, ~ In (DFG_SVar sv, n) (var_map (build_dfg ctx act))) ->
    forall op, In op (snd (Contract.tfs_schedule sched act)) ->
               ~ op_assigns_st (tf_dfg_s sv) op.
  Proof.
    intros Halign Hno op Hin. rewrite (final_ops_concrete act a_idx Halign) in Hin.
    apply in_map_iff in Hin. destruct Hin as [[var n] [Hop Hvm]].
    destruct (compile_dfg_expr _ _ _ _ _ _ _) as [expr valid].
    destruct var as [sv' | ov]; subst op; intros [e He]; inversion He; subst.
    apply (Hno n). exact Hvm.
  Qed.

  Lemma final_ops_no_ovar (act: tfs_action sched) a_idx (ov: o_var) :
    act_idx_aligned act a_idx ->
    (forall n, ~ In (DFG_OVar ov, n) (var_map (build_dfg ctx act))) ->
    forall op, In op (snd (Contract.tfs_schedule sched act)) ->
               ~ op_writes_out ov op.
  Proof.
    intros Halign Hno op Hin. rewrite (final_ops_concrete act a_idx Halign) in Hin.
    apply in_map_iff in Hin. destruct Hin as [[var n] [Hop Hvm]].
    destruct (compile_dfg_expr _ _ _ _ _ _ _) as [expr valid].
    destruct var as [sv | ov']; subst op; intros [e He]; inversion He; subst.
    apply (Hno n). exact Hvm.
  Qed.

  (* --- READOUT: a done cycle commits the compiled var_map expressions --- *)

  Lemma sched_step_done_svar (act: tfs_action sched) a_idx (ss: sched_sys_state)
        (input: input_t) (sv: s_var) (n: nat) :
    act_idx_aligned act a_idx ->
    done_set (sched_step act ss input) ->
    In (DFG_SVar sv, n) (var_map (build_dfg ctx act)) ->
    (fst (sched_step act ss input)).[tf_dfg_s sv]
    = eval_st (tf_dfg_s sv) (vm_expr act a_idx n) ss input.
  Proof.
    intros Halign Hdone Hin.
    rewrite sched_step_getst, (cycle_updates_done act ss input Hdone).
    unfold find_st_val.
    rewrite (find_st_update_app_None _ _ _ (reset_updates_no_svar sv)).
    rewrite (find_st_update_app_r_None _ _ _
               (find_st_update_not_in (tf_dfg_s sv) _ ss input
                  (fun op Hop => always_ops_no_svar act sv op Hop))).
    rewrite (find_st_update_unique_assign _ _ _ ss input
               (done_ops_no_dup act) (final_ops_svar_in act a_idx sv n Halign Hin)).
    reflexivity.
  Qed.

  Lemma sched_step_done_ovar (act: tfs_action sched) a_idx (ss: sched_sys_state)
        (input: input_t) (ov: o_var) (n: nat) :
    act_idx_aligned act a_idx ->
    done_set (sched_step act ss input) ->
    In (DFG_OVar ov, n) (var_map (build_dfg ctx act)) ->
    (snd (sched_step act ss input)).[ov]
    = eval_out ov (vm_expr act a_idx n) ss input.
  Proof.
    intros Halign Hdone Hin.
    rewrite sched_step_getout, (cycle_updates_done act ss input Hdone).
    unfold find_out_val.
    rewrite (find_out_update_app_None _ _ _ (reset_updates_no_out ov)).
    rewrite (find_out_update_app_r_None _ _ _
               (find_out_update_not_in ov _ ss input
                  (fun op Hop => always_ops_no_out act ov op Hop))).
    rewrite (find_out_update_unique_output _ _ _ ss input
               (done_ops_no_dup act) (final_ops_ovar_in act a_idx ov n Halign Hin)).
    reflexivity.
  Qed.

  (* A state var / output the action never writes survives the done cycle. *)
  Lemma sched_step_done_svar_untouched (act: tfs_action sched) a_idx
        (ss: sched_sys_state) (input: input_t) (sv: s_var) :
    act_idx_aligned act a_idx ->
    done_set (sched_step act ss input) ->
    (forall n, ~ In (DFG_SVar sv, n) (var_map (build_dfg ctx act))) ->
    (fst (sched_step act ss input)).[tf_dfg_s sv] = (fst ss).[tf_dfg_s sv].
  Proof.
    intros Halign Hdone Hno.
    rewrite sched_step_getst, (cycle_updates_done act ss input Hdone).
    unfold find_st_val.
    rewrite (find_st_update_app_None _ _ _ (reset_updates_no_svar sv)).
    rewrite (find_st_update_app_r_None _ _ _
               (find_st_update_not_in (tf_dfg_s sv) _ ss input
                  (fun op Hop => always_ops_no_svar act sv op Hop))).
    rewrite (find_st_update_not_in (tf_dfg_s sv) _ ss input
               (final_ops_no_svar act a_idx sv Halign Hno)).
    reflexivity.
  Qed.

  Lemma sched_step_done_ovar_untouched (act: tfs_action sched) a_idx
        (ss: sched_sys_state) (input: input_t) (ov: o_var) :
    act_idx_aligned act a_idx ->
    done_set (sched_step act ss input) ->
    (forall n, ~ In (DFG_OVar ov, n) (var_map (build_dfg ctx act))) ->
    (snd (sched_step act ss input)).[ov] = (snd ss).[ov].
  Proof.
    intros Halign Hdone Hno.
    rewrite sched_step_getout, (cycle_updates_done act ss input Hdone).
    unfold find_out_val.
    rewrite (find_out_update_app_None _ _ _ (reset_updates_no_out ov)).
    rewrite (find_out_update_app_r_None _ _ _
               (find_out_update_not_in ov _ ss input
                  (fun op Hop => always_ops_no_out act ov op Hop))).
    rewrite (find_out_update_not_in ov _ ss input
               (final_ops_no_ovar act a_idx ov Halign Hno)).
    reflexivity.
  Qed.

  (* ---- The done cycle clears every validity register ---- *)

  Lemma find_st_update_app_Some x (ups1 ups2: list (tf_update ss_sz oo_sz)) v :
    find_st_update sched x ups1 = Some v ->
    find_st_update sched x (ups1 ++ ups2) = Some v.
  Proof.
    induction ups1 as [| u ups1 IH]; intro Hsome; cbn [app] in *.
    - discriminate.
    - destruct u as [| var val | var val]; cbn [find_st_update] in *.
      + apply IH, Hsome.
      + destruct (eq_dec var x) as [Heq | Hneq]; [ exact Hsome | apply IH, Hsome ].
      + apply IH, Hsome.
  Qed.

  Lemma find_st_update_map_init (l: list (tfs_states sched)) (x: tfs_states sched) :
    In x l ->
    (forall v, In v l -> tfs_states_init sched v = Bits.zero) ->
    find_st_update sched x
      (List.map (fun v => tf_st_update ss_sz oo_sz v (tfs_states_init sched v)) l)
    = Some Bits.zero.
  Proof.
    induction l as [| v l IH]; [ intros [] |].
    intros Hin Hz. cbn [List.map find_st_update].
    destruct (eq_dec v x) as [Heq | Hne].
    - destruct Heq. rewrite (Hz v (or_introl eq_refl)). reflexivity.
    - apply IH.
      + destruct Hin as [He | Hin]; [ congruence | exact Hin ].
      + intros w Hw. apply Hz. right; exact Hw.
  Qed.

  Lemma reset_states_has_v
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (n_idx : Vect.index
        (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))) :
    In (tf_dfg_v a_idx n_idx) (reset_states ctx cost_limit).
  Proof.
    unfold reset_states. rewrite in_flat_map.
    exists (index_to_nat a_idx). split.
    - apply in_seq. pose proof (index_to_nat_bounded a_idx). lia.
    - rewrite index_of_nat_to_nat, in_flat_map.
      exists (index_to_nat n_idx). split.
      + apply in_seq. pose proof (index_to_nat_bounded n_idx). lia.
      + rewrite index_of_nat_to_nat. right; left; reflexivity.
  Qed.

  Lemma reset_updates_v
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (n_idx : Vect.index
        (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))) :
    find_st_update sched (tf_dfg_v a_idx n_idx)
      (tfs_reset_updates sched (tfs_reset_states sched)) = Some Bits.zero.
  Proof.
    unfold tfs_reset_updates. apply find_st_update_map_init.
    - exact (reset_states_has_v a_idx n_idx).
    - intros v Hv. exact (tfs_reset_states_init_zero sched v Hv).
  Qed.

  (* A done cycle resets every validity bit, so the VALID => SETTLED invariant
     is vacuously re-established across it. *)
  Lemma sched_step_done_v (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (n_idx : Vect.index
        (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])))
      (ss: sched_sys_state) (input: input_t) :
    done_set (sched_step act ss input) ->
    (fst (sched_step act ss input)).[tf_dfg_v a_idx n_idx] = Bits.zero.
  Proof.
    intro Hdone.
    rewrite sched_step_getst, (cycle_updates_done act ss input Hdone).
    unfold find_st_val.
    rewrite (find_st_update_app_Some _ _ _ _ (reset_updates_v a_idx n_idx)).
    reflexivity.
  Qed.

  (* THE INVARIANT (Phase 3b).  At EVERY cycle of a run started from a state
     whose validity bits are clear, a buffer whose validity bit is set holds its
     settled (fully inlined, buffer-free) value.  Unlike the Phase-2 saturation
     lemmas this needs no "not yet done" hypothesis: a done cycle clears all the
     validity bits, so the invariant is re-established vacuously, and a pre-done
     cycle recomputes each buffer from an expression whose buffered leaves are
     exactly the ones its own validity conjunction demands. *)
  Lemma valid_settled_run :
    forall (act: tfs_action sched) a_idx (input: input_t)
           (ss0: sched_sys_state) (k: nat),
      act_idx_aligned act a_idx ->
      (forall n_idx, (fst ss0).[tf_dfg_v a_idx n_idx] = Bits.zero) ->
      valid_settled act a_idx (run_n k act input ss0) input.
  Proof.
    intros act a_idx input ss0 k Halign Hz0.
    induction k as [| k IH].
    - intros n_idx Hv. exfalso. cbn [run_n] in Hv.
      rewrite Hz0 in Hv. apply ones1_neq_zero. symmetry. exact Hv.
    - set (ssk := run_n k act input ss0) in *.
      change (run_n (S k) act input ss0) with (sched_step act ssk input).
      destruct (done_set_dec (sched_step act ssk input)) as [Hd | Hnd].
      + intros n_idx Hv. exfalso.
        rewrite (sched_step_done_v act a_idx n_idx ssk input Hd) in Hv.
        apply ones1_neq_zero. symmetry. exact Hv.
      + intros n_idx Hv.
        destruct (vreg_nid_node_range act a_idx n_idx Halign) as [Hn1 Hnlen].
        pose proof (buffer_after_cycle act a_idx n_idx ssk input Halign Hnd) as Hba.
        cbv zeta in Hba. destruct Hba as [Hvalue Hvalid].
        unfold vreg_nid in Hn1, Hnlen.
        rewrite Hvalid in Hv.
        unfold vreg_nid. rewrite Hvalue. unfold node_ref_expr.
        rewrite (compile_nobuf_step_stable act a_idx ssk input Hnd).
        apply (compile_subst_valid act a_idx ssk input Halign IH).
        * intros e He. exact (proj1 (proj1 (filter_In _ e _) He)).
        * exact Hn1.
        * exact Hnlen.
        * exact Hnlen.
        * apply buffer_register_node_size. exact Halign.
        * exact Hv.
  Qed.

  (* ==================================================================== *)
  (* Phase 3c: glue.                                                      *)
  (* ==================================================================== *)

  (* Reading the mapped-back state at a spec variable is reading its tf_dfg_s slot. *)
  Lemma getenv_maps_from (env: sched_st_env) (sv: s_var) :
    getenv ContextEnv (maps_from ctx cost_limit env) sv = env.[tf_dfg_s sv].
  Proof. unfold maps_from. rewrite getenv_create. reflexivity. Qed.

  (* Every var_map output nid is a real (positive) node of the forward graph. *)
  Lemma find_pair_dec {A B} (eqA: forall x y: A, {x = y} + {x <> y})
        (l: list (A * B)) (a: A) :
    {b | In (a, b) l} + {forall b, ~ In (a, b) l}.
  Proof.
    induction l as [| [a' b'] l IH].
    - right. intros b [].
    - destruct (eqA a' a) as [Heq | Hne].
      + left. exists b'. left. rewrite Heq. reflexivity.
      + destruct IH as [[b Hb] | Hno].
        * left. exists b. right. exact Hb.
        * right. intros b [Heq | Hin];
            [ inversion Heq; contradiction | exact (Hno b Hin) ].
  Qed.

  Lemma var_map_node_range (act: tfs_action sched) n :
    In n (map snd (var_map (build_dfg ctx act))) ->
    1 <= n /\ n < length (graph (build_dfg ctx act)).
  Proof.
    intro Hmem. split.
    - apply in_map_iff in Hmem. destruct Hmem as [[k id] [Hsnd Hkin]].
      cbn in Hsnd. subst id.
      pose proof (build_dfg_args_pos act) as [Hvm _]. exact (Hvm k n Hkin).
    - destruct (var_map_snd_is_graph_nid act n Hmem) as [node [Hnode Hnid]].
      rewrite <- Hnid.
      destruct (In_nth _ _ {| nid := 0; op := DFG_Empty; sz := 0 |} Hnode)
        as [p [Hp Hnth]].
      pose proof (node_nid_at act p Hp) as Hp_nid.
      rewrite Hnth in Hp_nid. rewrite Hp_nid. exact Hp.
  Qed.

  (* Size well-formedness of the exported var_map: the node a variable is bound
     to is recorded at the variable's own width. *)
  Lemma wvsz_build_dfg : forall (act: tfs_action sched), wvsz (build_dfg ctx act).
  Proof.
    intro act.
    assert (Hempty : winv {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |}).
    { split; [ | split ].
      - intros k id Hin. destruct Hin.
      - unfold nid_seq. reflexivity.
      - intros a Ha x Hx. simpl in Ha. destruct Ha as [<-|[]]. simpl in Hx. destruct Hx. }
    assert (Hemvsz : wvsz {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |}).
    { intros v id Hin. destruct Hin. }
    assert (Hemfg : wfg {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |}).
    { intros node Hin. simpl in Hin. destruct Hin as [<-|[]].
      unfold node_args_sz. cbn [op]. exact I. }
    unfold build_dfg.
    pose proof (dataflow_ops_fg (tfs_spec_action_ops ctx act)
                  {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |}
                  Hempty Hemvsz Hemfg) as Hop.
    destruct (dataflow_ops ctx (tfs_spec_action_ops ctx act)
                {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |})
      as [u final] eqn:Ed.
    destruct Hop as [_ [_ [Hvsz _]]].
    intros v id Hin. cbn [var_map] in Hin.
    destruct (Hvsz v id Hin) as [node [Hng [Hnn Hsz]]].
    exists node. cbn [graph]. rewrite <- in_rev.
    split; [ exact Hng | split; [ exact Hnn | exact Hsz ] ].
  Qed.

  Lemma var_map_entry_size (act: tfs_action sched) v n :
    In (v, n) (var_map (build_dfg ctx act)) ->
    sz (nth n (graph (build_dfg ctx act)) {| nid := 0; op := DFG_Empty; sz := 0 |})
    = dfg_var_size ctx v.
  Proof.
    intro Hin.
    exact (proj2 (wsz_node_sz act n _ (wvsz_build_dfg act v n Hin))).
  Qed.

  (* CONCRETE done characterization: if the done flag fires, then EVERY var_map
     output node's compiled validity expression evaluated ones on the pre-cycle
     state (the done signal is exactly their conjunction). *)
  Lemma sched_step_done_valid (act: tfs_action sched) a_idx
        (ss: sched_sys_state) (input: input_t) n :
    act_idx_aligned act a_idx ->
    done_set (sched_step act ss input) ->
    In n (map snd (var_map (build_dfg ctx act))) ->
    eval1 (snd (compile_dfg_expr ctx cost_limit
                  (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n
                  (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])))
          ss input = Bits.ones 1.
  Proof.
    intros Halign Hdone Hin.
    destruct (done_exprs_concrete act a_idx Halign) as [rest Heq].
    unfold done_set in Hdone. rewrite sched_step_done in Hdone.
    unfold find_st_val in Hdone. rewrite Heq in Hdone.
    rewrite find_st_update_assign_head, combine_valid_eval in Hdone.
    rewrite bits1_nonzero_ones, fold_and_ones in Hdone.
    apply Hdone, in_map_iff.
    eexists. split; [ reflexivity |].
    apply in_map_iff. exists n. split; [ reflexivity |].
    apply nodup_In. exact Hin.
  Qed.

  (* A run of pre-done cycles disturbs neither the base state nor the outputs. *)
  Lemma run_preserves_svar (act: tfs_action sched) (input: input_t)
        (ss0: sched_sys_state) (M: nat) :
    (forall i, 1 <= i <= M -> ~ done_set (run_n i act input ss0)) ->
    forall sv, (fst (run_n M act input ss0)).[tf_dfg_s sv] = (fst ss0).[tf_dfg_s sv].
  Proof.
    induction M as [| M IH]; intros Hnd sv; [ reflexivity |].
    assert (Hstep : ~ done_set (sched_step act (run_n M act input ss0) input))
      by (apply (Hnd (S M)); lia).
    change (run_n (S M) act input ss0)
      with (sched_step act (run_n M act input ss0) input).
    rewrite (sched_step_preserves_svar act _ input sv Hstep).
    apply IH. intros i Hi. apply Hnd. lia.
  Qed.

  Lemma run_preserves_ovar (act: tfs_action sched) (input: input_t)
        (ss0: sched_sys_state) (M: nat) :
    (forall i, 1 <= i <= M -> ~ done_set (run_n i act input ss0)) ->
    forall ov, (snd (run_n M act input ss0)).[ov] = (snd ss0).[ov].
  Proof.
    induction M as [| M IH]; intros Hnd ov; [ reflexivity |].
    assert (Hstep : ~ done_set (sched_step act (run_n M act input ss0) input))
      by (apply (Hnd (S M)); lia).
    change (run_n (S M) act input ss0)
      with (sched_step act (run_n M act input ss0) input).
    rewrite (sched_step_preserves_ovar act _ input ov Hstep).
    apply IH. intros i Hi. apply Hnd. lia.
  Qed.

  (* ==================================================================== *)
  (* PHASE 3d, STEP 1: syntactic equations for [node_ref_expr].            *)
  (* The buffer-free compiled expression of a forward-graph node is the    *)
  (* node's own op applied to the compiled expressions of its args.  These *)
  (* are the equations that turn "evaluate the compiled DFG" into a        *)
  (* structural recursion over the graph, mirroring [tf_eval_expr].        *)
  (* ==================================================================== *)

  (* A node of the exported forward graph sits at the position given by its own
     [nid] field.  This is the bridge from the builder's [In]-based
     monotonicity ([wgmono]) to the compiler's positional [nth] lookups. *)
  Lemma node_at_nid (act: tfs_action sched) node :
    In node (graph (build_dfg ctx act)) ->
    nid node < length (graph (build_dfg ctx act))
    /\ nth (nid node) (graph (build_dfg ctx act))
           {| nid := 0; op := DFG_Empty; sz := 0 |} = node.
  Proof.
    intro Hin.
    destruct (In_nth _ _ {| nid := 0; op := DFG_Empty; sz := 0 |} Hin) as [p [Hp Hnth]].
    pose proof (node_nid_at act p Hp) as Hnid. rewrite Hnth in Hnid.
    rewrite Hnid. split; [ exact Hp | exact Hnth ].
  Qed.

  (* Every arg of a real forward node is itself a real node with a strictly
     smaller id — the rank that every structural recursion below descends on. *)
  Lemma node_args_range (act: tfs_action sched) n :
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    forall x, In x (get_args ctx (nth n (graph (build_dfg ctx act))
                                    {| nid := 0; op := DFG_Empty; sz := 0 |})) ->
      1 <= x /\ x < n.
  Proof.
    intros H1 H2 x Hx.
    assert (Hin : In (nth n (graph (build_dfg ctx act))
                        {| nid := 0; op := DFG_Empty; sz := 0 |})
                     (graph (build_dfg ctx act))) by (apply nth_In; exact H2).
    pose proof (build_dfg_args_pos act) as [_ [Hargpos _]].
    split; [ exact (Hargpos _ Hin x Hx) | ].
    pose proof (args_lt_fwd act _ Hin x Hx) as Hlt.
    rewrite (node_nid_at act n H2) in Hlt. exact Hlt.
  Qed.

  (* Any fuel above the node's id computes [node_ref_expr]. *)
  Lemma nre_fuel (act: tfs_action sched) a_idx x f :
    1 <= x -> x < length (graph (build_dfg ctx act)) -> x < f ->
    fst (compile_dfg_expr ctx cost_limit f a_idx (build_dfg ctx act) x [])
    = node_ref_expr act a_idx x.
  Proof.
    intros H1 H2 H3. unfold node_ref_expr.
    rewrite (compile_fuel_irrel act a_idx [] x H1 H2 f
               (length (graph (build_dfg ctx act))) H3 H2).
    reflexivity.
  Qed.

  Lemma nre_unfold (act: tfs_action sched) a_idx n :
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    node_ref_expr act a_idx n
    = fst (compile_dfg_expr ctx cost_limit (S n) a_idx (build_dfg ctx act) n []).
  Proof.
    intros H1 H2. symmetry.
    apply (nre_fuel act a_idx n (S n) H1 H2 (Nat.lt_succ_diag_r n)).
  Qed.

  Lemma nre_const (act: tfs_action sched) a_idx n c :
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    op (nth n (graph (build_dfg ctx act))
          {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Const c ->
    node_ref_expr act a_idx n = tf_const c.
  Proof.
    intros H1 H2 Hop. rewrite (nre_unfold act a_idx n H1 H2).
    cbn [compile_dfg_expr BitsToLists.list_assoc]. rewrite Hop. reflexivity.
  Qed.

  Lemma nre_input (act: tfs_action sched) a_idx n v :
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    op (nth n (graph (build_dfg ctx act))
          {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Input v ->
    node_ref_expr act a_idx n = tf_ivar v.
  Proof.
    intros H1 H2 Hop. rewrite (nre_unfold act a_idx n H1 H2).
    cbn [compile_dfg_expr BitsToLists.list_assoc]. rewrite Hop. reflexivity.
  Qed.

  Lemma nre_svar (act: tfs_action sched) a_idx n sv :
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    op (nth n (graph (build_dfg ctx act))
          {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Var (DFG_SVar sv) ->
    node_ref_expr act a_idx n = tf_svar (tf_dfg_s sv).
  Proof.
    intros H1 H2 Hop. rewrite (nre_unfold act a_idx n H1 H2).
    cbn [compile_dfg_expr BitsToLists.list_assoc]. rewrite Hop. reflexivity.
  Qed.

  Lemma nre_ovar (act: tfs_action sched) a_idx n ov :
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    op (nth n (graph (build_dfg ctx act))
          {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Var (DFG_OVar ov) ->
    node_ref_expr act a_idx n = tf_ovar ov.
  Proof.
    intros H1 H2 Hop. rewrite (nre_unfold act a_idx n H1 H2).
    cbn [compile_dfg_expr BitsToLists.list_assoc]. rewrite Hop. reflexivity.
  Qed.

  Lemma nre_unary (act: tfs_action sched) a_idx n uop arg :
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    op (nth n (graph (build_dfg ctx act))
          {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Unary uop arg ->
    node_ref_expr act a_idx n = tf_op1 uop (node_ref_expr act a_idx arg).
  Proof.
    intros H1 H2 Hop.
    assert (Hain : In arg (get_args ctx (nth n (graph (build_dfg ctx act))
                                           {| nid := 0; op := DFG_Empty; sz := 0 |})))
      by (unfold get_args; rewrite Hop; left; reflexivity).
    destruct (node_args_range act n H1 H2 arg Hain) as [Ha1 Ha3].
    assert (Ha2 : arg < length (graph (build_dfg ctx act))) by lia.
    rewrite (nre_unfold act a_idx n H1 H2).
    cbn [compile_dfg_expr BitsToLists.list_assoc]. rewrite Hop.
    destruct (compile_dfg_expr ctx cost_limit n a_idx (build_dfg ctx act) arg [])
      as [ae av] eqn:E.
    cbn [fst]. f_equal.
    rewrite <- (nre_fuel act a_idx arg n Ha1 Ha2 Ha3), E. reflexivity.
  Qed.

  Lemma nre_resize (act: tfs_action sched) a_idx n arg :
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    op (nth n (graph (build_dfg ctx act))
          {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Resize arg ->
    node_ref_expr act a_idx n
    = tf_op1 (tf_resize (sz (nth arg (graph (build_dfg ctx act))
                               {| nid := 0; op := DFG_Empty; sz := 0 |})))
        (node_ref_expr act a_idx arg).
  Proof.
    intros H1 H2 Hop.
    assert (Hain : In arg (get_args ctx (nth n (graph (build_dfg ctx act))
                                           {| nid := 0; op := DFG_Empty; sz := 0 |})))
      by (unfold get_args; rewrite Hop; left; reflexivity).
    destruct (node_args_range act n H1 H2 arg Hain) as [Ha1 Ha3].
    assert (Ha2 : arg < length (graph (build_dfg ctx act))) by lia.
    rewrite (nre_unfold act a_idx n H1 H2).
    cbn [compile_dfg_expr BitsToLists.list_assoc]. rewrite Hop.
    destruct (compile_dfg_expr ctx cost_limit n a_idx (build_dfg ctx act) arg [])
      as [ae av] eqn:E.
    cbn [fst]. f_equal.
    rewrite <- (nre_fuel act a_idx arg n Ha1 Ha2 Ha3), E. reflexivity.
  Qed.

  Lemma nre_binary (act: tfs_action sched) a_idx n bop a1 a2 :
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    op (nth n (graph (build_dfg ctx act))
          {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Binary bop a1 a2 ->
    node_ref_expr act a_idx n
    = tf_op2 bop (node_ref_expr act a_idx a1) (node_ref_expr act a_idx a2).
  Proof.
    intros H1 H2 Hop.
    assert (Hin1 : In a1 (get_args ctx (nth n (graph (build_dfg ctx act))
                                          {| nid := 0; op := DFG_Empty; sz := 0 |})))
      by (unfold get_args; rewrite Hop; left; reflexivity).
    assert (Hin2 : In a2 (get_args ctx (nth n (graph (build_dfg ctx act))
                                          {| nid := 0; op := DFG_Empty; sz := 0 |})))
      by (unfold get_args; rewrite Hop; right; left; reflexivity).
    destruct (node_args_range act n H1 H2 a1 Hin1) as [Hp1 Hl1].
    destruct (node_args_range act n H1 H2 a2 Hin2) as [Hp2 Hl2].
    assert (Hb1 : a1 < length (graph (build_dfg ctx act))) by lia.
    assert (Hb2 : a2 < length (graph (build_dfg ctx act))) by lia.
    rewrite (nre_unfold act a_idx n H1 H2).
    cbn [compile_dfg_expr BitsToLists.list_assoc]. rewrite Hop.
    destruct (compile_dfg_expr ctx cost_limit n a_idx (build_dfg ctx act) a1 [])
      as [e1 v1] eqn:E1.
    destruct (compile_dfg_expr ctx cost_limit n a_idx (build_dfg ctx act) a2 [])
      as [e2 v2] eqn:E2.
    cbn [fst]. f_equal.
    - rewrite <- (nre_fuel act a_idx a1 n Hp1 Hb1 Hl1), E1. reflexivity.
    - rewrite <- (nre_fuel act a_idx a2 n Hp2 Hb2 Hl2), E2. reflexivity.
  Qed.

  Lemma nre_phi (act: tfs_action sched) a_idx n cnd tid eid :
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    op (nth n (graph (build_dfg ctx act))
          {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Phi cnd tid eid ->
    node_ref_expr act a_idx n
    = tf_expr_if (node_ref_expr act a_idx cnd)
        (node_ref_expr act a_idx tid) (node_ref_expr act a_idx eid).
  Proof.
    intros H1 H2 Hop.
    assert (Hinc : In cnd (get_args ctx (nth n (graph (build_dfg ctx act))
                                           {| nid := 0; op := DFG_Empty; sz := 0 |})))
      by (unfold get_args; rewrite Hop; left; reflexivity).
    assert (Hint : In tid (get_args ctx (nth n (graph (build_dfg ctx act))
                                           {| nid := 0; op := DFG_Empty; sz := 0 |})))
      by (unfold get_args; rewrite Hop; right; left; reflexivity).
    assert (Hine : In eid (get_args ctx (nth n (graph (build_dfg ctx act))
                                           {| nid := 0; op := DFG_Empty; sz := 0 |})))
      by (unfold get_args; rewrite Hop; right; right; left; reflexivity).
    destruct (node_args_range act n H1 H2 cnd Hinc) as [Hpc Hlc].
    destruct (node_args_range act n H1 H2 tid Hint) as [Hpt Hlt].
    destruct (node_args_range act n H1 H2 eid Hine) as [Hpe Hle].
    assert (Hbc : cnd < length (graph (build_dfg ctx act))) by lia.
    assert (Hbt : tid < length (graph (build_dfg ctx act))) by lia.
    assert (Hbe : eid < length (graph (build_dfg ctx act))) by lia.
    rewrite (nre_unfold act a_idx n H1 H2).
    cbn [compile_dfg_expr BitsToLists.list_assoc]. rewrite Hop.
    destruct (compile_dfg_expr ctx cost_limit n a_idx (build_dfg ctx act) cnd [])
      as [ec vc] eqn:Ec.
    destruct (compile_dfg_expr ctx cost_limit n a_idx (build_dfg ctx act) tid [])
      as [et vt] eqn:Et.
    destruct (compile_dfg_expr ctx cost_limit n a_idx (build_dfg ctx act) eid [])
      as [ee ve] eqn:Ee.
    cbn [fst]. f_equal.
    - rewrite <- (nre_fuel act a_idx cnd n Hpc Hbc Hlc), Ec. reflexivity.
    - rewrite <- (nre_fuel act a_idx tid n Hpt Hbt Hlt), Et. reflexivity.
    - rewrite <- (nre_fuel act a_idx eid n Hpe Hbe Hle), Ee. reflexivity.
  Qed.

  (* ==================================================================== *)
  (* PHASE 3d, STEP 2: the DENOTATION of a graph node, and the bridge from  *)
  (* a node EMITTED by the builder to its position in the exported graph.   *)
  (* ==================================================================== *)

  (* The buffer-free value of forward-graph node [n], demanded at width [szB],
     in scheduler state [ss].  This is what [dfg_action_semantics] talks about. *)
  Definition nval (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (ss: sched_sys_state) (input: input_t) (szB: nat) (n: nid_t) : bits_t szB :=
    tf_eval_expr ss_sz i_sz oo_sz (szB := szB) (node_ref_expr act a_idx n) ss input.

  (* [F] is a builder state whose graph exports to [act]'s forward graph. *)
  Definition exports (act: tfs_action sched) (F: wst) : Prop :=
    graph (build_dfg ctx act) = rev (graph F).

  Lemma in_graph_fwd (act: tfs_action sched) F node :
    exports act F -> In node (graph F) -> In node (graph (build_dfg ctx act)).
  Proof. intros HF Hin. rewrite HF. rewrite <- in_rev. exact Hin. Qed.

  Lemma gne_gmono (s s': wst) :
    wgmono s s' -> 0 < length (graph s) -> 0 < length (graph s').
  Proof.
    intros Hg Hne. destruct (graph s) as [|n0 rest] eqn:E; [ cbn in Hne; lia | ].
    assert (Hin : In n0 (graph s')) by (apply Hg; rewrite E; left; reflexivity).
    destruct (graph s'); [ destruct Hin | cbn; lia ].
  Qed.

  (* THE BRIDGE.  A node emitted by the builder sits, in the EXPORTED forward
     graph, at exactly the position given by the id [emit] returned, carrying
     its own op and size.  Every semantic case below goes through this. *)
  Lemma emitted_node_at (act: tfs_action sched) F (s s': wst) o size id :
    exports act F ->
    0 < length (graph s) ->
    emit ctx o size s = (id, s') ->
    wgmono s' F ->
    1 <= id
    /\ id < length (graph (build_dfg ctx act))
    /\ op (nth id (graph (build_dfg ctx act))
             {| nid := 0; op := DFG_Empty; sz := 0 |}) = o
    /\ sz (nth id (graph (build_dfg ctx act))
             {| nid := 0; op := DFG_Empty; sz := 0 |}) = size.
  Proof.
    intros HF Hne Hem Hg.
    rewrite emit_red in Hem. injection Hem as Hid Hs'.
    assert (Hin' : In {| nid := length (graph s); op := o; sz := size |} (graph s'))
      by (rewrite <- Hs'; cbn [graph]; left; reflexivity).
    pose proof (in_graph_fwd act F _ HF (Hg _ Hin')) as Hin.
    destruct (node_at_nid act _ Hin) as [Hlt Hnth].
    cbn [nid] in Hlt, Hnth.
    subst id.
    split; [ lia | split; [ exact Hlt | rewrite Hnth; split; reflexivity ] ].
  Qed.

  Lemma ensure_var_node_at (act: tfs_action sched) F (s s': wst) v id :
    exports act F ->
    0 < length (graph s) ->
    ensure_var ctx v s = (id, s') ->
    wgmono s' F ->
    1 <= id
    /\ id < length (graph (build_dfg ctx act))
    /\ op (nth id (graph (build_dfg ctx act))
             {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Var v.
  Proof.
    intros HF Hne Hev Hg.
    destruct (ensure_var_graph v s id s' Hev) as [Hgr Hid].
    assert (Hin' : In {| nid := length (graph s); op := DFG_Var v;
                         sz := dfg_var_size ctx v |} (graph s'))
      by (rewrite Hgr; left; reflexivity).
    pose proof (in_graph_fwd act F _ HF (Hg _ Hin')) as Hin.
    destruct (node_at_nid act _ Hin) as [Hlt Hnth].
    cbn [nid] in Hlt, Hnth.
    subst id.
    split; [ lia | split; [ exact Hlt | rewrite Hnth; reflexivity ] ].
  Qed.

  (* A freshly-ensured variable node reads the CURRENT scheduler register:
     its compiled expression is literally [tf_svar (tf_dfg_s sv)] / [tf_ovar ov]. *)
  Lemma nval_fresh_svar (act: tfs_action sched) a_idx (ss: sched_sys_state)
        (input: input_t) F (s s': wst) sv id :
    exports act F -> 0 < length (graph s) ->
    ensure_var ctx (DFG_SVar sv) s = (id, s') -> wgmono s' F ->
    nval act a_idx ss input (s_sz sv) id = (fst ss).[tf_dfg_s sv].
  Proof.
    intros HF Hne Hev Hg.
    destruct (ensure_var_node_at act F s s' (DFG_SVar sv) id HF Hne Hev Hg)
      as [H1 [H2 H3]].
    unfold nval. rewrite (nre_svar act a_idx id sv H1 H2 H3).
    exact (eval_svar_same (tf_dfg_s sv) ss input).
  Qed.

  Lemma nval_fresh_ovar (act: tfs_action sched) a_idx (ss: sched_sys_state)
        (input: input_t) F (s s': wst) ov id :
    exports act F -> 0 < length (graph s) ->
    ensure_var ctx (DFG_OVar ov) s = (id, s') -> wgmono s' F ->
    nval act a_idx ss input (o_sz ov) id = (snd ss).[ov].
  Proof.
    intros HF Hne Hev Hg.
    destruct (ensure_var_node_at act F s s' (DFG_OVar ov) id HF Hne Hev Hg)
      as [H1 [H2 H3]].
    unfold nval. rewrite (nre_ovar act a_idx id ov H1 H2 H3).
    cbn [tf_eval_expr]. exact (convert_same _).
  Qed.

  (* ==================================================================== *)
  (* PHASE 3d, STEP 3: the semantic invariant of the DFG builder.          *)
  (* Every [var_map] binding evaluates (buffer-free, in [ss]) to the value  *)
  (* the SOURCE state holds for that variable; and a variable with no       *)
  (* binding still holds its initial value.  The second half is the frame   *)
  (* condition that makes the [merge_maps] / [ensure_var] cases go through. *)
  (* ==================================================================== *)

  Local Notation dvar := (@dfg_vars_t s_var o_var).

  Lemma list_assoc_None_notin {K} `{EqDec K} {A} (l: list (K * A)) k :
    BitsToLists.list_assoc l k = None -> forall a, ~ In (k, a) l.
  Proof.
    induction l as [| [k0 a0] l IH]; cbn; intros Hla a Hin.
    - exact Hin.
    - destruct (eq_dec k k0) as [Heq | Hne].
      + discriminate Hla.
      + destruct Hin as [Heq2 | Hin].
        * injection Heq2 as Hk Ha. apply Hne. symmetry. exact Hk.
        * exact (IH Hla a Hin).
  Qed.

  (* var_map effects of the two updating steps, stated purely with [In] so that
     no [eq_dec] instance has to be written down in a statement (the instance
     Coq picks when ELABORATING a statement need not be syntactically the one
     baked into [ensure_var]'s body, which breaks [destruct]/[reflexivity]). *)
  Lemma ensure_var_vm_head (v: dvar) (s: wst) id s' :
    ensure_var ctx v s = (id, s') -> In (v, id) (var_map s').
  Proof.
    unfold ensure_var, emit, bind, get_state, put_state, ret. simpl.
    intro H. injection H as <- <-. cbn [var_map]. left. reflexivity.
  Qed.

  Lemma ensure_var_vm_keep (v: dvar) (s: wst) id s' v' n' :
    ensure_var ctx v s = (id, s') -> In (v', n') (var_map s) -> v' <> v ->
    In (v', n') (var_map s').
  Proof.
    unfold ensure_var, emit, bind, get_state, put_state, ret. simpl.
    intro H. injection H as <- <-. intros Hin Hnv. cbn [var_map]. right.
    apply filter_In. split; [ exact Hin | ]. cbv beta iota.
    match goal with |- (if ?X then _ else _) = true => destruct X as [Heq | Hne2] end.
    - exfalso. apply Hnv. exact Heq.
    - reflexivity.
  Qed.

  Lemma ensure_var_vm_inv (v: dvar) (s: wst) id s' v' n' :
    ensure_var ctx v s = (id, s') -> In (v', n') (var_map s') ->
    (v' = v /\ n' = id) \/ In (v', n') (var_map s).
  Proof.
    unfold ensure_var, emit, bind, get_state, put_state, ret. simpl.
    intro H. injection H as <- <-. cbn [var_map]. intro Hin.
    destruct Hin as [Heq | Hin].
    - left. injection Heq as Hk Hn. split; [ symmetry; exact Hk | symmetry; exact Hn ].
    - right. exact (proj1 (proj1 (filter_In _ _ _) Hin)).
  Qed.

  Lemma set_var_graph (v: dvar) (id: nid_t) (s: wst) :
    graph (snd (set_var ctx v id s)) = graph s.
  Proof. unfold set_var, bind, get_state, put_state. reflexivity. Qed.

  Lemma set_var_vm_head (v: dvar) (id: nid_t) (s: wst) :
    In (v, id) (var_map (snd (set_var ctx v id s))).
  Proof.
    unfold set_var, bind, get_state, put_state. cbn [snd var_map].
    left. reflexivity.
  Qed.

  Lemma set_var_vm_keep (v: dvar) (id: nid_t) (s: wst) v' n' :
    In (v', n') (var_map s) -> v' <> v ->
    In (v', n') (var_map (snd (set_var ctx v id s))).
  Proof.
    intros Hin Hnv. unfold set_var, bind, get_state, put_state. cbn [snd var_map].
    right. apply filter_In. split; [ exact Hin | ]. cbv beta iota.
    match goal with |- (if ?X then _ else _) = true => destruct X as [Heq | Hne2] end.
    - exfalso. apply Hnv. exact Heq.
    - reflexivity.
  Qed.

  Lemma set_var_vm_inv (v: dvar) (id: nid_t) (s: wst) v' n' :
    In (v', n') (var_map (snd (set_var ctx v id s))) ->
    (v' = v /\ n' = id) \/ In (v', n') (var_map s).
  Proof.
    unfold set_var, bind, get_state, put_state. cbn [snd var_map]. intro Hin.
    destruct Hin as [Heq | Hin].
    - left. injection Heq as Hk Hn. split; [ symmetry; exact Hk | symmetry; exact Hn ].
    - right. exact (proj1 (proj1 (filter_In _ _ _) Hin)).
  Qed.

  (* Sharper inversion: surviving entries are guaranteed to have a different key. *)
  Lemma set_var_vm_inv2 (v: dvar) (id: nid_t) (s: wst) v' n' :
    In (v', n') (var_map (snd (set_var ctx v id s))) ->
    (v' = v /\ n' = id) \/ (In (v', n') (var_map s) /\ v' <> v).
  Proof.
    unfold set_var, bind, get_state, put_state. cbn [snd var_map]. intro Hin.
    destruct Hin as [Heq | Hin].
    - left. injection Heq as Hk Hn. split; [ symmetry; exact Hk | symmetry; exact Hn ].
    - apply filter_In in Hin. destruct Hin as [Hin Hb]. cbv beta iota in Hb.
      right. split; [ exact Hin | ].
      intro He. subst v'.
      match type of Hb with
      | (if ?X then _ else _) = true => destruct X as [Heq2 | Hne2]
      end.
      + discriminate Hb.
      + apply Hne2. reflexivity.
  Qed.

  (* [get_var] either reuses an existing binding or creates one via ensure_var. *)
  Lemma get_var_cases (v: dvar) (s: wst) id s' :
    get_var ctx v s = (id, s') ->
    (In (v, id) (var_map s) /\ s' = s)
    \/ (ensure_var ctx v s = (id, s') /\ forall n, ~ In (v, n) (var_map s)).
  Proof.
    unfold get_var, bind, get_state.
    destruct (BitsToLists.list_assoc (var_map s) v) as [id0 |] eqn:E; intro H.
    - unfold ret in H. injection H as H1 H2. subst id0. subst s'.
      apply wla_in in E. left. split; [ exact E | reflexivity ].
    - right. split; [ exact H | intro n; exact (list_assoc_None_notin (var_map s) v E n) ].
  Qed.

  (* Book-keeping about [emit] that the semantic induction needs at every node. *)
  Lemma emit_vm (o: @dfg_op_t s_var i_var o_var) size (s: wst) id s' :
    emit ctx o size s = (id, s') -> var_map s' = var_map s.
  Proof. rewrite emit_red. intro H. injection H as _ <-. reflexivity. Qed.

  Lemma emit_gmono (o: @dfg_op_t s_var i_var o_var) size (s: wst) id s' :
    emit ctx o size s = (id, s') -> wgmono s s'.
  Proof.
    rewrite emit_red. intro H. injection H as _ <-.
    intros node Hin. cbn [graph]. right. exact Hin.
  Qed.

  Lemma wsz_fwd (act: tfs_action sched) F id size :
    exports act F -> wsz F id size -> wsz (build_dfg ctx act) id size.
  Proof.
    intros HF [node [Hin [Hnid Hsz]]]. exists node.
    split; [ exact (in_graph_fwd act F node HF Hin) | split; assumption ].
  Qed.

  (* ==================================================================== *)
  (* PHASE 3d, STEP 5a: invariant-free facts about the map merger.         *)
  (* ==================================================================== *)

  Lemma ensure_var_gmono (v: dvar) (s: wst) id s' :
    ensure_var ctx v s = (id, s') -> wgmono s s'.
  Proof.
    intro H. destruct (ensure_var_graph v s id s' H) as [Hgr _].
    intros node Hin. rewrite Hgr. right. exact Hin.
  Qed.

  Lemma merge_key_basic cond_id k vt_opt ve_opt (s: wst) res s' :
    merge_key ctx cond_id k vt_opt ve_opt s = (res, s') ->
    wgmono s s' /\ (res = None -> vt_opt = None /\ ve_opt = None).
  Proof.
    intro Hrun. unfold merge_key in Hrun.
    destruct vt_opt as [vt |]; destruct ve_opt as [ve |].
    - destruct (eq_dec vt ve) as [Heq | Hnee].
      + unfold ret in Hrun. injection Hrun as Hr Hs. subst s'.
        split; [ apply wgmono_refl | intro Hn; rewrite <- Hr in Hn; discriminate Hn ].
      + destruct (emit ctx (DFG_Phi cond_id vt ve) (dfg_var_size ctx k) s)
          as [phi s1] eqn:Ee.
        rewrite (bind_red (emit ctx (DFG_Phi cond_id vt ve) (dfg_var_size ctx k))
                   _ s _ _ Ee) in Hrun.
        unfold ret in Hrun. injection Hrun as Hr Hs. subst s'.
        split; [ exact (emit_gmono _ _ _ _ _ Ee)
               | intro Hn; rewrite <- Hr in Hn; discriminate Hn ].
    - destruct (ensure_var ctx k s) as [ve0 sA] eqn:Ev.
      rewrite (bind_red (ensure_var ctx k) _ s _ _ Ev) in Hrun.
      destruct (emit ctx (DFG_Phi cond_id vt ve0) (dfg_var_size ctx k) sA)
        as [phi s1] eqn:Ee.
      rewrite (bind_red (emit ctx (DFG_Phi cond_id vt ve0) (dfg_var_size ctx k))
                 _ sA _ _ Ee) in Hrun.
      unfold ret in Hrun. injection Hrun as Hr Hs. subst s'.
      split; [ exact (wgmono_trans s sA s1 (ensure_var_gmono k s ve0 sA Ev)
                        (emit_gmono _ _ _ _ _ Ee))
             | intro Hn; rewrite <- Hr in Hn; discriminate Hn ].
    - destruct (ensure_var ctx k s) as [vt0 sA] eqn:Ev.
      rewrite (bind_red (ensure_var ctx k) _ s _ _ Ev) in Hrun.
      destruct (emit ctx (DFG_Phi cond_id vt0 ve) (dfg_var_size ctx k) sA)
        as [phi s1] eqn:Ee.
      rewrite (bind_red (emit ctx (DFG_Phi cond_id vt0 ve) (dfg_var_size ctx k))
                 _ sA _ _ Ee) in Hrun.
      unfold ret in Hrun. injection Hrun as Hr Hs. subst s'.
      split; [ exact (wgmono_trans s sA s1 (ensure_var_gmono k s vt0 sA Ev)
                        (emit_gmono _ _ _ _ _ Ee))
             | intro Hn; rewrite <- Hr in Hn; discriminate Hn ].
    - unfold ret in Hrun. injection Hrun as Hr Hs. subst s'.
      split; [ apply wgmono_refl | intro Hn; split; reflexivity ].
  Qed.

  Lemma merge_loop_gmono cond_id mt me :
    forall keys acc (s: wst) fin s',
      merge_loop ctx cond_id mt me keys acc s = (fin, s') -> wgmono s s'.
  Proof.
    induction keys as [| [k0 v0] rest IH]; intros acc s fin s' Hrun.
    - simpl in Hrun. unfold ret in Hrun. injection Hrun as Hf Hs. subst s'.
      apply wgmono_refl.
    - simpl in Hrun.
      destruct (BitsToLists.list_assoc acc k0) as [existing |] eqn:Ek.
      + exact (IH acc s fin s' Hrun).
      + unfold bind in Hrun. cbv beta in Hrun.
        destruct (merge_key ctx cond_id k0 (BitsToLists.list_assoc mt k0)
                    (BitsToLists.list_assoc me k0) s) as [res_opt s1] eqn:Emk.
        cbv beta iota in Hrun.
        destruct (merge_key_basic cond_id k0 _ _ s res_opt s1 Emk) as [Hgk _].
        destruct res_opt as [final_id |].
        * exact (wgmono_trans s s1 s'
                   Hgk (IH ((k0, final_id) :: acc) s1 fin s' Hrun)).
        * exact (wgmono_trans s s1 s' Hgk (IH acc s1 fin s' Hrun)).
  Qed.

  (* Coverage: every key of [keys] that is bound in [mt] or [me] ends up in
     the result.  Stated contrapositively so it feeds [vm_frame] directly. *)
  Lemma merge_loop_cover cond_id mt me :
    forall keys acc (s: wst) fin s' k,
      merge_loop ctx cond_id mt me keys acc s = (fin, s') ->
      (forall m, ~ In (k, m) fin) ->
      (forall n, ~ In (k, n) acc)
      /\ (forall n, In (k, n) keys ->
            (forall p, ~ In (k, p) mt) /\ (forall p, ~ In (k, p) me)).
  Proof.
    induction keys as [| [k0 v0] rest IH]; intros acc s fin s' k Hrun Hfin.
    - simpl in Hrun. unfold ret in Hrun. injection Hrun as Hf Hs. subst fin.
      split; [ exact Hfin | intros n Hin; destruct Hin ].
    - simpl in Hrun.
      destruct (BitsToLists.list_assoc acc k0) as [existing |] eqn:Ek.
      + destruct (IH acc s fin s' k Hrun Hfin) as [Hacc Hrest].
        split; [ exact Hacc | ].
        intros n Hin. destruct Hin as [Heq | Hin].
        * injection Heq as Hk Hv. exfalso. subst k0.
          apply wla_in in Ek. exact (Hacc existing Ek).
        * exact (Hrest n Hin).
      + unfold bind in Hrun. cbv beta in Hrun.
        destruct (merge_key ctx cond_id k0 (BitsToLists.list_assoc mt k0)
                    (BitsToLists.list_assoc me k0) s) as [res_opt s1] eqn:Emk.
        cbv beta iota in Hrun.
        destruct res_opt as [final_id |].
        * destruct (IH ((k0, final_id) :: acc) s1 fin s' k Hrun Hfin) as [Hacc' Hrest].
          assert (Hnek : k <> k0).
          { intro He. subst k0. exact (Hacc' final_id (or_introl eq_refl)). }
          split.
          -- intros n Hin. exact (Hacc' n (or_intror Hin)).
          -- intros n Hin. destruct Hin as [Heq | Hin].
             ++ injection Heq as Hk Hv. exfalso. apply Hnek. symmetry. exact Hk.
             ++ exact (Hrest n Hin).
        * destruct (merge_key_basic cond_id k0 _ _ s None s1 Emk) as [_ Hnn].
          destruct (Hnn eq_refl) as [Hmtn Hmen].
          destruct (IH acc s1 fin s' k Hrun Hfin) as [Hacc Hrest].
          split; [ exact Hacc | ].
          intros n Hin. destruct Hin as [Heq | Hin].
          -- injection Heq as Hk Hv. subst k0.
             split; [ intros p Hp; exact (list_assoc_None_notin mt k Hmtn p Hp)
                    | intros p Hp; exact (list_assoc_None_notin me k Hmen p Hp) ].
          -- exact (Hrest n Hin).
  Qed.

  Section DFGSem.
    Context (act: tfs_action sched)
            (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
            (ss: sched_sys_state) (input: input_t)
            (sp0: src_sys_state) (F: wst).
    Hypothesis HF  : exports act F.
    Hypothesis Hss : forall sv, (fst ss).[tf_dfg_s sv] = (fst sp0).[sv].
    Hypothesis Hoo : forall ov, (snd ss).[ov] = (snd sp0).[ov].

    Local Notation NV szB n := (nval act a_idx ss input szB n).

    (* The source value of a DFG variable, at the variable's natural width. *)
    Definition src_get (sp: src_sys_state) (v: dvar) : bits_t (dfg_var_size ctx v) :=
      match v with
      | DFG_SVar sv => (fst sp).[sv]
      | DFG_OVar ov => (snd sp).[ov]
      end.

    Definition vm_sem (vm: list (dvar * nid_t)) (sp: src_sys_state) : Prop :=
      forall v n, In (v, n) vm -> NV (dfg_var_size ctx v) n = src_get sp v.

    Definition vm_frame (vm: list (dvar * nid_t)) (sp: src_sys_state) : Prop :=
      forall v, (forall n, ~ In (v, n) vm) -> src_get sp v = src_get sp0 v.

    Definition sem_inv (s: wst) (sp: src_sys_state) : Prop :=
      vm_sem (var_map s) sp /\ vm_frame (var_map s) sp.

    (* A freshly ensured variable node denotes the INITIAL source value. *)
    Lemma nval_fresh (s s': wst) (v: dvar) id :
      0 < length (graph s) ->
      ensure_var ctx v s = (id, s') -> wgmono s' F ->
      NV (dfg_var_size ctx v) id = src_get sp0 v.
    Proof.
      intros Hne Hev Hg. destruct v as [sv | ov]; cbn [src_get dfg_var_size].
      - rewrite (nval_fresh_svar act a_idx ss input F s s' sv id HF Hne Hev Hg).
        exact (Hss sv).
      - rewrite (nval_fresh_ovar act a_idx ss input F s s' ov id HF Hne Hev Hg).
        exact (Hoo ov).
    Qed.

    (* [get_var] returns a node denoting the CURRENT source value, and keeps
       the invariant: either the binding already existed, or [ensure_var] adds
       one whose value is the initial one — which the frame condition says IS
       the current one, precisely because the variable had no binding. *)
    Lemma get_var_sem (s s': wst) (v: dvar) id sp :
      0 < length (graph s) ->
      get_var ctx v s = (id, s') ->
      wgmono s' F ->
      sem_inv s sp ->
      sem_inv s' sp /\ NV (dfg_var_size ctx v) id = src_get sp v.
    Proof.
      intros Hne Hgv Hg [Hsem Hfr].
      destruct (get_var_cases v s id s' Hgv) as [[Hin ->] | [Hev Hnotin]].
      - split; [ split; assumption | exact (Hsem v id Hin) ].
      - pose proof (nval_fresh s s' v id Hne Hev Hg) as Hfresh.
        assert (Hval : NV (dfg_var_size ctx v) id = src_get sp v)
          by (rewrite Hfresh; symmetry; exact (Hfr v Hnotin)).
        split; [ | exact Hval ]. split.
        + intros v' n' Hin.
          destruct (ensure_var_vm_inv v s id s' v' n' Hev Hin) as [[-> ->] | Hin0].
          * exact Hval.
          * exact (Hsem v' n' Hin0).
        + intros v' Hno. apply Hfr. intros n Hin. apply (Hno n).
          destruct (eq_dec v' v) as [Heq | Hne'].
          * exfalso. subst v'. exact (Hno id (ensure_var_vm_head v s id s' Hev)).
          * exact (ensure_var_vm_keep v s id s' v' n Hev Hin Hne').
    Qed.

    (* Any builder step that does not touch [var_map] preserves [sem_inv]. *)
    Lemma sem_inv_vm (s s': wst) sp :
      var_map s' = var_map s -> sem_inv s sp -> sem_inv s' sp.
    Proof. intros Hvm [Ha Hb]. unfold sem_inv. rewrite Hvm. split; assumption. Qed.

    (* ================================================================= *)
    (* PHASE 3d, STEP 4: [dataflow_expr] is semantics-preserving.         *)
    (* The node it returns denotes, in the compiled scheduler state, the  *)
    (* source value of the expression in the CURRENT source state [sp].   *)
    (* ================================================================= *)
    Lemma dataflow_expr_sem :
      forall e szE (s s': wst) id sp,
        0 < length (graph s) -> winv s -> wvsz s ->
        dataflow_expr ctx e szE s = (id, s') ->
        wgmono s' F ->
        sem_inv s sp ->
        sem_inv s' sp
        /\ NV szE id = tf_eval_expr s_sz i_sz o_sz (szB := szE) e sp input.
    Proof.
      induction e as [ c | sv | iv | ov | uop e1 IH1
                     | bop e1 IH1 e2 IH2 | ec IHc et IHt ee IHe ];
        intros szE s s' id sp Hne Hinv Hvsz Hde Hg' Hsem.
      - (* tf_const *)
        cbn [dataflow_expr] in Hde.
        destruct (emitted_node_at act F s s' (DFG_Const c) szE id HF Hne Hde Hg')
          as [R1 [R2 [Rop _]]].
        split.
        + apply (sem_inv_vm s s'); [ exact (emit_vm _ _ _ _ _ Hde) | exact Hsem ].
        + unfold nval. rewrite (nre_const act a_idx id c R1 R2 Rop). reflexivity.
      - (* tf_svar *)
        cbn [dataflow_expr] in Hde. unfold bind in Hde.
        pose proof (get_var_sz (DFG_SVar sv) s Hinv Hvsz) as Hgv.
        destruct (get_var ctx (DFG_SVar sv) s) as [src_id s1] eqn:Egv.
        destruct Hgv as [Hg1 [Hn1 [Hp1 [Hq1 Hz1]]]].
        cbv beta in Hde.
        assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Hg1 Hne).
        destruct (Nat.eqb _ szE) eqn:Eb.
        + unfold ret in Hde. injection Hde as Hid Hs'. subst id. subst s'.
          destruct (get_var_sem s s1 (DFG_SVar sv) src_id sp Hne Egv Hg' Hsem)
            as [Hsem1 Hval].
          split; [ exact Hsem1 | ].
          apply Nat.eqb_eq in Eb. subst szE.
          rewrite Hval. cbn [src_get dfg_var_size tf_eval_expr].
          symmetry. apply convert_same.
        + assert (Hg1F : wgmono s1 F)
            by exact (wgmono_trans s1 s' F (emit_gmono _ _ _ _ _ Hde) Hg').
          destruct (get_var_sem s s1 (DFG_SVar sv) src_id sp Hne Egv Hg1F Hsem)
            as [Hsem1 Hval].
          destruct (emitted_node_at act F s1 s' (DFG_Resize src_id) szE id
                      HF Hne1 Hde Hg') as [R1 [R2 [Rop _]]].
          split.
          * apply (sem_inv_vm s1 s'); [ exact (emit_vm _ _ _ _ _ Hde) | exact Hsem1 ].
          * assert (Hsrcsz : sz (nth src_id (graph (build_dfg ctx act))
                                   {| nid := 0; op := DFG_Empty; sz := 0 |})
                             = dfg_var_size ctx (DFG_SVar sv)).
            { destruct (wsz_node_sz act src_id (dfg_var_size ctx (DFG_SVar sv))
                          (wsz_fwd act F src_id _ HF
                             (wsz_gmono s1 F src_id _ Hz1 Hg1F))) as [_ Hz]. exact Hz. }
            unfold nval in Hval |- *.
            rewrite (nre_resize act a_idx id src_id R1 R2 Rop), Hsrcsz.
            cbn [tf_eval_expr]. rewrite Hval.
            cbn [src_get dfg_var_size]. reflexivity.
      - (* tf_ivar *)
        cbn [dataflow_expr] in Hde. unfold bind in Hde.
        destruct (emit ctx (DFG_Input iv) szE s) as [src_id s1] eqn:Eem.
        cbv beta in Hde.
        assert (Hg1 : wgmono s s1) by exact (emit_gmono _ _ _ _ _ Eem).
        assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Hg1 Hne).
        destruct (Nat.eqb _ szE) eqn:Eb.
        + unfold ret in Hde. injection Hde as Hid Hs'. subst id. subst s'.
          destruct (emitted_node_at act F s s1 (DFG_Input iv) szE src_id
                      HF Hne Eem Hg') as [R1 [R2 [Rop _]]].
          split.
          * apply (sem_inv_vm s s1); [ exact (emit_vm _ _ _ _ _ Eem) | exact Hsem ].
          * unfold nval. rewrite (nre_input act a_idx src_id iv R1 R2 Rop).
            cbn [tf_eval_expr]. reflexivity.
        + assert (Hg1F : wgmono s1 F)
            by exact (wgmono_trans s1 s' F (emit_gmono _ _ _ _ _ Hde) Hg').
          destruct (emitted_node_at act F s s1 (DFG_Input iv) szE src_id
                      HF Hne Eem Hg1F) as [R1 [R2 [Rop Rsz]]].
          destruct (emitted_node_at act F s1 s' (DFG_Resize src_id) szE id
                      HF Hne1 Hde Hg') as [Q1 [Q2 [Qop _]]].
          split.
          * apply (sem_inv_vm s s'); [ | exact Hsem ].
            rewrite (emit_vm _ _ _ _ _ Hde). exact (emit_vm _ _ _ _ _ Eem).
          * unfold nval.
            rewrite (nre_resize act a_idx id src_id Q1 Q2 Qop), Rsz.
            cbn [tf_eval_expr].
            rewrite (nre_input act a_idx src_id iv R1 R2 Rop).
            cbn [tf_eval_expr]. apply convert_same.
      - (* tf_ovar *)
        cbn [dataflow_expr] in Hde. unfold bind in Hde.
        pose proof (get_var_sz (DFG_OVar ov) s Hinv Hvsz) as Hgv.
        destruct (get_var ctx (DFG_OVar ov) s) as [src_id s1] eqn:Egv.
        destruct Hgv as [Hg1 [Hn1 [Hp1 [Hq1 Hz1]]]].
        cbv beta in Hde.
        assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Hg1 Hne).
        destruct (Nat.eqb _ szE) eqn:Eb.
        + unfold ret in Hde. injection Hde as Hid Hs'. subst id. subst s'.
          destruct (get_var_sem s s1 (DFG_OVar ov) src_id sp Hne Egv Hg' Hsem)
            as [Hsem1 Hval].
          split; [ exact Hsem1 | ].
          apply Nat.eqb_eq in Eb. subst szE.
          rewrite Hval. cbn [src_get dfg_var_size tf_eval_expr].
          symmetry. apply convert_same.
        + assert (Hg1F : wgmono s1 F)
            by exact (wgmono_trans s1 s' F (emit_gmono _ _ _ _ _ Hde) Hg').
          destruct (get_var_sem s s1 (DFG_OVar ov) src_id sp Hne Egv Hg1F Hsem)
            as [Hsem1 Hval].
          destruct (emitted_node_at act F s1 s' (DFG_Resize src_id) szE id
                      HF Hne1 Hde Hg') as [R1 [R2 [Rop _]]].
          split.
          * apply (sem_inv_vm s1 s'); [ exact (emit_vm _ _ _ _ _ Hde) | exact Hsem1 ].
          * assert (Hsrcsz : sz (nth src_id (graph (build_dfg ctx act))
                                   {| nid := 0; op := DFG_Empty; sz := 0 |})
                             = dfg_var_size ctx (DFG_OVar ov)).
            { destruct (wsz_node_sz act src_id (dfg_var_size ctx (DFG_OVar ov))
                          (wsz_fwd act F src_id _ HF
                             (wsz_gmono s1 F src_id _ Hz1 Hg1F))) as [_ Hz]. exact Hz. }
            unfold nval in Hval |- *.
            rewrite (nre_resize act a_idx id src_id R1 R2 Rop), Hsrcsz.
            cbn [tf_eval_expr]. rewrite Hval.
            cbn [src_get dfg_var_size]. reflexivity.
      - (* tf_op1 *)
        destruct uop as [ | source_size ].
        + (* tf_not *)
          cbn [dataflow_expr] in Hde. unfold bind in Hde.
          pose proof (dataflow_expr_sz e1 szE s Hinv Hvsz) as Hsz1.
          destruct (dataflow_expr ctx e1 szE s) as [src_id s1] eqn:Ee1.
          destruct Hsz1 as [Hg1 [Hn1 [Hp1 [Hq1 Hz1]]]].
          cbv beta in Hde.
          assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Hg1 Hne).
          assert (Hg1F : wgmono s1 F)
            by exact (wgmono_trans s1 s' F (emit_gmono _ _ _ _ _ Hde) Hg').
          destruct (IH1 szE s s1 src_id sp Hne Hinv Hvsz Ee1 Hg1F Hsem) as [Hsem1 Hv1].
          destruct (emitted_node_at act F s1 s' (DFG_Unary tf_not src_id) szE id
                      HF Hne1 Hde Hg') as [R1 [R2 [Rop _]]].
          split.
          * apply (sem_inv_vm s1 s'); [ exact (emit_vm _ _ _ _ _ Hde) | exact Hsem1 ].
          * unfold nval in Hv1 |- *.
            rewrite (nre_unary act a_idx id tf_not src_id R1 R2 Rop).
            cbn [tf_eval_expr]. rewrite Hv1. reflexivity.
        + (* tf_resize *)
          cbn [dataflow_expr] in Hde. unfold bind in Hde.
          pose proof (dataflow_expr_sz e1 source_size s Hinv Hvsz) as Hsz1.
          destruct (dataflow_expr ctx e1 source_size s) as [src_id s1] eqn:Ee1.
          destruct Hsz1 as [Hg1 [Hn1 [Hp1 [Hq1 Hz1]]]].
          cbv beta in Hde.
          assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Hg1 Hne).
          assert (Hg1F : wgmono s1 F)
            by exact (wgmono_trans s1 s' F (emit_gmono _ _ _ _ _ Hde) Hg').
          destruct (IH1 source_size s s1 src_id sp Hne Hinv Hvsz Ee1 Hg1F Hsem)
            as [Hsem1 Hv1].
          destruct (emitted_node_at act F s1 s'
                      (DFG_Unary (tf_resize source_size) src_id) szE id
                      HF Hne1 Hde Hg') as [R1 [R2 [Rop _]]].
          split.
          * apply (sem_inv_vm s1 s'); [ exact (emit_vm _ _ _ _ _ Hde) | exact Hsem1 ].
          * unfold nval in Hv1 |- *.
            rewrite (nre_unary act a_idx id (tf_resize source_size) src_id R1 R2 Rop).
            cbn [tf_eval_expr]. rewrite Hv1. reflexivity.
      - (* tf_op2 *)
        destruct bop as [ | | | | | | szC cop ].
        1-6: (cbn [dataflow_expr] in Hde; unfold bind in Hde;
              pose proof (dataflow_expr_sz e1 szE s Hinv Hvsz) as Hsz1;
              destruct (dataflow_expr ctx e1 szE s) as [id1 s1] eqn:Ee1;
              destruct Hsz1 as [Hg1 [Hn1 [Hp1 [Hq1 Hz1]]]];
              pose proof (dataflow_expr_sz e2 szE s1 Hp1 Hq1) as Hsz2;
              destruct (dataflow_expr ctx e2 szE s1) as [id2 s2] eqn:Ee2;
              destruct Hsz2 as [Hg2 [Hn2 [Hp2 [Hq2 Hz2]]]];
              cbv beta in Hde;
              assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Hg1 Hne);
              assert (Hne2 : 0 < length (graph s2)) by exact (gne_gmono s1 s2 Hg2 Hne1);
              assert (Hg2F : wgmono s2 F)
                by exact (wgmono_trans s2 s' F (emit_gmono _ _ _ _ _ Hde) Hg');
              assert (Hg1F : wgmono s1 F) by exact (wgmono_trans s1 s2 F Hg2 Hg2F);
              destruct (IH1 szE s s1 id1 sp Hne Hinv Hvsz Ee1 Hg1F Hsem) as [Hsem1 Hv1];
              destruct (IH2 szE s1 s2 id2 sp Hne1 Hp1 Hq1 Ee2 Hg2F Hsem1) as [Hsem2 Hv2];
              destruct (emitted_node_at act F s2 s' _ szE id HF Hne2 Hde Hg')
                as [R1 [R2 [Rop _]]];
              split;
              [ apply (sem_inv_vm s2 s');
                [ exact (emit_vm _ _ _ _ _ Hde) | exact Hsem2 ]
              | unfold nval in Hv1, Hv2 |- *;
                rewrite (nre_binary act a_idx id _ id1 id2 R1 R2 Rop);
                cbn [tf_eval_expr]; rewrite Hv1, Hv2; reflexivity ]).
        (* tf_cmp: both operands are compiled at the COMPARISON width szC. *)
        cbn [dataflow_expr] in Hde. unfold bind in Hde.
        pose proof (dataflow_expr_sz e1 szC s Hinv Hvsz) as Hsz1.
        destruct (dataflow_expr ctx e1 szC s) as [id1 s1] eqn:Ee1.
        destruct Hsz1 as [Hg1 [Hn1 [Hp1 [Hq1 Hz1]]]].
        pose proof (dataflow_expr_sz e2 szC s1 Hp1 Hq1) as Hsz2.
        destruct (dataflow_expr ctx e2 szC s1) as [id2 s2] eqn:Ee2.
        destruct Hsz2 as [Hg2 [Hn2 [Hp2 [Hq2 Hz2]]]].
        cbv beta in Hde.
        assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Hg1 Hne).
        assert (Hne2 : 0 < length (graph s2)) by exact (gne_gmono s1 s2 Hg2 Hne1).
        assert (Hg2F : wgmono s2 F)
          by exact (wgmono_trans s2 s' F (emit_gmono _ _ _ _ _ Hde) Hg').
        assert (Hg1F : wgmono s1 F) by exact (wgmono_trans s1 s2 F Hg2 Hg2F).
        destruct (IH1 szC s s1 id1 sp Hne Hinv Hvsz Ee1 Hg1F Hsem) as [Hsem1 Hv1].
        destruct (IH2 szC s1 s2 id2 sp Hne1 Hp1 Hq1 Ee2 Hg2F Hsem1) as [Hsem2 Hv2].
        destruct (emitted_node_at act F s2 s' (DFG_Binary (tf_cmp szC cop) id1 id2)
                    szE id HF Hne2 Hde Hg') as [R1 [R2 [Rop _]]].
        split.
        + apply (sem_inv_vm s2 s'); [ exact (emit_vm _ _ _ _ _ Hde) | exact Hsem2 ].
        + unfold nval in Hv1, Hv2 |- *.
          rewrite (nre_binary act a_idx id (tf_cmp szC cop) id1 id2 R1 R2 Rop).
          cbn [tf_eval_expr]. rewrite Hv1, Hv2. reflexivity.
      - (* tf_expr_if *)
        cbn [dataflow_expr] in Hde. unfold bind in Hde.
        pose proof (dataflow_expr_sz ec 1 s Hinv Hvsz) as HszC.
        destruct (dataflow_expr ctx ec 1 s) as [cid s1] eqn:Ec.
        destruct HszC as [Hg1 [Hn1 [Hp1 [Hq1 Hz1]]]].
        pose proof (dataflow_expr_sz et szE s1 Hp1 Hq1) as HszT.
        destruct (dataflow_expr ctx et szE s1) as [tid s2] eqn:Et.
        destruct HszT as [Hg2 [Hn2 [Hp2 [Hq2 Hz2]]]].
        pose proof (dataflow_expr_sz ee szE s2 Hp2 Hq2) as HszEl.
        destruct (dataflow_expr ctx ee szE s2) as [eid s3] eqn:El.
        destruct HszEl as [Hg3 [Hn3 [Hp3 [Hq3 Hz3]]]].
        cbv beta in Hde.
        assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Hg1 Hne).
        assert (Hne2 : 0 < length (graph s2)) by exact (gne_gmono s1 s2 Hg2 Hne1).
        assert (Hne3 : 0 < length (graph s3)) by exact (gne_gmono s2 s3 Hg3 Hne2).
        assert (Hg3F : wgmono s3 F)
          by exact (wgmono_trans s3 s' F (emit_gmono _ _ _ _ _ Hde) Hg').
        assert (Hg2F : wgmono s2 F) by exact (wgmono_trans s2 s3 F Hg3 Hg3F).
        assert (Hg1F : wgmono s1 F) by exact (wgmono_trans s1 s2 F Hg2 Hg2F).
        destruct (IHc 1 s s1 cid sp Hne Hinv Hvsz Ec Hg1F Hsem) as [Hsem1 Hvc].
        destruct (IHt szE s1 s2 tid sp Hne1 Hp1 Hq1 Et Hg2F Hsem1) as [Hsem2 Hvt].
        destruct (IHe szE s2 s3 eid sp Hne2 Hp2 Hq2 El Hg3F Hsem2) as [Hsem3 Hve].
        destruct (emitted_node_at act F s3 s' (DFG_Phi cid tid eid) szE id
                    HF Hne3 Hde Hg') as [R1 [R2 [Rop _]]].
        split.
        + apply (sem_inv_vm s3 s'); [ exact (emit_vm _ _ _ _ _ Hde) | exact Hsem3 ].
        + unfold nval in Hvc, Hvt, Hve |- *.
          rewrite (nre_phi act a_idx id cid tid eid R1 R2 Rop).
          cbn [tf_eval_expr]. rewrite Hvc, Hvt, Hve. reflexivity.
    Qed.

    (* ================================================================= *)
    (* PHASE 3d, STEP 5: the map merger is semantics-preserving.          *)
    (* [b] is the (abstract) branch selector: [true] means the ELSE side  *)
    (* was taken, matching [tf_expr_if]'s and [tf_ops_updates]'s          *)
    (* "cond = 0 -> else" convention.  Keeping it abstract avoids ever    *)
    (* writing [beq_dec] in a statement.                                  *)
    (* ================================================================= *)
    Lemma merge_key_sem (cond_id: nid_t) (k: dvar) vt_opt ve_opt
          (s s1: wst) res (b: bool) (spt spe spf: src_sys_state) :
      0 < length (graph s) ->
      merge_key ctx cond_id k vt_opt ve_opt s = (res, s1) ->
      wgmono s1 F ->
      (forall szB E1 E2,
         tf_eval_expr ss_sz i_sz oo_sz (szB := szB)
           (tf_expr_if (node_ref_expr act a_idx cond_id) E1 E2) ss input
         = if b then tf_eval_expr ss_sz i_sz oo_sz (szB := szB) E2 ss input
                else tf_eval_expr ss_sz i_sz oo_sz (szB := szB) E1 ss input) ->
      (forall kk, src_get spf kk = if b then src_get spe kk else src_get spt kk) ->
      (forall vt, vt_opt = Some vt -> NV (dfg_var_size ctx k) vt = src_get spt k) ->
      (forall ve, ve_opt = Some ve -> NV (dfg_var_size ctx k) ve = src_get spe k) ->
      (vt_opt = None -> src_get spt k = src_get sp0 k) ->
      (ve_opt = None -> src_get spe k = src_get sp0 k) ->
      forall fid, res = Some fid -> NV (dfg_var_size ctx k) fid = src_get spf k.
    Proof.
      intros Hne Hrun Hg1 Hb Hsel Hvt Hve Hvtn Hven fid Hfid.
      unfold merge_key in Hrun.
      destruct vt_opt as [vt |]; destruct ve_opt as [ve |].
      - (* both branches bind [k] *)
        destruct (eq_dec vt ve) as [Heq | Hnee].
        + unfold ret in Hrun. injection Hrun as Hr Hs. subst res. subst s1.
          injection Hfid as Hf. subst fid.
          rewrite Hsel. destruct b.
          * rewrite Heq. exact (Hve ve eq_refl).
          * exact (Hvt vt eq_refl).
        + destruct (emit ctx (DFG_Phi cond_id vt ve) (dfg_var_size ctx k) s)
            as [phi s2] eqn:Ee.
          rewrite (bind_red (emit ctx (DFG_Phi cond_id vt ve) (dfg_var_size ctx k))
                     _ s _ _ Ee) in Hrun.
          unfold ret in Hrun. injection Hrun as Hr Hs. subst res. subst s1.
          injection Hfid as Hf. subst fid.
          destruct (emitted_node_at act F s s2 (DFG_Phi cond_id vt ve)
                      (dfg_var_size ctx k) phi HF Hne Ee Hg1) as [R1 [R2 [Rop _]]].
          unfold nval. rewrite (nre_phi act a_idx phi cond_id vt ve R1 R2 Rop).
          rewrite Hb, Hsel. destruct b.
          * exact (Hve ve eq_refl).
          * exact (Hvt vt eq_refl).
      - (* only the THEN branch binds [k]: the else value is the initial one *)
        destruct (ensure_var ctx k s) as [ve0 sA] eqn:Ev.
        rewrite (bind_red (ensure_var ctx k) _ s _ _ Ev) in Hrun.
        destruct (emit ctx (DFG_Phi cond_id vt ve0) (dfg_var_size ctx k) sA)
          as [phi s2] eqn:Ee.
        rewrite (bind_red (emit ctx (DFG_Phi cond_id vt ve0) (dfg_var_size ctx k))
                   _ sA _ _ Ee) in Hrun.
        unfold ret in Hrun. injection Hrun as Hr Hs. subst res. subst s1.
        injection Hfid as Hf. subst fid.
        assert (HgA : wgmono sA F)
          by exact (wgmono_trans sA s2 F (emit_gmono _ _ _ _ _ Ee) Hg1).
        assert (HneA : 0 < length (graph sA))
          by exact (gne_gmono s sA (ensure_var_gmono k s ve0 sA Ev) Hne).
        assert (Hve0 : NV (dfg_var_size ctx k) ve0 = src_get spe k).
        { rewrite (nval_fresh s sA k ve0 Hne Ev HgA). symmetry. exact (Hven eq_refl). }
        destruct (emitted_node_at act F sA s2 (DFG_Phi cond_id vt ve0)
                    (dfg_var_size ctx k) phi HF HneA Ee Hg1) as [R1 [R2 [Rop _]]].
        unfold nval. rewrite (nre_phi act a_idx phi cond_id vt ve0 R1 R2 Rop).
        rewrite Hb, Hsel. destruct b.
        + exact Hve0.
        + exact (Hvt vt eq_refl).
      - (* only the ELSE branch binds [k] *)
        destruct (ensure_var ctx k s) as [vt0 sA] eqn:Ev.
        rewrite (bind_red (ensure_var ctx k) _ s _ _ Ev) in Hrun.
        destruct (emit ctx (DFG_Phi cond_id vt0 ve) (dfg_var_size ctx k) sA)
          as [phi s2] eqn:Ee.
        rewrite (bind_red (emit ctx (DFG_Phi cond_id vt0 ve) (dfg_var_size ctx k))
                   _ sA _ _ Ee) in Hrun.
        unfold ret in Hrun. injection Hrun as Hr Hs. subst res. subst s1.
        injection Hfid as Hf. subst fid.
        assert (HgA : wgmono sA F)
          by exact (wgmono_trans sA s2 F (emit_gmono _ _ _ _ _ Ee) Hg1).
        assert (HneA : 0 < length (graph sA))
          by exact (gne_gmono s sA (ensure_var_gmono k s vt0 sA Ev) Hne).
        assert (Hvt0 : NV (dfg_var_size ctx k) vt0 = src_get spt k).
        { rewrite (nval_fresh s sA k vt0 Hne Ev HgA). symmetry. exact (Hvtn eq_refl). }
        destruct (emitted_node_at act F sA s2 (DFG_Phi cond_id vt0 ve)
                    (dfg_var_size ctx k) phi HF HneA Ee Hg1) as [R1 [R2 [Rop _]]].
        unfold nval. rewrite (nre_phi act a_idx phi cond_id vt0 ve R1 R2 Rop).
        rewrite Hb, Hsel. destruct b.
        + exact (Hve ve eq_refl).
        + exact Hvt0.
      - (* neither branch binds [k]: no entry is produced *)
        unfold ret in Hrun. injection Hrun as Hr Hs. subst res. discriminate Hfid.
    Qed.

    Lemma merge_loop_sem (cond_id: nid_t) mt me (b: bool) (spt spe spf: src_sys_state) :
      (forall szB E1 E2,
         tf_eval_expr ss_sz i_sz oo_sz (szB := szB)
           (tf_expr_if (node_ref_expr act a_idx cond_id) E1 E2) ss input
         = if b then tf_eval_expr ss_sz i_sz oo_sz (szB := szB) E2 ss input
                else tf_eval_expr ss_sz i_sz oo_sz (szB := szB) E1 ss input) ->
      (forall kk, src_get spf kk = if b then src_get spe kk else src_get spt kk) ->
      vm_sem mt spt -> vm_frame mt spt ->
      vm_sem me spe -> vm_frame me spe ->
      forall keys acc (s: wst) fin s',
        0 < length (graph s) ->
        merge_loop ctx cond_id mt me keys acc s = (fin, s') ->
        wgmono s' F ->
        vm_sem acc spf ->
        vm_sem fin spf.
    Proof.
      intros Hb Hsel Hmt Hmtf Hme Hmef.
      induction keys as [| [k0 v0] rest IH];
        intros acc s fin s' Hne Hrun Hg' Hacc.
      - simpl in Hrun. unfold ret in Hrun. injection Hrun as Hf Hs.
        subst fin. exact Hacc.
      - simpl in Hrun.
        destruct (BitsToLists.list_assoc acc k0) as [existing |] eqn:Ek.
        + exact (IH acc s fin s' Hne Hrun Hg' Hacc).
        + unfold bind in Hrun. cbv beta in Hrun.
          destruct (merge_key ctx cond_id k0 (BitsToLists.list_assoc mt k0)
                      (BitsToLists.list_assoc me k0) s) as [res_opt s1] eqn:Emk.
          cbv beta iota in Hrun.
          destruct (merge_key_basic cond_id k0 _ _ s res_opt s1 Emk) as [Hgk _].
          assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Hgk Hne).
          destruct res_opt as [final_id |].
          * assert (Hg1F : wgmono s1 F)
              by exact (wgmono_trans s1 s' F
                          (merge_loop_gmono cond_id mt me rest
                             ((k0, final_id) :: acc) s1 fin s' Hrun) Hg').
            assert (Hval : NV (dfg_var_size ctx k0) final_id = src_get spf k0).
            { refine (merge_key_sem cond_id k0 _ _ s s1 (Some final_id) b spt spe spf
                        Hne Emk Hg1F Hb Hsel _ _ _ _ final_id eq_refl).
              - intros vt Hv. apply wla_in in Hv. exact (Hmt k0 vt Hv).
              - intros ve Hv. apply wla_in in Hv. exact (Hme k0 ve Hv).
              - intro Hn. apply Hmtf. intros n Hin.
                exact (list_assoc_None_notin mt k0 Hn n Hin).
              - intro Hn. apply Hmef. intros n Hin.
                exact (list_assoc_None_notin me k0 Hn n Hin). }
            apply (IH ((k0, final_id) :: acc) s1 fin s' Hne1 Hrun Hg').
            intros v n Hin. destruct Hin as [Heq | Hin].
            -- injection Heq as Hk Hn. subst v. subst n. exact Hval.
            -- exact (Hacc v n Hin).
          * assert (Hg1F : wgmono s1 F)
              by exact (wgmono_trans s1 s' F
                          (merge_loop_gmono cond_id mt me rest acc s1 fin s' Hrun) Hg').
            exact (IH acc s1 fin s' Hne1 Hrun Hg' Hacc).
    Qed.

    Lemma merge_maps_sem (cond_id: nid_t) mo mt me (b: bool)
          (spt spe spf: src_sys_state) (s: wst) fin s' :
      (forall szB E1 E2,
         tf_eval_expr ss_sz i_sz oo_sz (szB := szB)
           (tf_expr_if (node_ref_expr act a_idx cond_id) E1 E2) ss input
         = if b then tf_eval_expr ss_sz i_sz oo_sz (szB := szB) E2 ss input
                else tf_eval_expr ss_sz i_sz oo_sz (szB := szB) E1 ss input) ->
      (forall kk, src_get spf kk = if b then src_get spe kk else src_get spt kk) ->
      vm_sem mt spt -> vm_frame mt spt ->
      vm_sem me spe -> vm_frame me spe ->
      0 < length (graph s) ->
      merge_maps ctx cond_id mo mt me s = (fin, s') ->
      wgmono s' F ->
      vm_sem fin spf /\ vm_frame fin spf.
    Proof.
      intros Hb Hsel Hmt Hmtf Hme Hmef Hne Hrun Hg'.
      unfold merge_maps in Hrun.
      split.
      - exact (merge_loop_sem cond_id mt me b spt spe spf Hb Hsel Hmt Hmtf Hme Hmef
                 (mt ++ me) [] s fin s' Hne Hrun Hg'
                 (fun v n Hin => match Hin with end)).
      - intros v Hno.
        destruct (merge_loop_cover cond_id mt me (mt ++ me) [] s fin s' v Hrun Hno)
          as [_ Hcov].
        assert (Hnmt : forall p, ~ In (v, p) mt).
        { intros p Hin.
          destruct (Hcov p (in_or_app _ _ _ (or_introl Hin))) as [H1 _].
          exact (H1 p Hin). }
        assert (Hnme : forall p, ~ In (v, p) me).
        { intros p Hin.
          destruct (Hcov p (in_or_app _ _ _ (or_intror Hin))) as [_ H2].
          exact (H2 p Hin). }
        rewrite Hsel. destruct b; [ exact (Hmef v Hnme) | exact (Hmtf v Hnmt) ].
    Qed.

    (* ================================================================= *)
    (* PHASE 3d, STEP 6: the operations compiler is semantics-preserving. *)
    (* ================================================================= *)

    Lemma sem_inv_ext (s: wst) (sp sq: src_sys_state) :
      (forall v, src_get sp v = src_get sq v) -> sem_inv s sp -> sem_inv s sq.
    Proof.
      intros Hext [Ha Hb]. split.
      - intros v n Hin. rewrite <- Hext. exact (Ha v n Hin).
      - intros v Hno. rewrite <- Hext. exact (Hb v Hno).
    Qed.

    (* The seed builder state (empty var_map) trivially satisfies the invariant
       against the initial source state. *)
    Lemma sem_inv_empty (s: wst) : var_map s = [] -> sem_inv s sp0.
    Proof.
      intro Hvm. unfold sem_inv, vm_sem, vm_frame. rewrite Hvm. split.
      - intros v n Hin. destruct Hin.
      - intros v _. reflexivity.
    Qed.

    Lemma ops_run_nop (sp: src_sys_state) :
      tf_ops_run s_sz i_sz o_sz (tf_ops_base tf_nop) sp input = (fst sp, snd sp).
    Proof. reflexivity. Qed.

    Lemma ops_run_assign (dst: s_var) e (sp: src_sys_state) :
      tf_ops_run s_sz i_sz o_sz (tf_ops_base (tf_assign dst e)) sp input
      = (ContextEnv.(putenv) (fst sp) dst
           (tf_eval_expr s_sz i_sz o_sz (szB := s_sz dst) e sp input), snd sp).
    Proof. reflexivity. Qed.

    Lemma ops_run_output (dst: o_var) e (sp: src_sys_state) :
      tf_ops_run s_sz i_sz o_sz (tf_ops_base (tf_output dst e)) sp input
      = (fst sp, ContextEnv.(putenv) (snd sp) dst
           (tf_eval_expr s_sz i_sz o_sz (szB := o_sz dst) e sp input)).
    Proof. reflexivity. Qed.

    Lemma ops_run_cons o1 o2 (sp: src_sys_state) :
      tf_ops_run s_sz i_sz o_sz (tf_ops_cons o1 o2) sp input
      = tf_ops_run s_sz i_sz o_sz o2 (tf_ops_run s_sz i_sz o_sz o1 sp input) input.
    Proof.
      unfold tf_ops_run. cbn [tf_ops_updates].
      destruct (tf_ops_updates s_sz i_sz o_sz o1 sp input) as [u1 sp1].
      cbn [snd].
      destruct (tf_ops_updates s_sz i_sz o_sz o2 sp1 input) as [u2 sp2].
      reflexivity.
    Qed.

    Lemma src_get_put_s_eq (sp: src_sys_state) (dst: s_var) (val: bits_t (s_sz dst)) :
      src_get (ContextEnv.(putenv) (fst sp) dst val, snd sp) (DFG_SVar dst) = val.
    Proof. cbn [src_get fst snd]. rewrite get_put_eq. reflexivity. Qed.

    Lemma src_get_put_s_neq (sp: src_sys_state) (dst: s_var) (val: bits_t (s_sz dst))
          (v: dvar) :
      v <> DFG_SVar dst ->
      src_get (ContextEnv.(putenv) (fst sp) dst val, snd sp) v = src_get sp v.
    Proof.
      intro Hne. destruct v as [sv | ov]; cbn [src_get fst snd].
      - rewrite get_put_neq;
          [ reflexivity | intro He; apply Hne; rewrite He; reflexivity ].
      - reflexivity.
    Qed.

    Lemma src_get_put_o_eq (sp: src_sys_state) (dst: o_var) (val: bits_t (o_sz dst)) :
      src_get (fst sp, ContextEnv.(putenv) (snd sp) dst val) (DFG_OVar dst) = val.
    Proof. cbn [src_get fst snd]. rewrite get_put_eq. reflexivity. Qed.

    Lemma src_get_put_o_neq (sp: src_sys_state) (dst: o_var) (val: bits_t (o_sz dst))
          (v: dvar) :
      v <> DFG_OVar dst ->
      src_get (fst sp, ContextEnv.(putenv) (snd sp) dst val) v = src_get sp v.
    Proof.
      intro Hne. destruct v as [sv | ov]; cbn [src_get fst snd].
      - reflexivity.
      - rewrite get_put_neq;
          [ reflexivity | intro He; apply Hne; rewrite He; reflexivity ].
    Qed.

    Lemma dataflow_ops_sem :
      forall ops (s: wst) sp,
        0 < length (graph s) -> winv s -> wvsz s -> wfg s ->
        sem_inv s sp ->
        let (u, s') := dataflow_ops ctx ops s in
        wgmono s' F -> sem_inv s' (tf_ops_run s_sz i_sz o_sz ops sp input).
    Proof.
      induction ops as [op | op1 IHops1 op2 IHops2 | cond op1 IHops1 op2 IHops2];
        intros s sp Hne Hinv Hvsz Hfg Hsem.
      - destruct op as [ | dst expr | dst expr ].
        + (* nop *)
          cbn [dataflow_ops]. unfold ret. intro Hg'.
          rewrite ops_run_nop.
          apply (sem_inv_ext s sp); [ intro v; destruct v; reflexivity | exact Hsem ].
        + (* assign to a state variable *)
          cbn [dataflow_ops].
          pose proof (dataflow_expr_fg expr (dfg_var_size ctx (DFG_SVar dst)) s
                        Hinv Hvsz Hfg) as He.
          destruct (dataflow_expr ctx expr (dfg_var_size ctx (DFG_SVar dst)) s)
            as [res_id s1] eqn:Ee.
          destruct He as [Ge [Ne [Pe [Qe [Se Fe]]]]].
          rewrite (bind_red (dataflow_expr ctx expr (dfg_var_size ctx (DFG_SVar dst)))
                     _ s _ _ Ee).
          pose proof (set_var_vm_head (DFG_SVar dst) res_id s1) as Hhead.
          pose proof (set_var_vm_keep (DFG_SVar dst) res_id s1) as Hkeep.
          pose proof (set_var_vm_inv2 (DFG_SVar dst) res_id s1) as Hminv.
          pose proof (set_var_full (DFG_SVar dst) res_id s1 Pe Ne) as Hs.
          destruct (set_var ctx (DFG_SVar dst) res_id s1) as [u s'] eqn:Es.
          cbn [snd] in Hhead, Hkeep, Hminv.
          destruct Hs as [Gs Ps].
          intro Hg'.
          assert (Hg1F : wgmono s1 F) by exact (wgmono_trans s1 s' F Gs Hg').
          destruct (dataflow_expr_sem expr (dfg_var_size ctx (DFG_SVar dst)) s s1
                      res_id sp Hne Hinv Hvsz Ee Hg1F Hsem) as [[Hvm1 Hfr1] Hval].
          rewrite ops_run_assign. split.
          * intros v n Hin.
            destruct (Hminv v n Hin) as [[Hv Hn] | [Hin0 Hnv]].
            -- subst v. subst n. rewrite (src_get_put_s_eq sp dst _). exact Hval.
            -- rewrite (src_get_put_s_neq sp dst _ v Hnv). exact (Hvm1 v n Hin0).
          * intros v Hno.
            assert (Hnv : v <> DFG_SVar dst).
            { intro He. subst v. exact (Hno res_id Hhead). }
            rewrite (src_get_put_s_neq sp dst _ v Hnv).
            apply Hfr1. intros n Hin. exact (Hno n (Hkeep v n Hin Hnv)).
        + (* assign to an output variable *)
          cbn [dataflow_ops].
          pose proof (dataflow_expr_fg expr (dfg_var_size ctx (DFG_OVar dst)) s
                        Hinv Hvsz Hfg) as He.
          destruct (dataflow_expr ctx expr (dfg_var_size ctx (DFG_OVar dst)) s)
            as [res_id s1] eqn:Ee.
          destruct He as [Ge [Ne [Pe [Qe [Se Fe]]]]].
          rewrite (bind_red (dataflow_expr ctx expr (dfg_var_size ctx (DFG_OVar dst)))
                     _ s _ _ Ee).
          pose proof (set_var_vm_head (DFG_OVar dst) res_id s1) as Hhead.
          pose proof (set_var_vm_keep (DFG_OVar dst) res_id s1) as Hkeep.
          pose proof (set_var_vm_inv2 (DFG_OVar dst) res_id s1) as Hminv.
          pose proof (set_var_full (DFG_OVar dst) res_id s1 Pe Ne) as Hs.
          destruct (set_var ctx (DFG_OVar dst) res_id s1) as [u s'] eqn:Es.
          cbn [snd] in Hhead, Hkeep, Hminv.
          destruct Hs as [Gs Ps].
          intro Hg'.
          assert (Hg1F : wgmono s1 F) by exact (wgmono_trans s1 s' F Gs Hg').
          destruct (dataflow_expr_sem expr (dfg_var_size ctx (DFG_OVar dst)) s s1
                      res_id sp Hne Hinv Hvsz Ee Hg1F Hsem) as [[Hvm1 Hfr1] Hval].
          rewrite ops_run_output. split.
          * intros v n Hin.
            destruct (Hminv v n Hin) as [[Hv Hn] | [Hin0 Hnv]].
            -- subst v. subst n. rewrite (src_get_put_o_eq sp dst _). exact Hval.
            -- rewrite (src_get_put_o_neq sp dst _ v Hnv). exact (Hvm1 v n Hin0).
          * intros v Hno.
            assert (Hnv : v <> DFG_OVar dst).
            { intro He. subst v. exact (Hno res_id Hhead). }
            rewrite (src_get_put_o_neq sp dst _ v Hnv).
            apply Hfr1. intros n Hin. exact (Hno n (Hkeep v n Hin Hnv)).
      - (* sequential composition *)
        cbn [dataflow_ops].
        pose proof (dataflow_ops_fg op1 s Hinv Hvsz Hfg) as Fa.
        pose proof (IHops1 s sp Hne Hinv Hvsz Hfg Hsem) as H1.
        destruct (dataflow_ops ctx op1 s) as [u1 s1] eqn:E1.
        destruct Fa as [G1 [P1 [Q1 Ff1]]].
        rewrite (bind_red (dataflow_ops ctx op1) _ s _ _ E1).
        assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 G1 Hne).
        pose proof (dataflow_ops_fg op2 s1 P1 Q1 Ff1) as Fb.
        pose proof (fun Hs =>
                      IHops2 s1 (tf_ops_run s_sz i_sz o_sz op1 sp input)
                        Hne1 P1 Q1 Ff1 Hs) as H2.
        destruct (dataflow_ops ctx op2 s1) as [u2 s2] eqn:E2.
        destruct Fb as [G2 [P2 [Q2 Ff2]]].
        intro Hg'.
        assert (Hg1F : wgmono s1 F) by exact (wgmono_trans s1 s2 F G2 Hg').
        rewrite ops_run_cons.
        exact (H2 (H1 Hg1F) Hg').
      - (* conditional *)
        cbn [dataflow_ops].
        pose proof (dataflow_expr_fg cond 1 s Hinv Hvsz Hfg) as Hc.
        destruct (dataflow_expr ctx cond 1 s) as [cond_id s1] eqn:Ec.
        destruct Hc as [Gc [Nc [Pc [Qc [Sc Fc]]]]].
        rewrite (bind_red (dataflow_expr ctx cond 1) _ s _ _ Ec).
        rewrite (bind_red (get_state ctx) _ s1 _ _ (get_state_red s1)).
        assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Gc Hne).
        pose proof (dataflow_ops_fg op1 s1 Pc Qc Fc) as Ft.
        pose proof (fun Hs => IHops1 s1 sp Hne1 Pc Qc Fc Hs) as Ht.
        destruct (dataflow_ops ctx op1 s1) as [ut s_then] eqn:Et.
        destruct Ft as [Gthen [Pthen [Qthen Fthen]]].
        rewrite (bind_red (dataflow_ops ctx op1) _ s1 _ _ Et).
        rewrite (bind_red (get_state ctx) _ s_then _ _ (get_state_red s_then)).
        set (sR := {| graph := graph s_then; var_map := var_map s1 |} : wst).
        rewrite (bind_red (put_state ctx sR) _ s_then _ _ (put_state_red sR s_then)).
        assert (Gthen_sR : wgmono s_then sR) by (intros n Hn; unfold sR; simpl; exact Hn).
        assert (GsR_then : wgmono sR s_then)
          by (intros n Hn; unfold sR in Hn; simpl in Hn; exact Hn).
        assert (PsR : winv sR).
        { destruct Pc as [Hv1 [Hns1 Hab1]]. destruct Pthen as [Hvt [Hnst Habt]].
          split; [ | split ].
          - intros k id Hin. unfold sR in Hin; simpl in Hin.
            destruct (Hv1 k id Hin) as [node [Hn Hnid]].
            exists node. split; [ unfold sR; simpl; apply Gthen; exact Hn | exact Hnid ].
          - unfold nid_seq, sR; simpl. exact Hnst.
          - unfold sR; simpl. exact Habt. }
        assert (QsR : wvsz sR).
        { intros v id Hin. unfold sR in Hin; simpl in Hin.
          eapply wsz_gmono; [ apply Qc; exact Hin | ].
          intros n Hn; unfold sR; simpl; apply Gthen; exact Hn. }
        assert (FsR : wfg sR).
        { intros node Hin. unfold sR in Hin; simpl in Hin.
          eapply node_args_sz_gmono; [ apply Fthen; exact Hin | exact GsR_then ]. }
        assert (HneR : 0 < length (graph sR)).
        { unfold sR; simpl. exact (gne_gmono s1 s_then Gthen Hne1). }
        pose proof (dataflow_ops_fg op2 sR PsR QsR FsR) as Fe.
        pose proof (fun Hs => IHops2 sR sp HneR PsR QsR FsR Hs) as Hels.
        destruct (dataflow_ops ctx op2 sR) as [ue s_else] eqn:Ee.
        destruct Fe as [Gelse [Pelse [Qelse Felse]]].
        rewrite (bind_red (dataflow_ops ctx op2) _ sR _ _ Ee).
        rewrite (bind_red (get_state ctx) _ s_else _ _ (get_state_red s_else)).
        assert (Gs1_selse : wgmono s1 s_else)
          by (eapply wgmono_trans;
              [ exact Gthen | eapply wgmono_trans; [ exact Gthen_sR | exact Gelse ] ]).
        assert (Gthen_selse : wgmono s_then s_else)
          by (eapply wgmono_trans; [ exact Gthen_sR | exact Gelse ]).
        assert (HneE : 0 < length (graph s_else))
          by exact (gne_gmono sR s_else Gelse HneR).
        assert (Ncond : wnidwf s_else cond_id)
          by (eapply wnidwf_gmono; [ exact Nc | exact Gs1_selse ]).
        assert (Scond : wsz s_else cond_id 1)
          by (eapply wsz_gmono; [ exact Sc | exact Gs1_selse ]).
        assert (Hmtn : forall k id, In (k, id) (var_map s_then) -> wnidwf s_else id).
        { intros k id Hin. destruct Pthen as [Hvt _].
          destruct (Hvt k id Hin) as [node [Hn Hnid]].
          exists node. split; [ apply Gthen_selse; exact Hn | exact Hnid ]. }
        assert (Hmen : forall k id, In (k, id) (var_map s_else) -> wnidwf s_else id).
        { intros k id Hin. destruct Pelse as [Hve _]. exact (Hve k id Hin). }
        assert (Hmts : forall k id,
                   In (k, id) (var_map s_then) -> wsz s_else id (dfg_var_size ctx k)).
        { intros k id Hin. eapply wsz_gmono; [ apply Qthen; exact Hin | exact Gthen_selse ]. }
        assert (Hmes : forall k id,
                   In (k, id) (var_map s_else) -> wsz s_else id (dfg_var_size ctx k)).
        { intros k id Hin. apply Qelse; exact Hin. }
        pose proof (merge_maps_fg cond_id (var_map s1) (var_map s_then) (var_map s_else)
                      s_else Pelse Qelse Felse Ncond Scond Hmtn Hmen Hmts Hmes) as Hmerge.
        destruct (merge_maps ctx cond_id (var_map s1) (var_map s_then) (var_map s_else)
                    s_else) as [final_vars s_final] eqn:Em.
        destruct Hmerge as [Gmerge [Pfinal [Qfinal [Ffinal [Nfinal Sfinal]]]]].
        rewrite (bind_red (merge_maps ctx cond_id (var_map s1) (var_map s_then)
                             (var_map s_else)) _ s_else _ _ Em).
        rewrite (bind_red (get_state ctx) _ s_final _ _ (get_state_red s_final)).
        set (sF := {| graph := graph s_final; var_map := final_vars |} : wst).
        rewrite (put_state_red sF s_final).
        intro Hg'.
        assert (GsF : wgmono s_final sF) by (intros n Hn; unfold sF; simpl; exact Hn).
        assert (Hg_final : wgmono s_final F)
          by exact (wgmono_trans s_final sF F GsF Hg').
        assert (Hg_else : wgmono s_else F)
          by exact (wgmono_trans s_else s_final F Gmerge Hg_final).
        assert (Hg_sR : wgmono sR F) by exact (wgmono_trans sR s_else F Gelse Hg_else).
        assert (Hg_then : wgmono s_then F)
          by exact (wgmono_trans s_then sR F Gthen_sR Hg_sR).
        assert (Hg_s1 : wgmono s1 F) by exact (wgmono_trans s1 s_then F Gthen Hg_then).
        destruct (dataflow_expr_sem cond 1 s s1 cond_id sp Hne Hinv Hvsz Ec Hg_s1 Hsem)
          as [Hsem1 Hvc].
        unfold nval in Hvc.
        assert (HsemR : sem_inv sR sp).
        { apply (sem_inv_vm s1 sR); [ unfold sR; simpl; reflexivity | exact Hsem1 ]. }
        destruct (Ht Hsem1 Hg_then) as [Hmt1 Hmtf1].
        destruct (Hels HsemR Hg_else) as [Hme1 Hmef1].
        assert (HvmF : var_map sF = final_vars) by (unfold sF; reflexivity).
        unfold sem_inv. rewrite HvmF.
        unfold tf_ops_run. cbn [tf_ops_updates].
        match goal with
        | |- context [ if ?B then _ else _ ] =>
            assert (Hb : forall szB E1 E2,
                       tf_eval_expr ss_sz i_sz oo_sz (szB := szB)
                         (tf_expr_if (node_ref_expr act a_idx cond_id) E1 E2) ss input
                       = if B then tf_eval_expr ss_sz i_sz oo_sz (szB := szB) E2 ss input
                              else tf_eval_expr ss_sz i_sz oo_sz (szB := szB) E1 ss input)
              by (intros szB E1 E2; cbn [tf_eval_expr]; rewrite Hvc; reflexivity);
            destruct B
        end.
        + refine (merge_maps_sem cond_id (var_map s1) (var_map s_then) (var_map s_else)
                    true _ _ _ s_else final_vars s_final Hb _
                    Hmt1 Hmtf1 Hme1 Hmef1 HneE Em Hg_final).
          intro kk. reflexivity.
        + refine (merge_maps_sem cond_id (var_map s1) (var_map s_then) (var_map s_else)
                    false _ _ _ s_else final_vars s_final Hb _
                    Hmt1 Hmtf1 Hme1 Hmef1 HneE Em Hg_final).
          intro kk. reflexivity.
    Qed.

  End DFGSem.

  (* The exported DFG is the reverse of the final builder state's graph, and
     shares its var_map verbatim. *)
  Lemma build_dfg_final (act: tfs_action sched) :
    exists (Fin: wst),
      dataflow_ops ctx (tfs_spec_action_ops ctx act)
        {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |}
        = (tt, Fin)
      /\ exports act Fin
      /\ var_map (build_dfg ctx act) = var_map Fin.
  Proof.
    unfold exports, build_dfg.
    destruct (dataflow_ops ctx (tfs_spec_action_ops ctx act)
                {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |})
      as [u final] eqn:Ed.
    destruct u. exists final.
    split; [ reflexivity | cbn [graph var_map]; split; reflexivity ].
  Qed.

  (* ==================================================================== *)
  (* Phase 3d: the DFG really computes the source action.  This says       *)
  (* nothing about the scheduler, buffers, validity bits or cycles —       *)
  (* purely that [build_dfg] followed by the BUFFER-FREE                   *)
  (* [compile_dfg_expr] reproduces the source semantics [tf_ops_run].      *)
  (* ==================================================================== *)
  Lemma dfg_action_semantics (act: tfs_action sched) a_idx
        (sp: src_sys_state) (ss: sched_sys_state) (input: input_t) :
    act_idx_aligned act a_idx ->
    (forall sv, (fst ss).[tf_dfg_s sv] = (fst sp).[sv]) ->
    (forall ov, (snd ss).[ov] = (snd sp).[ov]) ->
    let sp1 := tf_ops_run s_sz i_sz o_sz (tfs_spec_action_ops ctx act) sp input in
    (forall sv n, In (DFG_SVar sv, n) (var_map (build_dfg ctx act)) ->
        eval_st (tf_dfg_s sv)
          (fst (compile_dfg_expr ctx cost_limit
                  (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n []))
          ss input
        = (fst sp1).[sv])
    /\ (forall ov n, In (DFG_OVar ov, n) (var_map (build_dfg ctx act)) ->
        eval_out ov
          (fst (compile_dfg_expr ctx cost_limit
                  (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n []))
          ss input
        = (snd sp1).[ov])
    /\ (forall sv, (forall n, ~ In (DFG_SVar sv, n) (var_map (build_dfg ctx act))) ->
        (fst sp1).[sv] = (fst sp).[sv])
    /\ (forall ov, (forall n, ~ In (DFG_OVar ov, n) (var_map (build_dfg ctx act))) ->
        (snd sp1).[ov] = (snd sp).[ov]).
  Proof.
    intros Halign Hs Ho.
    destruct (build_dfg_final act) as [Fin [Ed [Hgr Hvm]]].
    assert (Hempty : winv {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ];
                            var_map := [] |}).
    { split; [ | split ].
      - intros k id Hin. destruct Hin.
      - unfold nid_seq. reflexivity.
      - intros a Ha x Hx. simpl in Ha. destruct Ha as [<-|[]]. simpl in Hx. destruct Hx. }
    assert (Hemvsz : wvsz {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ];
                            var_map := [] |}).
    { intros v id Hin. destruct Hin. }
    assert (Hemfg : wfg {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ];
                          var_map := [] |}).
    { intros node Hin. simpl in Hin. destruct Hin as [<-|[]].
      unfold node_args_sz. cbn [op]. exact I. }
    assert (Hne0 : 0 < length (graph ({| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ];
                                        var_map := [] |} : wst))).
    { cbn [graph]. simpl. apply Nat.lt_0_1. }
    pose proof (dataflow_ops_sem act a_idx ss input sp Fin Hgr Hs Ho
                  (tfs_spec_action_ops ctx act)
                  {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |}
                  sp Hne0 Hempty Hemvsz Hemfg
                  (sem_inv_empty act a_idx ss input sp
                     {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ];
                        var_map := [] |} eq_refl)) as Hmain.
    rewrite Ed in Hmain.
    destruct (Hmain (wgmono_refl Fin)) as [Hsem Hfr].
    cbv zeta. split; [ | split; [ | split ] ].
    - intros sv n Hin. rewrite Hvm in Hin. exact (Hsem (DFG_SVar sv) n Hin).
    - intros ov n Hin. rewrite Hvm in Hin. exact (Hsem (DFG_OVar ov) n Hin).
    - intros sv Hno. apply (Hfr (DFG_SVar sv)).
      intros n Hin. apply (Hno n). rewrite Hvm. exact Hin.
    - intros ov Hno. apply (Hfr (DFG_OVar ov)).
      intros n Hin. apply (Hno n). rewrite Hvm. exact Hin.
  Qed.

  (* PHASE 3 (correctness at done): once the done flag is set, the mapped
     final states and outputs match the one-shot source evaluation. *)
  Lemma scheduler_done_correct :
    forall (act: tfs_action sched) (sp0: src_sys_state)
           (ss0: sched_sys_state) (input: input_t) (N: nat),
      start_rel sp0 ss0 ->
      (forall k, k < N -> ~ done_set (run_n k act input ss0)) ->
      done_set (run_n N act input ss0) ->
      let sp1 := tf_ops_run s_sz i_sz o_sz (tfs_spec_action_ops ctx act) sp0 input in
      maps_from ctx cost_limit (fst (run_n N act input ss0)) = fst sp1 /\
      snd (run_n N act input ss0) = snd sp1.
  Proof.
    intros act sp0 ss0 input N [Hout0 [Hst0 Hzero0]] Hbefore Hdone.
    destruct (exists_act_idx act) as [a_idx Halign].
    (* N = 0 is impossible: start_rel clears the done flag *)
    destruct N as [| M].
    { exfalso. apply Hdone. cbn [run_n]. apply (Hzero0 (tfs_done_signal sched) I). }
    set (ssM := run_n M act input ss0) in *.
    change (run_n (S M) act input ss0) with (sched_step act ssM input) in *.
    assert (Hpre : forall i, 1 <= i <= M -> ~ done_set (run_n i act input ss0))
      by (intros i Hi; apply Hbefore; lia).
    (* the pre-done prefix leaves the base state and the outputs at sp0 *)
    assert (Hs : forall sv, (fst ssM).[tf_dfg_s sv] = (fst sp0).[sv]).
    { intro sv. unfold ssM. rewrite (run_preserves_svar act input ss0 M Hpre sv).
      rewrite <- Hst0, getenv_maps_from. reflexivity. }
    assert (Ho : forall ov, (snd ssM).[ov] = (snd sp0).[ov]).
    { intro ov. unfold ssM. rewrite (run_preserves_ovar act input ss0 M Hpre ov).
      rewrite Hout0. reflexivity. }
    (* the invariant holds at ssM *)
    assert (Hinv : valid_settled act a_idx ssM input).
    { apply valid_settled_run; [ exact Halign |].
      intro n_idx. apply (Hzero0 (tf_dfg_v a_idx n_idx) I). }
    (* drop the buffers from any var_map node's compiled expression *)
    assert (Hdrop : forall v n szB,
              In (v, n) (var_map (build_dfg ctx act)) ->
              szB = dfg_var_size ctx v ->
              tf_eval_expr ss_sz i_sz oo_sz (szB := szB)
                (fst (compile_dfg_expr ctx cost_limit
                        (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n
                        (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])))
                ssM input
              = tf_eval_expr ss_sz i_sz oo_sz (szB := szB)
                (fst (compile_dfg_expr ctx cost_limit
                        (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n []))
                ssM input).
    { intros v n szB Hin HszB.
      assert (Hmem : In n (map snd (var_map (build_dfg ctx act))))
        by (apply (in_map snd _ (v, n)); exact Hin).
      destruct (var_map_node_range act n Hmem) as [Hn1 Hnlen].
      apply (compile_subst_valid act a_idx ssM input Halign Hinv).
      - intros e He. exact He.
      - exact Hn1.
      - exact Hnlen.
      - exact Hnlen.
      - rewrite HszB. symmetry. exact (var_map_entry_size act v n Hin).
      - exact (sched_step_done_valid act a_idx ssM input n Halign Hdone Hmem). }
    destruct (dfg_action_semantics act a_idx sp0 ssM input Halign Hs Ho)
      as [Hsem_s [Hsem_o [Hfix_s Hfix_o]]].
    split.
    - apply equiv_eq. unfold equiv. intro sv.
      rewrite getenv_maps_from.
      destruct (find_pair_dec eq_dec (var_map (build_dfg ctx act)) (DFG_SVar sv))
        as [[n Hn] | Hno].
      + rewrite (sched_step_done_svar act a_idx ssM input sv n Halign Hdone Hn).
        rewrite (Hdrop (DFG_SVar sv) n (ss_sz (tf_dfg_s sv)) Hn eq_refl).
        exact (Hsem_s sv n Hn).
      + rewrite (sched_step_done_svar_untouched act a_idx ssM input sv Halign Hdone Hno).
        rewrite (Hfix_s sv Hno). exact (Hs sv).
    - apply equiv_eq. unfold equiv. intro ov.
      destruct (find_pair_dec eq_dec (var_map (build_dfg ctx act)) (DFG_OVar ov))
        as [[n Hn] | Hno].
      + rewrite (sched_step_done_ovar act a_idx ssM input ov n Halign Hdone Hn).
        rewrite (Hdrop (DFG_OVar ov) n (oo_sz ov) Hn eq_refl).
        exact (Hsem_o ov n Hn).
      + rewrite (sched_step_done_ovar_untouched act a_idx ssM input ov Halign Hdone Hno).
        rewrite (Hfix_o ov Hno). exact (Ho ov).
  Qed.

  (* ==================================================================== *)
  (* Top-level correctness: one source step = run scheduled until done.   *)
  (* ==================================================================== *)
  Theorem variable_scheduler_correct :
    forall (act: tfs_action sched) (sp0: src_sys_state)
           (ss0: sched_sys_state) (input: input_t),
      start_rel sp0 ss0 ->
      exists N,
        (forall k, k < N -> ~ done_set (run_n k act input ss0)) /\
        done_set (run_n N act input ss0) /\
        let sp1 := tf_ops_run s_sz i_sz o_sz (tfs_spec_action_ops ctx act) sp0 input in
        maps_from ctx cost_limit (fst (run_n N act input ss0)) = fst sp1 /\
        snd (run_n N act input ss0) = snd sp1.
  Proof.
    intros act sp0 ss0 input Hstart.
    destruct (scheduler_reaches_done act sp0 ss0 input Hstart) as [N [Hbefore Hdone]].
    exists N. split; [ exact Hbefore |]. split; [ exact Hdone |].
    apply (scheduler_done_correct act sp0 ss0 input N Hstart Hbefore Hdone).
  Qed.

End SchedulerSimulation.

(* Sanity check: the top-level theorem must depend on no axioms and no
   admitted lemmas. *)
Print Assumptions variable_scheduler_correct.
