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

(* Structural facts about [find_st_update] over an append, proved against an
   ABSTRACT schedule: over the concrete record each [Qed] costs ~6 s, since the
   kernel unfolds it while re-checking the induction. *)
Section FindUpdateAppend.
  Context (SCH: TFSchedule).

  Hint Extern 0 (FiniteType (tfs_states SCH)) => exact (tfs_states_fin SCH)
    : typeclass_instances.
  Hint Extern 0 (FiniteType (tfs_outputs SCH)) => exact (tfs_outputs_fin SCH)
    : typeclass_instances.

  Local Notation upd :=
    (tf_update (tfs_states_size SCH) (tfs_outputs_size SCH)).

  Lemma find_st_update_app_None_gen (x: tfs_states SCH) (ups1 ups2: list upd) :
    find_st_update SCH x ups1 = None ->
    find_st_update SCH x (ups1 ++ ups2) = find_st_update SCH x ups2.
  Proof.
    induction ups1 as [| u ups1 IH]; intro Hnone.
    - reflexivity.
    - cbn [app]. destruct u as [| var val | var val];
        cbn [find_st_update] in *.
      + apply IH, Hnone.
      + destruct (eq_dec var x) as [Heq | Hneq]; [ discriminate | apply IH, Hnone ].
      + apply IH, Hnone.
  Qed.

  Lemma find_st_update_app_Some_gen (x: tfs_states SCH) (ups1 ups2: list upd) v :
    find_st_update SCH x ups1 = Some v ->
    find_st_update SCH x (ups1 ++ ups2) = Some v.
  Proof.
    induction ups1 as [| u ups1 IH]; intro Hsome; cbn [app] in *.
    - discriminate.
    - destruct u as [| var val | var val];
        cbn [find_st_update] in *.
      + apply IH, Hsome.
      + destruct (eq_dec var x) as [Heq | Hneq]; [ exact Hsome | apply IH, Hsome ].
      + apply IH, Hsome.
  Qed.

End FindUpdateAppend.

(* The scheduler record is huge; deprioritise unfolding it during conversion. *)
Strategy 1000 [tfs_schedule].

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
  (* Scheduled states are tf_dfg_states; outputs coincide with the spec's, and
     the inputs are the spec's PLUS one response channel per IP. *)
  Hint Extern 0 (FiniteType (tfs_states sched))  => exact (tfs_states_fin sched)  : typeclass_instances.
  Hint Extern 0 (FiniteType (tfs_outputs sched)) => exact (tfs_outputs_fin sched) : typeclass_instances.

  Local Notation sched_st_env  := (ContextEnv.(env_t) (tf_states_type (tfs_states_size sched))).
  Local Notation sched_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation sched_sys_state := (sched_st_env * sched_out_env)%type.

  Local Notation p_var  := (tfs_spec_ips ctx).
  (* The buffer table, computed once: recomputing it per use is what made the
     MARS build time out. *)
  Local Notation bneeds := (buffer_needs ctx cost_limit).
  Local Notation si_var := (tfs_inputs sched).
  Local Notation si_sz  := (tfs_inputs_size sched).

  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).
  Local Notation sched_input_t :=
    (forall x : tfs_inputs sched, type_denote (tf_inputs_type (tfs_inputs_size sched) x)).

  (* ---- The attached IP, as the scheduled model sees it ---- *)

  (* [tf_dfg_ov p] carries {strobe, payload} with the payload in the low bits,
     and holds a request's payload from its pulse until the next one. *)
  Definition drive_payload (ss: sched_sys_state) (p: tfs_ips sched)
    : bits_t (ip_req_sz (tfs_ip sched p)) :=
    Bits.slice 0 (ip_req_sz (tfs_ip sched p))
      ((fst ss).[tfs_drive_reg sched p]).

  (* A [DFG_Sample] reads the response wire LIVE, and the stall holds the request
     on the port until it does, so the answer available in a state is [ip_fn] of
     that state's driven payload.  Two calls on one IP therefore get two
     different answers, which a response fixed across the run could not give. *)
  Definition sched_input (input: input_t) (ss: sched_sys_state) : sched_input_t :=
    fun x => match x with
             | inl v => input v
             | inr p => ip_fn (tfs_ip sched p) (drive_payload ss p)
             end.

  (* ---- One scheduled cycle and its bounded iteration ---- *)
  Definition sched_step (act: tfs_action sched) (ss: sched_sys_state) (input: sched_input_t)
    : sched_sys_state :=
    tfs_next_cycle sched act ss input.

  (* The response is re-derived from the state each cycle, which is what lets
     two calls on one IP see two different answers. *)
  Fixpoint run_n (n: nat) (act: tfs_action sched) (input: input_t) (ss: sched_sys_state)
    : sched_sys_state :=
    match n with
    | 0 => ss
    | S k => let ss1 := run_n k act input ss in
             sched_step act ss1 (sched_input input ss1)
    end.

  (* ==================================================================== *)
  (* Phase 1: concrete characterization of ONE scheduled cycle.           *)
  (* ==================================================================== *)

  (* The list of updates a single cycle selects (mirrors the inline `updates`
     let inside tfs_next_cycle): always-updates unconditionally, plus the
     reset+done updates when the done flag fired this cycle. *)
  Definition cycle_updates (act: tfs_action sched) (ss: sched_sys_state) (input: sched_input_t) :=
    let always_updates := tfs_get_updates sched (fst (Contract.tfs_schedule sched act)) ss input in
    let done_updates   := tfs_get_updates sched (snd (Contract.tfs_schedule sched act)) ss input in
    let reset_updates  := tfs_reset_updates sched (tfs_reset_states sched) in
    let done_val := find_st_val sched (tfs_done_signal sched) always_updates ss in
    if beq_dec done_val Bits.zero then always_updates
    else reset_updates ++ done_updates ++ always_updates.

  (* One cycle, expressed as create over find_{st,out}_val of the selected updates. *)
  Lemma sched_step_eq (act: tfs_action sched) (ss: sched_sys_state) (input: sched_input_t) :
    sched_step act ss input =
    ( ContextEnv.(create) (fun x => find_st_val  sched x (cycle_updates act ss input) ss),
      ContextEnv.(create) (fun x => find_out_val sched x (cycle_updates act ss input) ss) ).
  Proof.
    unfold sched_step, tfs_next_cycle, cycle_updates. reflexivity.
  Qed.

  (* Reading a state register after one cycle. *)
  Lemma sched_step_getst (act: tfs_action sched) (ss: sched_sys_state) (input: sched_input_t) x :
    (fst (sched_step act ss input)).[x] =
    find_st_val sched x (cycle_updates act ss input) ss.
  Proof. rewrite sched_step_eq. cbn [fst]. rewrite getenv_create. reflexivity. Qed.

  (* Reading an output register after one cycle. *)
  Lemma sched_step_getout (act: tfs_action sched) (ss: sched_sys_state) (input: sched_input_t) x :
    (snd (sched_step act ss input)).[x] =
    find_out_val sched x (cycle_updates act ss input) ss.
  Proof. rewrite sched_step_eq. cbn [snd]. rewrite getenv_create. reflexivity. Qed.

  (* ---- Generic find_{st,out}_update reductions over tfs_get_updates ---- *)

  Local Notation ss_sz := (tfs_states_size sched).
  Local Notation oo_sz := (tfs_outputs_size sched).
  Local Notation eval_st  dst e ss input :=
    (tf_eval_expr ss_sz si_sz oo_sz (szB := ss_sz dst) e ss input).
  Local Notation eval_out dst e ss input :=
    (tf_eval_expr ss_sz si_sz oo_sz (szB := oo_sz dst) e ss input).

  (* tfs_get_updates is a map, so it peels one op at a time. *)
  Lemma tfs_get_updates_cons (op: @tf_op (tfs_states sched) si_var o_var Empty_set) ops ss input :
    tfs_get_updates sched (op :: ops) ss input =
    tf_op_step_updates ss_sz si_sz oo_sz no_ips op ss input :: tfs_get_updates sched ops ss input.
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
    intros Hne.
    destruct u as [| var val | var val];
      cbn [find_st_update]; try reflexivity.
    - destruct (eq_dec var x) as [Heq | Hneq].
      + exfalso. subst var. eapply Hne. reflexivity.
      + reflexivity.
  Qed.

  (* Predicate: op writes state x.  A lowered schedule is over [Empty_set] IPs,
     so no call can occur in one and neither predicate carries a call disjunct. *)
  Definition op_assigns_st (x: tfs_states sched)
      (op: @tf_op (tfs_states sched) si_var o_var Empty_set) : Prop :=
    exists e, op = tf_assign x e.
  (* Predicate: op writes output x. *)
  Definition op_writes_out (x: o_var)
      (op: @tf_op (tfs_states sched) si_var o_var Empty_set) : Prop :=
    exists e, op = tf_output x e.
  (* find_st_update skips a head op that does not assign the queried state. *)
  Lemma find_st_update_skip_head x (op: @tf_op (tfs_states sched) si_var o_var Empty_set) ops ss input :
    ~ op_assigns_st x op ->
    find_st_update sched x (tfs_get_updates sched (op :: ops) ss input)
    = find_st_update sched x (tfs_get_updates sched ops ss input).
  Proof.
    intro Hne. rewrite tfs_get_updates_cons. apply find_st_update_skip_cons.
    intro v. destruct op as [| dst e | dst e | ip dst e];
      cbn [tf_op_step_updates]; try discriminate; try destruct ip.
    intro H. inversion H. subst dst. apply Hne. exists e. reflexivity.
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
    intros Hne.
    destruct u as [| var val | var val];
      cbn [find_out_update]; try reflexivity.
    - destruct (eq_dec var x) as [Heq | Hneq].
      + exfalso. subst var. eapply Hne. reflexivity.
      + reflexivity.
  Qed.

  (* find_out_update skips a head op that does not output the queried var. *)
  Lemma find_out_update_skip_head x (op: @tf_op (tfs_states sched) si_var o_var Empty_set) ops ss input :
    ~ op_writes_out x op ->
    find_out_update sched x (tfs_get_updates sched (op :: ops) ss input)
    = find_out_update sched x (tfs_get_updates sched ops ss input).
  Proof.
    intro Hne. rewrite tfs_get_updates_cons. apply find_out_update_skip_cons.
    intro v. destruct op as [| dst e | dst e | ip dst e];
      cbn [tf_op_step_updates]; try discriminate; try destruct ip.
    intro H. inversion H. subst dst. apply Hne. exists e. reflexivity.
  Qed.


  (* If no op in the list assigns x, find_st_update returns None. *)
  Lemma find_st_update_not_in x ops ss input :
    (forall op, In op ops -> ~ op_assigns_st x op) ->
    find_st_update sched x (tfs_get_updates sched ops ss input) = None.
  Proof.
    induction ops as [| op ops IH]; intro Hnone.
    - reflexivity.
    - rewrite find_st_update_skip_head.
      + apply IH. intros op' Hin. apply Hnone. now right.
      + apply (Hnone op). now left.
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
    - destruct op as [| dst rhs | dst rhs | ip dst rhs].
      + apply IH; [ exact Hnd | exact Hin ].
      + inversion Hnd as [| tag tags Hnot Htail]; subst tag tags.
        destruct (eq_dec dst x) as [Hdx | Hdx].
        * subst dst. exfalso. apply Hnot. apply in_flat_map.
          exists (tf_assign x e). split; [ exact Hin |]. cbn [In]. left. reflexivity.
        * rewrite find_st_update_skip_head.
          -- apply IH; [ exact Htail | exact Hin ].
          -- intros [rhs' Heq]; inversion Heq; contradiction.
      + apply IH.
        * cbn [app] in Hnd. inversion Hnd. assumption.
        * exact Hin.
      + destruct ip.
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
      + intro Hw. exact (Hnone op (or_introl eq_refl) Hw).
  Qed.

  (* Raw-update version: if no update in the list targets state x, find is None. *)
  Lemma find_st_update_not_in_raw x (ups: list (tf_update ss_sz oo_sz)) :
    (forall u, In u ups -> forall val, u <> tf_st_update ss_sz oo_sz x val) ->
    find_st_update sched x ups = None.
  Proof.
    induction ups as [| u ups IH]; intro Hnone.
    - reflexivity.
    - rewrite find_st_update_skip_cons.
      + apply IH. intros u2 Hin. apply Hnone. now right.
      + intro val. eapply Hnone. now left.
  Qed.

  (* ---- Concrete shape of the compiled op lists for the variable scheduler ---- *)

  (* find_st_update over an append: if the prefix has no match, skip it. *)
  Local Notation find_st_update_app_None := (find_st_update_app_None_gen sched).

  (* The reset states are only buffer/valid registers, never the done flag. *)
  Lemma reset_states_not_done v :
    In v (reset_states ctx bneeds) -> v <> done_signal ctx bneeds.
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
    assert (Hrs: tfs_reset_states sched = reset_states ctx bneeds) by reflexivity.
    assert (Hds: tfs_done_signal sched = done_signal ctx bneeds) by reflexivity.
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
      = tf_assign (tfs_done_signal sched) (combine_valid_exprs ctx bneeds exprs) :: rest.
  Proof.
    unfold sched, tfs_schedule, tfs_schedule_bn, Contract.tfs_schedule, tfs_done_signal, done_signal.
    unfold schedule. cbv zeta. cbn [fst].
    unfold compile_dfg_valid. cbv zeta.
    eexists. eexists. reflexivity.
  Qed.

  (* The done-ops (final state/output writes) never assign the done flag. *)
  Lemma done_ops_no_done (act: tfs_action sched) (ss: sched_sys_state) (input: sched_input_t) :
    find_st_update sched (tfs_done_signal sched)
      (tfs_get_updates sched (snd (Contract.tfs_schedule sched act)) ss input) = None.
  Proof.
    (* The shape of [op] is derived from [Hin] first, then discriminated. *)
    apply find_st_update_not_in. intros op Hin Hass. revert Hass. revert Hin.
    unfold sched, tfs_schedule, tfs_schedule_bn, Contract.tfs_schedule, schedule.
    cbv zeta. cbn [snd]. unfold compile_dfg_aux. cbv zeta.
    destruct (index_of_nat _ _) as [a2 |]; [| intros []].
    rewrite in_map_iff. intros [[var nid] [Hop _]].
    match goal with
    | H : context [compile_dfg_expr_aux ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j] |- _ =>
        destruct (compile_dfg_expr_aux a b c d e f g h i j) as [expr valid]
    end.
    destruct var as [sv | ov]; subst op; intros [e He]; inversion He.
  Qed.

  (* The done value produced by one cycle equals the always-list done value,
     regardless of whether the reset/done prefix fired (neither touches done). *)
  Lemma cycle_done_val (act: tfs_action sched) (ss: sched_sys_state) (input: sched_input_t) :
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
  Lemma sched_step_done (act: tfs_action sched) (ss: sched_sys_state) (input: sched_input_t) :
    (fst (sched_step act ss input)).[tfs_done_signal sched]
    = find_st_val sched (tfs_done_signal sched)
        (tfs_get_updates sched (fst (Contract.tfs_schedule sched act)) ss input) ss.
  Proof. rewrite sched_step_getst. apply cycle_done_val. Qed.

  (* ---- Semantics of the compiled combined-validity expression ---- *)

  Local Notation eval1 e ss input :=
    (tf_eval_expr ss_sz si_sz oo_sz (szB := 1) e ss input).

  (* The size-1 constant `1` evaluates to the all-ones (single true) bit. *)
  Lemma eval1_const1 (ss: sched_sys_state) (input: sched_input_t) :
    eval1 (tf_const 1) ss input = Bits.ones 1.
  Proof. reflexivity. Qed.

  (* Reading a size-1 validity register through tf_svar is the register itself
     (the convert cast at szA = szB = 1 is the identity). *)
  Lemma eval1_svar_v (ss: sched_sys_state) (input: sched_input_t)
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

  (* [Bits.app hi lo] puts [lo] at the low indices, so the low slice of a
     concatenation gives it back.  The drive register is {strobe, payload}. *)
  Lemma slice_app_lo {hs ls} (hi: bits_t hs) (lo: bits_t ls) :
    Bits.slice 0 ls (Bits.app hi lo) = lo.
  Proof.
    apply (vect_to_list_inj bool ls).
    rewrite (BitsToLists.slice (ls + hs) (Bits.app hi lo) 0 ls).
    unfold BitsToLists.take_drop'. cbn [List.firstn List.skipn].
    rewrite Nat.sub_0_r, Nat.min_l by lia.
    rewrite Nat.sub_diag. cbn [repeat]. rewrite List.app_nil_r.
    rewrite vect_to_list_app, List.firstn_app.
    rewrite List.firstn_all2 by (rewrite vect_to_list_length; lia).
    rewrite vect_to_list_length, Nat.sub_diag. cbn [List.firstn].
    apply List.app_nil_r.
  Qed.

  (* A cast between propositionally equal widths survives a low slice. *)
  Lemma slice_convert_eq {szA szB} (x: bits_t szA) (w: nat) :
    szA = szB ->
    Bits.slice 0 w (Semantics.convert (szB := szB) x) = Bits.slice 0 w x.
  Proof.
    intro e. subst szB. rewrite convert_same. reflexivity.
  Qed.

  (* The payload half, as a slice of the named register. *)
  Lemma drive_payload_slice (p: p_var) (ss: sched_sys_state) :
    drive_payload ss p
    = Bits.slice 0 (ip_req_sz (tfs_spec_ip ctx p)) ((fst ss).[tf_dfg_ov p]).
  Proof. reflexivity. Qed.

  (* The payload half of a drive register is what [tf_svar] reads at the request
     width: the cast down from [1 + req] is exactly that slice. *)
  Lemma drive_payload_eval (p: p_var) (ss: sched_sys_state) (input: sched_input_t) :
    drive_payload ss p
    = tf_eval_expr ss_sz si_sz oo_sz (szB := ip_req_sz (tfs_spec_ip ctx p))
        (tf_svar (tf_dfg_ov p)) ss input.
  Proof.
    cbn [tf_eval_expr]. unfold Semantics.convert, drive_payload.
    destruct (eq_dec (ss_sz (tf_dfg_ov p)) (ip_req_sz (tfs_spec_ip ctx p))) as [e | ne].
    - exfalso. cbn in e. lia.
    - reflexivity.
  Qed.

  (* Reading any state register through tf_svar at its OWN size is the register
     itself (convert is the identity when szB = ss_sz v). *)
  Lemma eval_svar_same (v: tfs_states sched) (ss: sched_sys_state) (input: sched_input_t) :
    tf_eval_expr ss_sz si_sz oo_sz (szB := ss_sz v) (tf_svar v) ss input = (fst ss).[v].
  Proof.
    cbn [tf_eval_expr]. apply convert_same.
  Qed.

  (* Eval/convert commute at a state-variable leaf: [tf_svar v] read at its own
     size then converted to [szB] equals reading it at [szB].  The (star)
     obligation for a buffered DFG_Var node, whose size is [ss_sz v]. *)
  Lemma eval_convert_svar (v: tfs_states sched) (szB: nat)
        (ss: sched_sys_state) (input: sched_input_t) :
    Semantics.convert (szA := ss_sz v) (szB := szB)
      (tf_eval_expr ss_sz si_sz oo_sz (szB := ss_sz v) (tf_svar v) ss input)
    = tf_eval_expr ss_sz si_sz oo_sz (szB := szB) (tf_svar v) ss input.
  Proof.
    rewrite eval_svar_same. reflexivity.
  Qed.

  (* Same commutation for an input leaf [tf_ivar v]. *)
  Lemma eval_convert_ivar (v: si_var) (szB: nat)
        (ss: sched_sys_state) (input: sched_input_t) :
    Semantics.convert (szA := si_sz v) (szB := szB)
      (tf_eval_expr ss_sz si_sz oo_sz (szB := si_sz v) (tf_ivar v) ss input)
    = tf_eval_expr ss_sz si_sz oo_sz (szB := szB) (tf_ivar v) ss input.
  Proof.
    cbn [tf_eval_expr]. rewrite convert_same. reflexivity.
  Qed.

  (* Same commutation for an output leaf [tf_ovar v]. *)
  Lemma eval_convert_ovar (v: o_var) (szB: nat)
        (ss: sched_sys_state) (input: sched_input_t) :
    Semantics.convert (szA := oo_sz v) (szB := szB)
      (tf_eval_expr ss_sz si_sz oo_sz (szB := oo_sz v) (tf_ovar v) ss input)
    = tf_eval_expr ss_sz si_sz oo_sz (szB := szB) (tf_ovar v) ss input.
  Proof.
    cbn [tf_eval_expr]. rewrite convert_same. reflexivity.
  Qed.


  (* ---- The stall counter's arithmetic ---- *)

  (* One increment of a counter that has not yet saturated.  [counter_sz l] is
     [S (log2 l)] bits, which holds 0 .. l-1 with room to spare, so no
     wrap-around happens before the counter reaches [pred l]. *)
  Lemma bits_plus_one_to_nat (sz: nat) (b: bits_t sz) :
    S (Bits.to_nat b) < pow2 sz ->
    Bits.to_nat (Bits.plus b (Bits.of_nat sz 1)) = S (Bits.to_nat b).
  Proof.
    intro Hlt.
    assert (Hone : (1 < 2 ^ N.of_nat sz)%N).
    { pose proof (Bits.nat_lt_pow2_N sz 1 ltac:(lia)) as H. cbn in H. exact H. }
    assert (HbN : Bits.to_N b = N.of_nat (Bits.to_nat b))
      by (unfold Bits.to_nat; rewrite N2Nat.id; reflexivity).
    assert (Hsum : (Bits.to_N b + N.of_nat 1 < 2 ^ N.of_nat sz)%N).
    { rewrite HbN.
      replace (N.of_nat (Bits.to_nat b) + N.of_nat 1)%N
        with (N.of_nat (S (Bits.to_nat b))) by lia.
      exact (Bits.nat_lt_pow2_N sz _ Hlt). }
    unfold Bits.plus, Bits.of_nat, Bits.to_nat.
    rewrite (Bits.to_N_of_N (N.of_nat 1) sz ltac:(cbn; exact Hone)).
    rewrite (Bits.to_N_of_N _ sz Hsum).
    rewrite HbN, <- Nat2N.inj_add, Nat2N.id. lia.
  Qed.

  Lemma bits_to_nat_inj (sz: nat) (x y: bits_t sz) :
    Bits.to_nat x = Bits.to_nat y -> x = y.
  Proof.
    unfold Bits.to_nat. intro H. apply Bits.to_N_inj. apply N2Nat.inj. exact H.
  Qed.

  (* [counter_sz l] is wide enough for the counter to reach [pred l]. *)
  Lemma pred_lt_counter_sz (l: nat) : 1 <= l -> pred l < pow2 (counter_sz l).
  Proof.
    intro Hl. unfold counter_sz. rewrite pow2_correct.
    pose proof (Nat.log2_spec l ltac:(lia)) as [_ Hub]. lia.
  Qed.

  (* A SATURATING COUNTER, as arithmetic: zero at the start, advancing whenever
     [adv] holds and it has not yet reached [top], never past [top].  Once [adv]
     holds from cycle [r] on, it reads [top] from cycle [r + top] on.  This is
     the shape [compile_dfg_buffers] gives a stall's buffer. *)
  Lemma counter_saturates (sz top r K: nat) (b: nat -> bits_t sz) (adv: nat -> bool) :
    top < pow2 sz ->
    Bits.to_nat (b 0) = 0 ->
    (forall j, j < K -> Bits.to_nat (b j) <= top ->
               Bits.to_nat (b (S j))
               = if andb (adv j) (negb (Nat.eqb (Bits.to_nat (b j)) top))
                 then S (Bits.to_nat (b j)) else Bits.to_nat (b j)) ->
    (forall j, r <= j < K -> adv j = true) ->
    forall k, r + top <= k <= K -> Bits.to_nat (b k) = top.
  Proof.
    intros Htop Hzero Hrec Hadv.
    (* it never passes [top] *)
    assert (Hle : forall j, j <= K -> Bits.to_nat (b j) <= top).
    { intro j. induction j as [| j IHj]; intro Hj; [ lia |].
      rewrite (Hrec j ltac:(lia) (IHj ltac:(lia))).
      destruct (andb _ _) eqn:Hc; [| apply IHj; lia ].
      apply andb_prop in Hc. destruct Hc as [_ Hne].
      apply negb_true_iff, Nat.eqb_neq in Hne.
      pose proof (IHj ltac:(lia)). lia. }
    (* from [r] on it gains at least one per cycle until it saturates *)
    assert (Hge : forall i, r + i <= K -> Nat.min i top <= Bits.to_nat (b (r + i))).
    { intro i. induction i as [| i IHi]; intro Hi; [ lia |].
      replace (r + S i) with (S (r + i)) by lia.
      rewrite (Hrec (r + i) ltac:(lia) (Hle (r + i) ltac:(lia))),
              (Hadv (r + i) ltac:(lia)). cbn [andb].
      destruct (Nat.eqb (Bits.to_nat (b (r + i))) top) eqn:Heq.
      - apply Nat.eqb_eq in Heq. cbn [negb]. lia.
      - apply Nat.eqb_neq in Heq. cbn [negb].
        pose proof (Hle (r + i) ltac:(lia)). pose proof (IHi ltac:(lia)). lia. }
    intros k Hk.
    pose proof (Hge top ltac:(lia)) as Hg. pose proof (Hle k ltac:(lia)) as Hl.
    assert (Hmono : forall j j2, j <= j2 -> j2 <= K ->
                    Bits.to_nat (b j) <= Bits.to_nat (b j2)).
    { intros j j2 Hjj. induction Hjj as [| j2 Hjj IHjj]; intro HK; [ lia |].
      rewrite (Hrec j2 ltac:(lia) (Hle j2 ltac:(lia))).
      pose proof (IHjj ltac:(lia)). destruct (andb _ _); lia. }
    pose proof (Hmono (r + top) k ltac:(lia) ltac:(lia)). lia.
  Qed.

  Lemma valid_and_eval
    (e1 e2: @tf_expr (tfs_states sched) si_var o_var) (ss: sched_sys_state) (input: sched_input_t) :
    eval1 (valid_expr_and ctx bneeds e1 e2) ss input
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
    (cond t e: @tf_expr (tfs_states sched) si_var o_var) (ss: sched_sys_state) (input: sched_input_t) :
    eval1 t ss input = Bits.ones 1 ->
    eval1 e ss input = Bits.ones 1 ->
    eval1 (valid_expr_if ctx bneeds cond t e) ss input = Bits.ones 1.
  Proof.
    intros Ht He.
    assert (Hcase: valid_expr_if ctx bneeds cond t e = tf_const 1
                   \/ valid_expr_if ctx bneeds cond t e = tf_expr_if cond t e).
    { unfold valid_expr_if.
      destruct t as [vt| | | | | |]; try (right; reflexivity).
      destruct vt as [|[|vt]]; try (right; reflexivity).
      destruct e as [ve| | | | | |]; try (right; reflexivity).
      destruct ve as [|[|ve]]; try (right; reflexivity).
      left; reflexivity. }
    destruct Hcase as [Hc | Hc]; rewrite Hc.
    - apply eval1_const1.
    - cbn [tf_eval_expr].
      destruct (beq_dec (tf_eval_expr ss_sz si_sz oo_sz (szB := 1) cond ss input) Bits.zero).
      + exact He.
      + exact Ht.
  Qed.

  (* One branch is enough when it is the one the condition SELECTS: the
     collapsed form needs neither, and the runtime form reads only that one. *)
  Lemma valid_if_eval_sel
    (cond t e: @tf_expr (tfs_states sched) si_var o_var) (ss: sched_sys_state) (input: sched_input_t) :
    (eval1 cond ss input <> Bits.zero -> eval1 t ss input = Bits.ones 1) ->
    (eval1 cond ss input = Bits.zero -> eval1 e ss input = Bits.ones 1) ->
    eval1 (valid_expr_if ctx bneeds cond t e) ss input = Bits.ones 1.
  Proof.
    intros Ht He.
    assert (Hcase: valid_expr_if ctx bneeds cond t e = tf_const 1
                   \/ valid_expr_if ctx bneeds cond t e = tf_expr_if cond t e).
    { unfold valid_expr_if.
      destruct t as [vt| | | | | |]; try (right; reflexivity).
      destruct vt as [|[|vt]]; try (right; reflexivity).
      destruct e as [ve| | | | | |]; try (right; reflexivity).
      destruct ve as [|[|ve]]; try (right; reflexivity).
      left; reflexivity. }
    destruct Hcase as [Hc | Hc]; rewrite Hc.
    - apply eval1_const1.
    - cbn [tf_eval_expr].
      destruct (beq_dec (tf_eval_expr ss_sz si_sz oo_sz (szB := 1) cond ss input)
                  Bits.zero) eqn:Hb.
      + apply He. exact (proj1 (beq_dec_iff _ _ _) Hb).
      + apply Ht. intro Hz.
        change (tf_eval_expr ss_sz si_sz oo_sz (szB := 1) cond ss input)
          with (eval1 cond ss input) in Hb.
        rewrite Hz, beq_dec_refl in Hb. discriminate.
  Qed.

  (* The compiled combined-validity expression evaluates to the AND-fold of the
     individual validity exprs (base case = all-ones for the empty conjunction). *)
  Lemma combine_valid_eval
    (exprs: list (@tf_expr (tfs_states sched) si_var o_var)) (ss: sched_sys_state) (input: sched_input_t) :
    eval1 (combine_valid_exprs ctx bneeds exprs) ss input
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

  Lemma ones1_neq_zero : Bits.ones 1 <> Bits.zero.
  Proof. apply (proj2 (bits1_nonzero_ones (Bits.ones 1))). reflexivity. Qed.

  Lemma bits1_and_split (a b: bits_t 1) :
    Bits.and a b = Bits.ones 1 -> a = Bits.ones 1 /\ b = Bits.ones 1.
  Proof.
    intro H.
    destruct (bits1_cases a) as [Ha | Ha]; destruct (bits1_cases b) as [Hb | Hb];
      subst; try (split; reflexivity); exfalso; vm_compute in H; discriminate.
  Qed.

  Lemma bits1_and_not_ones (a: bits_t 1) :
    Bits.and a (Bits.neg (Bits.ones 1)) = Bits.zero.
  Proof. destruct (bits1_cases a) as [-> | ->]; vm_compute; reflexivity. Qed.

  Lemma bits1_and_zero_r (a: bits_t 1) : Bits.and a Bits.zero = Bits.zero.
  Proof. destruct (bits1_cases a) as [-> | ->]; vm_compute; reflexivity. Qed.

  Lemma bits1_and_zero_l (a: bits_t 1) : Bits.and Bits.zero a = Bits.zero.
  Proof. destruct (bits1_cases a) as [-> | ->]; vm_compute; reflexivity. Qed.

  Lemma bits1_neg_ones : Bits.neg (Bits.ones 1) = Bits.zero.
  Proof. vm_compute. reflexivity. Qed.

  Lemma bits1_neg_ones_inv (a: bits_t 1) : Bits.neg a = Bits.ones 1 -> a = Bits.zero.
  Proof.
    destruct (bits1_cases a) as [-> | ->];
      [ intro H; vm_compute in H; discriminate | reflexivity ].
  Qed.

  (* Converse of valid_if_eval: a valid_expr_if that fires tells us the
     SELECTED branch is valid (and if it collapsed to [tf_const 1], both
     branches were literally [tf_const 1], hence valid). *)
  Lemma valid_if_eval_inv
    (cond t e: @tf_expr (tfs_states sched) si_var o_var) (ss: sched_sys_state) (input: sched_input_t) :
    eval1 (valid_expr_if ctx bneeds cond t e) ss input = Bits.ones 1 ->
    (eval1 cond ss input <> Bits.zero -> eval1 t ss input = Bits.ones 1) /\
    (eval1 cond ss input = Bits.zero -> eval1 e ss input = Bits.ones 1).
  Proof.
    intro H.
    assert (Hcase: (t = tf_const 1 /\ e = tf_const 1)
                   \/ valid_expr_if ctx bneeds cond t e = tf_expr_if cond t e).
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
  Lemma done_val_eval (act: tfs_action sched) (ss: sched_sys_state) (input: sched_input_t) :
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
  Lemma sched_step_done_set (act: tfs_action sched) (ss: sched_sys_state) (input: sched_input_t) :
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
  (* A stall's buffer is a COUNTER, so its start value is observable: the
     validity it publishes is "counter = lat-1".  The hardware resets it --
     [reset_states] lists [tf_dfg_b] beside [tf_dfg_v] and [maps_to] zeroes it
     -- so saying so here is reading the design, not strengthening it. *)
  Definition zeroed_at_start (x: tfs_states sched) : Prop :=
    match x with
    | tf_dfg_b _ _ => True
    | tf_dfg_v _ _ => True
    | tf_dfg_done  => True
    | _            => False
    end.

  (* Starting relation between a spec state and a scheduled state. *)
  Definition start_rel (sp: src_sys_state) (ss: sched_sys_state) : Prop :=
    snd ss = snd sp                                     (* outputs coincide *)
    /\ maps_from ctx bneeds (fst ss) = fst sp       (* tf_dfg_s slots = spec state *)
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
    (calc_target_cycle cost_limit (calc_backward_cost ctx cost_limit (build_dfg ctx act))).

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

  (* ---- What a DFG node is, as the buffer compiler asks ---- *)

  Definition node_op (act: tfs_action sched) (n: nid_t) :=
    op (nth n (graph (build_dfg ctx act)) {| nid := 0; op := DFG_Empty; sz := 0 |}).

  Definition stall_lat_of (act: tfs_action sched) (n: nid_t) : option nat :=
    match node_op act n with DFG_Stall l _ => Some l | _ => None end.

  Definition is_sample_of (act: tfs_action sched) (n: nid_t) : bool :=
    match node_op act n with DFG_Sample _ _ _ => true | _ => false end.

  (* The node a sample's REQUEST was built from: through its token, through the
     stall when the IP declares a latency, and through the ordering join when
     the call was sequenced behind an earlier one.  This mirrors what
     [dataflow_ops] emits for a [tf_call]. *)
  Definition sample_req_head (act: tfs_action sched) (h: nid_t) : option nid_t :=
    match node_op act h with
    | DFG_Drive _ a _ => Some a
    | DFG_Join d _ =>
        match node_op act d with
        | DFG_Drive _ a _ => Some a
        | _ => None
        end
    | _ => None
    end.

  Definition sample_req (act: tfs_action sched) (n: nid_t) : option nid_t :=
    match node_op act n with
    | DFG_Sample _ tok _ =>
        match node_op act tok with
        | DFG_Stall _ h => sample_req_head act h
        | _ => sample_req_head act tok
        end
    | _ => None
    end.

  (* The DRIVE a sample.s request came from: [sample_req].s walk, stopped one
     node earlier and checked to be on the sample.s own port. *)
  Definition sample_drive_head (act: tfs_action sched) (p: p_var) (h: nid_t)
    : option nid_t :=
    match node_op act h with
    | DFG_Drive p' _ _ => if (tfs_spec_ips_eq_dec ctx).(eq_dec) p' p then Some h else None
    | DFG_Join d _ =>
        match node_op act d with
        | DFG_Drive p' _ _ => if (tfs_spec_ips_eq_dec ctx).(eq_dec) p' p then Some d else None
        | _ => None
        end
    | _ => None
    end.

  Definition sample_drive (act: tfs_action sched) (n: nid_t) : option nid_t :=
    match node_op act n with
    | DFG_Sample p tok _ =>
        match node_op act tok with
        | DFG_Stall _ h => sample_drive_head act p h
        | _ => sample_drive_head act p tok
        end
    | _ => None
    end.

  Lemma sample_drive_head_op (act: tfs_action sched) p h d :
    sample_drive_head act p h = Some d ->
    exists a en, node_op act d = DFG_Drive p a en.
  Proof.
    unfold sample_drive_head.
    destruct (node_op act h) eqn:Hh; try discriminate.
    - destruct ((tfs_spec_ips_eq_dec ctx).(eq_dec) p0 p) as [-> | Hne]; [| discriminate].
      intro Heq. injection Heq as <-. exists arg, en. exact Hh.
    - destruct (node_op act a) eqn:Ha; try discriminate.
      destruct ((tfs_spec_ips_eq_dec ctx).(eq_dec) p0 p) as [-> | Hne]; [| discriminate].
      intro Heq. injection Heq as <-. exists arg, en. exact Ha.
  Qed.

  (* The two walks agree: the drive [sample_drive] stops at is the one whose
     argument [sample_req] returns. *)
  Lemma sample_drive_req (act: tfs_action sched) n d p a en :
    sample_drive act n = Some d ->
    node_op act d = DFG_Drive p a en ->
    sample_req act n = Some a.
  Proof.
    unfold sample_drive, sample_req.
    destruct (node_op act n) eqn:Hn; try discriminate.
    assert (Hh : forall h, sample_drive_head act p0 h = Some d ->
              node_op act d = DFG_Drive p a en -> sample_req_head act h = Some a).
    { intros h. unfold sample_drive_head, sample_req_head.
      destruct (node_op act h) eqn:Hhh; try discriminate.
      - destruct ((tfs_spec_ips_eq_dec ctx).(eq_dec) p1 p0); [| discriminate].
        intros Heq Hd. injection Heq as <-. rewrite Hhh in Hd.
        injection Hd as _ <- _. reflexivity.
      - destruct (node_op act a0) eqn:Ha0; try discriminate.
        destruct ((tfs_spec_ips_eq_dec ctx).(eq_dec) p1 p0); [| discriminate].
        intros Heq Hd. injection Heq as <-. rewrite Ha0 in Hd.
        injection Hd as _ <- _. reflexivity. }
    destruct (node_op act tok) eqn:Ht; apply Hh.
  Qed.

  Lemma sample_drive_op (act: tfs_action sched) n d p tok en :
    node_op act n = DFG_Sample p tok en ->
    sample_drive act n = Some d ->
    exists a en', node_op act d = DFG_Drive p a en'.
  Proof.
    intros Hn Hd. unfold sample_drive in Hd. rewrite Hn in Hd.
    destruct (node_op act tok) eqn:Ht;
      exact (sample_drive_head_op act p _ d Hd).
  Qed.

  (* A node that carries an op at all is inside the graph. *)
  Lemma node_op_range (act: tfs_action sched) n :
    node_op act n <> DFG_Empty -> n < length (graph (build_dfg ctx act)).
  Proof.
    unfold node_op. intro Hne.
    destruct (Nat.ltb n (length (graph (build_dfg ctx act)))) eqn:Hlt;
      [ apply Nat.ltb_lt; exact Hlt |].
    exfalso. apply Nat.ltb_ge in Hlt.
    rewrite nth_overflow in Hne by exact Hlt. cbn [op] in Hne.
    apply Hne. reflexivity.
  Qed.

  (* SATURATION RANK.  Ranking by node id alone is unsound in V4: a stall makes
     its consumer wait [lat] cycles, not one.  The rank is the id plus the extra
     cycles every stall UP TO AND INCLUDING it costs -- including its own, so a
     stall's rank already covers its wait and everything above it sits past it. *)
  Definition stall_weight (act: tfs_action sched) (n: nid_t) : nat :=
    match stall_lat_of act n with Some l => pred l | None => 0 end.

  Fixpoint node_rank (act: tfs_action sched) (n: nat) : nat :=
    match n with
    | 0 => stall_weight act 0
    | S m => S (node_rank act m) + stall_weight act (S m)
    end.

  Lemma node_rank_le act n : n <= node_rank act n.
  Proof. induction n as [| n IH]; cbn [node_rank]; lia. Qed.

  Lemma node_rank_mono act n n2 : n < n2 -> node_rank act n < node_rank act n2.
  Proof.
    revert n. induction n2 as [| n2 IH]; intros n Hlt; [ lia |].
    cbn [node_rank].
    destruct (Nat.eq_dec n n2) as [-> | Hne]; [ lia |].
    specialize (IH n ltac:(lia)). lia.
  Qed.

  Lemma node_rank_child act x n bound :
    x < n -> node_rank act n <= bound -> node_rank act x < bound.
  Proof. intros H1 H2. pose proof (node_rank_mono act x n H1). lia. Qed.

  Lemma node_rank_mono_le act n n2 : n <= n2 -> node_rank act n <= node_rank act n2.
  Proof.
    intro H. destruct (Nat.eq_dec n n2) as [-> | Hne]; [ lia |].
    pose proof (node_rank_mono act n n2 ltac:(lia)). lia.
  Qed.

  (* A stall ranks a full wait above its argument: that is the weight
     [stall_weight] adds, and it is what lets the counter saturate before the
     stall's own rank is reached. *)
  Lemma node_rank_stall act n arg l :
    stall_lat_of act n = Some l -> arg < n ->
    S (node_rank act arg) + pred l <= node_rank act n.
  Proof.
    intros Hst Harg. destruct n as [| m]; [ lia |].
    cbn [node_rank]. unfold stall_weight. rewrite Hst.
    pose proof (node_rank_mono_le act arg m ltac:(lia)). lia.
  Qed.

  (* nid of the DFG node cached by validity/value register (a_idx, n_idx). *)
  Definition vreg_nid
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (n_idx : Vect.index (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])))
    : nat :=
    fst (nth (index_to_nat n_idx)
             (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])
             (0, (0, 0))).

  (* The buffers a reference expression KEEPS: exactly the sample ones.  This
     is [guard_expr]'s [sbufs] -- "buffers are substituted only for samples,
     every other source is stable across the action".  A sample reads a LIVE
     wire and its buffer LATCHES, so inlining through one would compare a
     latched answer against whatever the port carries now; with two calls on a
     port those differ, and MARS's Quote has eight samples on one. *)
  Definition sample_bufs
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
    : list (nid_t * (nat * sz_t)) :=
    filter (fun '(n, _) => is_sample_of act n)
           (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []).

  (* Reference expression for DFG node n of act: inlined down to the sample
     buffers, which stand for the answers already received. *)
  Definition node_ref_expr
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (n: nat) : @tf_expr (tfs_states sched) si_var o_var :=
    fst (compile_dfg_expr ctx bneeds
           (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n
           (sample_bufs act a_idx)).

  (* The validity that goes with [node_ref_expr]: ones exactly when every sample
     buffer the reference reads has already latched. *)
  Definition node_ref_valid
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (n: nat) : @tf_expr (tfs_states sched) si_var o_var :=
    snd (compile_dfg_expr ctx bneeds
           (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n
           (sample_bufs act a_idx)).

  (* The GATE a buffer's validity register is assigned from: its own slot is
     removed from the table, since the register is what that slot feeds. *)
  Local Notation buf_gate act a_idx n_idx :=
    (snd (compile_dfg_expr ctx bneeds
            (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act)
            (vreg_nid a_idx n_idx)
            (filter (fun '(b_nid, _) => negb (Nat.eqb b_nid (vreg_nid a_idx n_idx)))
               (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])))).

  (* [a_idx] indexes the SAME action as [act]: buffer_needs is built by mapping
     over spec_all_actions, so length (buffer_needs …) = length spec_all_actions
     and act's slot is finite_index act. *)
  Definition act_idx_aligned
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit))) : Prop :=
    index_to_nat a_idx = @finite_index _ (tfs_action_fin sched) act.

  (* map fst over get_sizes_and_idx recovers the input node list unchanged
     (the indices/sizes it attaches are dropped by fst). *)
  Lemma gsi_map_fst (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var) (outputs_var := o_var) (ips_var := p_var))
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
  Lemma gsi_length (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var) (outputs_var := o_var) (ips_var := p_var))
        (nodes: list nat) :
    length (get_sizes_and_idx ctx dfg nodes) = length nodes.
  Proof.
    rewrite <- (gsi_map_fst dfg nodes) at 2. rewrite map_length. reflexivity.
  Qed.

  (* The slot stored at position [m] is numbered [m]. *)
  Lemma gsi_idx_at
        (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var) (outputs_var := o_var) (ips_var := p_var))
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
        (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var) (outputs_var := o_var) (ips_var := p_var))
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
        (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var) (outputs_var := o_var) (ips_var := p_var))
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
        (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var) (outputs_var := o_var) (ips_var := p_var))
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
                            (calc_backward_cost ctx cost_limit (build_dfg ctx a)))))
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
                (calc_backward_cost ctx cost_limit (build_dfg ctx act)))).
  Proof.
    intros act a_idx Halign.
    unfold act_idx_aligned in Halign.
    rewrite Halign, buffer_needs_eq.
    set (F := fun a => get_sizes_and_idx ctx (build_dfg ctx a)
                         (require_buffer ctx (build_dfg ctx a)
                            (calc_target_cycle cost_limit
                               (calc_backward_cost ctx cost_limit (build_dfg ctx a))))).
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
                       (calc_backward_cost ctx cost_limit (build_dfg ctx act)))) in *.
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


  (* A plain buffer RECOMPUTES, a sample LATCHES as its validity rises, and a
     stall COUNTS to [lat-1].  The three shapes are why the buffer lemmas below
     cannot treat a buffer as caching the value of its node. *)
  Definition buf_value_expr (act: tfs_action sched) a_idx n_idx
      (sz: nat) (expr valid: @tf_expr (tfs_states sched) si_var o_var) (n: nid_t)
      : @tf_expr (tfs_states sched) si_var o_var :=
    let cnt := tf_svar (tf_dfg_b a_idx n_idx) in
    match stall_lat_of act n with
    | Some l =>
        tf_expr_if (tf_op2 tf_and valid
                      (tf_op1 tf_not (tf_op2 (tf_cmp sz tf_eq) cnt (tf_const (pred l)))))
          (tf_op2 tf_add cnt (tf_const 1)) cnt
    | None =>
        if is_sample_of act n
        then tf_expr_if (tf_op2 tf_and valid
                           (tf_op1 tf_not (tf_svar (tf_dfg_v a_idx n_idx))))
               expr cnt
        else expr
    end.

  Definition buf_valid_expr (act: tfs_action sched) a_idx n_idx
      (sz: nat) (valid: @tf_expr (tfs_states sched) si_var o_var) (n: nid_t)
      : @tf_expr (tfs_states sched) si_var o_var :=
    match stall_lat_of act n with
    | Some l =>
        tf_op2 tf_and valid
          (tf_op2 (tf_cmp sz tf_eq) (tf_svar (tf_dfg_b a_idx n_idx))
             (tf_const (pred l)))
    | None => valid
    end.

  (* The whole assignment the validity register takes next cycle: the gate for
     a plain buffer, the gate AND the count for a stall. *)
  Local Notation buf_valid_next act a_idx n_idx :=
    (buf_valid_expr act a_idx n_idx
       (snd (snd (nth (index_to_nat n_idx)
                    (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])
                    (0, (0, 0)))))
       (buf_gate act a_idx n_idx) (vreg_nid a_idx n_idx)).

  (* ONE CYCLE of a stall's counter, read off what compile_dfg_buffers emits:
     it advances exactly when the stall's argument is valid and it has not yet
     reached [pred l], and holds otherwise.  The range hypothesis is what keeps
     the increment from wrapping. *)
  Lemma stall_counter_step
        (act: tfs_action sched) a_idx n_idx
        (ss: sched_sys_state) (input: sched_input_t) l expr valid :
    stall_lat_of act (vreg_nid a_idx n_idx) = Some l ->
    pred l < pow2 (ss_sz (tf_dfg_b a_idx n_idx)) ->
    Bits.to_nat ((fst ss).[tf_dfg_b a_idx n_idx]) <= pred l ->
    Bits.to_nat
      (eval_st (tf_dfg_b a_idx n_idx)
         (buf_value_expr act a_idx n_idx (ss_sz (tf_dfg_b a_idx n_idx))
            expr valid (vreg_nid a_idx n_idx)) ss input)
    = (if andb (if beq_dec (eval1 valid ss input) Bits.zero then false else true)
               (negb (Nat.eqb (Bits.to_nat ((fst ss).[tf_dfg_b a_idx n_idx])) (pred l)))
       then S (Bits.to_nat ((fst ss).[tf_dfg_b a_idx n_idx]))
       else Bits.to_nat ((fst ss).[tf_dfg_b a_idx n_idx])).
  Proof.
    intros Hst Hwide Hinv.
    unfold buf_value_expr. rewrite Hst. cbv beta iota.
    cbn [tf_eval_expr]. rewrite !convert_same.
    (* [cbn] rebuilds the register read under a second type annotation, so the
       two sides of the goal hold two terms that print alike and match nothing
       of each other's.  Put the statement's form back before the case split. *)
    match goal with
    | |- Bits.to_nat (if _ then ?r else _) = _ =>
        replace r with ((fst ss).[tf_dfg_b a_idx n_idx]) by reflexivity
    end.
    assert (Hpl : Bits.to_nat (Bits.of_nat (ss_sz (tf_dfg_b a_idx n_idx)) (pred l))
                  = pred l) by (apply Bits.to_nat_of_nat; exact Hwide).
    destruct (bits1_cases (eval1 valid ss input)) as [Hv | Hv];
      change (tf_eval_expr ss_sz si_sz oo_sz (szB := 1) valid ss input)
        with (eval1 valid ss input); rewrite Hv.
    - (* the argument IS valid *)
      replace (beq_dec (Bits.ones 1) Bits.zero) with false
        by (vm_compute; reflexivity).
      cbn [andb].
      (* Take the comparison FROM the goal: writing it out resolves a second
         [EqDec] instance, and a [destruct] on that leaves the goal alone. *)
      match goal with
      | |- context [ if ?c then Bits.of_nat 1 1 else Bits.of_nat 1 0 ] =>
          destruct c eqn:Hb
      end.
      + (* saturated: the guard reads zero and the counter holds *)
        match goal with
        | |- context [ @beq_dec ?T ?E ?c ?z ] =>
            let H := fresh in
            assert (H : @beq_dec T E c z = true) by (vm_compute; reflexivity);
            rewrite H; clear H
        end.
        apply beq_dec_iff in Hb. rewrite Hb, Hpl, Nat.eqb_refl. reflexivity.
      + (* below the top: the guard reads one and the counter advances *)
        match goal with
        | |- context [ @beq_dec ?T ?E ?c ?z ] =>
            let H := fresh in
            assert (H : @beq_dec T E c z = false) by (vm_compute; reflexivity);
            rewrite H; clear H
        end.
        assert (Hne : Bits.to_nat ((fst ss).[tf_dfg_b a_idx n_idx]) <> pred l).
        { intro Heq. apply (proj1 (beq_dec_false_iff _ _ _) Hb).
          apply bits_to_nat_inj. rewrite Hpl. exact Heq. }
        rewrite (proj2 (Nat.eqb_neq _ _) Hne). cbn [negb].
        apply bits_plus_one_to_nat. lia.
    - (* the argument reads zero: the guard is zero and the counter holds *)
      rewrite !beq_dec_refl. cbn [andb].
      reflexivity.
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
    let compiled := compile_dfg_expr ctx bneeds
                      (length (graph (build_dfg ctx act))) a_idx
                      (build_dfg ctx act) n buffers' in
    let sz := snd (snd entry) in
    In (tf_assign (tf_dfg_b a_idx n_idx)
          (buf_value_expr act a_idx n_idx sz (fst compiled) (snd compiled) n))
       (compile_dfg_buffers ctx bneeds (index_to_nat a_idx)
          (build_dfg ctx act) buffers)
    /\
    In (tf_assign (tf_dfg_v a_idx n_idx)
          (buf_valid_expr act a_idx n_idx sz (snd compiled) n))
       (compile_dfg_buffers ctx bneeds (index_to_nat a_idx)
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

  (* What [compile_dfg_drives] assigns port [p]'s request register: {strobe,
     payload}, both halves selecting on the PULSE, with the register itself as
     the base case -- so a request's payload is taken at its own cycle and HELD.
     Replicates the map body of [compile_dfg_drives]. *)
  Definition drive_value_expr
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (p: p_var) : @tf_expr (tfs_states sched) si_var o_var :=
    let dfg := build_dfg ctx act in
    let buffers := nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [] in
    let fuel := length (graph dfg) in
    let sbufs := filter (fun '(n, _) =>
                           match op (nth n (graph dfg)
                                       {| nid := 0; op := DFG_Empty; sz := 0 |}) with
                           | DFG_Sample _ _ _ => true
                           | _ => false
                           end) buffers in
    tf_op2 (tf_concat 1 (ip_req_sz (tfs_spec_ip ctx p)))
      (fold_right
         (fun n acc =>
            let '(_, v) := compile_dfg_expr ctx bneeds fuel a_idx dfg n buffers in
            let en_val :=
              match op (nth n (graph dfg)
                          {| nid := 0; op := DFG_Empty; sz := 0 |}) with
              | DFG_Drive _ _ en =>
                  guard_expr ctx bneeds (get_tainted ctx dfg) (decl_facts ctx dfg)
                    fuel a_idx dfg sbufs en
              | _ => tf_const 1
              end in
            let '(vgate, vfirst) :=
              match chain_gate ctx dfg n with
              | Some (g, h) =>
                  (snd (compile_dfg_expr ctx bneeds fuel a_idx dfg g buffers),
                   stall_start ctx bneeds a_idx dfg buffers h)
              | None => (v, tf_const 1)
              end in
            tf_expr_if (tf_op2 tf_and en_val (tf_op2 tf_and vgate vfirst))
              (tf_const 1) acc)
         (tf_const 0) (drive_nodes ctx dfg p))
      (fold_right
         (fun n acc =>
            let '(e, v) := compile_dfg_expr ctx bneeds fuel a_idx dfg n buffers in
            let en_val :=
              match op (nth n (graph dfg)
                          {| nid := 0; op := DFG_Empty; sz := 0 |}) with
              | DFG_Drive _ _ en =>
                  guard_expr ctx bneeds (get_tainted ctx dfg) (decl_facts ctx dfg)
                    fuel a_idx dfg sbufs en
              | _ => tf_const 1
              end in
            let '(vgate, vfirst) :=
              match chain_gate ctx dfg n with
              | Some (g, h) =>
                  (snd (compile_dfg_expr ctx bneeds fuel a_idx dfg g buffers),
                   stall_start ctx bneeds a_idx dfg buffers h)
              | None => (v, tf_const 1)
              end in
            tf_expr_if (tf_op2 tf_and en_val (tf_op2 tf_and vgate vfirst))
              e acc)
         (tf_svar (tf_dfg_ov p)) (drive_nodes ctx dfg p)).

  (* The gate a drive's request rides: its path condition, the validity of the
     node the stall waits on, and the first cycle of that wait. *)
  Definition drive_pulse
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (n: nid_t) : @tf_expr (tfs_states sched) si_var o_var :=
    let dfg := build_dfg ctx act in
    let buffers := nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [] in
    let fuel := length (graph dfg) in
    let sbufs := filter (fun '(m, _) =>
                           match op (nth m (graph dfg)
                                       {| nid := 0; op := DFG_Empty; sz := 0 |}) with
                           | DFG_Sample _ _ _ => true
                           | _ => false
                           end) buffers in
    let en_val :=
      match op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}) with
      | DFG_Drive _ _ en =>
          guard_expr ctx bneeds (get_tainted ctx dfg) (decl_facts ctx dfg)
            fuel a_idx dfg sbufs en
      | _ => tf_const 1
      end in
    let '(vgate, vfirst) :=
      match chain_gate ctx dfg n with
      | Some (g, h) =>
          (snd (compile_dfg_expr ctx bneeds fuel a_idx dfg g buffers),
           stall_start ctx bneeds a_idx dfg buffers h)
      | None => (snd (compile_dfg_expr ctx bneeds fuel a_idx dfg n buffers), tf_const 1)
      end in
    tf_op2 tf_and en_val (tf_op2 tf_and vgate vfirst).

  (* The last of the three gate halves on its own: the first cycle of the
     stall.s wait, which is where 3b reasons about the port. *)
  Definition drive_vfirst
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (n: nid_t) : @tf_expr (tfs_states sched) si_var o_var :=
    match chain_gate ctx (build_dfg ctx act) n with
    | Some (_, h) =>
        stall_start ctx bneeds a_idx (build_dfg ctx act)
          (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) h
    | None => tf_const 1
    end.

  (* The pulse is an AND, so a wait that has already started puts it down. *)
  Lemma drive_pulse_zero_of_vfirst
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit))) (n: nid_t)
        (ss: sched_sys_state) (input: sched_input_t) :
    eval1 (drive_vfirst act a_idx n) ss input = Bits.zero ->
    eval1 (drive_pulse act a_idx n) ss input = Bits.zero.
  Proof.
    unfold drive_pulse, drive_vfirst. cbv zeta.
    destruct (chain_gate ctx (build_dfg ctx act) n) as [[g h] |]; intro Hz.
    - cbn [tf_eval_expr]. rewrite Hz, bits1_and_zero_r, bits1_and_zero_r. reflexivity.
    - exfalso. rewrite eval1_const1 in Hz. exact (ones1_neq_zero Hz).
  Qed.

  (* The middle gate half: the validity of the node the stall waits on. *)
  Lemma drive_pulse_zero_of_vgate
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit))) (n g h: nid_t)
        (ss: sched_sys_state) (input: sched_input_t) :
    chain_gate ctx (build_dfg ctx act) n = Some (g, h) ->
    eval1 (snd (compile_dfg_expr ctx bneeds (length (graph (build_dfg ctx act))) a_idx
                  (build_dfg ctx act) g
                  (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))) ss input
      = Bits.zero ->
    eval1 (drive_pulse act a_idx n) ss input = Bits.zero.
  Proof.
    intros Hcg Hz. unfold drive_pulse. cbv zeta. rewrite Hcg.
    cbn [tf_eval_expr]. rewrite Hz, bits1_and_zero_l, bits1_and_zero_r. reflexivity.
  Qed.

  (* The sample buffers a guard keeps -- the only ones [compile_dfg_drives]
     substitutes, since every other source is stable across the action. *)
  Definition drive_sbufs (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      : list (nid_t * (nat * sz_t)) :=
    filter (fun '(m, _) =>
              match op (nth m (graph (build_dfg ctx act))
                          {| nid := 0; op := DFG_Empty; sz := 0 |}) with
              | DFG_Sample _ _ _ => true
              | _ => false
              end) (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []).

  (* One literal of a path condition, as the expression the guard ANDs in. *)
  Definition guard_lit (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (sbufs: list (nid_t * (nat * sz_t))) (l: nid_t * bool)
      : @tf_expr (tfs_states sched) si_var o_var :=
    let dfg := build_dfg ctx act in
    let v := fst (compile_dfg_expr ctx bneeds (length (graph dfg)) a_idx dfg (fst l) sbufs) in
    if snd l then v else tf_op1 tf_not v.

  Local Notation gexpr act a_idx sbufs en :=
    (guard_expr ctx bneeds (get_tainted ctx (build_dfg ctx act))
       (decl_facts ctx (build_dfg ctx act)) (length (graph (build_dfg ctx act)))
       a_idx (build_dfg ctx act) sbufs en).

  Lemma guard_expr_fold (act: tfs_action sched) a_idx sbufs en :
    gexpr act a_idx sbufs en
    = fold_right (fun l acc => tf_op2 tf_and (guard_lit act a_idx sbufs l) acc)
        (tf_const 1) en.
  Proof. reflexivity. Qed.

  (* A path condition with one literal down is down. *)
  Lemma guard_expr_zero (act: tfs_action sched) a_idx sbufs en l
        (ss: sched_sys_state) (input: sched_input_t) :
    In l en ->
    eval1 (guard_lit act a_idx sbufs l) ss input = Bits.zero ->
    eval1 (gexpr act a_idx sbufs en) ss input = Bits.zero.
  Proof.
    rewrite guard_expr_fold. intros Hin Hz.
    induction en as [| a en IH]; [ destruct Hin |].
    cbn [fold_right tf_eval_expr].
    destruct Hin as [-> | Hin].
    - rewrite Hz. apply bits1_and_zero_l.
    - rewrite (IH Hin). apply bits1_and_zero_r.
  Qed.

  (* Guards that disagree on a literal cannot both be up, which is how two
     calls in mutually exclusive branches stay off one port. *)
  Lemma guards_disjoint_excl (act: tfs_action sched) a_idx sbufs en1 en2
        (ss: sched_sys_state) (input: sched_input_t) :
    guards_disjoint en1 en2 = true ->
    eval1 (gexpr act a_idx sbufs en1) ss input = Bits.zero
    \/ eval1 (gexpr act a_idx sbufs en2) ss input = Bits.zero.
  Proof.
    unfold guards_disjoint. intro Hex.
    apply existsb_exists in Hex. destruct Hex as [l1 [Hin1 Hex2]].
    apply existsb_exists in Hex2. destruct Hex2 as [l2 [Hin2 Hb]].
    apply andb_true_iff in Hb. destruct Hb as [Hfst Hsnd].
    apply Nat.eqb_eq in Hfst. apply negb_true_iff in Hsnd.
    apply Bool.eqb_false_iff in Hsnd.
    destruct (bits1_cases (eval1 (guard_lit act a_idx sbufs l1) ss input)) as [Hv | Hv];
      [| left; exact (guard_expr_zero act a_idx sbufs en1 l1 ss input Hin1 Hv) ].
    right. apply (guard_expr_zero act a_idx sbufs en2 l2 ss input Hin2).
    destruct l1 as [c1 b1]. destruct l2 as [c2 b2].
    cbn [fst snd] in Hfst, Hsnd. subst c2.
    unfold guard_lit in Hv |- *. cbv zeta in Hv |- *. cbn [fst snd] in Hv |- *.
    destruct b1; destruct b2; try (exfalso; apply Hsnd; reflexivity);
      cbn [tf_eval_expr] in Hv |- *.
    - rewrite Hv. apply bits1_neg_ones.
    - apply bits1_neg_ones_inv in Hv. exact Hv.
  Qed.

  (* The path condition is the first of the three gate halves. *)
  Lemma drive_pulse_zero_of_en (act: tfs_action sched) a_idx n p arg en
        (ss: sched_sys_state) (input: sched_input_t) :
    node_op act n = DFG_Drive p arg en ->
    eval1 (gexpr act a_idx (drive_sbufs act a_idx) en) ss input = Bits.zero ->
    eval1 (drive_pulse act a_idx n) ss input = Bits.zero.
  Proof.
    intros Hop Hz. unfold node_op in Hop.
    unfold drive_pulse. cbv zeta. rewrite Hop.
    destruct (chain_gate ctx (build_dfg ctx act) n) as [[g h] |];
      cbn [tf_eval_expr];
      change (filter
                (fun '(m, _) =>
                   match op (nth m (graph (build_dfg ctx act))
                               {| nid := 0; op := DFG_Empty; sz := 0 |}) with
                   | DFG_Sample _ _ _ => true
                   | _ => false
                   end) (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))
        with (drive_sbufs act a_idx);
      rewrite Hz; apply bits1_and_zero_l.
  Qed.

  (* Two calls in mutually exclusive branches never hold one port at once. *)
  Lemma drive_pulse_excl (act: tfs_action sched) a_idx n1 n2 p arg1 en1 arg2 en2
        (ss: sched_sys_state) (input: sched_input_t) :
    node_op act n1 = DFG_Drive p arg1 en1 ->
    node_op act n2 = DFG_Drive p arg2 en2 ->
    guards_disjoint en1 en2 = true ->
    eval1 (drive_pulse act a_idx n1) ss input = Bits.zero
    \/ eval1 (drive_pulse act a_idx n2) ss input = Bits.zero.
  Proof.
    intros H1 H2 Hd.
    destruct (guards_disjoint_excl act a_idx (drive_sbufs act a_idx) en1 en2 ss input Hd)
      as [Hz | Hz].
    - left. exact (drive_pulse_zero_of_en act a_idx n1 p arg1 en1 ss input H1 Hz).
    - right. exact (drive_pulse_zero_of_en act a_idx n2 p arg2 en2 ss input H2 Hz).
  Qed.

  (* The two halves of the drive register, each a fold over [drive_nodes]
     (LATEST FIRST, so the latest pulse wins) selecting on [drive_pulse]. *)
  Definition drive_strobe_expr
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (p: p_var) : @tf_expr (tfs_states sched) si_var o_var :=
    fold_right (fun n acc => tf_expr_if (drive_pulse act a_idx n) (tf_const 1) acc)
      (tf_const 0) (drive_nodes ctx (build_dfg ctx act) p).

  Definition drive_payload_expr
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (p: p_var) : @tf_expr (tfs_states sched) si_var o_var :=
    fold_right (fun n acc =>
                  tf_expr_if (drive_pulse act a_idx n)
                    (fst (compile_dfg_expr ctx bneeds
                            (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n
                            (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])))
                    acc)
      (tf_svar (tf_dfg_ov p)) (drive_nodes ctx (build_dfg ctx act) p).

  Lemma drive_value_expr_split
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit))) (p: p_var) :
    drive_value_expr act a_idx p
    = tf_op2 (tf_concat 1 (ip_req_sz (tfs_spec_ip ctx p)))
        (drive_strobe_expr act a_idx p) (drive_payload_expr act a_idx p).
  Proof.
    unfold drive_value_expr, drive_strobe_expr, drive_payload_expr, drive_pulse.
    cbv zeta. f_equal;
      induction (drive_nodes ctx (build_dfg ctx act) p) as [| a l IH]; cbn [fold_right];
      try reflexivity;
      destruct (compile_dfg_expr ctx bneeds (length (graph (build_dfg ctx act))) a_idx
                  (build_dfg ctx act) a
                  (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) as [e v];
      destruct (chain_gate ctx (build_dfg ctx act) a) as [[g h] | ];
      rewrite IH; reflexivity.
  Qed.

  (* A pulse fold with every pulse down reads its base case. *)
  Lemma eval_pulse_fold_hold
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
        (body: nid_t -> @tf_expr (tfs_states sched) si_var o_var)
        (base: @tf_expr (tfs_states sched) si_var o_var)
        (l: list nid_t) (szB: nat) (ss: sched_sys_state) (input: sched_input_t) :
    (forall n, In n l -> eval1 (drive_pulse act a_idx n) ss input = Bits.zero) ->
    tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
      (fold_right (fun n acc => tf_expr_if (drive_pulse act a_idx n) (body n) acc) base l)
      ss input
    = tf_eval_expr ss_sz si_sz oo_sz (szB := szB) base ss input.
  Proof.
    intro Hdown. induction l as [| a l IH]; cbn [fold_right]; [ reflexivity |].
    cbn [tf_eval_expr]. rewrite (Hdown a (or_introl eq_refl)), beq_dec_refl.
    apply IH. intros n Hn. exact (Hdown n (or_intror Hn)).
  Qed.

  (* [drive_nodes] is latest first, so the fold takes the first pulse it meets. *)
  Lemma eval_pulse_fold_take
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
        (body: nid_t -> @tf_expr (tfs_states sched) si_var o_var)
        (base: @tf_expr (tfs_states sched) si_var o_var)
        (pre post: list nid_t) (n: nid_t) (szB: nat)
        (ss: sched_sys_state) (input: sched_input_t) :
    (forall m, In m pre -> eval1 (drive_pulse act a_idx m) ss input = Bits.zero) ->
    eval1 (drive_pulse act a_idx n) ss input <> Bits.zero ->
    tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
      (fold_right (fun m acc => tf_expr_if (drive_pulse act a_idx m) (body m) acc)
         base (pre ++ n :: post))
      ss input
    = tf_eval_expr ss_sz si_sz oo_sz (szB := szB) (body n) ss input.
  Proof.
    intros Hpre Hn. induction pre as [| a pre IH]; cbn [app fold_right tf_eval_expr].
    - match goal with
      | |- context [ @beq_dec ?T ?E ?x ?z ] => destruct (@beq_dec T E x z) eqn:Hb
      end.
      + exfalso. apply Hn. exact (proj1 (beq_dec_iff _ _ _) Hb).
      + reflexivity.
    - rewrite (Hpre a (or_introl eq_refl)), beq_dec_refl.
      apply IH. intros m Hm. exact (Hpre m (or_intror Hm)).
  Qed.

  (* With no drive pulsing, the payload half reads the payload already held. *)
  Lemma drive_payload_expr_hold
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit))) (p: p_var)
        (ss: sched_sys_state) (input: sched_input_t) :
    (forall n, In n (drive_nodes ctx (build_dfg ctx act) p) ->
       eval1 (drive_pulse act a_idx n) ss input = Bits.zero) ->
    tf_eval_expr ss_sz si_sz oo_sz (szB := ip_req_sz (tfs_spec_ip ctx p))
      (drive_payload_expr act a_idx p) ss input
    = drive_payload ss p.
  Proof.
    intro Hdown. unfold drive_payload_expr.
    rewrite (eval_pulse_fold_hold act a_idx _ _ _ _ ss input Hdown).
    symmetry. apply drive_payload_eval.
  Qed.

  (* The drive register's assignment is one of the always-ops. *)
  Lemma compile_dfg_drives_entry
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit))) (p: p_var) :
    In (tf_assign (tf_dfg_ov p) (drive_value_expr act a_idx p))
       (compile_dfg_drives ctx bneeds (index_to_nat a_idx) (build_dfg ctx act)
          (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])).
  Proof.
    unfold compile_dfg_drives. rewrite index_of_nat_to_nat.
    apply in_map_iff. exists p. split; [ reflexivity |].
    unfold driven_ports.
    exact (nth_error_In _ _ (@finite_surjective p_var (tfs_spec_ips_fin ctx) p)).
  Qed.

  (* The nid cached in a buffer register is a member of that action's
     require_buffer list. *)
  Lemma vreg_nid_in_require_buffer :
    forall (act: tfs_action sched) a_idx n_idx,
      act_idx_aligned act a_idx ->
      In (vreg_nid a_idx n_idx)
         (require_buffer ctx (build_dfg ctx act)
            (calc_target_cycle cost_limit
               (calc_backward_cost ctx cost_limit (build_dfg ctx act)))).
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
                    (calc_backward_cost ctx cost_limit (build_dfg ctx act)))) in *.
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
      (getn cost_map (nid node) + cost_fn ctx cost_limit (op node) (sz node)).

  Lemma calc_backward_cost_fold dfg :
    calc_backward_cost ctx cost_limit dfg = fold_left bc_aux (rev (graph dfg)) [].
  Proof. unfold calc_backward_cost, bc_aux, getn. reflexivity. Qed.

  (* Frozen-key propagation: if key (nid N) is never in the key-set of any
     node processed later, then the inequality getn x >= getn (nid N) is
     preserved through the rest of the fold. *)
  Lemma cost_ge_after_fold :
    forall (suf: list (@dfg_node_t s_var i_var o_var p_var)) acc
           (N: @dfg_node_t s_var i_var o_var p_var) x,
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
  Definition ids_desc (L : list (@dfg_node_t s_var i_var o_var p_var)) : Prop :=
    forall pre a rest, L = pre ++ a :: rest ->
      forall M, In M rest -> nid M < nid a.

  (* Every node's args reference strictly-earlier (lower) ids. *)
  Definition args_lt (L : list (@dfg_node_t s_var i_var o_var p_var)) : Prop :=
    forall a, In a L -> forall x, In x (get_args ctx a) -> x < nid a.

  (* ===================================================================== *)
  (* build_dfg_wf : the builder emits nodes with strictly increasing ids   *)
  (* and every node's args reference already-emitted (lower) ids.          *)
  (* Proved by a state-monad invariant [winv] threaded through the builder.*)
  (* ===================================================================== *)

  Local Notation wst := (@dfg_state_t s_var i_var o_var p_var).

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

  (* [last_sample] returns the nid of a node it found in the graph. *)
  Lemma last_sample_nidwf (s: wst) ip en prev :
    last_sample ctx s ip en = Some prev -> wnidwf s prev.
  Proof.
    unfold last_sample.
    destruct (find _ (graph s)) as [nd |] eqn:Ef; [| discriminate].
    intro H. injection H as <-.
    apply find_some in Ef. destruct Ef as [Hin _].
    exists nd. split; [ exact Hin | reflexivity ].
  Qed.

  (* What it returns: a SAMPLE on that port whose guard it could share. *)
  Lemma last_sample_spec (s: wst) (ip: p_var) en prev :
    last_sample ctx s ip en = Some prev ->
    exists nd tok en',
      In nd (graph s) /\ nid nd = prev
      /\ op nd = DFG_Sample ip tok en'
      /\ guards_disjoint en en' = false.
  Proof.
    unfold last_sample.
    destruct (find _ (graph s)) as [nd |] eqn:Ef; [| discriminate].
    intro H. injection H as <-.
    apply find_some in Ef. destruct Ef as [Hin Hp]. cbv beta in Hp.
    destruct (op nd) as [ c | iv | v2 | uop a | bop a1 a2 | a | cd t e
                        | slat sa | dov dn den | siv sn sen | ja jb | ] eqn:Eo;
      try discriminate Hp.
    destruct ((tfs_spec_ips_eq_dec ctx).(eq_dec) siv ip) as [-> | Hne];
      [| discriminate Hp].
    exists nd, sn, sen. repeat split; [ exact Hin | exact Eo |].
    apply negb_true_iff in Hp. exact Hp.
  Qed.

  (* [find] scans left to right and the graph is nid-descending, so the match
     it returns carries the LARGEST id among the matches. *)
  Lemma find_ge_desc (P: @dfg_node_t s_var i_var o_var p_var -> bool) L x y :
    ids_desc L -> find P L = Some x -> In y L -> P y = true -> nid y <= nid x.
  Proof.
    revert x y. induction L as [| a L IH]; intros x y Hd Hf Hin Hy; [ destruct Hin |].
    cbn [find] in Hf. destruct (P a) eqn:Ha.
    - injection Hf as <-.
      destruct Hin as [<- | Hin]; [ lia |].
      apply Nat.lt_le_incl. exact (Hd [] a L eq_refl y Hin).
    - destruct Hin as [<- | Hin]; [ rewrite Ha in Hy; discriminate |].
      apply (IH x y); [| exact Hf | exact Hin | exact Hy ].
      intros pre b rest Hsplit M HM.
      apply (Hd (a :: pre) b rest); [ rewrite Hsplit; reflexivity | exact HM ].
  Qed.

  (* So [last_sample] finds a match whenever one exists ... *)
  Lemma last_sample_found (s: wst) (ip: p_var) en nd tok en' :
    In nd (graph s) -> op nd = DFG_Sample ip tok en' ->
    guards_disjoint en en' = false ->
    exists prev, last_sample ctx s ip en = Some prev.
  Proof.
    intros Hin Hop Hdis. unfold last_sample.
    destruct (find _ (graph s)) as [x |] eqn:Ef; [ exists (nid x); reflexivity |].
    exfalso. pose proof (find_none _ _ Ef nd Hin) as Hn. cbv beta in Hn.
    rewrite Hop in Hn.
    destruct ((tfs_spec_ips_eq_dec ctx).(eq_dec) ip ip) as [_ | Hne];
      [| apply Hne; reflexivity ].
    rewrite Hdis in Hn. cbn [negb] in Hn. discriminate Hn.
  Qed.

  (* ... and the one it finds is the LAST, which is what sequences the calls. *)
  Lemma last_sample_max (s: wst) (ip: p_var) en nd tok en' prev :
    ids_desc (graph s) ->
    In nd (graph s) -> op nd = DFG_Sample ip tok en' ->
    guards_disjoint en en' = false ->
    last_sample ctx s ip en = Some prev ->
    nid nd <= prev.
  Proof.
    intros Hd Hin Hop Hdis Hls. unfold last_sample in Hls.
    destruct (find _ (graph s)) as [x |] eqn:Ef; [| discriminate Hls ].
    injection Hls as <-.
    apply (find_ge_desc _ (graph s) x nd Hd Ef Hin).
    cbv beta. rewrite Hop.
    destruct ((tfs_spec_ips_eq_dec ctx).(eq_dec) ip ip) as [_ | Hne];
      [| exfalso; apply Hne; reflexivity ].
    rewrite Hdis. reflexivity.
  Qed.

  (* Every ordering join sits between a drive and a SAMPLE on the same port
     whose guard it could share -- which is exactly what [last_sample] gave. *)
  Definition joins_sequence (L : list (@dfg_node_t s_var i_var o_var p_var)) : Prop :=
    forall j d prev, In j L -> op j = DFG_Join d prev ->
      exists (p: p_var) arg en tok en' nd ns,
        In nd L /\ nid nd = d /\ op nd = DFG_Drive p arg en
        /\ In ns L /\ nid ns = prev /\ op ns = DFG_Sample p tok en'
        /\ guards_disjoint en en' = false.

  Lemma joins_sequence_emit_other (s: wst) o size :
    joins_sequence (graph s) ->
    (forall d prev, o <> DFG_Join d prev) ->
    joins_sequence (graph (snd (emit ctx o size s))).
  Proof.
    intros Hjs Hno. rewrite emit_red. cbn [snd graph].
    intros j d prev Hin Hop. cbn [In] in Hin.
    destruct Hin as [<- | Hin]; [ cbn [op] in Hop; exfalso; exact (Hno d prev Hop) |].
    destruct (Hjs j d prev Hin Hop)
      as [p [arg [en [tok [en' [nd [ns [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]]]]]]]].
    exists p, arg, en, tok, en', nd, ns.
    split; [ right; exact H1 |]. split; [ exact H2 |]. split; [ exact H3 |].
    split; [ right; exact H4 |]. split; [ exact H5 |]. split; [ exact H6 | exact H7 ].
  Qed.

  Lemma joins_sequence_emit_join (s: wst) d prev (p: p_var) arg en tok en' :
    joins_sequence (graph s) ->
    (exists nd, In nd (graph s) /\ nid nd = d /\ op nd = DFG_Drive p arg en) ->
    (exists ns, In ns (graph s) /\ nid ns = prev /\ op ns = DFG_Sample p tok en') ->
    guards_disjoint en en' = false ->
    joins_sequence (graph (snd (emit ctx (DFG_Join d prev) 1 s))).
  Proof.
    intros Hjs [nd [Hnd [Hnid Hdop]]] [ns [Hns [Hpid Hsop]]] Hdis.
    rewrite emit_red. cbn [snd graph].
    intros j d0 prev0 Hin Hop. cbn [In] in Hin.
    destruct Hin as [<- | Hin].
    - cbn [op] in Hop. injection Hop as <- <-.
      exists p, arg, en, tok, en', nd, ns.
      split; [ right; exact Hnd |]. split; [ exact Hnid |]. split; [ exact Hdop |].
      split; [ right; exact Hns |]. split; [ exact Hpid |].
      split; [ exact Hsop | exact Hdis ].
    - destruct (Hjs j d0 prev0 Hin Hop)
        as [p2 [arg2 [en2 [tok2 [en2' [nd2 [ns2 [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]]]]]]]].
      exists p2, arg2, en2, tok2, en2', nd2, ns2.
      split; [ right; exact H1 |]. split; [ exact H2 |]. split; [ exact H3 |].
      split; [ right; exact H4 |]. split; [ exact H5 |]. split; [ exact H6 | exact H7 ].
  Qed.


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

  (* [read_var] either reuses a [DFG_Var v] node already in the graph (state
     untouched) or emits a fresh one.  The guards in its [find] predicate are
     exactly the three facts the reuse case has to supply. *)
  Lemma read_var_cases (v: dfg_vars_t (states_var:=s_var) (outputs_var:=o_var))
        (s: wst) id s' :
    read_var ctx v s = (id, s') ->
    (In {| nid := id; op := DFG_Var v; sz := dfg_var_size ctx v |} (graph s)
     /\ 1 <= id /\ s' = s)
    \/ emit ctx (DFG_Var v) (dfg_var_size ctx v) s = (id, s').
  Proof.
    unfold read_var, bind, get_state.
    match goal with
    | |- context [find ?P ?l] => destruct (find P l) as [nd|] eqn:Ef
    end; intro H.
    - unfold ret in H. injection H as Hid Hs. subst s'. left.
      apply find_some in Ef. destruct Ef as [Hin Hpred]. cbv beta in Hpred.
      destruct (op nd) as [ c | iv | v2 | uop a | bop a1 a2 | a | cd t e | slat sa | dov dn den | siv sn sen | ja jb | ] eqn:Eo;
        try discriminate Hpred.
      apply andb_true_iff in Hpred. destruct Hpred as [Hpred Hpos].
      apply andb_true_iff in Hpred. destruct Hpred as [Hveq Hsz].
      destruct (eq_dec v2 v) as [Hvv | _]; [ | discriminate Hveq ].
      apply Nat.eqb_eq in Hsz. apply Nat.ltb_lt in Hpos.
      assert (Hnd : nd = {| nid := id; op := DFG_Var v; sz := dfg_var_size ctx v |}).
      { destruct nd as [n0 o0 z0]; cbn in *. subst o0. subst v2. subst z0.
        rewrite <- Hid. reflexivity. }
      rewrite Hnd in Hin. split; [ exact Hin | split; [ rewrite <- Hid; exact Hpos | reflexivity ] ].
    - right. exact H.
  Qed.

  (* Threading it through the builder: a monadic step that emits no join. *)
  Definition preserves_js {A} (m: M ctx A) : Prop :=
    forall s, joins_sequence (graph s) -> joins_sequence (graph (snd (m s))).

  Lemma preserves_js_ret {A} (x: A) : preserves_js (ret ctx x).
  Proof. intros s Hs. exact Hs. Qed.

  Lemma preserves_js_bind {A B} (m: M ctx A) (f: A -> M ctx B) :
    preserves_js m -> (forall x, preserves_js (f x)) -> preserves_js (bind ctx m f).
  Proof.
    intros Hm Hf s Hs. unfold bind.
    specialize (Hm s Hs). destruct (m s) as [x s1]. cbn [snd] in Hm.
    exact (Hf x s1 Hm).
  Qed.

  Lemma preserves_js_emit o size :
    (forall d prev, o <> DFG_Join d prev) -> preserves_js (emit ctx o size).
  Proof. intros Hno s Hs. exact (joins_sequence_emit_other s o size Hs Hno). Qed.

  Lemma preserves_js_get_var v : preserves_js (get_var ctx v).
  Proof.
    intros s Hs. unfold get_var, bind, get_state.
    destruct (BitsToLists.list_assoc (var_map s) v) as [id |]; [ exact Hs |].
    destruct (read_var ctx v s) as [id s'] eqn:Er. cbn [snd].
    destruct (read_var_cases v s id s' Er) as [[_ [_ ->]] | Hem]; [ exact Hs |].
    apply (f_equal snd) in Hem. cbn [snd] in Hem. rewrite <- Hem.
    apply joins_sequence_emit_other; [ exact Hs |].
    intros d prev Hc. discriminate Hc.
  Qed.

  (* The graph only grows, with no [winv] side condition -- which is what the
     [tf_call] case needs to carry [last_sample].s witness forward. *)
  Definition grows {A} (m: M ctx A) : Prop :=
    forall s, wgmono s (snd (m s)).

  Lemma grows_ret {A} (x: A) : grows (ret ctx x).
  Proof. intros s. apply wgmono_refl. Qed.

  Lemma grows_bind {A B} (m: M ctx A) (f: A -> M ctx B) :
    grows m -> (forall x, grows (f x)) -> grows (bind ctx m f).
  Proof.
    intros Hm Hf s. unfold bind. specialize (Hm s).
    destruct (m s) as [x s1]. cbn [snd] in Hm.
    exact (wgmono_trans s s1 _ Hm (Hf x s1)).
  Qed.

  Lemma grows_emit o size : grows (emit ctx o size).
  Proof. intros s. rewrite emit_red. cbn [snd graph]. intros n Hn. right. exact Hn. Qed.

  Lemma grows_get_var v : grows (get_var ctx v).
  Proof.
    intros s. unfold get_var, bind, get_state.
    destruct (BitsToLists.list_assoc (var_map s) v) as [id |]; [ apply wgmono_refl |].
    destruct (read_var ctx v s) as [id s'] eqn:Er. cbn [snd].
    destruct (read_var_cases v s id s' Er) as [[_ [_ ->]] | Hem]; [ apply wgmono_refl |].
    apply (f_equal snd) in Hem. cbn [snd] in Hem. rewrite <- Hem.
    apply grows_emit.
  Qed.

  Lemma dataflow_expr_grows e sz : grows (dataflow_expr ctx e sz).
  Proof.
    revert sz.
    induction e as [ c | v | v | v | uop src IHsrc | bop s1 IH1 s2 IH2 | c IHc t IHt e IHe ];
      intro sz; cbn [dataflow_expr].
    - apply grows_emit.
    - apply grows_bind; [ apply grows_get_var | intro x ].
      destruct (Nat.eqb _ sz); [ apply grows_ret | apply grows_emit ].
    - apply grows_bind; [ apply grows_emit | intro x ].
      destruct (Nat.eqb _ sz); [ apply grows_ret | apply grows_emit ].
    - apply grows_bind; [ apply grows_get_var | intro x ].
      destruct (Nat.eqb _ sz); [ apply grows_ret | apply grows_emit ].
    - destruct uop; (apply grows_bind; [ apply IHsrc | intro x ]; apply grows_emit).
    - destruct bop;
        (apply grows_bind; [ apply IH1 | intro x ];
         apply grows_bind; [ apply IH2 | intro y ]; apply grows_emit).
    - apply grows_bind; [ apply IHc | intro x ].
      apply grows_bind; [ apply IHt | intro y ].
      apply grows_bind; [ apply IHe | intro z ]. apply grows_emit.
  Qed.

  (* A bind that keeps the link between the step and the state it lands in --
     needed where a later step reads a state bound by an earlier [get_state]. *)
  Lemma preserves_js_bind_st {A B} (m: M ctx A) (f: A -> M ctx B) :
    preserves_js m ->
    (forall s x s1, m s = (x, s1) -> joins_sequence (graph s1) ->
       joins_sequence (graph (snd (f x s1)))) ->
    preserves_js (bind ctx m f).
  Proof.
    intros Hm Hf s Hs. unfold bind.
    specialize (Hm s Hs). destruct (m s) as [x s1] eqn:E. cbn [snd] in Hm.
    exact (Hf s x s1 E Hm).
  Qed.

  Lemma dataflow_expr_joins e sz : preserves_js (dataflow_expr ctx e sz).
  Proof.
    revert sz.
    induction e as [ c | v | v | v | uop src IHsrc | bop s1 IH1 s2 IH2 | c IHc t IHt e IHe ];
      intro sz; cbn [dataflow_expr].
    - apply preserves_js_emit. intros d prev Hc. discriminate Hc.
    - apply preserves_js_bind; [ apply preserves_js_get_var | intro x ].
      destruct (Nat.eqb _ sz);
        [ apply preserves_js_ret
        | apply preserves_js_emit; intros d prev Hc; discriminate Hc ].
    - apply preserves_js_bind;
        [ apply preserves_js_emit; intros d prev Hc; discriminate Hc | intro x ].
      destruct (Nat.eqb _ sz);
        [ apply preserves_js_ret
        | apply preserves_js_emit; intros d prev Hc; discriminate Hc ].
    - apply preserves_js_bind; [ apply preserves_js_get_var | intro x ].
      destruct (Nat.eqb _ sz);
        [ apply preserves_js_ret
        | apply preserves_js_emit; intros d prev Hc; discriminate Hc ].
    - destruct uop;
        (apply preserves_js_bind; [ apply IHsrc | intro x ];
         apply preserves_js_emit; intros d prev Hc; discriminate Hc).
    - destruct bop;
        (apply preserves_js_bind; [ apply IH1 | intro x ];
         apply preserves_js_bind; [ apply IH2 | intro y ];
         apply preserves_js_emit; intros d prev Hc; discriminate Hc).
    - apply preserves_js_bind; [ apply IHc | intro x ].
      apply preserves_js_bind; [ apply IHt | intro y ].
      apply preserves_js_bind; [ apply IHe | intro z ].
      apply preserves_js_emit; intros d prev Hc; discriminate Hc.
  Qed.

  Lemma preserves_js_set_var v id : preserves_js (set_var ctx v id).
  Proof.
    intros s Hs. unfold set_var, bind, get_state, put_state. cbn [snd graph]. exact Hs.
  Qed.

  Lemma preserves_js_ensure_var v : preserves_js (ensure_var ctx v).
  Proof.
    intros s Hs. unfold ensure_var, bind, get_state, put_state, ret.
    destruct (emit ctx (DFG_Var v) (dfg_var_size ctx v) s) as [id s1] eqn:Ee.
    cbn [snd graph].
    assert (Hs1 : joins_sequence (graph s1)).
    { pose proof (joins_sequence_emit_other s (DFG_Var v) (dfg_var_size ctx v) Hs
                    ltac:(intros d prev Hc; discriminate Hc)) as H.
      rewrite Ee in H. cbn [snd] in H. exact H. }
    exact Hs1.
  Qed.

  Lemma preserves_js_merge_key c k vt ve : preserves_js (merge_key ctx c k vt ve).
  Proof.
    unfold merge_key.
    destruct vt as [x |]; destruct ve as [y |].
    - destruct (eq_dec x y); [ apply preserves_js_ret |].
      apply preserves_js_bind;
        [ apply preserves_js_emit; intros d prev Hc; discriminate Hc
        | intro z; apply preserves_js_ret ].
    - apply preserves_js_bind; [ apply preserves_js_ensure_var | intro z ].
      apply preserves_js_bind;
        [ apply preserves_js_emit; intros d prev Hc; discriminate Hc
        | intro w; apply preserves_js_ret ].
    - apply preserves_js_bind; [ apply preserves_js_ensure_var | intro z ].
      apply preserves_js_bind;
        [ apply preserves_js_emit; intros d prev Hc; discriminate Hc
        | intro w; apply preserves_js_ret ].
    - apply preserves_js_ret.
  Qed.

  Lemma preserves_js_merge_loop c mt me keys acc :
    preserves_js (merge_loop ctx c mt me keys acc).
  Proof.
    revert acc. induction keys as [| [k kid] keys IH]; intro acc;
      cbn [merge_loop]; [ apply preserves_js_ret |].
    destruct (BitsToLists.list_assoc acc k) as [x |]; [ apply IH |].
    apply preserves_js_bind; [ apply preserves_js_merge_key | intro r ].
    destruct r as [fid |]; apply IH.
  Qed.

  Lemma preserves_js_merge_maps c mo mt me :
    preserves_js (merge_maps ctx c mo mt me).
  Proof. apply preserves_js_merge_loop. Qed.

  Lemma preserves_js_get_state : preserves_js (get_state ctx).
  Proof. intros s Hs. exact Hs. Qed.

  (* The same bind, applied at ONE state, so a later step can use the state an
     earlier [get_state] bound. *)
  Lemma js_bind_at {A B} (m: M ctx A) (f: A -> M ctx B) (s: wst) :
    joins_sequence (graph (snd (m s))) ->
    (forall x s1, m s = (x, s1) -> joins_sequence (graph s1) ->
       joins_sequence (graph (snd (f x s1)))) ->
    joins_sequence (graph (snd (bind ctx m f s))).
  Proof.
    intros Hm Hf. unfold bind.
    destruct (m s) as [x s1] eqn:E. cbn [snd] in Hm. exact (Hf x s1 eq_refl Hm).
  Qed.

  (* The one emit in the builder that IS a join: a call.s ordering node, which
     [last_sample] has just named a sample on the same port for. *)
  Lemma js_call_head (s0 s2 s3: wst) (ip: p_var) arg_id en drive_id size :
    joins_sequence (graph s3) ->
    wgmono s0 s2 ->
    emit ctx (DFG_Drive ip arg_id en) size s2 = (drive_id, s3) ->
    joins_sequence
      (graph (snd (match last_sample ctx s0 ip en with
                   | Some prev => emit ctx (DFG_Join drive_id prev) 1
                   | None => ret ctx drive_id
                   end s3))).
  Proof.
    intros H3 Hg02 Ed.
    destruct (last_sample ctx s0 ip en) as [prev |] eqn:Elast; [| exact H3 ].
    destruct (last_sample_spec s0 ip en prev Elast)
      as [nd [tok [en' [Hnd [Hnid [Hop Hdis]]]]]].
    rewrite emit_red in Ed. injection Ed as Hdid Hs3.
    apply (joins_sequence_emit_join s3 drive_id prev ip arg_id en tok en' H3).
    - exists {| nid := length (graph s2);
                op := DFG_Drive ip arg_id en; sz := size |}.
      rewrite <- Hs3. cbn [graph nid op].
      split; [ left; reflexivity | split; [ exact Hdid | reflexivity ] ].
    - exists nd. rewrite <- Hs3. cbn [graph].
      split; [ right; exact (Hg02 nd Hnd) | split; [ exact Hnid | exact Hop ] ].
    - exact Hdis.
  Qed.

  (* [joins_sequence] reads only the graph. *)
  Lemma joins_sequence_graph_eq (s1 s2: wst) :
    graph s1 = graph s2 -> joins_sequence (graph s1) -> joins_sequence (graph s2).
  Proof. intro Hg. rewrite Hg. intro H. exact H. Qed.

  Lemma dataflow_ops_joins :
    forall (ops: @tf_ops s_var i_var o_var p_var) en,
      preserves_js (dataflow_ops ctx en ops).
  Proof.
    induction ops as [op | op1 IHo1 op2 IHo2 | cond op1 IHo1 op2 IHo2]; intro en.
    - destruct op as [ | dst e | dst e | ip dst e ]; cbn [dataflow_ops].
      + apply preserves_js_ret.
      + apply preserves_js_bind; [ apply dataflow_expr_joins | intro x ].
        apply preserves_js_set_var.
      + apply preserves_js_bind; [ apply dataflow_expr_joins | intro x ].
        apply preserves_js_set_var.
      + intros s Hs.
        rewrite (bind_red (get_state ctx) _ s s s (get_state_red s)).
        assert (Hg : forall a2 s2, dataflow_expr ctx e (ip_req_sz (tfs_spec_ip ctx ip)) s
                                   = (a2, s2) -> wgmono s s2).
        { intros a2 s2 Ea.
          pose proof (dataflow_expr_grows e (ip_req_sz (tfs_spec_ip ctx ip)) s) as H0.
          rewrite Ea in H0. cbn [snd] in H0. exact H0. }
        apply js_bind_at; [ apply dataflow_expr_joins; exact Hs | intros arg_id s2 Ea H2 ].
        apply js_bind_at;
          [ apply joins_sequence_emit_other;
            [ exact H2 | intros d prev Hc; discriminate Hc ]
          | intros drive_id s3 Ed H3 ].
        apply js_bind_at;
          [ exact (js_call_head s s2 s3 ip arg_id en drive_id _ H3 (Hg _ _ Ea) Ed)
          | intros head_id s4 Eh H4 ].
        apply js_bind_at.
        * unfold stall_chain. destruct (ip_lat (tfs_spec_ip ctx ip));
            [ exact H4
            | apply joins_sequence_emit_other;
              [ exact H4 | intros d prev Hc; discriminate Hc ] ].
        * intros stall_id s5 Es H5.
          apply js_bind_at;
            [ apply joins_sequence_emit_other;
              [ exact H5 | intros d prev Hc; discriminate Hc ]
            | intros samp_id s6 Esa H6 ].
          exact (preserves_js_set_var (DFG_SVar dst) samp_id s6 H6).
    - cbn [dataflow_ops]. apply preserves_js_bind; [ apply IHo1 | intro x ]. apply IHo2.
    - intros s Hs. cbn [dataflow_ops].
      apply js_bind_at; [ apply dataflow_expr_joins; exact Hs | intros cid s1 Ec H1 ].
      rewrite (bind_red (get_state ctx) _ s1 s1 s1 (get_state_red s1)).
      apply js_bind_at; [ apply IHo1; exact H1 | intros u2 s2 E2 H2 ].
      rewrite (bind_red (get_state ctx) _ s2 s2 s2 (get_state_red s2)).
      rewrite (bind_red (put_state ctx _) _ s2 tt _ (put_state_red _ s2)).
      apply js_bind_at; [ apply IHo2; exact H2 | intros u3 s3 E3 H3 ].
      rewrite (bind_red (get_state ctx) _ s3 s3 s3 (get_state_red s3)).
      apply js_bind_at; [ apply preserves_js_merge_maps; exact H3 | intros fv s4 E4 H4 ].
      rewrite (bind_red (get_state ctx) _ s4 s4 s4 (get_state_red s4)).
      cbn [snd]. exact H4.
  Qed.

  Lemma joins_sequence_rev L : joins_sequence L -> joins_sequence (rev L).
  Proof.
    intros H j d prev Hin Hop.
    apply (proj2 (in_rev L j)) in Hin.
    destruct (H j d prev Hin Hop)
      as [p [arg [en [tok [en' [nd [ns [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]]]]]]]].
    exists p, arg, en, tok, en', nd, ns.
    split; [ apply (proj1 (in_rev L nd)); exact H1 |]. split; [ exact H2 |].
    split; [ exact H3 |].
    split; [ apply (proj1 (in_rev L ns)); exact H4 |]. split; [ exact H5 |].
    split; [ exact H6 | exact H7 ].
  Qed.

  (* A second, pointwise invariant, generic in the node predicate: [emit]
     prepends one node, so anything true of every node is preserved by any step
     whose fresh node satisfies it. *)
  Definition all_nodes (Q: @dfg_node_t s_var i_var o_var p_var -> Prop)
      (L: list (@dfg_node_t s_var i_var o_var p_var)) : Prop :=
    forall nd, In nd L -> Q nd.

  Definition preserves_all (Q: @dfg_node_t s_var i_var o_var p_var -> Prop)
      {A} (m: M ctx A) : Prop :=
    forall s, all_nodes Q (graph s) -> all_nodes Q (graph (snd (m s))).

  (* [Q] holds of every node the builder emits EXCEPT a join or a stall, which
     are the two the call sequence places by hand. *)
  Definition Q_plain (Q: @dfg_node_t s_var i_var o_var p_var -> Prop) : Prop :=
    forall n z o, (forall d prev, o <> DFG_Join d prev) ->
                  (forall l a, o <> DFG_Stall l a) ->
      Q {| nid := n; op := o; sz := z |}.

  Lemma preserves_all_ret Q {A} (x: A) : preserves_all Q (ret ctx x).
  Proof. intros s Hs. exact Hs. Qed.

  Lemma preserves_all_bind Q {A B} (m: M ctx A) (f: A -> M ctx B) :
    preserves_all Q m -> (forall x, preserves_all Q (f x)) ->
    preserves_all Q (bind ctx m f).
  Proof.
    intros Hm Hf s Hs. unfold bind.
    specialize (Hm s Hs). destruct (m s) as [x s1]. cbn [snd] in Hm.
    exact (Hf x s1 Hm).
  Qed.

  Lemma all_bind_at Q {A B} (m: M ctx A) (f: A -> M ctx B) (s: wst) :
    all_nodes Q (graph (snd (m s))) ->
    (forall x s1, m s = (x, s1) -> all_nodes Q (graph s1) ->
       all_nodes Q (graph (snd (f x s1)))) ->
    all_nodes Q (graph (snd (bind ctx m f s))).
  Proof.
    intros Hm Hf. unfold bind.
    destruct (m s) as [x s1] eqn:E. cbn [snd] in Hm. exact (Hf x s1 eq_refl Hm).
  Qed.

  Lemma all_nodes_emit Q (s: wst) o size :
    all_nodes Q (graph s) ->
    Q {| nid := length (graph s); op := o; sz := size |} ->
    all_nodes Q (graph (snd (emit ctx o size s))).
  Proof.
    intros Hs Hq. rewrite emit_red. cbn [snd graph].
    intros nd [<- | Hin]; [ exact Hq | exact (Hs nd Hin) ].
  Qed.

  Lemma preserves_all_emit Q o size :
    Q_plain Q ->
    (forall d prev, o <> DFG_Join d prev) -> (forall l a, o <> DFG_Stall l a) ->
    preserves_all Q (emit ctx o size).
  Proof.
    intros HQ H1 H2 s Hs. apply all_nodes_emit; [ exact Hs | apply HQ; assumption ].
  Qed.

  Lemma preserves_all_set_var Q v id : preserves_all Q (set_var ctx v id).
  Proof.
    intros s Hs. unfold set_var, bind, get_state, put_state. cbn [snd graph]. exact Hs.
  Qed.

  Lemma preserves_all_get_var Q : Q_plain Q -> forall v, preserves_all Q (get_var ctx v).
  Proof.
    intros HQ v s Hs. unfold get_var, bind, get_state.
    destruct (BitsToLists.list_assoc (var_map s) v) as [id |]; [ exact Hs |].
    destruct (read_var ctx v s) as [id s'] eqn:Er. cbn [snd].
    destruct (read_var_cases v s id s' Er) as [[_ [_ ->]] | Hem]; [ exact Hs |].
    apply (f_equal snd) in Hem. cbn [snd] in Hem. rewrite <- Hem.
    apply all_nodes_emit; [ exact Hs |].
    apply HQ; intros; discriminate.
  Qed.

  Lemma preserves_all_ensure_var Q : Q_plain Q -> forall v, preserves_all Q (ensure_var ctx v).
  Proof.
    intros HQ v s Hs. unfold ensure_var, bind, get_state, put_state, ret.
    destruct (emit ctx (DFG_Var v) (dfg_var_size ctx v) s) as [id s1] eqn:Ee.
    cbn [snd graph].
    pose proof (all_nodes_emit Q s (DFG_Var v) (dfg_var_size ctx v) Hs
                  ltac:(apply HQ; intros; discriminate)) as H.
    rewrite Ee in H. cbn [snd] in H. exact H.
  Qed.

  Lemma preserves_all_merge_key Q : Q_plain Q ->
    forall c k vt ve, preserves_all Q (merge_key ctx c k vt ve).
  Proof.
    intros HQ c k vt ve. unfold merge_key.
    destruct vt as [x |]; destruct ve as [y |].
    - destruct (eq_dec x y); [ apply preserves_all_ret |].
      apply preserves_all_bind;
        [ apply preserves_all_emit; [ exact HQ | intros; discriminate | intros; discriminate ]
        | intro z; apply preserves_all_ret ].
    - apply preserves_all_bind; [ apply preserves_all_ensure_var; exact HQ | intro z ].
      apply preserves_all_bind;
        [ apply preserves_all_emit; [ exact HQ | intros; discriminate | intros; discriminate ]
        | intro w; apply preserves_all_ret ].
    - apply preserves_all_bind; [ apply preserves_all_ensure_var; exact HQ | intro z ].
      apply preserves_all_bind;
        [ apply preserves_all_emit; [ exact HQ | intros; discriminate | intros; discriminate ]
        | intro w; apply preserves_all_ret ].
    - apply preserves_all_ret.
  Qed.

  Lemma preserves_all_merge_loop Q : Q_plain Q ->
    forall c mt me keys acc, preserves_all Q (merge_loop ctx c mt me keys acc).
  Proof.
    intros HQ c mt me keys. induction keys as [| [k kid] keys IH]; intro acc;
      cbn [merge_loop]; [ apply preserves_all_ret |].
    destruct (BitsToLists.list_assoc acc k) as [x |]; [ apply IH |].
    apply preserves_all_bind; [ apply preserves_all_merge_key; exact HQ | intro r ].
    destruct r as [fid |]; apply IH.
  Qed.

  Lemma dataflow_expr_all Q : Q_plain Q ->
    forall e sz, preserves_all Q (dataflow_expr ctx e sz).
  Proof.
    intros HQ e. induction e as [ c | v | v | v | uop src IHsrc
                                | bop s1 IH1 s2 IH2 | c IHc t IHt e IHe ];
      intro sz; cbn [dataflow_expr].
    - apply preserves_all_emit; [ exact HQ | intros; discriminate | intros; discriminate ].
    - apply preserves_all_bind; [ apply preserves_all_get_var; exact HQ | intro x ].
      destruct (Nat.eqb _ sz);
        [ apply preserves_all_ret
        | apply preserves_all_emit; [ exact HQ | intros; discriminate | intros; discriminate ] ].
    - apply preserves_all_bind;
        [ apply preserves_all_emit; [ exact HQ | intros; discriminate | intros; discriminate ]
        | intro x ].
      destruct (Nat.eqb _ sz);
        [ apply preserves_all_ret
        | apply preserves_all_emit; [ exact HQ | intros; discriminate | intros; discriminate ] ].
    - apply preserves_all_bind; [ apply preserves_all_get_var; exact HQ | intro x ].
      destruct (Nat.eqb _ sz);
        [ apply preserves_all_ret
        | apply preserves_all_emit; [ exact HQ | intros; discriminate | intros; discriminate ] ].
    - destruct uop;
        (apply preserves_all_bind; [ apply IHsrc | intro x ];
         apply preserves_all_emit; [ exact HQ | intros; discriminate | intros; discriminate ]).
    - destruct bop;
        (apply preserves_all_bind; [ apply IH1 | intro x ];
         apply preserves_all_bind; [ apply IH2 | intro y ];
         apply preserves_all_emit; [ exact HQ | intros; discriminate | intros; discriminate ]).
    - apply preserves_all_bind; [ apply IHc | intro x ].
      apply preserves_all_bind; [ apply IHt | intro y ].
      apply preserves_all_bind; [ apply IHe | intro z ].
      apply preserves_all_emit; [ exact HQ | intros; discriminate | intros; discriminate ].
  Qed.

  (* The two nodes a call places by hand sit immediately above what they wait
     on: [emit] hands out consecutive ids and nothing intervenes. *)
  Definition succ_arg_node (nd: @dfg_node_t s_var i_var o_var p_var) : Prop :=
    (forall d prev, op nd = DFG_Join d prev -> nid nd = S d)
    /\ (forall l a, op nd = DFG_Stall l a -> nid nd = S a).

  Lemma Q_plain_succ : Q_plain succ_arg_node.
  Proof.
    intros n z o H1 H2. split.
    - intros d prev Hop. cbn [op] in Hop. exfalso. exact (H1 d prev Hop).
    - intros l a Hop. cbn [op] in Hop. exfalso. exact (H2 l a Hop).
  Qed.

  Lemma dataflow_ops_succ :
    forall (ops: @tf_ops s_var i_var o_var p_var) en,
      preserves_all succ_arg_node (dataflow_ops ctx en ops).
  Proof.
    induction ops as [op | op1 IHo1 op2 IHo2 | cond op1 IHo1 op2 IHo2]; intro en.
    - destruct op as [ | dst e | dst e | ip dst e ]; cbn [dataflow_ops].
      + apply preserves_all_ret.
      + apply preserves_all_bind;
          [ apply dataflow_expr_all; apply Q_plain_succ | intro x ].
        apply preserves_all_set_var.
      + apply preserves_all_bind;
          [ apply dataflow_expr_all; apply Q_plain_succ | intro x ].
        apply preserves_all_set_var.
      + intros s Hs.
        rewrite (bind_red (get_state ctx) _ s s s (get_state_red s)).
        apply all_bind_at;
          [ apply dataflow_expr_all; [ apply Q_plain_succ | exact Hs ]
          | intros arg_id s2 Ea H2 ].
        apply all_bind_at;
          [ apply all_nodes_emit;
            [ exact H2 | apply Q_plain_succ; intros; discriminate ]
          | intros drive_id s3 Ed H3 ].
        rewrite emit_red in Ed. injection Ed as Hdid Hs3.
        assert (H3len : length (graph s3) = S drive_id).
        { rewrite <- Hs3. cbn [graph length]. rewrite Hdid. reflexivity. }
        destruct (last_sample ctx s ip en) as [prev |] eqn:Elast.
        * apply all_bind_at.
          -- apply all_nodes_emit; [ exact H3 |]. split.
             ++ intros d0 prev0 Hop. cbn [op nid] in *. injection Hop as <- <-.
                exact H3len.
             ++ intros l a Hop. cbn [op] in Hop. discriminate Hop.
          -- intros head_id s4 Eh H4.
             rewrite emit_red in Eh. injection Eh as Hhid Hs4.
             assert (H4len : length (graph s4) = S head_id).
             { rewrite <- Hs4. cbn [graph length]. rewrite Hhid. reflexivity. }
             apply all_bind_at.
             ++ unfold stall_chain. destruct (ip_lat (tfs_spec_ip ctx ip));
                  [ exact H4 |].
                apply all_nodes_emit; [ exact H4 |]. split.
                ** intros d0 prev0 Hop. cbn [op] in Hop. discriminate Hop.
                ** intros l a Hop. cbn [op nid] in *. injection Hop as <- <-.
                   exact H4len.
             ++ intros stall_id s5 Es H5.
                apply all_bind_at;
                  [ apply all_nodes_emit;
                    [ exact H5 | apply Q_plain_succ; intros; discriminate ]
                  | intros samp_id s6 Esa H6 ].
                exact (preserves_all_set_var succ_arg_node (DFG_SVar dst) samp_id s6 H6).
        * rewrite (bind_red (ret ctx drive_id) _ s3 drive_id s3 eq_refl).
          apply all_bind_at.
          -- unfold stall_chain. destruct (ip_lat (tfs_spec_ip ctx ip));
               [ exact H3 |].
             apply all_nodes_emit; [ exact H3 |]. split.
             ++ intros d0 prev0 Hop. cbn [op] in Hop. discriminate Hop.
             ++ intros l a Hop. cbn [op nid] in *. injection Hop as <- <-.
                exact H3len.
          -- intros stall_id s5 Es H5.
             apply all_bind_at;
               [ apply all_nodes_emit;
                 [ exact H5 | apply Q_plain_succ; intros; discriminate ]
               | intros samp_id s6 Esa H6 ].
             exact (preserves_all_set_var succ_arg_node (DFG_SVar dst) samp_id s6 H6).
    - cbn [dataflow_ops]. apply preserves_all_bind; [ apply IHo1 | intro x ]. apply IHo2.
    - intros s Hs. cbn [dataflow_ops].
      apply all_bind_at;
        [ apply dataflow_expr_all; [ apply Q_plain_succ | exact Hs ] | intros cid s1 Ec H1 ].
      rewrite (bind_red (get_state ctx) _ s1 s1 s1 (get_state_red s1)).
      apply all_bind_at; [ apply IHo1; exact H1 | intros u2 s2 E2 H2 ].
      rewrite (bind_red (get_state ctx) _ s2 s2 s2 (get_state_red s2)).
      rewrite (bind_red (put_state ctx _) _ s2 tt _ (put_state_red _ s2)).
      apply all_bind_at; [ apply IHo2; exact H2 | intros u3 s3 E3 H3 ].
      rewrite (bind_red (get_state ctx) _ s3 s3 s3 (get_state_red s3)).
      apply all_bind_at;
        [ apply preserves_all_merge_loop; [ apply Q_plain_succ | exact H3 ]
        | intros fv s4 E4 H4 ].
      rewrite (bind_red (get_state ctx) _ s4 s4 s4 (get_state_red s4)).
      cbn [snd]. exact H4.
  Qed.

  Lemma all_nodes_rev Q L : all_nodes Q L -> all_nodes Q (rev L).
  Proof. intros H nd Hin. apply H. apply (proj2 (in_rev L nd)). exact Hin. Qed.

  Lemma succ_args_build_dfg (act: tfs_action sched) :
    all_nodes succ_arg_node (graph (build_dfg ctx act)).
  Proof.
    unfold build_dfg.
    pose proof (dataflow_ops_succ (tfs_spec_action_ops ctx act) []
                  {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0 |} ];
                     var_map := [] |}) as H.
    cbn beta in H.
    assert (Hbase : all_nodes succ_arg_node
              (graph {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0 |} ];
                        var_map := [] |})).
    { intros nd Hin. cbn [graph In] in Hin. destruct Hin as [<- | []].
      split; intros; cbn [op] in *; discriminate. }
    specialize (H Hbase).
    destruct (dataflow_ops ctx [] (tfs_spec_action_ops ctx act)
                {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0 |} ];
                   var_map := [] |}) as [u final] eqn:Ed.
    cbn [snd] in H. cbn [graph].
    apply all_nodes_rev. exact H.
  Qed.

  (* The third and last builder invariant, and this one is generic in the
     graph predicate: every step but a call.s own emits a node that is neither
     a drive, a sample nor a join, and that is all these lemmas need. *)
  Definition P_emit_expr (P: list (@dfg_node_t s_var i_var o_var p_var) -> Prop) : Prop :=
    forall L o z,
      (forall p arg en, o <> DFG_Drive p arg en) ->
      (forall p tok en, o <> DFG_Sample p tok en) ->
      (forall d prev, o <> DFG_Join d prev) ->
      P L -> P ({| nid := length L; op := o; sz := z |} :: L).

  Definition preserves_g (P: list (@dfg_node_t s_var i_var o_var p_var) -> Prop)
      {A} (m: M ctx A) : Prop :=
    forall s, P (graph s) -> P (graph (snd (m s))).

  Lemma preserves_g_ret P {A} (x: A) : preserves_g P (ret ctx x).
  Proof. intros s Hs. exact Hs. Qed.

  Lemma preserves_g_bind P {A B} (m: M ctx A) (f: A -> M ctx B) :
    preserves_g P m -> (forall x, preserves_g P (f x)) -> preserves_g P (bind ctx m f).
  Proof.
    intros Hm Hf s Hs. unfold bind.
    specialize (Hm s Hs). destruct (m s) as [x s1]. cbn [snd] in Hm.
    exact (Hf x s1 Hm).
  Qed.

  Lemma g_bind_at P {A B} (m: M ctx A) (f: A -> M ctx B) (s: wst) :
    P (graph (snd (m s))) ->
    (forall x s1, m s = (x, s1) -> P (graph s1) -> P (graph (snd (f x s1)))) ->
    P (graph (snd (bind ctx m f s))).
  Proof.
    intros Hm Hf. unfold bind.
    destruct (m s) as [x s1] eqn:E. cbn [snd] in Hm. exact (Hf x s1 eq_refl Hm).
  Qed.

  Lemma preserves_g_emit P o size :
    P_emit_expr P ->
    (forall p arg en, o <> DFG_Drive p arg en) ->
    (forall p tok en, o <> DFG_Sample p tok en) ->
    (forall d prev, o <> DFG_Join d prev) ->
    preserves_g P (emit ctx o size).
  Proof.
    intros HP H1 H2 H3 s Hs. rewrite emit_red. cbn [snd graph].
    exact (HP (graph s) o size H1 H2 H3 Hs).
  Qed.

  Lemma preserves_g_set_var P v id : preserves_g P (set_var ctx v id).
  Proof.
    intros s Hs. unfold set_var, bind, get_state, put_state. cbn [snd graph]. exact Hs.
  Qed.

  Lemma preserves_g_get_var P : P_emit_expr P -> forall v, preserves_g P (get_var ctx v).
  Proof.
    intros HP v s Hs. unfold get_var, bind, get_state.
    destruct (BitsToLists.list_assoc (var_map s) v) as [id |]; [ exact Hs |].
    destruct (read_var ctx v s) as [id s'] eqn:Er. cbn [snd].
    destruct (read_var_cases v s id s' Er) as [[_ [_ ->]] | Hem]; [ exact Hs |].
    apply (f_equal snd) in Hem. cbn [snd] in Hem. rewrite <- Hem.
    assert (H : preserves_g P (emit ctx (DFG_Var v) (dfg_var_size ctx v)))
      by (apply (preserves_g_emit P _ _ HP); intros; discriminate).
    exact (H s Hs).
  Qed.

  Lemma preserves_g_ensure_var P : P_emit_expr P -> forall v, preserves_g P (ensure_var ctx v).
  Proof.
    intros HP v s Hs. unfold ensure_var, bind, get_state, put_state, ret.
    destruct (emit ctx (DFG_Var v) (dfg_var_size ctx v) s) as [id s1] eqn:Ee.
    cbn [snd graph].
    assert (H : preserves_g P (emit ctx (DFG_Var v) (dfg_var_size ctx v)))
      by (apply (preserves_g_emit P _ _ HP); intros; discriminate).
    specialize (H s Hs). rewrite Ee in H. cbn [snd] in H. exact H.
  Qed.

  Lemma preserves_g_merge_key P : P_emit_expr P ->
    forall c k vt ve, preserves_g P (merge_key ctx c k vt ve).
  Proof.
    intros HP c k vt ve. unfold merge_key.
    assert (Hphi : forall a b, preserves_g P (emit ctx (DFG_Phi c a b) (dfg_var_size ctx k)))
      by (intros a b; apply (preserves_g_emit P _ _ HP); intros; discriminate).
    destruct vt as [x |]; destruct ve as [y |].
    - destruct (eq_dec x y); [ apply preserves_g_ret |].
      apply preserves_g_bind; [ apply Hphi | intro z; apply preserves_g_ret ].
    - apply preserves_g_bind; [ apply preserves_g_ensure_var; exact HP | intro z ].
      apply preserves_g_bind; [ apply Hphi | intro w; apply preserves_g_ret ].
    - apply preserves_g_bind; [ apply preserves_g_ensure_var; exact HP | intro z ].
      apply preserves_g_bind; [ apply Hphi | intro w; apply preserves_g_ret ].
    - apply preserves_g_ret.
  Qed.

  Lemma preserves_g_merge_loop P : P_emit_expr P ->
    forall c mt me keys acc, preserves_g P (merge_loop ctx c mt me keys acc).
  Proof.
    intros HP c mt me keys. induction keys as [| [k kid] keys IH]; intro acc;
      cbn [merge_loop]; [ apply preserves_g_ret |].
    destruct (BitsToLists.list_assoc acc k) as [x |]; [ apply IH |].
    apply preserves_g_bind; [ apply preserves_g_merge_key; exact HP | intro r ].
    destruct r as [fid |]; apply IH.
  Qed.

  Lemma dataflow_expr_g P : P_emit_expr P ->
    forall e sz, preserves_g P (dataflow_expr ctx e sz).
  Proof.
    intros HP e. induction e as [ c | v | v | v | uop src IHsrc
                                | bop s1 IH1 s2 IH2 | c IHc t IHt e IHe ];
      intro sz;
      assert (Hem : forall o size,
                (forall p arg en, o <> DFG_Drive p arg en) ->
                (forall p tok en, o <> DFG_Sample p tok en) ->
                (forall d prev, o <> DFG_Join d prev) ->
                preserves_g P (emit ctx o size))
        by (intros; apply (preserves_g_emit P _ _ HP); assumption);
      cbn [dataflow_expr].
    - apply Hem; intros; discriminate.
    - apply preserves_g_bind; [ apply preserves_g_get_var; exact HP | intro x ].
      destruct (Nat.eqb _ sz);
        [ apply preserves_g_ret | apply Hem; intros; discriminate ].
    - apply preserves_g_bind; [ apply Hem; intros; discriminate | intro x ].
      destruct (Nat.eqb _ sz);
        [ apply preserves_g_ret | apply Hem; intros; discriminate ].
    - apply preserves_g_bind; [ apply preserves_g_get_var; exact HP | intro x ].
      destruct (Nat.eqb _ sz);
        [ apply preserves_g_ret | apply Hem; intros; discriminate ].
    - destruct uop;
        (apply preserves_g_bind; [ apply IHsrc | intro x ];
         apply Hem; intros; discriminate).
    - destruct bop;
        (apply preserves_g_bind; [ apply IH1 | intro x ];
         apply preserves_g_bind; [ apply IH2 | intro y ];
         apply Hem; intros; discriminate).
    - apply preserves_g_bind; [ apply IHc | intro x ].
      apply preserves_g_bind; [ apply IHt | intro y ].
      apply preserves_g_bind; [ apply IHe | intro z ].
      apply Hem; intros; discriminate.
  Qed.

  (* Samples are only ever added by a call, so a step that adds none leaves
     every sample of its result inside the graph it started from. *)
  Definition samples_within (L0 L: list (@dfg_node_t s_var i_var o_var p_var)) : Prop :=
    forall nd, In nd L -> forall p tok en, op nd = DFG_Sample p tok en -> In nd L0.

  Lemma P_emit_expr_samples L0 : P_emit_expr (samples_within L0).
  Proof.
    intros L o z H1 H2 H3 H nd [<- | Hin] p tok en Hop; cbn [op] in Hop;
      [ exfalso; exact (H2 p tok en Hop) | exact (H nd Hin p tok en Hop) ].
  Qed.

  Definition nids_bounded (L: list (@dfg_node_t s_var i_var o_var p_var)) : Prop :=
    forall nd, In nd L -> nid nd < length L.

  (* THE LAST BUILDER INVARIANT: a call that could see an earlier call.s answer
     on the same port is sequenced behind it by a join. *)
  Definition calls_main (L: list (@dfg_node_t s_var i_var o_var p_var)) : Prop :=
    forall (p: p_var) m arg en s tok en',
      (exists nm, In nm L /\ nid nm = m /\ op nm = DFG_Drive p arg en) ->
      (exists ns, In ns L /\ nid ns = s /\ op ns = DFG_Sample p tok en') ->
      s < m -> guards_disjoint en en' = false ->
      exists j prev, In j L /\ op j = DFG_Join m prev /\ s <= prev.

  Definition calls_sequenced (L: list (@dfg_node_t s_var i_var o_var p_var)) : Prop :=
    nids_bounded L /\ ids_desc L /\ calls_main L.

  Lemma nids_bounded_cons L o z :
    nids_bounded L -> nids_bounded ({| nid := length L; op := o; sz := z |} :: L).
  Proof.
    intros H nd [<- | Hin]; cbn [nid length]; [ lia |].
    pose proof (H nd Hin). cbn [length]. lia.
  Qed.

  Lemma ids_desc_cons L o z :
    nids_bounded L -> ids_desc L ->
    ids_desc ({| nid := length L; op := o; sz := z |} :: L).
  Proof.
    intros Hb Hd pre a rest Hsplit M HM.
    destruct pre as [| b pre]; cbn [app] in Hsplit.
    - injection Hsplit as <- <-. cbn [nid]. exact (Hb M HM).
    - injection Hsplit as <- Hrest.
      exact (Hd pre a rest Hrest M HM).
  Qed.

  (* A step that emits neither a drive nor a sample nor a join keeps it. *)
  Lemma P_emit_expr_calls : P_emit_expr calls_sequenced.
  Proof.
    intros L o z H1 H2 H3 [Hb [Hd Hmain]].
    split; [ exact (nids_bounded_cons L o z Hb) |].
    split; [ exact (ids_desc_cons L o z Hb Hd) |].
    intros p m arg en s tok en' Hdr Hsa Hlt Hdis.
    destruct Hdr as [nm [Hnm [Hmid Hmop]]].
    destruct Hsa as [ns [Hns [Hsid Hsop]]].
    cbn [In] in Hnm, Hns.
    destruct Hnm as [<- | Hnm]; [ cbn [op] in Hmop; exfalso; exact (H1 p arg en Hmop) |].
    destruct Hns as [<- | Hns]; [ cbn [op] in Hsop; exfalso; exact (H2 p tok en' Hsop) |].
    destruct (Hmain p m arg en s tok en'
                (ex_intro _ nm (conj Hnm (conj Hmid Hmop)))
                (ex_intro _ ns (conj Hns (conj Hsid Hsop))) Hlt Hdis)
      as [j [prev [Hj [Hjop Hle]]]].
    exists j, prev. split; [ right; exact Hj | split; [ exact Hjop | exact Hle ] ].
  Qed.

  (* Prepending the call.s own SAMPLE: its id is above every drive already
     present, so it can only be the later end of a pair. *)
  Lemma calls_sequenced_cons_sample L (p: p_var) tok en z :
    calls_sequenced L ->
    calls_sequenced ({| nid := length L; op := DFG_Sample p tok en; sz := z |} :: L).
  Proof.
    intros [Hb [Hd Hmain]].
    split; [ apply nids_bounded_cons; exact Hb |].
    split; [ apply ids_desc_cons; assumption |].
    intros p2 m arg en2 s tok2 en' Hdr Hsa Hlt Hdis.
    destruct Hdr as [nm [Hnm [Hmid Hmop]]].
    destruct Hsa as [ns [Hns [Hsid Hsop]]].
    cbn [In] in Hnm, Hns.
    destruct Hnm as [<- | Hnm]; [ cbn [op] in Hmop; discriminate Hmop |].
    destruct Hns as [<- | Hns].
    - exfalso. cbn [nid] in Hsid. subst s.
      pose proof (Hb nm Hnm) as Hlen. lia.
    - destruct (Hmain p2 m arg en2 s tok2 en'
                  (ex_intro _ nm (conj Hnm (conj Hmid Hmop)))
                  (ex_intro _ ns (conj Hns (conj Hsid Hsop))) Hlt Hdis)
        as [j [prev [Hj [Hjop Hle]]]].
      exists j, prev. split; [ right; exact Hj | split; [ exact Hjop | exact Hle ] ].
  Qed.

  (* THE CALL.S OWN STEP: the drive and, when [last_sample] found one, the join.
     This is the only place the obligation is ever discharged. *)
  Lemma calls_sequenced_head
        (s0 s2 s3: wst) (ip: p_var) arg_id en size drive_id :
    calls_sequenced (graph s2) ->
    ids_desc (graph s0) ->
    samples_within (graph s0) (graph s2) ->
    emit ctx (DFG_Drive ip arg_id en) size s2 = (drive_id, s3) ->
    calls_sequenced
      (graph (snd (match last_sample ctx s0 ip en with
                   | Some prev => emit ctx (DFG_Join drive_id prev) 1
                   | None => ret ctx drive_id
                   end s3))).
  Proof.
    intros [Hb [Hd Hmain]] Hd0 Hsw Ed.
    rewrite emit_red in Ed. injection Ed as Hdid Hs3.
    assert (Hb3 : nids_bounded (graph s3)).
    { rewrite <- Hs3. cbn [graph]. apply nids_bounded_cons. exact Hb. }
    assert (Hd3 : ids_desc (graph s3)).
    { rewrite <- Hs3. cbn [graph]. apply ids_desc_cons; assumption. }
    destruct (last_sample ctx s0 ip en) as [prev |] eqn:Elast.
    - rewrite emit_red. cbn [snd graph].
      split; [ apply nids_bounded_cons; exact Hb3 |].
      split; [ apply ids_desc_cons; assumption |].
      intros p2 m arg en2 s tok2 en' Hdr Hsa Hlt Hdis.
      destruct Hdr as [nm [Hnm [Hmid Hmop]]].
      destruct Hsa as [ns [Hns [Hsid Hsop]]].
      cbn [In] in Hnm, Hns.
      destruct Hnm as [<- | Hnm]; [ cbn [op] in Hmop; discriminate Hmop |].
      destruct Hns as [<- | Hns]; [ cbn [op] in Hsop; discriminate Hsop |].
      rewrite <- Hs3 in Hnm, Hns. cbn [graph In] in Hnm, Hns.
      destruct Hns as [<- | Hns]; [ cbn [op] in Hsop; discriminate Hsop |].
      assert (Hns0 : In ns (graph s0)) by exact (Hsw ns Hns p2 tok2 en' Hsop).
      destruct Hnm as [<- | Hnm].
      + cbn [op nid] in Hmop, Hmid. injection Hmop as <- <- <-.
        exists {| nid := length (graph s3); op := DFG_Join drive_id prev; sz := 1 |}, prev.
        split; [ left; reflexivity |]. cbn [op]. rewrite <- Hmid, <- Hdid.
        split; [ reflexivity |].
        rewrite <- Hsid.
        exact (last_sample_max s0 ip en ns tok2 en' prev Hd0 Hns0 Hsop Hdis Elast).
      + destruct (Hmain p2 m arg en2 s tok2 en'
                    (ex_intro _ nm (conj Hnm (conj Hmid Hmop)))
                    (ex_intro _ ns (conj Hns (conj Hsid Hsop))) Hlt Hdis)
          as [j [prev2 [Hj [Hjop Hle]]]].
        exists j, prev2. split; [ right; rewrite <- Hs3; cbn [graph]; right; exact Hj |].
        split; [ exact Hjop | exact Hle ].
    - cbn [snd].
      split; [ exact Hb3 |]. split; [ exact Hd3 |].
      intros p2 m arg en2 s tok2 en' Hdr Hsa Hlt Hdis.
      destruct Hdr as [nm [Hnm [Hmid Hmop]]].
      destruct Hsa as [ns [Hns [Hsid Hsop]]].
      rewrite <- Hs3 in Hnm, Hns. cbn [graph In] in Hnm, Hns.
      destruct Hns as [<- | Hns]; [ cbn [op] in Hsop; discriminate Hsop |].
      assert (Hns0 : In ns (graph s0)) by exact (Hsw ns Hns p2 tok2 en' Hsop).
      destruct Hnm as [<- | Hnm].
      + exfalso. cbn [op] in Hmop. injection Hmop as <- <- <-.
        destruct (last_sample_found s0 ip en ns tok2 en' Hns0 Hsop Hdis) as [q Hq].
        rewrite Elast in Hq. discriminate Hq.
      + destruct (Hmain p2 m arg en2 s tok2 en'
                    (ex_intro _ nm (conj Hnm (conj Hmid Hmop)))
                    (ex_intro _ ns (conj Hns (conj Hsid Hsop))) Hlt Hdis)
          as [j [prev2 [Hj [Hjop Hle]]]].
        exists j, prev2. split; [ rewrite <- Hs3; cbn [graph]; right; exact Hj |].
        split; [ exact Hjop | exact Hle ].
  Qed.

  Lemma preserves_g_merge_maps P : P_emit_expr P ->
    forall c mo mt me, preserves_g P (merge_maps ctx c mo mt me).
  Proof. intros HP c mo mt me. apply preserves_g_merge_loop. exact HP. Qed.

  Lemma dataflow_ops_calls :
    forall (ops: @tf_ops s_var i_var o_var p_var) en,
      preserves_g calls_sequenced (dataflow_ops ctx en ops).
  Proof.
    induction ops as [op | op1 IHo1 op2 IHo2 | cond op1 IHo1 op2 IHo2]; intro en.
    - destruct op as [ | dst e | dst e | ip dst e ]; cbn [dataflow_ops].
      + apply preserves_g_ret.
      + apply preserves_g_bind;
          [ apply dataflow_expr_g; apply P_emit_expr_calls | intro x ].
        apply preserves_g_set_var.
      + apply preserves_g_bind;
          [ apply dataflow_expr_g; apply P_emit_expr_calls | intro x ].
        apply preserves_g_set_var.
      + intros s Hs.
        pose proof (proj1 (proj2 Hs)) as Hd0.
        rewrite (bind_red (get_state ctx) _ s s s (get_state_red s)).
        assert (Hsw0 : samples_within (graph s) (graph s))
          by (intros nd Hin q tok en' _; exact Hin).
        pose proof (dataflow_expr_g (samples_within (graph s))
                      (P_emit_expr_samples (graph s)) e
                      (ip_req_sz (tfs_spec_ip ctx ip)) s Hsw0) as Hsw.
        pose proof (dataflow_expr_g calls_sequenced P_emit_expr_calls e
                      (ip_req_sz (tfs_spec_ip ctx ip)) s Hs) as Hcs.
        destruct (dataflow_expr ctx e (ip_req_sz (tfs_spec_ip ctx ip)) s)
          as [arg_id s2] eqn:Ea.
        cbn [snd] in Hsw, Hcs.
        rewrite (bind_red _ _ s arg_id s2 Ea).
        destruct (emit ctx (DFG_Drive ip arg_id en) (ip_req_sz (tfs_spec_ip ctx ip)) s2)
          as [drive_id s3] eqn:Ed.
        rewrite (bind_red _ _ s2 drive_id s3 Ed).
        pose proof (calls_sequenced_head s s2 s3 ip arg_id en
                      (ip_req_sz (tfs_spec_ip ctx ip)) drive_id Hcs Hd0 Hsw Ed) as Hhead.
        apply (g_bind_at calls_sequenced); [ exact Hhead | intros head_id s4 Eh H4 ].
        apply (g_bind_at calls_sequenced).
        * unfold stall_chain. destruct (ip_lat (tfs_spec_ip ctx ip)); [ exact H4 |].
          rewrite emit_red. cbn [snd graph].
          apply P_emit_expr_calls;
            [ intros; discriminate | intros; discriminate | intros; discriminate
            | exact H4 ].
        * intros stall_id s5 Es H5.
          apply (g_bind_at calls_sequenced).
          -- rewrite emit_red. cbn [snd graph].
             apply calls_sequenced_cons_sample. exact H5.
          -- intros samp_id s6 Esa H6.
             exact (preserves_g_set_var calls_sequenced (DFG_SVar dst) samp_id s6 H6).
    - cbn [dataflow_ops]. apply preserves_g_bind; [ apply IHo1 | intro x ]. apply IHo2.
    - intros s Hs. cbn [dataflow_ops].
      apply (g_bind_at calls_sequenced);
        [ apply dataflow_expr_g; [ apply P_emit_expr_calls | exact Hs ]
        | intros cid s1 Ec H1 ].
      rewrite (bind_red (get_state ctx) _ s1 s1 s1 (get_state_red s1)).
      apply (g_bind_at calls_sequenced); [ apply IHo1; exact H1 | intros u2 s2 E2 H2 ].
      rewrite (bind_red (get_state ctx) _ s2 s2 s2 (get_state_red s2)).
      rewrite (bind_red (put_state ctx _) _ s2 tt _ (put_state_red _ s2)).
      apply (g_bind_at calls_sequenced); [ apply IHo2; exact H2 | intros u3 s3 E3 H3 ].
      rewrite (bind_red (get_state ctx) _ s3 s3 s3 (get_state_red s3)).
      apply (g_bind_at calls_sequenced);
        [ apply (preserves_g_merge_maps calls_sequenced);
          [ apply P_emit_expr_calls | exact H3 ]
        | intros fv s4 E4 H4 ].
      rewrite (bind_red (get_state ctx) _ s4 s4 s4 (get_state_red s4)).
      cbn [snd]. exact H4.
  Qed.

  (* The exported graph is the REVERSE, so [ids_desc] does not survive -- but
     the clause that matters is [In]-based and does. *)
  Lemma calls_main_rev L : calls_main L -> calls_main (rev L).
  Proof.
    intros H p m arg en s tok en' Hdr Hsa Hlt Hdis.
    destruct Hdr as [nm [Hnm [Hmid Hmop]]].
    destruct Hsa as [ns [Hns [Hsid Hsop]]].
    apply (proj2 (in_rev L nm)) in Hnm.
    apply (proj2 (in_rev L ns)) in Hns.
    destruct (H p m arg en s tok en'
                (ex_intro _ nm (conj Hnm (conj Hmid Hmop)))
                (ex_intro _ ns (conj Hns (conj Hsid Hsop))) Hlt Hdis)
      as [j [prev [Hj [Hjop Hle]]]].
    exists j, prev.
    split; [ apply (proj1 (in_rev L j)); exact Hj | split; [ exact Hjop | exact Hle ] ].
  Qed.

  Lemma calls_main_build_dfg (act: tfs_action sched) :
    calls_main (graph (build_dfg ctx act)).
  Proof.
    unfold build_dfg.
    pose proof (dataflow_ops_calls (tfs_spec_action_ops ctx act) []
                  {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0 |} ];
                     var_map := [] |}) as H.
    cbn beta in H.
    assert (Hbase : calls_sequenced
              (graph {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0 |} ];
                        var_map := [] |})).
    { split; [| split ].
      - intros nd Hin. cbn [graph In length] in *. destruct Hin as [<- | []].
        cbn [nid]. lia.
      - intros pre a rest Hsplit M HM. cbn [graph] in Hsplit.
        destruct pre as [| b pre]; cbn [app] in Hsplit.
        + injection Hsplit as <- <-. destruct HM.
        + injection Hsplit as <- Hr. destruct pre; cbn [app] in Hr; discriminate Hr.
      - intros p m arg en s tok en' [nm [Hnm [_ Hmop]]] _ _ _.
        cbn [graph In] in Hnm. destruct Hnm as [<- | []].
        cbn [op] in Hmop. discriminate Hmop. }
    specialize (H Hbase).
    destruct (dataflow_ops ctx [] (tfs_spec_action_ops ctx act)
                {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0 |} ];
                   var_map := [] |}) as [u final] eqn:Ed.
    cbn [snd] in H. cbn [graph].
    apply calls_main_rev. exact (proj2 (proj2 H)).
  Qed.

  (* And a sample sits immediately above its token, by the same emission
     arithmetic.  Carried separately because [Q_plain] lets a step emit a
     sample, which this clause is not vacuous on. *)
  Definition succ_sample_node (nd: @dfg_node_t s_var i_var o_var p_var) : Prop :=
    forall p tok en, op nd = DFG_Sample p tok en -> nid nd = S tok.

  Lemma P_emit_expr_ssucc : P_emit_expr (all_nodes succ_sample_node).
  Proof.
    intros L o z H1 H2 H3 H nd [<- | Hin] p tok en Hop; cbn [op] in Hop;
      [ exfalso; exact (H2 p tok en Hop) | exact (H nd Hin p tok en Hop) ].
  Qed.

  Lemma dataflow_ops_ssucc :
    forall (ops: @tf_ops s_var i_var o_var p_var) en,
      preserves_g (all_nodes succ_sample_node) (dataflow_ops ctx en ops).
  Proof.
    induction ops as [op | op1 IHo1 op2 IHo2 | cond op1 IHo1 op2 IHo2]; intro en.
    - destruct op as [ | dst e | dst e | ip dst e ]; cbn [dataflow_ops].
      + apply preserves_g_ret.
      + apply preserves_g_bind;
          [ apply dataflow_expr_g; apply P_emit_expr_ssucc | intro x ].
        apply preserves_g_set_var.
      + apply preserves_g_bind;
          [ apply dataflow_expr_g; apply P_emit_expr_ssucc | intro x ].
        apply preserves_g_set_var.
      + intros s Hs.
        rewrite (bind_red (get_state ctx) _ s s s (get_state_red s)).
        apply (g_bind_at (all_nodes succ_sample_node));
          [ apply dataflow_expr_g; [ apply P_emit_expr_ssucc | exact Hs ]
          | intros arg_id s2 Ea H2 ].
        apply (g_bind_at (all_nodes succ_sample_node));
          [ apply all_nodes_emit; [ exact H2 | intros q tok en2 Hop; discriminate Hop ]
          | intros drive_id s3 Ed H3 ].
        rewrite emit_red in Ed. injection Ed as Hdid Hs3.
        assert (H3len : length (graph s3) = S drive_id).
        { rewrite <- Hs3. cbn [graph length]. rewrite Hdid. reflexivity. }
        destruct (last_sample ctx s ip en) as [prev |] eqn:Elast.
        * apply (g_bind_at (all_nodes succ_sample_node));
            [ apply all_nodes_emit;
              [ exact H3 | intros q tok en2 Hop; discriminate Hop ]
            | intros head_id s4 Eh H4 ].
          rewrite emit_red in Eh. injection Eh as Hhid Hs4.
          assert (H4len : length (graph s4) = S head_id).
          { rewrite <- Hs4. cbn [graph length]. rewrite Hhid. reflexivity. }
          apply (g_bind_at (all_nodes succ_sample_node)).
          -- unfold stall_chain. destruct (ip_lat (tfs_spec_ip ctx ip));
               [ exact H4 |].
             apply all_nodes_emit;
               [ exact H4 | intros q tok en2 Hop; discriminate Hop ].
          -- intros stall_id s5 Es H5.
             assert (H5len : length (graph s5) = S stall_id).
             { unfold stall_chain in Es.
               destruct (ip_lat (tfs_spec_ip ctx ip)).
               - unfold ret in Es. injection Es as <- <-. exact H4len.
               - rewrite emit_red in Es. injection Es as Hsid Hs5.
                 rewrite <- Hs5. cbn [graph length]. rewrite Hsid. reflexivity. }
             apply (g_bind_at (all_nodes succ_sample_node)).
             ++ apply all_nodes_emit; [ exact H5 |].
                intros q tok en2 Hop. cbn [op nid] in *.
                injection Hop as <- <- <-. exact H5len.
             ++ intros samp_id s6 Esa H6.
                exact (preserves_g_set_var (all_nodes succ_sample_node)
                         (DFG_SVar dst) samp_id s6 H6).
        * rewrite (bind_red (ret ctx drive_id) _ s3 drive_id s3 eq_refl).
          apply (g_bind_at (all_nodes succ_sample_node)).
          -- unfold stall_chain. destruct (ip_lat (tfs_spec_ip ctx ip));
               [ exact H3 |].
             apply all_nodes_emit;
               [ exact H3 | intros q tok en2 Hop; discriminate Hop ].
          -- intros stall_id s5 Es H5.
             assert (H5len : length (graph s5) = S stall_id).
             { unfold stall_chain in Es.
               destruct (ip_lat (tfs_spec_ip ctx ip)).
               - unfold ret in Es. injection Es as <- <-. exact H3len.
               - rewrite emit_red in Es. injection Es as Hsid Hs5.
                 rewrite <- Hs5. cbn [graph length]. rewrite Hsid. reflexivity. }
             apply (g_bind_at (all_nodes succ_sample_node)).
             ++ apply all_nodes_emit; [ exact H5 |].
                intros q tok en2 Hop. cbn [op nid] in *.
                injection Hop as <- <- <-. exact H5len.
             ++ intros samp_id s6 Esa H6.
                exact (preserves_g_set_var (all_nodes succ_sample_node)
                         (DFG_SVar dst) samp_id s6 H6).
    - cbn [dataflow_ops]. apply preserves_g_bind; [ apply IHo1 | intro x ]. apply IHo2.
    - intros s Hs. cbn [dataflow_ops].
      apply (g_bind_at (all_nodes succ_sample_node));
        [ apply dataflow_expr_g; [ apply P_emit_expr_ssucc | exact Hs ]
        | intros cid s1 Ec H1 ].
      rewrite (bind_red (get_state ctx) _ s1 s1 s1 (get_state_red s1)).
      apply (g_bind_at (all_nodes succ_sample_node));
        [ apply IHo1; exact H1 | intros u2 s2 E2 H2 ].
      rewrite (bind_red (get_state ctx) _ s2 s2 s2 (get_state_red s2)).
      rewrite (bind_red (put_state ctx _) _ s2 tt _ (put_state_red _ s2)).
      apply (g_bind_at (all_nodes succ_sample_node));
        [ apply IHo2; exact H2 | intros u3 s3 E3 H3 ].
      rewrite (bind_red (get_state ctx) _ s3 s3 s3 (get_state_red s3)).
      apply (g_bind_at (all_nodes succ_sample_node));
        [ apply (preserves_g_merge_maps (all_nodes succ_sample_node));
          [ apply P_emit_expr_ssucc | exact H3 ]
        | intros fv s4 E4 H4 ].
      rewrite (bind_red (get_state ctx) _ s4 s4 s4 (get_state_red s4)).
      cbn [snd]. exact H4.
  Qed.

  Lemma ssucc_build_dfg (act: tfs_action sched) :
    all_nodes succ_sample_node (graph (build_dfg ctx act)).
  Proof.
    unfold build_dfg.
    pose proof (dataflow_ops_ssucc (tfs_spec_action_ops ctx act) []
                  {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0 |} ];
                     var_map := [] |}) as H.
    cbn beta in H.
    assert (Hbase : all_nodes succ_sample_node
              (graph {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0 |} ];
                        var_map := [] |})).
    { intros nd Hin. cbn [graph In] in Hin. destruct Hin as [<- | []].
      intros q tok en Hop. cbn [op] in Hop. discriminate Hop. }
    specialize (H Hbase).
    destruct (dataflow_ops ctx [] (tfs_spec_action_ops ctx act)
                {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0 |} ];
                   var_map := [] |}) as [u final] eqn:Ed.
    cbn [snd] in H. cbn [graph].
    apply all_nodes_rev. exact H.
  Qed.

  (* Every ordering join carries a stall: [stall_chain] emits one on the head,
     and [ip_lat_pos] says the latency it is given is at least one. *)
  Definition joins_stalled (L: list (@dfg_node_t s_var i_var o_var p_var)) : Prop :=
    forall j d prev, In j L -> op j = DFG_Join d prev ->
      exists t l, In t L /\ op t = DFG_Stall l (nid j).

  Lemma joins_stalled_cons_nonjoin L o z :
    (forall d prev, o <> DFG_Join d prev) ->
    joins_stalled L ->
    joins_stalled ({| nid := length L; op := o; sz := z |} :: L).
  Proof.
    intros Hno H j d prev Hin Hop. cbn [In] in Hin.
    destruct Hin as [<- | Hin]; [ cbn [op] in Hop; exfalso; exact (Hno d prev Hop) |].
    destruct (H j d prev Hin Hop) as [t [l [Ht Htop]]].
    exists t, l. split; [ right; exact Ht | exact Htop ].
  Qed.

  Lemma P_emit_expr_jst : P_emit_expr joins_stalled.
  Proof. intros L o z _ _ H3 H. exact (joins_stalled_cons_nonjoin L o z H3 H). Qed.

  (* The call.s own join and the stall emitted straight above it. *)
  Lemma joins_stalled_cons2 L (d prev: nid_t) (l: nat) z1 z2 :
    joins_stalled L ->
    joins_stalled
      ({| nid := S (length L); op := DFG_Stall l (length L); sz := z2 |}
       :: {| nid := length L; op := DFG_Join d prev; sz := z1 |} :: L).
  Proof.
    intros H j d2 prev2 Hin Hop. cbn [In] in Hin.
    destruct Hin as [<- | [<- | Hin]].
    - cbn [op] in Hop. discriminate Hop.
    - exists {| nid := S (length L); op := DFG_Stall l (length L); sz := z2 |}, l.
      split; [ left; reflexivity | cbn [op nid]; reflexivity ].
    - destruct (H j d2 prev2 Hin Hop) as [t [l2 [Ht Htop]]].
      exists t, l2. split; [ right; right; exact Ht | exact Htop ].
  Qed.

  Lemma joins_stalled_rev L : joins_stalled L -> joins_stalled (rev L).
  Proof.
    intros H j d prev Hin Hop.
    apply (proj2 (in_rev L j)) in Hin.
    destruct (H j d prev Hin Hop) as [t [l [Ht Htop]]].
    exists t, l. split; [ apply (proj1 (in_rev L t)); exact Ht | exact Htop ].
  Qed.

  Lemma dataflow_ops_jst :
    forall (ops: @tf_ops s_var i_var o_var p_var) en,
      preserves_g joins_stalled (dataflow_ops ctx en ops).
  Proof.
    induction ops as [op | op1 IHo1 op2 IHo2 | cond op1 IHo1 op2 IHo2]; intro en.
    - destruct op as [ | dst e | dst e | ip dst e ]; cbn [dataflow_ops].
      + apply preserves_g_ret.
      + apply preserves_g_bind;
          [ apply dataflow_expr_g; apply P_emit_expr_jst | intro x ].
        apply preserves_g_set_var.
      + apply preserves_g_bind;
          [ apply dataflow_expr_g; apply P_emit_expr_jst | intro x ].
        apply preserves_g_set_var.
      + intros s Hs.
        assert (Hlat : 1 <= ip_lat (tfs_spec_ip ctx ip))
          by (apply ip_lat_pos).
        rewrite (bind_red (get_state ctx) _ s s s (get_state_red s)).
        apply (g_bind_at joins_stalled);
          [ apply dataflow_expr_g; [ apply P_emit_expr_jst | exact Hs ]
          | intros arg_id s2 Ea H2 ].
        apply (g_bind_at joins_stalled);
          [ rewrite emit_red; cbn [snd graph];
            apply joins_stalled_cons_nonjoin;
            [ intros d prev Hc; discriminate Hc | exact H2 ]
          | intros drive_id s3 Ed H3 ].
        destruct (last_sample ctx s ip en) as [prev |] eqn:Elast.
        * destruct (emit ctx (DFG_Join drive_id prev) 1 s3) as [head_id s4] eqn:Eh.
          rewrite (bind_red _ _ s3 head_id s4 Eh).
          unfold stall_chain.
          destruct (ip_lat (tfs_spec_ip ctx ip)) as [| lk] eqn:Elat;
            [ exfalso; try rewrite Elat in Hlat; lia |].
          destruct (emit ctx (DFG_Stall (S lk) head_id) (counter_sz (S lk)) s4)
            as [stall_id s5] eqn:Es.
          rewrite (bind_red _ _ s4 stall_id s5 Es).
          assert (H5 : joins_stalled (graph s5)).
          { rewrite emit_red in Eh. injection Eh as Hhid Hs4.
            rewrite emit_red in Es. injection Es as Hsid Hs5.
            rewrite <- Hs5. cbn [graph]. rewrite <- Hs4. cbn [graph length].
            rewrite <- Hhid. apply joins_stalled_cons2. exact H3. }
          apply (g_bind_at joins_stalled);
            [ rewrite emit_red; cbn [snd graph];
              apply joins_stalled_cons_nonjoin;
              [ intros d2 prev2 Hc; discriminate Hc | exact H5 ]
            | intros samp_id s6 Esa H6 ].
          exact (preserves_g_set_var joins_stalled (DFG_SVar dst) samp_id s6 H6).
        * rewrite (bind_red (ret ctx drive_id) _ s3 drive_id s3 eq_refl).
          apply (g_bind_at joins_stalled).
          -- unfold stall_chain.
             destruct (ip_lat (tfs_spec_ip ctx ip)) as [| lk] eqn:Elat;
               [ exfalso; try rewrite Elat in Hlat; lia |].
             rewrite emit_red. cbn [snd graph].
             apply joins_stalled_cons_nonjoin;
               [ intros d2 prev2 Hc; discriminate Hc | exact H3 ].
          -- intros stall_id s5 Es H5.
             apply (g_bind_at joins_stalled);
               [ rewrite emit_red; cbn [snd graph];
                 apply joins_stalled_cons_nonjoin;
                 [ intros d2 prev2 Hc; discriminate Hc | exact H5 ]
               | intros samp_id s6 Esa H6 ].
             exact (preserves_g_set_var joins_stalled (DFG_SVar dst) samp_id s6 H6).
    - cbn [dataflow_ops]. apply preserves_g_bind; [ apply IHo1 | intro x ]. apply IHo2.
    - intros s Hs. cbn [dataflow_ops].
      apply (g_bind_at joins_stalled);
        [ apply dataflow_expr_g; [ apply P_emit_expr_jst | exact Hs ]
        | intros cid s1 Ec H1 ].
      rewrite (bind_red (get_state ctx) _ s1 s1 s1 (get_state_red s1)).
      apply (g_bind_at joins_stalled); [ apply IHo1; exact H1 | intros u2 s2 E2 H2 ].
      rewrite (bind_red (get_state ctx) _ s2 s2 s2 (get_state_red s2)).
      rewrite (bind_red (put_state ctx _) _ s2 tt _ (put_state_red _ s2)).
      apply (g_bind_at joins_stalled); [ apply IHo2; exact H2 | intros u3 s3 E3 H3 ].
      rewrite (bind_red (get_state ctx) _ s3 s3 s3 (get_state_red s3)).
      apply (g_bind_at joins_stalled);
        [ apply (preserves_g_merge_maps joins_stalled);
          [ apply P_emit_expr_jst | exact H3 ]
        | intros fv s4 E4 H4 ].
      rewrite (bind_red (get_state ctx) _ s4 s4 s4 (get_state_red s4)).
      cbn [snd]. exact H4.
  Qed.

  Lemma joins_stalled_build_dfg (act: tfs_action sched) :
    joins_stalled (graph (build_dfg ctx act)).
  Proof.
    unfold build_dfg.
    pose proof (dataflow_ops_jst (tfs_spec_action_ops ctx act) []
                  {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0 |} ];
                     var_map := [] |}) as H.
    cbn beta in H.
    assert (Hbase : joins_stalled
              (graph {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0 |} ];
                        var_map := [] |})).
    { intros j d prev Hin Hop. cbn [graph In] in Hin.
      destruct Hin as [<- | []]. cbn [op] in Hop. discriminate Hop. }
    specialize (H Hbase).
    destruct (dataflow_ops ctx [] (tfs_spec_action_ops ctx act)
                {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0 |} ];
                   var_map := [] |}) as [u final] eqn:Ed.
    cbn [snd] in H. cbn [graph].
    apply joins_stalled_rev. exact H.
  Qed.

  (* THE STRUCTURAL FACT, on the exported forward graph. *)
  Lemma joins_sequence_build_dfg (act: tfs_action sched) :
    joins_sequence (graph (build_dfg ctx act)).
  Proof.
    unfold build_dfg.
    pose proof (dataflow_ops_joins (tfs_spec_action_ops ctx act) []
                  {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0 |} ];
                     var_map := [] |}) as H.
    cbn beta in H.
    assert (Hbase : joins_sequence
              (graph {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0 |} ];
                        var_map := [] |})).
    { intros j d prev Hin Hop. cbn [graph In] in Hin.
      destruct Hin as [<- | []]. cbn [op] in Hop. discriminate Hop. }
    specialize (H Hbase).
    destruct (dataflow_ops ctx [] (tfs_spec_action_ops ctx act)
                {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0 |} ];
                   var_map := [] |}) as [u final] eqn:Ed.
    cbn [snd] in H. cbn [graph].
    apply joins_sequence_rev. exact H.
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
    - destruct (read_var ctx v s) as [id s'] eqn:Er.
      destruct (read_var_cases v s id s' Er) as [[Hin [_ ->]] | Hem].
      + split; [ apply wgmono_refl | split; [ | exact Hinv ] ].
        eexists. split; [ exact Hin | reflexivity ].
      + pose proof (emit_full (DFG_Var v) (dfg_var_size ctx v) s Hinv
                      (fun x Hx => match Hx with end)) as Hf.
        rewrite Hem in Hf. exact Hf.
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
    - destruct (read_var ctx v s) as [id s'] eqn:Er.
      destruct (read_var_cases v s id s' Er) as [[Hin [_ ->]] | Hem].
      + split; [ apply wgmono_refl
               | split; [ | split; [ exact Hinv | split; [ exact Hvsz | ] ] ] ].
        * eexists. split; [ exact Hin | reflexivity ].
        * eexists. split; [ exact Hin | split; reflexivity ].
      + pose proof (emit_sz (DFG_Var v) (dfg_var_size ctx v) s Hinv Hvsz
                      (fun x Hx => match Hx with end)) as Hf.
        rewrite Hem in Hf. exact Hf.
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

  Definition node_args_sz (s: wst) (node: @dfg_node_t s_var i_var o_var p_var) : Prop :=
    match op node with
    | DFG_Unary uop a =>
        match uop with
        | tf_not => wsz s a (sz node)
        | tf_resize source_size => wsz s a source_size
        end
    | DFG_Binary bop a1 a2 =>
        match bop with
        | tf_cmp szC _ => wsz s a1 szC /\ wsz s a2 szC
        (* SPIKE: concat reads its operands at their declared widths. *)
        | tf_concat hz lz => wsz s a1 hz /\ wsz s a2 lz
        | _ => wsz s a1 (sz node) /\ wsz s a2 (sz node)
        end
    | DFG_Phi c t e => wsz s c 1 /\ wsz s t (sz node) /\ wsz s e (sz node)
    (* The round trip is a VALIDITY chain, and only the drive carries a value:
       the payload IS read at the drive's own width.  A stall's size is its
       COUNTER's width and it carries no value; a sample reads its token for
       validity alone, its own value being [tf_ivar (inr p)]; and the ordering
       join has no value either.  None of the three relates two widths. *)
    | DFG_Drive _ a _ => wsz s a (sz node)
    (* A stall's own width is its COUNTER's: [stall_chain] emits it at
       [counter_sz lat], and emits nothing at all at latency zero. *)
    | DFG_Stall l _ => 1 <= l /\ sz node = counter_sz l
    | DFG_Sample _ _ _ => True
    | DFG_Join _ _ => True
    | _ => True
    end.

  Definition wfg (s: wst) : Prop :=
    forall node, In node (graph s) -> node_args_sz s node.

  Lemma node_args_sz_gmono s s' node :
    node_args_sz s node -> wgmono s s' -> node_args_sz s' node.
  Proof.
    unfold node_args_sz. intros H Hg.
    destruct (op node) as [c|v|v|uop a|bop a1 a2|a|cd t e|sa|dov dn den|siv sn sen|ja jb|];
      [ exact I | exact I | exact I | | | exact I | | exact H | | exact I | exact I | exact I ].
    - destruct uop; eapply wsz_gmono; eauto.
    - destruct bop; destruct H as [H1 H2]; split; eapply wsz_gmono; eauto.
    - destruct H as [H1 [H2 H3]]; repeat split; eapply wsz_gmono; eauto.
    - (* only the drive carries a value; stall, sample and join are [True] *)
      eapply wsz_gmono; eauto.
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
    - destruct (read_var ctx v s) as [id s'] eqn:Er.
      destruct (read_var_cases v s id s' Er) as [[Hin [_ ->]] | Hem].
      + split; [ apply wgmono_refl
               | split; [ | split; [ exact Hinv
                          | split; [ exact Hvsz | split; [ | exact Hfg ] ] ] ] ].
        * eexists. split; [ exact Hin | reflexivity ].
        * eexists. split; [ exact Hin | split; reflexivity ].
      + pose proof (emit_fg (DFG_Var v) (dfg_var_size ctx v) s Hinv Hvsz Hfg
                      (fun x Hx => match Hx with end) I) as Hf.
        rewrite Hem in Hf. exact Hf.
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
      cbn [dataflow_expr]. destruct bop0 as [ | | | | | | szC cop | hz lz ];
        try (unfold bind;
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
      (* tf_concat: the only binary op whose operands are emitted at DIFFERENT
         widths, so the uniform tactic above cannot bind a single [?z]. *)
      unfold bind.
      pose proof (IHe1 hz s Hinv Hvsz Hfg) as H1.
      destruct (dataflow_expr ctx e1 hz s) as [id1 s1].
      destruct H1 as [Hg1 [Hn1 [Hw1 [Hv1 [Hs1 Hf1]]]]].
      pose proof (IHe2 lz s1 Hw1 Hv1 Hf1) as H2.
      destruct (dataflow_expr ctx e2 lz s1) as [id2 s2].
      destruct H2 as [Hg2 [Hn2 [Hw2 [Hv2 [Hs2 Hf2]]]]].
      assert (Hargs : forall x, In x (get_args ctx {| nid := length (graph s2);
                        op := DFG_Binary (tf_concat hz lz) id1 id2; sz := size |}) -> wnidwf s2 x)
        by (intros x Hx; simpl in Hx; destruct Hx as [<-|[<-|[]]];
            [ eapply wnidwf_gmono; [ exact Hn1 | exact Hg2 ] | exact Hn2 ]).
      assert (Hnode : node_args_sz s2 {| nid := length (graph s2);
                        op := DFG_Binary (tf_concat hz lz) id1 id2; sz := size |})
        by (unfold node_args_sz; cbn [op sz];
            split; [ eapply wsz_gmono; [ exact Hs1 | exact Hg2 ] | exact Hs2 ]).
      pose proof (emit_fg (DFG_Binary (tf_concat hz lz) id1 id2) size s2
                    Hw2 Hv2 Hf2 Hargs Hnode) as He.
      destruct (emit ctx (DFG_Binary (tf_concat hz lz) id1 id2) size s2) as [id3 s3].
      destruct He as [Hg3 [Hn3 [Hp3 [Hq3 [Hs3 Hf3]]]]].
      split; [ eapply wgmono_trans; [ exact Hg1 | eapply wgmono_trans; [ exact Hg2 | exact Hg3 ] ]
             | split; [ exact Hn3 | split; [ exact Hp3 | split; [ exact Hq3 | split; [ exact Hs3 | exact Hf3 ] ] ] ] ].
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
    forall (ops: @tf_ops s_var i_var o_var p_var) (en: list (nid_t * bool)) (s: wst),
      winv s ->
      (* a drive carries its path condition, and [get_args] reaches those nodes *)
      (forall x, In x (map fst en) -> wnidwf s x) ->
      let (u, s2) := dataflow_ops ctx en ops s in wgmono s s2 /\ winv s2.
  Proof.
    induction ops as [op | op1 IHops1 op2 IHops2 | cond op1 IHops1 op2 IHops2];
      intros en s Hinv Hen.
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
      + (* THE ROUND TRIP: arg -> drive -> (join) -> stall -> sample -> dst.
           Four emits where the old shape had two set_vars, and the drive's
           path condition is an argument, hence [Hen]. *)
        simpl.
        rewrite (bind_red (get_state ctx) _ s _ _ (get_state_red s)).
        pose proof (dataflow_expr_full arg (ip_req_sz (tfs_spec_ip ctx ip)) s Hinv) as Ha.
        destruct (dataflow_expr ctx arg (ip_req_sz (tfs_spec_ip ctx ip)) s)
          as [arg_id sa] eqn:Ea.
        destruct Ha as [Ga [Na Pa]].
        rewrite (bind_red (dataflow_expr ctx arg (ip_req_sz (tfs_spec_ip ctx ip)))
                   _ s _ _ Ea).
        assert (Hen_a : forall x, In x (map fst en) -> wnidwf sa x)
          by (intros x Hx; eapply wnidwf_gmono; [ apply Hen, Hx | exact Ga ]).
        (* the drive *)
        assert (Hd : let (id, s') :=
                       emit ctx (DFG_Drive ip arg_id en) (ip_req_sz (tfs_spec_ip ctx ip)) sa in
                     wgmono sa s' /\ wnidwf s' id /\ winv s').
        { apply emit_full; [ exact Pa |].
          intros x Hx. cbn [get_args] in Hx.
          destruct Hx as [<- | Hx]; [ exact Na | exact (Hen_a x Hx) ]. }
        destruct (emit ctx (DFG_Drive ip arg_id en) (ip_req_sz (tfs_spec_ip ctx ip)) sa)
          as [drive_id sd] eqn:Ed.
        destruct Hd as [Gd [Nd Pd]].
        rewrite (bind_red (emit ctx (DFG_Drive ip arg_id en)
                             (ip_req_sz (tfs_spec_ip ctx ip))) _ sa _ _ Ed).
        (* the join, when an earlier call on this IP is still outstanding *)
        assert (Hhead : let (hid, sh) :=
                          match last_sample ctx s ip en with
                          | None => ret ctx drive_id
                          | Some prev => emit ctx (DFG_Join drive_id prev) 1
                          end sd in
                        wgmono sd sh /\ wnidwf sh hid /\ winv sh).
        { destruct (last_sample ctx s ip en) as [prev |] eqn:Elast.
          - apply emit_full; [ exact Pd |].
            intros x Hx. cbn [get_args] in Hx.
            destruct Hx as [<- | [<- | []]]; [ exact Nd |].
            eapply wnidwf_gmono; [ exact (last_sample_nidwf s ip en prev Elast) |].
            eapply wgmono_trans; [ exact Ga | exact Gd ].
          - unfold ret. split; [ apply wgmono_refl | split; [ exact Nd | exact Pd ] ]. }
        destruct (match last_sample ctx s ip en with
                  | None => ret ctx drive_id
                  | Some prev => emit ctx (DFG_Join drive_id prev) 1
                  end sd) as [head_id sh] eqn:Eh.
        destruct Hhead as [Gh [Nh Ph]].
        rewrite (bind_red _ _ sd _ _ Eh).
        (* the stall: ONE node, or nothing at all when the latency is zero *)
        assert (Hstall : let (sid, s1) :=
                           stall_chain ctx (ip_lat (tfs_spec_ip ctx ip)) head_id sh in
                         wgmono sh s1 /\ wnidwf s1 sid /\ winv s1).
        { unfold stall_chain. destruct (ip_lat (tfs_spec_ip ctx ip)).
          - unfold ret. split; [ apply wgmono_refl | split; [ exact Nh | exact Ph ] ].
          - apply emit_full; [ exact Ph |].
            intros x Hx. cbn [get_args] in Hx. destruct Hx as [<- | []]. exact Nh. }
        destruct (stall_chain ctx (ip_lat (tfs_spec_ip ctx ip)) head_id sh)
          as [stall_id s1] eqn:Es1.
        destruct Hstall as [Gt [Nt Pt]].
        rewrite (bind_red (stall_chain ctx (ip_lat (tfs_spec_ip ctx ip)) head_id)
                   _ sh _ _ Es1).
        (* the sample *)
        assert (Hsm : let (id, s') :=
                        emit ctx (DFG_Sample ip stall_id en)
                          (dfg_var_size ctx (DFG_SVar dst)) s1 in
                      wgmono s1 s' /\ wnidwf s' id /\ winv s').
        { apply emit_full; [ exact Pt |].
          intros x Hx. cbn [get_args] in Hx. destruct Hx as [<- | []]. exact Nt. }
        destruct (emit ctx (DFG_Sample ip stall_id en)
                    (dfg_var_size ctx (DFG_SVar dst)) s1) as [samp_id s2] eqn:Esm.
        destruct Hsm as [Gm [Nm Pm]].
        rewrite (bind_red (emit ctx (DFG_Sample ip stall_id en)
                             (dfg_var_size ctx (DFG_SVar dst))) _ s1 _ _ Esm).
        pose proof (set_var_full (DFG_SVar dst) samp_id s2 Pm Nm) as Hs.
        destruct (set_var ctx (DFG_SVar dst) samp_id s2) as [u s3] eqn:Es.
        destruct Hs as [Gs Ps].
        split;
          [ eapply wgmono_trans; [ exact Ga |];
            eapply wgmono_trans; [ exact Gd |];
            eapply wgmono_trans; [ exact Gh |];
            eapply wgmono_trans; [ exact Gt |];
            eapply wgmono_trans; [ exact Gm |]; exact Gs
          | exact Ps ].
    - (* cons *)
      simpl.
      pose proof (IHops1 en s Hinv Hen) as H1.
      destruct (dataflow_ops ctx en op1 s) as [u1 s1] eqn:E1.
      destruct H1 as [G1 P1].
      rewrite (bind_red (dataflow_ops ctx en op1) _ s _ _ E1).
      assert (Hen1 : forall x, In x (map fst en) -> wnidwf s1 x)
        by (intros x Hx; eapply wnidwf_gmono; [ apply Hen, Hx | exact G1 ]).
      pose proof (IHops2 en s1 P1 Hen1) as H2.
      destruct (dataflow_ops ctx en op2 s1) as [u2 s2] eqn:E2.
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
      assert (Hen_t : forall x, In x (map fst ((cond_id, true) :: en)) -> wnidwf s1 x).
      { intros x Hx. cbn [map In] in Hx. destruct Hx as [<- | Hx]; [ exact Nc |].
        eapply wnidwf_gmono; [ apply Hen, Hx | exact Gc ]. }
      pose proof (IHops1 ((cond_id, true) :: en) s1 Pc Hen_t) as Hthen.
      destruct (dataflow_ops ctx ((cond_id, true) :: en) op1 s1) as [ut s_then] eqn:Et.
      destruct Hthen as [Gthen Pthen].
      rewrite (bind_red (dataflow_ops ctx ((cond_id, true) :: en) op1) _ s1 _ _ Et).
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
      assert (Hen_e : forall x, In x (map fst ((cond_id, false) :: en)) -> wnidwf sR x).
      { intros x Hx. eapply wnidwf_gmono;
          [ apply Hen_t; cbn [map In] in Hx |- *; exact Hx
          | eapply wgmono_trans; [ exact Gthen | exact Gthen_sR ] ]. }
      pose proof (IHops2 ((cond_id, false) :: en) sR PsR Hen_e) as Helse.
      destruct (dataflow_ops ctx ((cond_id, false) :: en) op2 sR) as [ue s_else] eqn:Ee.
      destruct Helse as [Gelse Pelse].
      rewrite (bind_red (dataflow_ops ctx ((cond_id, false) :: en) op2) _ sR _ _ Ee).
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
    forall (ops: @tf_ops s_var i_var o_var p_var) (en: list (nid_t * bool)) (s: wst),
      winv s -> wvsz s -> wfg s ->
      (forall x, In x (map fst en) -> wnidwf s x) ->
      let (u, s2) := dataflow_ops ctx en ops s in
      wgmono s s2 /\ winv s2 /\ wvsz s2 /\ wfg s2.
  Proof.
    induction ops as [op | op1 IHops1 op2 IHops2 | cond op1 IHops1 op2 IHops2];
      intros en s Hinv Hvsz Hfg Hen.
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
      + (* THE ROUND TRIP, carrying wvsz and wfg through the four emits.  Only
           the drive's [node_args_sz] says anything: the rest of the spine is
           validity, so its obligations are [True]. *)
        simpl.
        rewrite (bind_red (get_state ctx) _ s _ _ (get_state_red s)).
        pose proof (dataflow_expr_fg arg (ip_req_sz (tfs_spec_ip ctx ip)) s Hinv Hvsz Hfg) as Ha.
        destruct (dataflow_expr ctx arg (ip_req_sz (tfs_spec_ip ctx ip)) s)
          as [arg_id sa] eqn:Ea.
        destruct Ha as [Ga [Na [Pa [Qa [Sa Fa]]]]].
        rewrite (bind_red (dataflow_expr ctx arg (ip_req_sz (tfs_spec_ip ctx ip)))
                   _ s _ _ Ea).
        assert (Hen_a : forall x, In x (map fst en) -> wnidwf sa x)
          by (intros x Hx; eapply wnidwf_gmono; [ apply Hen, Hx | exact Ga ]).
        (* the drive *)
        assert (Hd : let (id, s') :=
                       emit ctx (DFG_Drive ip arg_id en) (ip_req_sz (tfs_spec_ip ctx ip)) sa in
                     wgmono sa s' /\ wnidwf s' id /\ winv s' /\ wvsz s' /\
                     wsz s' id (ip_req_sz (tfs_spec_ip ctx ip)) /\ wfg s').
        { apply emit_fg; [ exact Pa | exact Qa | exact Fa | | ].
          - intros x Hx. cbn [get_args] in Hx.
            destruct Hx as [<- | Hx]; [ exact Na | exact (Hen_a x Hx) ].
          - unfold node_args_sz. cbn [op]. exact Sa. }
        destruct (emit ctx (DFG_Drive ip arg_id en) (ip_req_sz (tfs_spec_ip ctx ip)) sa)
          as [drive_id sd] eqn:Ed.
        destruct Hd as [Gd [Nd [Pd [Qd [Sd Fd]]]]].
        rewrite (bind_red (emit ctx (DFG_Drive ip arg_id en)
                             (ip_req_sz (tfs_spec_ip ctx ip))) _ sa _ _ Ed).
        (* the ordering join *)
        assert (Hhead : let (hid, sh) :=
                          match last_sample ctx s ip en with
                          | None => ret ctx drive_id
                          | Some prev => emit ctx (DFG_Join drive_id prev) 1
                          end sd in
                        wgmono sd sh /\ wnidwf sh hid /\ winv sh /\ wvsz sh /\ wfg sh).
        { destruct (last_sample ctx s ip en) as [prev |] eqn:Elast.
          - pose proof (emit_fg (DFG_Join drive_id prev) 1 sd Pd Qd Fd) as Hj.
            match type of Hj with
            | ?A -> ?B -> _ =>
                assert (HA : A) by
                  (intros x Hx; cbn [get_args] in Hx;
                   destruct Hx as [<- | [<- | []]]; [ exact Nd |];
                   eapply wnidwf_gmono; [ exact (last_sample_nidwf s ip en prev Elast) |];
                   eapply wgmono_trans; [ exact Ga | exact Gd ]);
                assert (HB : B) by (unfold node_args_sz; cbn [op]; exact I);
                specialize (Hj HA HB)
            end.
            destruct (emit ctx (DFG_Join drive_id prev) 1 sd) as [hid sh].
            destruct Hj as [Gj [Nj [Pj [Qj [_ Fj]]]]].
            split; [ exact Gj | split; [ exact Nj | split; [ exact Pj
              | split; [ exact Qj | exact Fj ] ] ] ].
          - unfold ret. split; [ apply wgmono_refl | split; [ exact Nd
              | split; [ exact Pd | split; [ exact Qd | exact Fd ] ] ] ]. }
        destruct (match last_sample ctx s ip en with
                  | None => ret ctx drive_id
                  | Some prev => emit ctx (DFG_Join drive_id prev) 1
                  end sd) as [head_id sh] eqn:Eh.
        destruct Hhead as [Gh [Nh [Ph [Qh Fh]]]].
        rewrite (bind_red _ _ sd _ _ Eh).
        (* the stall *)
        assert (Hstall : let (sid, s1) :=
                           stall_chain ctx (ip_lat (tfs_spec_ip ctx ip)) head_id sh in
                         wgmono sh s1 /\ wnidwf s1 sid /\ winv s1 /\ wvsz s1 /\ wfg s1).
        { unfold stall_chain. destruct (ip_lat (tfs_spec_ip ctx ip)) as [| l].
          - unfold ret. split; [ apply wgmono_refl | split; [ exact Nh
              | split; [ exact Ph | split; [ exact Qh | exact Fh ] ] ] ].
          - pose proof (emit_fg (DFG_Stall (S l) head_id) (counter_sz (S l)) sh Ph Qh Fh) as Ht.
            match type of Ht with
            | ?A -> ?B -> _ =>
                assert (HA : A) by
                  (intros x Hx; cbn [get_args] in Hx;
                   destruct Hx as [<- | []]; exact Nh);
                assert (HB : B) by
                  (unfold node_args_sz; cbn [op sz]; split; [ lia | reflexivity ]);
                specialize (Ht HA HB)
            end.
            destruct (emit ctx (DFG_Stall (S l) head_id) (counter_sz (S l)) sh) as [sid s1].
            destruct Ht as [Gt [Nt [Pt [Qt [_ Ft]]]]].
            split; [ exact Gt | split; [ exact Nt | split; [ exact Pt
              | split; [ exact Qt | exact Ft ] ] ] ]. }
        destruct (stall_chain ctx (ip_lat (tfs_spec_ip ctx ip)) head_id sh)
          as [stall_id s1] eqn:Es1.
        destruct Hstall as [Gt [Nt [Pt [Qt Ft]]]].
        rewrite (bind_red (stall_chain ctx (ip_lat (tfs_spec_ip ctx ip)) head_id)
                   _ sh _ _ Es1).
        (* the sample, which is what [dst] is set from *)
        assert (Hsm : let (id, s') :=
                        emit ctx (DFG_Sample ip stall_id en)
                          (dfg_var_size ctx (DFG_SVar dst)) s1 in
                      wgmono s1 s' /\ wnidwf s' id /\ winv s' /\ wvsz s' /\
                      wsz s' id (dfg_var_size ctx (DFG_SVar dst)) /\ wfg s').
        { apply emit_fg; [ exact Pt | exact Qt | exact Ft | | ].
          - intros x Hx. cbn [get_args] in Hx. destruct Hx as [<- | []]. exact Nt.
          - unfold node_args_sz. cbn [op]. exact I. }
        destruct (emit ctx (DFG_Sample ip stall_id en)
                    (dfg_var_size ctx (DFG_SVar dst)) s1) as [samp_id s2] eqn:Esm.
        destruct Hsm as [Gm [Nm [Pm [Qm [Sm Fm]]]]].
        rewrite (bind_red (emit ctx (DFG_Sample ip stall_id en)
                             (dfg_var_size ctx (DFG_SVar dst))) _ s1 _ _ Esm).
        pose proof (set_var_fg (DFG_SVar dst) samp_id s2 Pm Qm Fm Nm Sm) as Hs.
        destruct (set_var ctx (DFG_SVar dst) samp_id s2) as [u s3] eqn:Es.
        destruct Hs as [Gs [Ps [Qs Fs]]].
        split;
          [ eapply wgmono_trans; [ exact Ga |];
            eapply wgmono_trans; [ exact Gd |];
            eapply wgmono_trans; [ exact Gh |];
            eapply wgmono_trans; [ exact Gt |];
            eapply wgmono_trans; [ exact Gm |]; exact Gs
          | split; [ exact Ps | split; [ exact Qs | exact Fs ] ] ].
    - (* cons *)
      simpl.
      pose proof (IHops1 en s Hinv Hvsz Hfg Hen) as H1.
      destruct (dataflow_ops ctx en op1 s) as [u1 s1] eqn:E1.
      destruct H1 as [G1 [P1 [Q1 F1]]].
      rewrite (bind_red (dataflow_ops ctx en op1) _ s _ _ E1).
      assert (Hen1 : forall x, In x (map fst en) -> wnidwf s1 x)
        by (intros x Hx; eapply wnidwf_gmono; [ apply Hen, Hx | exact G1 ]).
      pose proof (IHops2 en s1 P1 Q1 F1 Hen1) as H2.
      destruct (dataflow_ops ctx en op2 s1) as [u2 s2] eqn:E2.
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
      assert (Hen_t : forall x, In x (map fst ((cond_id, true) :: en)) -> wnidwf s1 x).
      { intros x Hx. cbn [map In] in Hx. destruct Hx as [<- | Hx]; [ exact Nc |].
        eapply wnidwf_gmono; [ apply Hen, Hx | exact Gc ]. }
      pose proof (IHops1 ((cond_id, true) :: en) s1 Pc Qc Fc Hen_t) as Hthen.
      destruct (dataflow_ops ctx ((cond_id, true) :: en) op1 s1) as [ut s_then] eqn:Et.
      destruct Hthen as [Gthen [Pthen [Qthen Fthen]]].
      rewrite (bind_red (dataflow_ops ctx ((cond_id, true) :: en) op1) _ s1 _ _ Et).
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
      assert (Hen_e : forall x, In x (map fst ((cond_id, false) :: en)) -> wnidwf sR x).
      { intros x Hx. eapply wnidwf_gmono;
          [ apply Hen_t; cbn [map In] in Hx |- *; exact Hx
          | eapply wgmono_trans; [ exact Gthen | exact Gthen_sR ] ]. }
      pose proof (IHops2 ((cond_id, false) :: en) sR PsR QsR FsR Hen_e) as Helse.
      destruct (dataflow_ops ctx ((cond_id, false) :: en) op2 sR) as [ue s_else] eqn:Ee.
      destruct Helse as [Gelse [Pelse [Qelse Felse]]].
      rewrite (bind_red (dataflow_ops ctx ((cond_id, false) :: en) op2) _ sR _ _ Ee).
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
    /\ (forall node, In node (graph s) -> op node = DFG_Empty -> nid node = 0)
    (* Only the sentinel has id 0.  A call SEQUENCED after another reads the
       earlier sample back out of the graph ([last_sample]), and [emit_pos]
       wants that id positive. *)
    /\ (forall node, In node (graph s) -> op node <> DFG_Empty -> 1 <= nid node).

  Lemma ensure_var_vmap v (s: wst) id s' :
    ensure_var ctx v s = (id, s') ->
    exists f, var_map s' = (v, id) :: filter f (var_map s).
  Proof.
    unfold ensure_var, emit, bind, get_state, put_state, ret. intro H.
    injection H as <- <-. eexists. reflexivity.
  Qed.

  (* [last_sample] returns a SAMPLE node found in the graph, so gpos puts its
     id above the sentinel. *)
  Lemma last_sample_pos (s: wst) ip en prev :
    gpos s -> last_sample ctx s ip en = Some prev -> 1 <= prev.
  Proof.
    intros [_ [_ [_ [_ Hnz]]]]. unfold last_sample.
    destruct (find _ (graph s)) as [nd |] eqn:Ef; [| discriminate].
    intro H. injection H as <-.
    apply find_some in Ef. destruct Ef as [Hin Hpred].
    apply Hnz; [ exact Hin |].
    intro He. rewrite He in Hpred. cbn in Hpred. discriminate Hpred.
  Qed.

  Lemma emit_pos op sz (s: wst) :
    gpos s -> op <> DFG_Empty ->
    (forall x, In x (get_args ctx {| nid := length (graph s); op := op; sz := sz |}) -> 1 <= x) ->
    let (id, s') := emit ctx op sz s in 1 <= id /\ gpos s'.
  Proof.
    intros [Hlen [Hvm [Hargs [Hemp Hnz]]]] Hne Hnew.
    rewrite emit_red.
    split; [ exact Hlen | ].
    split; [ | split; [ | split; [ | split ] ] ].
    - cbn [graph length]. lia.
    - cbn [var_map]. exact Hvm.
    - cbn [graph]. intros node Hin x Hx. destruct Hin as [<-|Hin].
      + exact (Hnew x Hx).
      + exact (Hargs node Hin x Hx).
    - cbn [graph]. intros node Hin He. destruct Hin as [<-|Hin].
      + cbn in He. exfalso. apply Hne. exact He.
      + exact (Hemp node Hin He).
    - cbn [graph]. intros node Hin He. destruct Hin as [<-|Hin].
      + cbn [nid]. exact Hlen.
      + exact (Hnz node Hin He).
  Qed.

  Lemma ensure_var_pos v (s: wst) :
    gpos s ->
    let (id, s') := ensure_var ctx v s in 1 <= id /\ gpos s'.
  Proof.
    intros Hp.
    destruct (ensure_var ctx v s) as [id s'] eqn:Ev.
    pose proof (ensure_var_graph v s id s' Ev) as [Hg Hid].
    pose proof (ensure_var_vmap v s id s' Ev) as [f Hvm2].
    destruct Hp as [Hlen [Hvm [Hargs [Hemp Hnz]]]].
    split; [ rewrite Hid; exact Hlen | ].
    split; [ | split; [ | split; [ | split ] ] ].
    - rewrite Hg. cbn [graph length]. lia.
    - rewrite Hvm2. intros k id0 Hin. destruct Hin as [Heq|Hin].
      + injection Heq as <- <-. rewrite Hid; exact Hlen.
      + apply filter_In in Hin. destruct Hin as [Hin _]. exact (Hvm k id0 Hin).
    - rewrite Hg. cbn [graph]. intros node Hin x Hx. destruct Hin as [<-|Hin].
      + cbn in Hx. destruct Hx.
      + exact (Hargs node Hin x Hx).
    - rewrite Hg. cbn [graph]. intros node Hin He. destruct Hin as [<-|Hin].
      + cbn in He. discriminate He.
      + exact (Hemp node Hin He).
    - rewrite Hg. cbn [graph]. intros node Hin He. destruct Hin as [<-|Hin].
      + cbn [nid]. exact Hlen.
      + exact (Hnz node Hin He).
  Qed.

  Lemma set_var_pos v id (s: wst) :
    gpos s -> 1 <= id ->
    let (u, s') := set_var ctx v id s in gpos s'.
  Proof.
    intros [Hlen [Hvm [Hargs [Hemp Hnz]]]] Hi.
    unfold set_var, bind, get_state, put_state. simpl.
    split; [ | split; [ | split; [ | split ] ] ].
    - cbn [graph length]. exact Hlen.
    - cbn [var_map]. intros k id0 Hin. destruct Hin as [Heq|Hin].
      + injection Heq as <- <-. exact Hi.
      + apply filter_In in Hin. destruct Hin as [Hin _]. exact (Hvm k id0 Hin).
    - cbn [graph]. exact Hargs.
    - cbn [graph]. exact Hemp.
    - cbn [graph]. exact Hnz.
  Qed.

  Lemma get_var_pos v (s: wst) :
    gpos s ->
    let (id, s') := get_var ctx v s in 1 <= id /\ gpos s'.
  Proof.
    intros Hp. unfold get_var, bind, get_state.
    destruct (BitsToLists.list_assoc (var_map s) v) as [id|] eqn:E.
    - unfold ret. split; [ | exact Hp ].
      destruct Hp as [_ [Hvm _]]. apply wla_in in E. exact (Hvm v id E).
    - destruct (read_var ctx v s) as [id s'] eqn:Er.
      destruct (read_var_cases v s id s' Er) as [[_ [Hpos ->]] | Hem].
      + split; [ exact Hpos | exact Hp ].
      + pose proof (emit_pos (DFG_Var v) (dfg_var_size ctx v) s Hp
                      ltac:(discriminate) (fun x Hx => match Hx with end)) as Hf.
        rewrite Hem in Hf. exact Hf.
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
    forall (ops: @tf_ops s_var i_var o_var p_var) (en: list (nid_t * bool)) (s: wst),
      gpos s ->
      (forall x, In x (map fst en) -> 1 <= x) ->
      let (u, s2) := dataflow_ops ctx en ops s in gpos s2.
  Proof.
    induction ops as [op | op1 IHops1 op2 IHops2 | cond op1 IHops1 op2 IHops2];
      intros en s Hp Hen.
    - destruct op as [ | dst expr | dst expr | ip dst arg ].
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
      + (* THE ROUND TRIP.  [prev] comes back out of the graph via [last_sample],
           and gpos's last clause is what makes its id positive. *)
        simpl.
        rewrite (bind_red (get_state ctx) _ s _ _ (get_state_red s)).
        pose proof (dataflow_expr_pos arg (ip_req_sz (tfs_spec_ip ctx ip)) s Hp) as Ha.
        destruct (dataflow_expr ctx arg (ip_req_sz (tfs_spec_ip ctx ip)) s)
          as [arg_id sa] eqn:Ea.
        destruct Ha as [Na Pa].
        rewrite (bind_red (dataflow_expr ctx arg (ip_req_sz (tfs_spec_ip ctx ip)))
                   _ s _ _ Ea).
        assert (Hd : let (id, s') :=
                       emit ctx (DFG_Drive ip arg_id en) (ip_req_sz (tfs_spec_ip ctx ip)) sa in
                     1 <= id /\ gpos s').
        { apply emit_pos; [ exact Pa | discriminate |].
          intros x Hx. cbn [get_args] in Hx.
          destruct Hx as [<- | Hx]; [ exact Na | exact (Hen x Hx) ]. }
        destruct (emit ctx (DFG_Drive ip arg_id en) (ip_req_sz (tfs_spec_ip ctx ip)) sa)
          as [drive_id sd] eqn:Ed.
        destruct Hd as [Nd Pd].
        rewrite (bind_red (emit ctx (DFG_Drive ip arg_id en)
                             (ip_req_sz (tfs_spec_ip ctx ip))) _ sa _ _ Ed).
        assert (Hhead : let (hid, sh) :=
                          match last_sample ctx s ip en with
                          | None => ret ctx drive_id
                          | Some prev => emit ctx (DFG_Join drive_id prev) 1
                          end sd in
                        1 <= hid /\ gpos sh).
        { destruct (last_sample ctx s ip en) as [prev |] eqn:Elast.
          - apply emit_pos; [ exact Pd | discriminate |].
            intros x Hx. cbn [get_args] in Hx.
            destruct Hx as [<- | [<- | []]]; [ exact Nd |].
            exact (last_sample_pos s ip en prev Hp Elast).
          - unfold ret. split; [ exact Nd | exact Pd ]. }
        destruct (match last_sample ctx s ip en with
                  | None => ret ctx drive_id
                  | Some prev => emit ctx (DFG_Join drive_id prev) 1
                  end sd) as [head_id sh] eqn:Eh.
        destruct Hhead as [Nh Ph].
        rewrite (bind_red _ _ sd _ _ Eh).
        assert (Hstall : let (sid, s1) :=
                           stall_chain ctx (ip_lat (tfs_spec_ip ctx ip)) head_id sh in
                         1 <= sid /\ gpos s1).
        { unfold stall_chain. destruct (ip_lat (tfs_spec_ip ctx ip)) as [| l].
          - unfold ret. split; [ exact Nh | exact Ph ].
          - apply emit_pos; [ exact Ph | discriminate |].
            intros x Hx. cbn [get_args] in Hx. destruct Hx as [<- | []]. exact Nh. }
        destruct (stall_chain ctx (ip_lat (tfs_spec_ip ctx ip)) head_id sh)
          as [stall_id s1] eqn:Es1.
        destruct Hstall as [Nt Pt].
        rewrite (bind_red (stall_chain ctx (ip_lat (tfs_spec_ip ctx ip)) head_id)
                   _ sh _ _ Es1).
        assert (Hsm : let (id, s') :=
                        emit ctx (DFG_Sample ip stall_id en)
                          (dfg_var_size ctx (DFG_SVar dst)) s1 in
                      1 <= id /\ gpos s').
        { apply emit_pos; [ exact Pt | discriminate |].
          intros x Hx. cbn [get_args] in Hx. destruct Hx as [<- | []]. exact Nt. }
        destruct (emit ctx (DFG_Sample ip stall_id en)
                    (dfg_var_size ctx (DFG_SVar dst)) s1) as [samp_id s2] eqn:Esm.
        destruct Hsm as [Nm Pm].
        rewrite (bind_red (emit ctx (DFG_Sample ip stall_id en)
                             (dfg_var_size ctx (DFG_SVar dst))) _ s1 _ _ Esm).
        pose proof (set_var_pos (DFG_SVar dst) samp_id s2 Pm Nm) as Hs.
        destruct (set_var ctx (DFG_SVar dst) samp_id s2) as [u s3] eqn:Es.
        exact Hs.
    - simpl.
      pose proof (IHops1 en s Hp Hen) as H1.
      destruct (dataflow_ops ctx en op1 s) as [u1 s1] eqn:E1.
      rewrite (bind_red (dataflow_ops ctx en op1) _ s _ _ E1).
      pose proof (IHops2 en s1 H1 Hen) as H2.
      destruct (dataflow_ops ctx en op2 s1) as [u2 s2] eqn:E2.
      exact H2.
    - simpl.
      pose proof (dataflow_expr_pos cond 1 s Hp) as Hc.
      destruct (dataflow_expr ctx cond 1 s) as [cond_id s1] eqn:Ec.
      destruct Hc as [Nc Pc].
      rewrite (bind_red (dataflow_expr ctx cond 1) _ s _ _ Ec).
      rewrite (bind_red (get_state ctx) _ s1 _ _ (get_state_red s1)).
      assert (Hen_t : forall x, In x (map fst ((cond_id, true) :: en)) -> 1 <= x).
      { intros x Hx. cbn [map In] in Hx. destruct Hx as [<- | Hx];
          [ exact Nc | exact (Hen x Hx) ]. }
      pose proof (IHops1 ((cond_id, true) :: en) s1 Pc Hen_t) as Hthen.
      destruct (dataflow_ops ctx ((cond_id, true) :: en) op1 s1) as [ut s_then] eqn:Et.
      rewrite (bind_red (dataflow_ops ctx ((cond_id, true) :: en) op1) _ s1 _ _ Et).
      rewrite (bind_red (get_state ctx) _ s_then _ _ (get_state_red s_then)).
      set (sR := {| graph := graph s_then; var_map := var_map s1 |} : wst).
      rewrite (bind_red (put_state ctx sR) _ s_then _ _ (put_state_red sR s_then)).
      assert (PsR : gpos sR).
      { destruct Pc as [_ [Hvm1 _]]. destruct Hthen as [Hlt [_ [Habt [Hempt Hnzt]]]].
        split; [ | split; [ | split; [ | split ] ] ].
        - unfold sR; cbn [graph]. exact Hlt.
        - unfold sR; cbn [var_map]. exact Hvm1.
        - unfold sR; cbn [graph]. exact Habt.
        - unfold sR; cbn [graph]. exact Hempt.
        - unfold sR; cbn [graph]. exact Hnzt. }
      pose proof (IHops2 ((cond_id, false) :: en) sR PsR
                    (fun x Hx => Hen_t x Hx)) as Helse.
      destruct (dataflow_ops ctx ((cond_id, false) :: en) op2 sR) as [ue s_else] eqn:Ee.
      rewrite (bind_red (dataflow_ops ctx ((cond_id, false) :: en) op2) _ sR _ _ Ee).
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
      destruct Pfinal as [Hlf [_ [Habf [Hempf Hnzf]]]].
      split; [ | split; [ | split; [ | split ] ] ].
      + unfold sF; cbn [graph]. exact Hlf.
      + unfold sF; cbn [var_map]. exact Nfinal.
      + unfold sF; cbn [graph]. exact Habf.
      + unfold sF; cbn [graph]. exact Hempf.
      + unfold sF; cbn [graph]. exact Hnzf.
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
    { split; [ | split; [ | split; [ | split ] ] ].
      - cbn. lia.
      - intros k id Hin. destruct Hin.
      - intros node Hin x Hx. cbn in Hin. destruct Hin as [<-|[]]. cbn in Hx. destruct Hx.
      - intros node Hin He. cbn in Hin. destruct Hin as [<-|[]]. cbn. reflexivity.
      - intros node Hin He. cbn in Hin. destruct Hin as [<-|[]]. cbn in He.
        exfalso. apply He. reflexivity. }
    unfold build_dfg.
    (* the top-level path condition is empty, so its literals are vacuous *)
    pose proof (dataflow_ops_pos (tfs_spec_action_ops ctx act) []
                  {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |} Hempty
                  (fun x Hx => match Hx with end)) as Hop.
    destruct (dataflow_ops ctx [] (tfs_spec_action_ops ctx act)
                {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |})
      as [u final] eqn:Ed.
    destruct Hop as [_ [Hvm [Hargs [Hemp _]]]].
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
    pose proof (dataflow_ops_full (tfs_spec_action_ops ctx act) []
                  {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |} Hempty
                  (fun x Hx => match Hx with end)) as Hop.
    destruct (dataflow_ops ctx [] (tfs_spec_action_ops ctx act)
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
    pose proof (dataflow_ops_fg (tfs_spec_action_ops ctx act) []
                  {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |}
                  Hempty Hemvsz Hemfg (fun x Hx => match Hx with end)) as Hop.
    destruct (dataflow_ops ctx [] (tfs_spec_action_ops ctx act)
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
    pose proof (dataflow_ops_full (tfs_spec_action_ops ctx act) []
                  {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |} Hempty
                  (fun x Hx => match Hx with end)) as Hop.
    destruct (dataflow_ops ctx [] (tfs_spec_action_ops ctx act)
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
               (calc_backward_cost ctx cost_limit (build_dfg ctx act)) (nid node) with
       | Some c => c | None => 0 end)
      <= (match BitsToLists.list_assoc
               (calc_backward_cost ctx cost_limit (build_dfg ctx act)) x with
          | Some c => c | None => 0 end).
  Proof.
    intros act node x Hnode Hx.
    change (getn (calc_backward_cost ctx cost_limit (build_dfg ctx act)) (nid node)
            <= getn (calc_backward_cost ctx cost_limit (build_dfg ctx act)) x).
    rewrite calc_backward_cost_fold.
    (* split the processing list at [node] *)
    pose proof Hnode as HinL. apply in_rev in HinL.
    apply in_split in HinL. destruct HinL as [pre [rest Hsplit]].
    rewrite Hsplit, fold_left_app. cbn [fold_left].
    set (acc0 := fold_left bc_aux pre []).
    (* base inequality after processing [node] itself *)
    apply cost_ge_after_fold.
    - unfold bc_aux.
      set (w := getn acc0 (nid node) + cost_fn ctx cost_limit (op node) (sz node)).
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
                (calc_backward_cost ctx cost_limit (build_dfg ctx act)) (nid node)) as [c1|];
    destruct (BitsToLists.list_assoc
                (calc_backward_cost ctx cost_limit (build_dfg ctx act)) x) as [c2|];
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
        (calc_backward_cost ctx cost_limit (build_dfg ctx act)) (nid node) <> None.
  Proof.
    intros act node Hin. unfold calc_backward_cost.
    apply in_rev in Hin.
    apply (fold_pres_mem (fun n => nid n)
             (fun cost_map n =>
                     list_assoc_set_all_max cost_map
                       (nid n :: get_args ctx n)
                       (match BitsToLists.list_assoc cost_map (nid n) with
                        | Some c => c | None => 0 end
                        + cost_fn ctx cost_limit (op n) (sz n)))).
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
      (calc_backward_cost ctx cost_limit (build_dfg ctx act)) n); cbn [option_map]; congruence.
  Qed.

  (* Every edge either remains within one target cycle or crosses a cycle
     boundary, in which case the argument is buffered -- unless it is a source
     node, which is stable for the whole action and is re-read in place. *)
  Lemma arg_same_cycle_or_buffer :
    forall (act: tfs_action sched) node x,
      In node (graph (build_dfg ctx act)) ->
      In x (get_args ctx node) ->
      node_cycle act x = node_cycle act (nid node)
      \/ is_source ctx (build_dfg ctx act) x = true
      \/ In x (require_buffer ctx (build_dfg ctx act) (act_cycle_map act)).
  Proof.
    intros act node x Hnode Hx.
    destruct (Nat.eq_dec (node_cycle act x) (node_cycle act (nid node))) as [Heq | Hneq].
    - left. exact Heq.
    - destruct (is_source ctx (build_dfg ctx act) x) eqn:Hsrc; [ right; left; reflexivity |].
      right. right. unfold require_buffer. apply nodup_In. apply in_app_iff. left.
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
      rewrite Hsrc.
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
     Vacuous at the empty start state; the preservation step over dataflow_ops
     is the sole remaining assumption here. *)
  Definition vmg (s : dfg_state_t (states_var:=s_var)(inputs_var:=i_var)(outputs_var:=o_var)(ips_var:=p_var)) : Prop :=
    forall k id, In (k, id) (var_map s) ->
                 exists node, In node (graph s) /\ nid node = id.

  Local Notation dstate :=
    (dfg_state_t (states_var:=s_var)(inputs_var:=i_var)(outputs_var:=o_var)(ips_var:=p_var)).

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
    - destruct (read_var ctx dfg_v s) as [id s'] eqn:Er.
      destruct (read_var_cases dfg_v s id s' Er) as [[Hin [_ ->]] | Hem].
      + split; [ apply gmono_refl | intro Hv; split; [ | exact Hv ] ].
        eexists. split; [ exact Hin | reflexivity ].
      + pose proof (emit_spec (DFG_Var dfg_v) (dfg_var_size ctx dfg_v) s) as Hf.
        rewrite Hem in Hf. exact (proj1 Hf).
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

  (* The control-flow-merge core: if every then/else binding names a node of the
     current graph, then after merge_maps every resulting binding names a node
     of the grown graph.  The sole assumption under dataflow_ops_preserves_vmg. *)

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
    forall (ops: @tf_ops s_var i_var o_var p_var) (en: list (nid_t * bool)) s, vmg s ->
      let (u, s') := dataflow_ops ctx en ops s in ospecv s s'.
  Proof.
    induction ops as [ op | op1 IH1 op2 IH2 | cond then_ops IHthen else_ops IHelse ];
      intros en s Hv.
    - (* tf_ops_base *)
      destruct op as [ | dst expr | dst expr | ip dst arg ]; cbn [dataflow_ops].
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
      + (* THE ROUND TRIP: four emits and one set_var, chained through espec. *)
        unfold bind. cbn [get_state].
        pose proof (dataflow_expr_spec arg (ip_req_sz (tfs_spec_ip ctx ip)) s Hv) as Ha.
        destruct (dataflow_expr ctx arg (ip_req_sz (tfs_spec_ip ctx ip)) s)
          as [arg_id sa]. destruct Ha as [ga [na va]].
        pose proof (emit_spec (DFG_Drive ip arg_id en)
                      (ip_req_sz (tfs_spec_ip ctx ip)) sa) as Hd.
        destruct (emit ctx (DFG_Drive ip arg_id en)
                    (ip_req_sz (tfs_spec_ip ctx ip)) sa) as [drive_id sd].
        destruct Hd as [[gd vd] _]. destruct (vd va) as [nd vd2].
        assert (Hhead : let (hid, sh) :=
                          match last_sample ctx s ip en with
                          | None => ret ctx drive_id
                          | Some prev => emit ctx (DFG_Join drive_id prev) 1
                          end sd in
                        gmono sd sh /\ nidwf sh hid /\ vmg sh).
        { destruct (last_sample ctx s ip en) as [prev |].
          - pose proof (emit_spec (DFG_Join drive_id prev) 1 sd) as Hj.
            destruct (emit ctx (DFG_Join drive_id prev) 1 sd) as [hid sh].
            destruct Hj as [[gj vj] _]. destruct (vj vd2) as [nj vj2].
            split; [ exact gj | split; [ exact nj | exact vj2 ] ].
          - unfold ret. split; [ apply gmono_refl | split; [ exact nd | exact vd2 ] ]. }
        destruct (match last_sample ctx s ip en with
                  | None => ret ctx drive_id
                  | Some prev => emit ctx (DFG_Join drive_id prev) 1
                  end sd) as [head_id sh].
        destruct Hhead as [gh [nh vh]].
        assert (Hstall : let (sid, s1) :=
                           stall_chain ctx (ip_lat (tfs_spec_ip ctx ip)) head_id sh in
                         gmono sh s1 /\ nidwf s1 sid /\ vmg s1).
        { unfold stall_chain. destruct (ip_lat (tfs_spec_ip ctx ip)) as [| l].
          - unfold ret. split; [ apply gmono_refl | split; [ exact nh | exact vh ] ].
          - pose proof (emit_spec (DFG_Stall (S l) head_id) (counter_sz (S l)) sh) as Ht.
            destruct (emit ctx (DFG_Stall (S l) head_id) (counter_sz (S l)) sh) as [sid s1].
            destruct Ht as [[gt vt] _]. destruct (vt vh) as [nt vt2].
            split; [ exact gt | split; [ exact nt | exact vt2 ] ]. }
        destruct (stall_chain ctx (ip_lat (tfs_spec_ip ctx ip)) head_id sh)
          as [stall_id s1].
        destruct Hstall as [gt [nt vt]].
        pose proof (emit_spec (DFG_Sample ip stall_id en)
                      (dfg_var_size ctx (DFG_SVar dst)) s1) as Hm.
        destruct (emit ctx (DFG_Sample ip stall_id en)
                    (dfg_var_size ctx (DFG_SVar dst)) s1) as [samp_id s2].
        destruct Hm as [[gm vm] _]. destruct (vm vt) as [nm vm2].
        pose proof (set_var_ospecv (DFG_SVar dst) samp_id s2 nm vm2) as Hs.
        destruct (set_var ctx (DFG_SVar dst) samp_id s2) as [u s3].
        destruct Hs as [gs vs].
        split;
          [ eapply gmono_trans; [ exact ga |];
            eapply gmono_trans; [ exact gd |];
            eapply gmono_trans; [ exact gh |];
            eapply gmono_trans; [ exact gt |];
            eapply gmono_trans; [ exact gm |]; exact gs
          | exact vs ].
    - (* tf_ops_cons *)
      cbn [dataflow_ops]. unfold bind.
      specialize (IH1 en s Hv).
      destruct (dataflow_ops ctx en op1 s) as [u1 s1]. destruct IH1 as [g1 v1].
      specialize (IH2 en s1 v1).
      destruct (dataflow_ops ctx en op2 s1) as [u2 s2]. destruct IH2 as [g2 v2].
      split; [ eapply gmono_trans; eauto | exact v2 ].
    - (* tf_ops_if *)
      unfold ospecv. cbn [dataflow_ops]. unfold bind, get_state, put_state.
      (* cond *)
      pose proof (dataflow_expr_spec cond 1 s Hv) as Hc.
      destruct (dataflow_expr ctx cond 1 s) as [cond_id s0].
      destruct Hc as [g0 [n0 v0]].
      (* then branch on s0 *)
      specialize (IHthen ((cond_id, true) :: en) s0 v0).
      destruct (dataflow_ops ctx ((cond_id, true) :: en) then_ops s0) as [ut s1].
      destruct IHthen as [g1 v1].
      (* else branch on sp = {graph:=graph s1; var_map:=var_map s0} *)
      assert (Hvsp : vmg {| graph := graph s1; var_map := var_map s0 |}).
      { unfold vmg; cbn. intros k id Hin.
        destruct (v0 k id Hin) as [node [Hn Hnid]].
        exists node. split; [ apply g1; exact Hn | exact Hnid ]. }
      specialize (IHelse ((cond_id, false) :: en) _ Hvsp).
      destruct (dataflow_ops ctx ((cond_id, false) :: en) else_ops
                  {| graph := graph s1; var_map := var_map s0 |})
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
    forall (ops: @tf_ops s_var i_var o_var p_var) (en: list (nid_t * bool)) s,
      vmg s -> vmg (snd (dataflow_ops ctx en ops s)).
  Proof.
    intros ops en s Hv. pose proof (dataflow_ops_spec ops en s Hv) as H.
    destruct (dataflow_ops ctx en ops s) as [u s2]. cbn. apply (proj2 H).
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
    destruct (dataflow_ops ctx [] (tfs_spec_action_ops ctx act)
                {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0 |} ]; var_map := [] |})
      as [u final] eqn:E.
    cbn in Hin |- *.
    assert (Hv : vmg final).
    { pose proof (dataflow_ops_preserves_vmg (tfs_spec_action_ops ctx act) []
                    {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0 |} ]; var_map := [] |}) as HP.
      rewrite E in HP. cbn in HP. apply HP.
      unfold vmg. intros k0 id0 HI. cbn in HI. destruct HI. }
    destruct (Hv k id Hin) as [node [Hng Hnn]].
    exists node. split; [ rewrite <- in_rev; exact Hng | exact Hnn ].
  Qed.

  (* Well-formedness of build_dfg: every var_map output node has a cost entry,
     being in the graph.  The cost-existence half is proved; the structural
     var_map_snd_is_graph_nid is assumed. *)
  Lemma var_map_output_has_cost :
    forall (act: tfs_action sched) n,
      In n (map snd (var_map (build_dfg ctx act))) ->
      BitsToLists.list_assoc
        (calc_target_cycle cost_limit
           (calc_backward_cost ctx cost_limit (build_dfg ctx act))) n <> None.
  Proof.
    intros act n Hn.
    rewrite list_assoc_calc_target_cycle.
    destruct (var_map_snd_is_graph_nid act n Hn) as [node [Hnode Hnid]].
    subst n.
    pose proof (graph_nid_has_cost act node Hnode) as Hc.
    destruct (BitsToLists.list_assoc
                (calc_backward_cost ctx cost_limit (build_dfg ctx act)) (nid node)) as [c|].
    - cbn [option_map]. discriminate.
    - congruence.
  Qed.


  (* Every buffered nid is a REAL node of the forward graph: the arg-part holds
     args of graph nodes, the out-part var_map values (positive by
     build_dfg_args_pos, graph nids by var_map_snd_is_graph_nid). *)
  Lemma require_buffer_node_range :
    forall (act: tfs_action sched) n,
      In n (require_buffer ctx (build_dfg ctx act)
              (calc_target_cycle cost_limit
                 (calc_backward_cost ctx cost_limit (build_dfg ctx act)))) ->
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
    destruct Hin as [HA | Hrest];
      [| apply in_app_iff in Hrest; destruct Hrest as [HB | HC] ].
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
    - (* a sample, buffered wherever the schedule puts it *)
      unfold sample_nodes in HC. apply in_map_iff in HC.
      destruct HC as [node [Hnid Hnode]]. apply filter_In in Hnode.
      destruct Hnode as [Hnode Hsam]. subst n.
      split; [| exact (Hnid_lt node Hnode) ].
      (* a sample reads its token, and an arg ranks below its node *)
      destruct (op node) as [c|iv|dv|uop ua|bop b1 b2|ra|pc pt pe|slat sa
                            |dp da den|sp tok sen|ja jb|] eqn:Hop;
        try discriminate Hsam.
      assert (Htok : In tok (get_args ctx node))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      pose proof (args_lt_fwd act node Hnode tok Htok). lia.
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

  (* A stall's counter register is wide enough to reach [pred l]: [stall_chain]
     emits the node at [counter_sz l], and [wfg] carries that width to the
     register through [buffer_register_node_size]. *)
  Lemma stall_counter_wide
        (act: tfs_action sched) a_idx n_idx l :
    act_idx_aligned act a_idx ->
    stall_lat_of act (vreg_nid a_idx n_idx) = Some l ->
    1 <= l /\ pred l < pow2 (ss_sz (tf_dfg_b a_idx n_idx)).
  Proof.
    intros Halign Hst.
    destruct (vreg_nid_node_range act a_idx n_idx Halign) as [_ Hlen].
    pose proof (wfg_build_dfg act
      (nth (vreg_nid a_idx n_idx) (graph (build_dfg ctx act))
         {| nid := 0; op := DFG_Empty; sz := 0 |})
      (nth_In _ _ Hlen)) as Hfg.
    unfold stall_lat_of, node_op in Hst.
    unfold node_args_sz in Hfg.
    destruct (op (nth (vreg_nid a_idx n_idx) (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |})) eqn:Hop;
      try discriminate Hst.
    injection Hst as <-. destruct Hfg as [Hl Hsz].
    split; [ exact Hl |].
    rewrite (buffer_register_node_size act a_idx n_idx Halign), Hsz.
    apply pred_lt_counter_sz. exact Hl.
  Qed.

  Lemma list_assoc_in_some {K} `{EqDec K} {A} (l: list (K * A)) k v :
    In (k, v) l -> BitsToLists.list_assoc l k <> None.
  Proof.
    induction l as [| [k0 v0] l IH]; [ intros [] |].
    cbn [In BitsToLists.list_assoc]. intros [Heq | Hin].
    - injection Heq as Hk _. subst k0.
      destruct (eq_dec k k); [ discriminate | congruence ].
    - destruct (eq_dec k k0); [ discriminate | apply IH; exact Hin ].
  Qed.

  (* Every sample has a buffer, so a reference expression stops at a register
     and never inlines to the port: [require_buffer] takes [sample_nodes]
     outright, whatever the schedule does with the cycles. *)
  (* A sample sits IN the graph: past the end [nth] gives the empty node. *)
  Lemma sample_node_in_range (act: tfs_action sched) n :
    is_sample_of act n = true -> n < length (graph (build_dfg ctx act)).
  Proof.
    unfold is_sample_of, node_op. intro Hs.
    destruct (Nat.ltb n (length (graph (build_dfg ctx act)))) eqn:Hlt;
      [ apply Nat.ltb_lt; exact Hlt |].
    apply Nat.ltb_ge in Hlt. rewrite nth_overflow in Hs by exact Hlt.
    cbn [op] in Hs. discriminate Hs.
  Qed.

  Lemma sample_is_buffered (act: tfs_action sched) a_idx n :
    act_idx_aligned act a_idx ->
    is_sample_of act n = true ->
    BitsToLists.list_assoc (sample_bufs act a_idx) n <> None.
  Proof.
    intros Halign Hsam.
    pose proof (sample_node_in_range act n Hsam) as Hlen.
    assert (Hin : In n (require_buffer ctx (build_dfg ctx act)
                          (calc_target_cycle cost_limit
                             (calc_backward_cost ctx cost_limit (build_dfg ctx act))))).
    { apply nodup_In, in_app_iff. right. apply in_app_iff. right.
      unfold sample_nodes. apply in_map_iff.
      exists (nth n (graph (build_dfg ctx act))
                {| nid := 0; op := DFG_Empty; sz := 0 |}).
      split; [ apply node_nid_at; exact Hlen |].
      apply filter_In. split; [ apply nth_In; exact Hlen |].
      unfold is_sample_of, node_op in Hsam. exact Hsam. }
    assert (Hfst : In n (map fst (nth (index_to_nat a_idx)
                                    (buffer_needs ctx cost_limit) []))).
    { rewrite (buffer_slot_eq act a_idx Halign), gsi_map_fst. exact Hin. }
    apply in_map_iff in Hfst. destruct Hfst as [[n' v] [Heq Hentry]].
    cbn [fst] in Heq. subst n'.
    apply (list_assoc_in_some _ n v).
    unfold sample_bufs. apply filter_In. split; [ exact Hentry | exact Hsam ].
  Qed.

  (* When a cycle does NOT fire the done flag, tfs_next_cycle takes the ALWAYS
     branch: cycle_updates reduces to just the always-updates (no reset/done
     prefix).  This is the entry point for pre-done buffer reasoning. *)
  Lemma cycle_updates_not_done (act: tfs_action sched) (ss: sched_sys_state) (input: sched_input_t) :
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
  (* Every op compile_dfg_drives emits is a [tf_assign (tf_dfg_ov o)], i.e. a
     SCHEDULER register.  That is what keeps [always_ops_no_out] true: the
     always half writes registers the scheduler invented, never outputs. *)
  Lemma compile_dfg_drives_no_out
    (a_idx: nat)
    (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var) (outputs_var := o_var) (ips_var := p_var))
    (buffers: list (nat * (nat * nat))) (o: o_var)
    (op: @tf_op (tfs_states sched) si_var o_var Empty_set) :
    In op (compile_dfg_drives ctx bneeds a_idx dfg buffers) ->
    ~ op_writes_out o op.
  Proof.
    unfold compile_dfg_drives.
    destruct (index_of_nat _ a_idx) as [a' |]; [| intros []].
    intro Hin. apply in_map_iff in Hin. destruct Hin as [o' [Hop _]].
    subst op. intros [e He]; discriminate He.
  Qed.

  Lemma compile_dfg_drives_no_svar
    (a_idx: nat)
    (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var) (outputs_var := o_var) (ips_var := p_var))
    (buffers: list (nat * (nat * nat))) (sv: s_var)
    (op: @tf_op (tfs_states sched) si_var o_var Empty_set) :
    In op (compile_dfg_drives ctx bneeds a_idx dfg buffers) ->
    ~ op_assigns_st (tf_dfg_s sv) op.
  Proof.
    unfold compile_dfg_drives.
    destruct (index_of_nat _ a_idx) as [a' |]; [| intros []].
    intro Hin. apply in_map_iff in Hin. destruct Hin as [o' [Hop _]].
    subst op. intros [e He]; inversion He.
  Qed.

  Lemma compile_dfg_buffers_no_svar
    (a_idx: nat)
    (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var) (outputs_var := o_var) (ips_var := p_var))
    (buffers: list (nat * (nat * nat))) (s: s_var)
    (op: @tf_op (tfs_states sched) si_var o_var Empty_set) :
    In op (compile_dfg_buffers ctx bneeds a_idx dfg buffers) ->
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
    (op: @tf_op (tfs_states sched) si_var o_var Empty_set) :
    In op (fst (Contract.tfs_schedule sched act)) ->
    ~ op_assigns_st (tf_dfg_s s) op.
  Proof.
    unfold sched, tfs_schedule, tfs_schedule_bn, Contract.tfs_schedule, schedule. cbv zeta. cbn [fst].
    intro Hin. cbn [In] in Hin. destruct Hin as [Heq | Hin].
    - subst op. unfold compile_dfg_valid. cbv zeta.
      intros [e He]; discriminate He.
    - apply in_app_iff in Hin. destruct Hin as [Hb | Hd].
      + exact (compile_dfg_buffers_no_svar _ _ _ s op Hb).
      + exact (compile_dfg_drives_no_svar _ _ _ s op Hd).
  Qed.

  (* A non-done cycle leaves every base state var tf_dfg_s unchanged: the always-
     ops never assign tf_dfg_s, so find_st_update returns None and the value
     falls through to the pre-cycle register. *)
  Lemma sched_step_preserves_svar (act: tfs_action sched) (ss: sched_sys_state)
    (input: sched_input_t) (s: s_var) :
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
    (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var) (outputs_var := o_var) (ips_var := p_var))
    (buffers: list (nat * (nat * nat))) (o: o_var)
    (op: @tf_op (tfs_states sched) si_var o_var Empty_set) :
    In op (compile_dfg_buffers ctx bneeds a_idx dfg buffers) ->
    ~ op_writes_out o op.
  Proof.
    unfold compile_dfg_buffers.
    destruct (index_of_nat _ a_idx) as [a' |]; [| intros []].
    intro Hin. apply in_flat_map in Hin.
    destruct Hin as [[bnid x] [_ Hop]].
    destruct (index_of_nat _ (fst x)) as [n' |]; [| destruct Hop].
    destruct (compile_dfg_expr _ _ _ _ _ _ _) as [expr valid].
    cbn [In] in Hop.
    (* [op_writes_out] now has TWO disjuncts, since a call writes its request
       port; buffer ops are neither. *)
    destruct Hop as [Heq | [Heq | []]]; subst op;
      intros [e He]; discriminate He.
  Qed.

  (* No op in the always-ops list writes an output: the head assigns the done
     flag and the tail is compile_dfg_buffers (only tf_dfg_b / tf_dfg_v writes).
     Outputs are produced exclusively by the DONE branch of tfs_next_cycle. *)
  Lemma always_ops_no_out (act: tfs_action sched) (o: o_var)
    (op: @tf_op (tfs_states sched) si_var o_var Empty_set) :
    In op (fst (Contract.tfs_schedule sched act)) ->
    ~ op_writes_out o op.
  Proof.
    unfold sched, tfs_schedule, tfs_schedule_bn, Contract.tfs_schedule, schedule. cbv zeta. cbn [fst].
    intro Hin. cbn [In] in Hin. destruct Hin as [Heq | Hin].
    - subst op. unfold compile_dfg_valid. cbv zeta.
      intros [e He]; discriminate He.
    - apply in_app_iff in Hin. destruct Hin as [Hb | Hd].
      + exact (compile_dfg_buffers_no_out _ _ _ o op Hb).
      + exact (compile_dfg_drives_no_out _ _ _ o op Hd).
  Qed.

  (* A non-done cycle leaves every output unchanged. *)
  Lemma sched_step_preserves_ovar (act: tfs_action sched) (ss: sched_sys_state)
    (input: sched_input_t) (o: o_var) :
    ~ done_set (sched_step act ss input) ->
    (snd (sched_step act ss input)).[o] = (snd ss).[o].
  Proof.
    intro Hnd. rewrite sched_step_getout. rewrite (cycle_updates_not_done _ _ _ Hnd).
    unfold find_out_val.
    rewrite (find_out_update_not_in o _ ss input
               (fun op Hin => always_ops_no_out act o op Hin)).
    reflexivity.
  Qed.

  (* The branch path the compiler descends into at a phi occurrence: unchanged
     when the phi stays critical (both branch validities are read), extended by
     the selector when it does not. *)
  Local Notation ppath tainted dfacts pi cnd b :=
    (phi_path (phi_crit tainted dfacts cnd pi) cnd b pi).

  Local Notation ppath_at act pi cnd b :=
    (phi_path (phi_crit (get_tainted ctx (build_dfg ctx act))
                 (decl_facts ctx (build_dfg ctx act)) cnd pi) cnd b pi).

  (* The path only decides criticality, which lives in the VALIDITY component,
     so the value expression is the same under any path. *)
  Lemma compile_fst_pi_irrel (tainted: list nid_t)
        (dfacts: list gfact) a_idx
        (dfg: @dfg_state_t s_var i_var o_var p_var)
        (bufs: list (nid_t * (nat * sz_t))) :
    forall fuel n pi pi',
      fst (compile_dfg_expr_aux ctx bneeds tainted dfacts pi  fuel a_idx dfg n bufs)
      = fst (compile_dfg_expr_aux ctx bneeds tainted dfacts pi' fuel a_idx dfg n bufs).
  Proof.
    induction fuel as [| fuel IH]; intros n pi pi'; [ reflexivity | ].
    cbn [compile_dfg_expr_aux].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |]; [ reflexivity | ].
    cbv beta iota zeta.
    destruct (op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa | dov dn den | siv sn sen | ja jb | ];
      cbv beta iota zeta; try reflexivity.
    - destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  dfg arg bufs) as [ae ve] eqn:E1.
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi' fuel a_idx
                  dfg arg bufs) as [ae' ve'] eqn:E1'.
      pose proof (IH arg pi pi') as Ha. rewrite E1, E1' in Ha. cbn [fst] in Ha.
      cbn [fst]. rewrite Ha. reflexivity.
    - destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  dfg a1 bufs) as [a1e v1e] eqn:E1.
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  dfg a2 bufs) as [a2e v2e] eqn:E2.
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi' fuel a_idx
                  dfg a1 bufs) as [a1e' v1e'] eqn:E1'.
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi' fuel a_idx
                  dfg a2 bufs) as [a2e' v2e'] eqn:E2'.
      pose proof (IH a1 pi pi') as Ha. rewrite E1, E1' in Ha. cbn [fst] in Ha.
      pose proof (IH a2 pi pi') as Hb. rewrite E2, E2' in Hb. cbn [fst] in Hb.
      cbn [fst]. rewrite Ha, Hb. reflexivity.
    - destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  dfg arg bufs) as [ae ve] eqn:E1.
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi' fuel a_idx
                  dfg arg bufs) as [ae' ve'] eqn:E1'.
      pose proof (IH arg pi pi') as Ha. rewrite E1, E1' in Ha. cbn [fst] in Ha.
      cbn [fst]. rewrite Ha. reflexivity.
    - destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  dfg cnd bufs) as [ce cv] eqn:Ec.
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts
                  (ppath tainted dfacts pi cnd true) fuel a_idx dfg tid bufs)
        as [te tv] eqn:Et.
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts
                  (ppath tainted dfacts pi cnd false) fuel a_idx dfg eid bufs)
        as [ee ev] eqn:Ee.
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi' fuel a_idx
                  dfg cnd bufs) as [ce' cv'] eqn:Ec'.
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts
                  (ppath tainted dfacts pi' cnd true) fuel a_idx dfg tid bufs)
        as [te' tv'] eqn:Et'.
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts
                  (ppath tainted dfacts pi' cnd false) fuel a_idx dfg eid bufs)
        as [ee' ev'] eqn:Ee'.
      pose proof (IH cnd pi pi') as Hc. rewrite Ec, Ec' in Hc. cbn [fst] in Hc.
      pose proof (IH tid (ppath tainted dfacts pi cnd true)
                     (ppath tainted dfacts pi' cnd true)) as Ht.
      rewrite Et, Et' in Ht. cbn [fst] in Ht.
      pose proof (IH eid (ppath tainted dfacts pi cnd false)
                     (ppath tainted dfacts pi' cnd false)) as He.
      rewrite Ee, Ee' in He. cbn [fst] in He.
      cbn [fst]. rewrite Hc, Ht, He. reflexivity.
    - (* DFG_Stall: carries no value, so both sides are [tf_const 0] once the
         recursive call is destructed. *)
      cbn [fst].
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx dfg sa bufs).
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi' fuel a_idx dfg sa bufs).
      reflexivity.
    - (* DFG_Drive: its value IS its argument's, so the IH is the whole proof. *)
      apply IH.
    - (* DFG_Sample: the VALUE half is [tf_ivar v], which does not mention the
         path at all. *)
      cbn [fst].
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx dfg sn bufs).
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi' fuel a_idx dfg sn bufs).
      reflexivity.
    - (* DFG_Join: no value either. *)
      cbn [fst].
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx dfg ja bufs).
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx dfg jb bufs).
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi' fuel a_idx dfg ja bufs).
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi' fuel a_idx dfg jb bufs).
      reflexivity.
  Qed.

  Lemma guard_incl_mono (g pi pi': list lit) :
    (forall x, In x pi -> In x pi') ->
    guard_incl g pi = true -> guard_incl g pi' = true.
  Proof.
    intros Hsub H. apply forallb_forall. intros a Ha.
    pose proof (proj1 (forallb_forall _ _) H a Ha) as Hex.
    apply existsb_exists in Hex. destruct Hex as [b [Hb Heq]].
    apply existsb_exists. exists b. split; [ apply Hsub; exact Hb | exact Heq ].
  Qed.

  (* A longer path declassifies more, so it can only make a phi SELECTING. *)
  Lemma phi_crit_mono (tainted: list nid_t) (dfacts: list gfact)
        (c: nid_t) (pi pi': list lit) :
    (forall x, In x pi -> In x pi') ->
    phi_crit tainted dfacts c pi' = true -> phi_crit tainted dfacts c pi = true.
  Proof.
    intros Hsub H. unfold phi_crit in *.
    apply andb_true_iff in H. destruct H as [Hm Hd].
    apply andb_true_iff. split; [ exact Hm |].
    apply negb_true_iff in Hd. apply negb_true_iff.
    destruct (declassified_at dfacts c pi) eqn:E; [| reflexivity ].
    exfalso. unfold declassified_at in *.
    apply existsb_exists in E. destruct E as [g [Hg Hincl]].
    assert (Hex : existsb (fun g0 => guard_incl g0 pi') (gfacts_of dfacts c) = true).
    { apply existsb_exists. exists g.
      split; [ exact Hg | exact (guard_incl_mono g pi pi' Hsub Hincl) ]. }
    rewrite Hex in Hd. discriminate.
  Qed.

  (* Compiling under a LONGER path condition only WEAKENS the validity: the
     path enters only through [declassified_at], so a phi that was critical --
     both branches -- becomes selecting, which the first implies. *)
  Lemma compile_valid_path_mono
        (act: tfs_action sched) a_idx (ss: sched_sys_state) (input: sched_input_t)
        (bufs: list (nid_t * (nat * sz_t))) :
    forall fuel n (pi pi': list lit),
      (forall x, In x pi -> In x pi') ->
      eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                    (build_dfg ctx act) n bufs)) ss input = Bits.ones 1 ->
      eval1 (snd (compile_dfg_expr_at ctx bneeds pi' fuel a_idx
                    (build_dfg ctx act) n bufs)) ss input = Bits.ones 1.
  Proof.
    intro fuel. induction fuel as [| fuel IH]; intros n pi pi' Hsub Hval;
      [ exact Hval |].
    cbn [compile_dfg_expr_aux] in Hval |- *.
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:Hla;
      [ exact Hval |].
    cbv beta iota in Hval |- *.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | op1 arg | op1 arg1 arg2 | arg | cnd tid eid | slat sa | dov dn den | siv sn sen | ja jb | ] eqn:Hop.
    - exact Hval.
    - exact Hval.
    - destruct v; exact Hval.
    - (* Unary *)
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  arg bufs) as [ae ve] eqn:E1.
      destruct (compile_dfg_expr_at ctx bneeds pi' fuel a_idx (build_dfg ctx act)
                  arg bufs) as [ae' ve'] eqn:E2.
      cbn [snd] in Hval |- *.
      pose proof (IH arg pi pi' Hsub ltac:(rewrite E1; cbn [snd]; exact Hval)) as Hc.
      rewrite E2 in Hc. cbn [snd] in Hc. exact Hc.
    - (* Binary *)
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  arg1 bufs) as [a1e v1e] eqn:E1.
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  arg2 bufs) as [a2e v2e] eqn:E2.
      destruct (compile_dfg_expr_at ctx bneeds pi' fuel a_idx (build_dfg ctx act)
                  arg1 bufs) as [a1e' v1e'] eqn:E3.
      destruct (compile_dfg_expr_at ctx bneeds pi' fuel a_idx (build_dfg ctx act)
                  arg2 bufs) as [a2e' v2e'] eqn:E4.
      cbn [snd] in Hval |- *.
      rewrite valid_and_eval in Hval.
      destruct (bits1_and_split _ _ Hval) as [Hv1 Hv2].
      pose proof (IH arg1 pi pi' Hsub ltac:(rewrite E1; cbn [snd]; exact Hv1)) as Hc1.
      pose proof (IH arg2 pi pi' Hsub ltac:(rewrite E2; cbn [snd]; exact Hv2)) as Hc2.
      rewrite E3 in Hc1. rewrite E4 in Hc2. cbn [snd] in Hc1, Hc2.
      rewrite valid_and_eval, Hc1, Hc2. vm_compute. reflexivity.
    - (* Resize *)
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  arg bufs) as [ae ve] eqn:E1.
      destruct (compile_dfg_expr_at ctx bneeds pi' fuel a_idx (build_dfg ctx act)
                  arg bufs) as [ae' ve'] eqn:E2.
      cbn [snd] in Hval |- *.
      pose proof (IH arg pi pi' Hsub ltac:(rewrite E1; cbn [snd]; exact Hval)) as Hc.
      rewrite E2 in Hc. cbn [snd] in Hc. exact Hc.
    - (* Phi: the only place the path is read *)
      pose proof (compile_fst_pi_irrel (get_tainted ctx (build_dfg ctx act))
                    (decl_facts ctx (build_dfg ctx act)) a_idx (build_dfg ctx act)
                    bufs fuel cnd pi pi') as Hce.
      destruct (phi_crit (get_tainted ctx (build_dfg ctx act))
                  (decl_facts ctx (build_dfg ctx act)) cnd pi) eqn:Hcp;
        destruct (phi_crit (get_tainted ctx (build_dfg ctx act))
                    (decl_facts ctx (build_dfg ctx act)) cnd pi') eqn:Hcp';
        cbn [phi_path] in Hval |- *.
      + (* critical both sides *)
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    cnd bufs) as [ce cv] eqn:Ec.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    tid bufs) as [te tv] eqn:Et.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    eid bufs) as [ee ev] eqn:Ee.
        destruct (compile_dfg_expr_at ctx bneeds pi' fuel a_idx (build_dfg ctx act)
                    cnd bufs) as [ce' cv'] eqn:Ec'.
        destruct (compile_dfg_expr_at ctx bneeds pi' fuel a_idx (build_dfg ctx act)
                    tid bufs) as [te' tv'] eqn:Et'.
        destruct (compile_dfg_expr_at ctx bneeds pi' fuel a_idx (build_dfg ctx act)
                    eid bufs) as [ee' ev'] eqn:Ee'.
        cbn [snd] in Hval |- *.
        rewrite valid_and_eval, valid_and_eval in Hval.
        destruct (bits1_and_split _ _ Hval) as [Hte Hcv].
        destruct (bits1_and_split _ _ Hte) as [Htv Hev].
        pose proof (IH cnd pi pi' Hsub ltac:(rewrite Ec; cbn [snd]; exact Hcv)) as Hac.
        pose proof (IH tid pi pi' Hsub ltac:(rewrite Et; cbn [snd]; exact Htv)) as Hat.
        pose proof (IH eid pi pi' Hsub ltac:(rewrite Ee; cbn [snd]; exact Hev)) as Hae.
        rewrite Ec' in Hac. rewrite Et' in Hat. rewrite Ee' in Hae.
        cbn [snd] in Hac, Hat, Hae.
        rewrite valid_and_eval, valid_and_eval, Hac, Hat, Hae.
        vm_compute. reflexivity.
      + (* critical at [pi], selecting at [pi']: both branches give the one *)
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    cnd bufs) as [ce cv] eqn:Ec.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    tid bufs) as [te tv] eqn:Et.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    eid bufs) as [ee ev] eqn:Ee.
        destruct (compile_dfg_expr_at ctx bneeds pi' fuel a_idx (build_dfg ctx act)
                    cnd bufs) as [ce' cv'] eqn:Ec'.
        destruct (compile_dfg_expr_at ctx bneeds ((cnd, true) :: pi') fuel a_idx
                    (build_dfg ctx act) tid bufs) as [te' tv'] eqn:Et'.
        destruct (compile_dfg_expr_at ctx bneeds ((cnd, false) :: pi') fuel a_idx
                    (build_dfg ctx act) eid bufs) as [ee' ev'] eqn:Ee'.
        cbn [snd] in Hval |- *.
        rewrite valid_and_eval, valid_and_eval in Hval.
        destruct (bits1_and_split _ _ Hval) as [Hte Hcv].
        destruct (bits1_and_split _ _ Hte) as [Htv Hev].
        assert (Hsubt : forall x, In x pi -> In x ((cnd, true) :: pi'))
          by (intros x Hx; right; apply Hsub; exact Hx).
        assert (Hsube : forall x, In x pi -> In x ((cnd, false) :: pi'))
          by (intros x Hx; right; apply Hsub; exact Hx).
        pose proof (IH cnd pi pi' Hsub ltac:(rewrite Ec; cbn [snd]; exact Hcv)) as Hac.
        pose proof (IH tid pi _ Hsubt ltac:(rewrite Et; cbn [snd]; exact Htv)) as Hat.
        pose proof (IH eid pi _ Hsube ltac:(rewrite Ee; cbn [snd]; exact Hev)) as Hae.
        rewrite Ec' in Hac. rewrite Et' in Hat. rewrite Ee' in Hae.
        cbn [snd] in Hac, Hat, Hae.
        rewrite valid_and_eval, Hac, (valid_if_eval ce' tv' ev' ss input Hat Hae).
        vm_compute. reflexivity.
      + (* selecting at [pi], critical at [pi']: impossible *)
        exfalso. rewrite (phi_crit_mono _ _ cnd pi pi' Hsub Hcp') in Hcp.
        discriminate.
      + (* selecting both sides *)
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    cnd bufs) as [ce cv] eqn:Ec.
        destruct (compile_dfg_expr_at ctx bneeds ((cnd, true) :: pi) fuel a_idx
                    (build_dfg ctx act) tid bufs) as [te tv] eqn:Et.
        destruct (compile_dfg_expr_at ctx bneeds ((cnd, false) :: pi) fuel a_idx
                    (build_dfg ctx act) eid bufs) as [ee ev] eqn:Ee.
        destruct (compile_dfg_expr_at ctx bneeds pi' fuel a_idx (build_dfg ctx act)
                    cnd bufs) as [ce' cv'] eqn:Ec'.
        destruct (compile_dfg_expr_at ctx bneeds ((cnd, true) :: pi') fuel a_idx
                    (build_dfg ctx act) tid bufs) as [te' tv'] eqn:Et'.
        destruct (compile_dfg_expr_at ctx bneeds ((cnd, false) :: pi') fuel a_idx
                    (build_dfg ctx act) eid bufs) as [ee' ev'] eqn:Ee'.
        cbn [snd] in Hval |- *. cbn [fst] in Hce.
        rewrite valid_and_eval in Hval.
        destruct (bits1_and_split _ _ Hval) as [Hcv Hif].
        destruct (valid_if_eval_inv ce tv ev ss input Hif) as [Hthen Helse].
        pose proof (IH cnd pi pi' Hsub ltac:(rewrite Ec; cbn [snd]; exact Hcv)) as Hac.
        rewrite Ec' in Hac. cbn [snd] in Hac.
        assert (Hsubt : forall x, In x ((cnd, true) :: pi) -> In x ((cnd, true) :: pi'))
          by (intros x [Hx | Hx]; [ left; exact Hx | right; apply Hsub; exact Hx ]).
        assert (Hsube : forall x, In x ((cnd, false) :: pi) -> In x ((cnd, false) :: pi'))
          by (intros x [Hx | Hx]; [ left; exact Hx | right; apply Hsub; exact Hx ]).
        rewrite valid_and_eval, Hac.
        rewrite (valid_if_eval_sel ce' tv' ev' ss input).
        * vm_compute. reflexivity.
        * intro Hnz.
          pose proof (IH tid _ _ Hsubt
            ltac:(rewrite Et; cbn [snd]; apply Hthen; rewrite Hce; exact Hnz)) as Hat.
          rewrite Et' in Hat. cbn [snd] in Hat. exact Hat.
        * intro Hz.
          pose proof (IH eid _ _ Hsube
            ltac:(rewrite Ee; cbn [snd]; apply Helse; rewrite Hce; exact Hz)) as Hae.
          rewrite Ee' in Hae. cbn [snd] in Hae. exact Hae.
    - (* Stall *)
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  sa bufs) as [ae ve] eqn:E1.
      destruct (compile_dfg_expr_at ctx bneeds pi' fuel a_idx (build_dfg ctx act)
                  sa bufs) as [ae' ve'] eqn:E2.
      cbn [snd] in Hval |- *.
      pose proof (IH sa pi pi' Hsub ltac:(rewrite E1; cbn [snd]; exact Hval)) as Hc.
      rewrite E2 in Hc. cbn [snd] in Hc. exact Hc.
    - (* Drive *) exact (IH dn pi pi' Hsub Hval).
    - (* Sample *)
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  sn bufs) as [ae ve] eqn:E1.
      destruct (compile_dfg_expr_at ctx bneeds pi' fuel a_idx (build_dfg ctx act)
                  sn bufs) as [ae' ve'] eqn:E2.
      cbn [snd] in Hval |- *.
      pose proof (IH sn pi pi' Hsub ltac:(rewrite E1; cbn [snd]; exact Hval)) as Hc.
      rewrite E2 in Hc. cbn [snd] in Hc. exact Hc.
    - (* Join *)
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  ja bufs) as [a1e v1e] eqn:E1.
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  jb bufs) as [a2e v2e] eqn:E2.
      destruct (compile_dfg_expr_at ctx bneeds pi' fuel a_idx (build_dfg ctx act)
                  ja bufs) as [a1e' v1e'] eqn:E3.
      destruct (compile_dfg_expr_at ctx bneeds pi' fuel a_idx (build_dfg ctx act)
                  jb bufs) as [a2e' v2e'] eqn:E4.
      cbn [snd] in Hval |- *.
      rewrite valid_and_eval in Hval.
      destruct (bits1_and_split _ _ Hval) as [Hv1 Hv2].
      pose proof (IH ja pi pi' Hsub ltac:(rewrite E1; cbn [snd]; exact Hv1)) as Hc1.
      pose proof (IH jb pi pi' Hsub ltac:(rewrite E2; cbn [snd]; exact Hv2)) as Hc2.
      rewrite E3 in Hc1. rewrite E4 in Hc2. cbn [snd] in Hc1, Hc2.
      rewrite valid_and_eval, Hc1, Hc2. vm_compute. reflexivity.
    - exact Hval.
  Qed.

  (* Packages the phi step of the VALUE component in one equation, so proofs
     never destructure the three branch compiles.  Stated over variables --
     concrete analysis arguments make the destructs miss. *)
  Lemma compile_fst_phi_gen (tainted: list nid_t)
        (dfacts: list gfact) (pi: list lit) a_idx
        (dfg: @dfg_state_t s_var i_var o_var p_var)
        (bufs: list (nid_t * (nat * sz_t))) fuel n cnd tid eid :
    BitsToLists.list_assoc bufs n = None ->
    op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |})
      = DFG_Phi cnd tid eid ->
    fst (compile_dfg_expr_aux ctx bneeds tainted dfacts pi (S fuel) a_idx dfg n bufs)
    = tf_expr_if
        (fst (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx dfg cnd bufs))
        (fst (compile_dfg_expr_aux ctx bneeds tainted dfacts
                (ppath tainted dfacts pi cnd true) fuel a_idx dfg tid bufs))
        (fst (compile_dfg_expr_aux ctx bneeds tainted dfacts
                (ppath tainted dfacts pi cnd false) fuel a_idx dfg eid bufs)).
  Proof.
    intros Hla Hop.
    cbn [compile_dfg_expr_aux]. rewrite Hla. cbv beta iota zeta.
    rewrite Hop. cbv beta iota zeta.
    destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                dfg cnd bufs) as [ce cv].
    destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts
                (ppath tainted dfacts pi cnd true) fuel a_idx dfg tid bufs) as [te tv].
    destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts
                (ppath tainted dfacts pi cnd false) fuel a_idx dfg eid bufs) as [ee ev].
    cbn [fst]. reflexivity.
  Qed.

  (* The same at the empty path, with the branches normalised back to it. *)
  Lemma compile_fst_phi (act: tfs_action sched) a_idx
        (bufs: list (nid_t * (nat * sz_t))) fuel n cnd tid eid :
    BitsToLists.list_assoc bufs n = None ->
    op (nth n (graph (build_dfg ctx act))
          {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Phi cnd tid eid ->
    fst (compile_dfg_expr ctx bneeds (S fuel) a_idx (build_dfg ctx act) n bufs)
    = tf_expr_if
        (fst (compile_dfg_expr ctx bneeds fuel a_idx (build_dfg ctx act) cnd bufs))
        (fst (compile_dfg_expr ctx bneeds fuel a_idx (build_dfg ctx act) tid bufs))
        (fst (compile_dfg_expr ctx bneeds fuel a_idx (build_dfg ctx act) eid bufs)).
  Proof.
    intros Hla Hop.
    rewrite (compile_fst_phi_gen _ _ _ a_idx _ bufs fuel n cnd tid eid Hla Hop).
    rewrite (compile_fst_pi_irrel _ _ a_idx _ bufs fuel tid
               (ppath (get_tainted ctx (build_dfg ctx act))
                  (decl_facts ctx (build_dfg ctx act)) [] cnd true) []).
    rewrite (compile_fst_pi_irrel _ _ a_idx _ bufs fuel eid
               (ppath (get_tainted ctx (build_dfg ctx act))
                  (decl_facts ctx (build_dfg ctx act)) [] cnd false) []).
    reflexivity.
  Qed.

  (* A BUFFER-FREE compiled expression reads only base state vars (tf_dfg_s),
     outputs and the input, so its value only depends on those.  This is what
     makes a settled value stable across further pre-done cycles. *)
  (* An entry of the slot at index [m] is cached by register [n_idx']. *)
  Lemma vreg_nid_of_entry (act: tfs_action sched) a_idx n m msz n_idx' :
    act_idx_aligned act a_idx ->
    In (n, (m, msz)) (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) ->
    index_of_nat (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) m
      = Some n_idx' ->
    vreg_nid a_idx n_idx' = n.
  Proof.
    intros Halign Hin Hidx.
    assert (Hmi : index_to_nat n_idx' = m) by (apply index_to_nat_of_nat; exact Hidx).
    unfold vreg_nid. rewrite Hmi, (buffer_slot_eq act a_idx Halign).
    rewrite (gsi_entry_at _ _ n m msz
               ltac:(rewrite <- (buffer_slot_eq act a_idx Halign); exact Hin)).
    reflexivity.
  Qed.

  (* The width a buffer slot names is the width its table entry records. *)
  Lemma buffer_slot_size (act: tfs_action sched) a_idx n m msz n_idx' :
    act_idx_aligned act a_idx ->
    In (n, (m, msz)) (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) ->
    index_of_nat (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) m
      = Some n_idx' ->
    ss_sz (tf_dfg_b a_idx n_idx') = msz.
  Proof.
    intros Halign Hin Hidx.
    assert (Hmi : index_to_nat n_idx' = m) by (apply index_to_nat_of_nat; exact Hidx).
    change (ss_sz (tf_dfg_b a_idx n_idx'))
      with (snd (snd (nth (index_to_nat n_idx')
                       (nth (index_to_nat a_idx) bneeds []) (0, (0, 0))))).
    rewrite Hmi, (buffer_slot_eq act a_idx Halign).
    rewrite (gsi_entry_at _ _ n m msz
               ltac:(rewrite <- (buffer_slot_eq act a_idx Halign); exact Hin)).
    reflexivity.
  Qed.

  (* [stall_start] reads the stall.s counter, so it is down once the wait has
     moved off its first cycle. *)
  Lemma eval_stall_start_zero
        (act: tfs_action sched) a_idx h m msz n_idx
        (ss: sched_sys_state) (input: sched_input_t) :
    act_idx_aligned act a_idx ->
    BitsToLists.list_assoc
      (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) h = Some (m, msz) ->
    index_of_nat (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) m
      = Some n_idx ->
    (fst ss).[tf_dfg_b a_idx n_idx] <> Bits.zero ->
    eval1 (stall_start ctx bneeds a_idx (build_dfg ctx act)
             (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) h) ss input
    = Bits.zero.
  Proof.
    intros Halign Hassoc Hidx Hnz.
    pose proof (buffer_slot_size act a_idx h m msz n_idx Halign
                  (wla_in _ _ _ Hassoc) Hidx) as Hsz.
    subst msz.
    unfold stall_start. rewrite Hassoc, Hidx.
    cbn [tf_eval_expr]. rewrite convert_same.
    match goal with
    | |- context [ @beq_dec ?T ?E ?x ?z ] => destruct (@beq_dec T E x z) eqn:Hb
    end.
    - exfalso. exact (Hnz (proj1 (beq_dec_iff _ _ _) Hb)).
    - rewrite convert_same. reflexivity.
  Qed.

  (* THE DRIVE PULSES ONCE: its request leaves the wire as soon as the stall it
     gates on has counted a cycle. *)
  Lemma drive_pulse_zero_of_counter
        (act: tfs_action sched) a_idx n g h m msz n_idx
        (ss: sched_sys_state) (input: sched_input_t) :
    act_idx_aligned act a_idx ->
    chain_gate ctx (build_dfg ctx act) n = Some (g, h) ->
    BitsToLists.list_assoc
      (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) h = Some (m, msz) ->
    index_of_nat (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) m
      = Some n_idx ->
    (fst ss).[tf_dfg_b a_idx n_idx] <> Bits.zero ->
    eval1 (drive_pulse act a_idx n) ss input = Bits.zero.
  Proof.
    intros Halign Hcg Hassoc Hidx Hnz.
    apply drive_pulse_zero_of_vfirst.
    unfold drive_vfirst. rewrite Hcg.
    exact (eval_stall_start_zero act a_idx h m msz n_idx ss input
             Halign Hassoc Hidx Hnz).
  Qed.

  (* STATE INDEPENDENCE, gated by VALIDITY.  A sample's buffer latches on
     [valid && !v], so a validity bit that already reads ones says the register
     will not move; the gate is what turns that into stability of the whole
     reference.  An untainted Phi needs only the branch it selects. *)
  Lemma compile_nobuf_state_indep_gen
        (act: tfs_action sched) a_idx (input1 input2: sched_input_t)
        (ss1 ss2: sched_sys_state)
        (tainted: list nid_t) (dfacts: list gfact)
        (bufs: list (nid_t * (nat * sz_t))) :
    act_idx_aligned act a_idx ->
    (forall s, (fst ss1).[tf_dfg_s s] = (fst ss2).[tf_dfg_s s]) ->
    (forall o, (snd ss1).[o] = (snd ss2).[o]) ->
    (forall v, input1 (inl v) = input2 (inl v)) ->
    (forall e, In e bufs ->
       In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
    (* a buffer of the table whose bit is up reads the same in both states *)
    (forall n_idx, BitsToLists.list_assoc bufs (vreg_nid a_idx n_idx) <> None ->
       (fst ss1).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
       (fst ss1).[tf_dfg_b a_idx n_idx] = (fst ss2).[tf_dfg_b a_idx n_idx]) ->
    forall fuel n szB (pi: list lit),
      n < length (graph (build_dfg ctx act)) ->
      (* the table keeps every sample the expression can reach *)
      (forall x, x <= n -> is_sample_of act x = true ->
         BitsToLists.list_assoc bufs x <> None) ->
      eval1 (snd (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                    (build_dfg ctx act) n bufs)) ss1 input1
        = Bits.ones 1 ->
      tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
        (fst (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                (build_dfg ctx act) n bufs))
        ss1 input1
      = tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
        (fst (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                (build_dfg ctx act) n bufs))
        ss2 input2.
  Proof.
    intros Halign Hs Ho Hi Hsub Hb fuel.
    induction fuel as [| fuel IH]; intros n szB pi Hnlen Hsamples Hval;
      [ reflexivity | ].
    cbn [compile_dfg_expr_aux] in Hval |- *.
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:Hla.
    { (* a SAMPLE buffer: both sides read the register, pinned by its validity *)
      destruct (index_of_nat _ m) as [n_idx' |] eqn:Hn_idx'; [| reflexivity].
      cbv beta iota in Hval |- *.
      assert (Hvn : vreg_nid a_idx n_idx' = n)
        by (apply (vreg_nid_of_entry act a_idx n m msz n_idx' Halign
                     (Hsub _ (wla_in _ _ _ Hla)) Hn_idx')).
      assert (Hmem : BitsToLists.list_assoc bufs (vreg_nid a_idx n_idx') <> None)
        by (rewrite Hvn, Hla; discriminate).
      assert (Hv1 : (fst ss1).[tf_dfg_v a_idx n_idx'] = Bits.ones 1).
      { destruct (op (nth n (graph (build_dfg ctx act))
                        {| nid := 0; op := DFG_Empty; sz := 0 |}));
          cbn [snd tf_eval_expr] in Hval; rewrite convert_same in Hval; exact Hval. }
      destruct (op (nth n (graph (build_dfg ctx act))
                      {| nid := 0; op := DFG_Empty; sz := 0 |}));
        cbn [fst tf_eval_expr];
        try (f_equal; exact (Hb n_idx' Hmem Hv1)); reflexivity. }
    cbv beta iota in Hval |- *.
    (* every recursive call is at an ARGUMENT, hence below [n] *)
    assert (Harg : forall x, In x (get_args ctx
                     (nth n (graph (build_dfg ctx act))
                        {| nid := 0; op := DFG_Empty; sz := 0 |})) -> x < n).
    { intros x Hx.
      pose proof (args_lt_fwd act _ (nth_In _ _ Hnlen) x Hx) as Hlt.
      rewrite (node_nid_at act n Hnlen) in Hlt. exact Hlt. }
    assert (IHb : forall x, x < n -> forall szx (p: list lit),
              eval1 (snd (compile_dfg_expr_aux ctx bneeds tainted dfacts p fuel a_idx
                            (build_dfg ctx act) x bufs)) ss1 input1 = Bits.ones 1 ->
              tf_eval_expr ss_sz si_sz oo_sz (szB := szx)
                (fst (compile_dfg_expr_aux ctx bneeds tainted dfacts p fuel a_idx
                        (build_dfg ctx act) x bufs)) ss1 input1
              = tf_eval_expr ss_sz si_sz oo_sz (szB := szx)
                (fst (compile_dfg_expr_aux ctx bneeds tainted dfacts p fuel a_idx
                        (build_dfg ctx act) x bufs)) ss2 input2).
    { intros x Hx szx p.
      apply (IH x szx p (Nat.lt_trans _ _ _ Hx Hnlen)).
      intros y Hy. apply Hsamples. lia. }
    clear IH.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | op1 arg | op1 arg1 arg2 | arg | cnd tid eid | slat sa | dov dn den | siv sn sen | ja jb | ] eqn:Hop.
    - reflexivity.
    - cbn [fst tf_eval_expr]. rewrite Hi. reflexivity.
    - destruct v; cbn [fst tf_eval_expr]; [ rewrite Hs | rewrite Ho ]; reflexivity.
    - destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  (build_dfg ctx act) arg bufs) as [ae ve] eqn:E1.
      cbn [fst snd] in Hval |- *. destruct op1 as [| src];
        cbn [tf_eval_expr];
        [ specialize (IHb arg ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) szB pi) | specialize (IHb arg ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) src pi) ];
        rewrite E1 in IHb; cbn [fst snd] in IHb; rewrite (IHb Hval); reflexivity.
    - destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  (build_dfg ctx act) arg1 bufs) as [a1e v1e] eqn:E1.
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  (build_dfg ctx act) arg2 bufs) as [a2e v2e] eqn:E2.
      cbn [fst snd] in Hval |- *.
      rewrite valid_and_eval in Hval.
      apply bits1_and_split in Hval. destruct Hval as [Hv1 Hv2].
      pose proof (IHb arg1 ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) szB pi) as Hc1. pose proof (IHb arg2 ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) szB pi) as Hc2.
      rewrite E1 in Hc1. rewrite E2 in Hc2. cbn [fst snd] in Hc1, Hc2.
      specialize (Hc1 Hv1). specialize (Hc2 Hv2).
      destruct op1 as [ | | | | | | szC cop | hz lz ];
        cbn [tf_eval_expr]; try (rewrite Hc1, Hc2; reflexivity).
      + pose proof (IHb arg1 ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) szC pi) as Hd1. pose proof (IHb arg2 ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) szC pi) as Hd2.
        rewrite E1 in Hd1. rewrite E2 in Hd2. cbn [fst snd] in Hd1, Hd2.
        rewrite (Hd1 Hv1), (Hd2 Hv2). destruct cop; reflexivity.
      + pose proof (IHb arg1 ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) hz pi) as He1. pose proof (IHb arg2 ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) lz pi) as He2.
        rewrite E1 in He1. rewrite E2 in He2. cbn [fst snd] in He1, He2.
        rewrite (He1 Hv1), (He2 Hv2). reflexivity.
    - destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  (build_dfg ctx act) arg bufs) as [ae ve] eqn:E1.
      cbn [fst snd tf_eval_expr] in Hval |- *.
      specialize (IHb arg ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) (sz (nth arg (graph (build_dfg ctx act))
                                {| nid := 0; op := DFG_Empty; sz := 0 |})) pi).
      rewrite E1 in IHb. cbn [fst snd] in IHb. rewrite (IHb Hval). reflexivity.
    - destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  (build_dfg ctx act) cnd bufs) as [ce cv] eqn:Ec.
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts
                  (ppath tainted dfacts pi cnd true) fuel a_idx
                  (build_dfg ctx act) tid bufs) as [te tv] eqn:Et.
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts
                  (ppath tainted dfacts pi cnd false) fuel a_idx
                  (build_dfg ctx act) eid bufs) as [ee ev] eqn:Ee.
      cbn [fst snd] in Hval |- *.
      pose proof (IHb cnd ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) 1 pi) as Hcc. rewrite Ec in Hcc. cbn [fst snd] in Hcc.
      pose proof (IHb tid ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) szB (ppath tainted dfacts pi cnd true)) as Hct.
      rewrite Et in Hct. cbn [fst snd] in Hct.
      pose proof (IHb eid ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) szB (ppath tainted dfacts pi cnd false)) as Hce.
      rewrite Ee in Hce. cbn [fst snd] in Hce.
      (* the condition is valid either way, so the two sides SELECT alike *)
      assert (Hcv : eval1 cv ss1 input1 = Bits.ones 1
                    /\ (eval1 ce ss1 input1 <> Bits.zero ->
                        eval1 tv ss1 input1 = Bits.ones 1)
                    /\ (eval1 ce ss1 input1 = Bits.zero ->
                        eval1 ev ss1 input1 = Bits.ones 1)).
      { destruct (phi_crit tainted dfacts cnd pi).
        - rewrite valid_and_eval in Hval. apply bits1_and_split in Hval.
          destruct Hval as [Hval Hc]. rewrite valid_and_eval in Hval.
          apply bits1_and_split in Hval. destruct Hval as [Ht He].
          split; [ exact Hc | split; intros _; assumption ].
        - rewrite valid_and_eval in Hval. apply bits1_and_split in Hval.
          destruct Hval as [Hc Hif]. split; [ exact Hc |].
          exact (valid_if_eval_inv ce tv ev ss1 input1 Hif). }
      destruct Hcv as [Hc [Ht He]].
      assert (Hceq : eval1 ce ss1 input1 = eval1 ce ss2 input2) by exact (Hcc Hc).
      cbn [tf_eval_expr].
      (* both conditions come FROM the goal, then the equation lines them up *)
      match goal with
      | |- (if beq_dec ?c1 _ then _ else _) = _ =>
          replace c1 with (eval1 ce ss1 input1) by reflexivity
      end.
      match goal with
      | |- _ = (if beq_dec ?c2 _ then _ else _) =>
          replace c2 with (eval1 ce ss2 input2) by reflexivity
      end.
      rewrite Hceq.
      match goal with | |- (if ?g then _ else _) = _ => destruct g eqn:Hb0 end.
      + apply Hce, He. rewrite Hceq. exact (proj1 (beq_dec_iff _ _ _) Hb0).
      + apply Hct, Ht. rewrite Hceq. intro Hz.
        rewrite Hz, beq_dec_refl in Hb0. discriminate.
    - (* DFG_Stall: no value, so both sides are [tf_const 0]. *)
      cbn [fst].
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  (build_dfg ctx act) sa bufs).
      reflexivity.
    - (* DFG_Drive, pass-through. *)
      cbn [fst snd] in Hval |- *. exact (IHb dn ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) szB pi Hval).
    - (* DFG_Sample: every sample is buffered, so this arm is unreachable. *)
      exfalso. apply (Hsamples n ltac:(lia));
        [ unfold is_sample_of, node_op; rewrite Hop; reflexivity | exact Hla ].
    - (* DFG_Join: no value either. *)
      cbn [fst].
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  (build_dfg ctx act) ja bufs).
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  (build_dfg ctx act) jb bufs).
      reflexivity.
    - reflexivity.
  Qed.

  Lemma compile_nobuf_state_indep
        (act: tfs_action sched) a_idx (input1 input2: sched_input_t)
        (ss1 ss2: sched_sys_state) :
    act_idx_aligned act a_idx ->
    (forall s, (fst ss1).[tf_dfg_s s] = (fst ss2).[tf_dfg_s s]) ->
    (forall o, (snd ss1).[o] = (snd ss2).[o]) ->
    (forall v, input1 (inl v) = input2 (inl v)) ->
    (forall n_idx, is_sample_of act (vreg_nid a_idx n_idx) = true ->
       (fst ss1).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
       (fst ss1).[tf_dfg_b a_idx n_idx] = (fst ss2).[tf_dfg_b a_idx n_idx]) ->
    forall fuel n szB,
      n < length (graph (build_dfg ctx act)) ->
      eval1 (snd (compile_dfg_expr ctx bneeds fuel a_idx (build_dfg ctx act)
                    n (sample_bufs act a_idx))) ss1 input1 = Bits.ones 1 ->
      tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
        (fst (compile_dfg_expr ctx bneeds fuel a_idx (build_dfg ctx act) n (sample_bufs act a_idx)))
        ss1 input1
      = tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
        (fst (compile_dfg_expr ctx bneeds fuel a_idx (build_dfg ctx act) n (sample_bufs act a_idx)))
        ss2 input2.
  Proof.
    intros Halign Hs Ho Hi Hb fuel n szB Hnlen.
    apply (compile_nobuf_state_indep_gen act a_idx input1 input2 ss1 ss2 _ _
             (sample_bufs act a_idx) Halign Hs Ho Hi).
    - intros e He. exact (proj1 (proj1 (filter_In _ e _) He)).
    - (* an entry of [sample_bufs] IS a sample *)
      intros m Hmem Hv. apply (Hb m); [| exact Hv ].
      destruct (BitsToLists.list_assoc (sample_bufs act a_idx)
                  (vreg_nid a_idx m)) as [e |] eqn:He;
        [| exfalso; apply Hmem; reflexivity ].
      pose proof (wla_in _ _ _ He) as Hin.
      unfold sample_bufs in Hin. apply filter_In in Hin.
      exact (proj2 Hin).
    - exact Hnlen.
    - intros x _ Hx. exact (sample_is_buffered act a_idx x Halign Hx).
  Qed.

  (* The VALIDITY twin: a validity that fires in one state fires in the other,
     given that a valid buffer's bit only goes up and its value stays put.  An
     untainted Phi needs the condition to SELECT alike, which is the value
     lemma above, gated on the condition's own validity. *)
  Lemma compile_valid_state_indep_gen
        (act: tfs_action sched) a_idx (input1 input2: sched_input_t)
        (ss1 ss2: sched_sys_state)
        (tainted: list nid_t) (dfacts: list gfact)
        (bufs: list (nid_t * (nat * sz_t))) :
    act_idx_aligned act a_idx ->
    (forall s, (fst ss1).[tf_dfg_s s] = (fst ss2).[tf_dfg_s s]) ->
    (forall o, (snd ss1).[o] = (snd ss2).[o]) ->
    (forall v, input1 (inl v) = input2 (inl v)) ->
    (forall e, In e bufs ->
       In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
    (forall n_idx, BitsToLists.list_assoc bufs (vreg_nid a_idx n_idx) <> None ->
       (fst ss1).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
       (fst ss1).[tf_dfg_b a_idx n_idx] = (fst ss2).[tf_dfg_b a_idx n_idx]) ->
    (forall n_idx, (fst ss1).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
       (fst ss2).[tf_dfg_v a_idx n_idx] = Bits.ones 1) ->
    forall fuel n (pi: list lit),
      n < length (graph (build_dfg ctx act)) ->
      (forall x, x < n -> is_sample_of act x = true ->
         BitsToLists.list_assoc bufs x <> None) ->
      eval1 (snd (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                    (build_dfg ctx act) n bufs)) ss1 input1 = Bits.ones 1 ->
      eval1 (snd (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                    (build_dfg ctx act) n bufs)) ss2 input2 = Bits.ones 1.
  Proof.
    intros Halign Hs Ho Hi Hsub Hb Hmono fuel.
    induction fuel as [| fuel IH]; intros n pi Hnlen Hsamples Hval; [ exact Hval |].
    cbn [compile_dfg_expr_aux] in Hval |- *.
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:Hla.
    { destruct (index_of_nat _ m) as [n_idx' |] eqn:Hn_idx'; [| exact Hval].
      cbv beta iota in Hval |- *.
      assert (Hv1 : (fst ss1).[tf_dfg_v a_idx n_idx'] = Bits.ones 1).
      { destruct (op (nth n (graph (build_dfg ctx act))
                        {| nid := 0; op := DFG_Empty; sz := 0 |}));
          cbn [snd tf_eval_expr] in Hval; rewrite convert_same in Hval; exact Hval. }
      pose proof (Hmono n_idx' Hv1) as Hv2.
      destruct (op (nth n (graph (build_dfg ctx act))
                      {| nid := 0; op := DFG_Empty; sz := 0 |}));
        cbn [snd tf_eval_expr]; rewrite convert_same; exact Hv2. }
    cbv beta iota in Hval |- *.
    assert (Harg : forall x, In x (get_args ctx
                     (nth n (graph (build_dfg ctx act))
                        {| nid := 0; op := DFG_Empty; sz := 0 |})) -> x < n).
    { intros x Hx.
      pose proof (args_lt_fwd act _ (nth_In _ _ Hnlen) x Hx) as Hlt.
      rewrite (node_nid_at act n Hnlen) in Hlt. exact Hlt. }
    assert (IHb : forall x, x < n -> forall (p: list lit),
              eval1 (snd (compile_dfg_expr_aux ctx bneeds tainted dfacts p fuel a_idx
                            (build_dfg ctx act) x bufs)) ss1 input1 = Bits.ones 1 ->
              eval1 (snd (compile_dfg_expr_aux ctx bneeds tainted dfacts p fuel a_idx
                            (build_dfg ctx act) x bufs)) ss2 input2 = Bits.ones 1).
    { intros x Hx p.
      apply (IH x p (Nat.lt_trans _ _ _ Hx Hnlen)).
      intros y Hy. apply Hsamples. lia. }
    clear IH.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | op1 arg | op1 arg1 arg2 | arg | cnd tid eid | slat sa | dov dn den | siv sn sen | ja jb | ] eqn:Hop.
    - exact Hval.
    - exact Hval.
    - destruct v; exact Hval.
    - (* Unary *)
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  (build_dfg ctx act) arg bufs) as [ae ve] eqn:E1.
      cbn [snd] in Hval |- *.
      pose proof (IHb arg ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) pi ltac:(rewrite E1; cbn [snd]; exact Hval)) as Hc.
      rewrite E1 in Hc. cbn [snd] in Hc. exact Hc.
    - (* Binary *)
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  (build_dfg ctx act) arg1 bufs) as [a1e v1e] eqn:E1.
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  (build_dfg ctx act) arg2 bufs) as [a2e v2e] eqn:E2.
      cbn [snd] in Hval |- *.
      rewrite valid_and_eval in Hval.
      destruct (bits1_and_split _ _ Hval) as [Hv1 Hv2].
      pose proof (IHb arg1 ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) pi ltac:(rewrite E1; cbn [snd]; exact Hv1)) as Hc1.
      pose proof (IHb arg2 ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) pi ltac:(rewrite E2; cbn [snd]; exact Hv2)) as Hc2.
      rewrite E1 in Hc1. rewrite E2 in Hc2. cbn [snd] in Hc1, Hc2.
      rewrite valid_and_eval, Hc1, Hc2. vm_compute. reflexivity.
    - (* Resize *)
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  (build_dfg ctx act) arg bufs) as [ae ve] eqn:E1.
      cbn [snd] in Hval |- *.
      pose proof (IHb arg ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) pi ltac:(rewrite E1; cbn [snd]; exact Hval)) as Hc.
      rewrite E1 in Hc. cbn [snd] in Hc. exact Hc.
    - (* Phi *)
      assert (Hcnd : cnd < n)
        by (apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto).
      pose proof (compile_nobuf_state_indep_gen act a_idx input1 input2 ss1 ss2
                    tainted dfacts bufs Halign Hs Ho Hi Hsub Hb
                    fuel cnd 1 pi ltac:(lia)
                    ltac:(intros y Hy; apply Hsamples; lia)) as Hcond.
      remember (ppath tainted dfacts pi cnd true) as pt eqn:Hpt. clear Hpt.
      remember (ppath tainted dfacts pi cnd false) as pe eqn:Hpe. clear Hpe.
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  (build_dfg ctx act) cnd bufs) as [ce cv] eqn:Ec.
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pt fuel a_idx
                  (build_dfg ctx act) tid bufs) as [te tv] eqn:Et.
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pe fuel a_idx
                  (build_dfg ctx act) eid bufs) as [ee ev] eqn:Ee.
      cbn [snd] in Hval |- *. cbn [fst] in Hcond.
      match type of Hval with context [if ?B then _ else _] => destruct B end.
      + (* critical: all three *)
        rewrite valid_and_eval, valid_and_eval in Hval.
        destruct (bits1_and_split _ _ Hval) as [Hte Hcv].
        destruct (bits1_and_split _ _ Hte) as [Htv Hev].
        pose proof (IHb cnd ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) pi ltac:(rewrite Ec; cbn [snd]; exact Hcv)) as Hac.
        pose proof (IHb tid ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) pt ltac:(rewrite Et; cbn [snd]; exact Htv)) as Hat.
        pose proof (IHb eid ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) pe ltac:(rewrite Ee; cbn [snd]; exact Hev)) as Hae.
        rewrite Ec in Hac. rewrite Et in Hat. rewrite Ee in Hae.
        cbn [snd] in Hac, Hat, Hae.
        rewrite valid_and_eval, valid_and_eval, Hac, Hat, Hae.
        vm_compute. reflexivity.
      + (* selecting: the two states select alike *)
        rewrite valid_and_eval in Hval.
        destruct (bits1_and_split _ _ Hval) as [Hcv Hif].
        pose proof (IHb cnd ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) pi ltac:(rewrite Ec; cbn [snd]; exact Hcv)) as Hac.
        rewrite Ec in Hac. cbn [snd] in Hac.
        destruct (valid_if_eval_inv ce tv ev ss1 input1 Hif) as [Hthen Helse].
        specialize (Hcond ltac:(cbn [snd]; exact Hcv)).
        rewrite valid_and_eval, Hac.
        rewrite (valid_if_eval_sel ce tv ev ss2 input2).
        * vm_compute. reflexivity.
        * intro Hnz.
          pose proof (IHb tid ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) pt ltac:(rewrite Et; cbn [snd]; apply Hthen;
            intro Hz; apply Hnz; rewrite <- Hcond; exact Hz)) as Hat.
          rewrite Et in Hat. cbn [snd] in Hat. exact Hat.
        * intro Hz.
          pose proof (IHb eid ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) pe ltac:(rewrite Ee; cbn [snd]; apply Helse;
            rewrite Hcond; exact Hz)) as Hae.
          rewrite Ee in Hae. cbn [snd] in Hae. exact Hae.
    - (* Stall *)
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  (build_dfg ctx act) sa bufs) as [ae ve] eqn:E1.
      cbn [snd] in Hval |- *.
      pose proof (IHb sa ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) pi ltac:(rewrite E1; cbn [snd]; exact Hval)) as Hc.
      rewrite E1 in Hc. cbn [snd] in Hc. exact Hc.
    - (* Drive *) exact (IHb dn ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) pi Hval).
    - (* Sample *)
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  (build_dfg ctx act) sn bufs) as [ae ve] eqn:E1.
      cbn [snd] in Hval |- *.
      pose proof (IHb sn ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) pi ltac:(rewrite E1; cbn [snd]; exact Hval)) as Hc.
      rewrite E1 in Hc. cbn [snd] in Hc. exact Hc.
    - (* Join *)
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  (build_dfg ctx act) ja bufs) as [a1e v1e] eqn:E1.
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx
                  (build_dfg ctx act) jb bufs) as [a2e v2e] eqn:E2.
      cbn [snd] in Hval |- *.
      rewrite valid_and_eval in Hval.
      destruct (bits1_and_split _ _ Hval) as [Hv1 Hv2].
      pose proof (IHb ja ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) pi ltac:(rewrite E1; cbn [snd]; exact Hv1)) as Hc1.
      pose proof (IHb jb ltac:(apply Harg; unfold get_args; rewrite Hop; cbn [In]; tauto) pi ltac:(rewrite E2; cbn [snd]; exact Hv2)) as Hc2.
      rewrite E1 in Hc1. rewrite E2 in Hc2. cbn [snd] in Hc1, Hc2.
      rewrite valid_and_eval, Hc1, Hc2. vm_compute. reflexivity.
    - exact Hval.
  Qed.

  (* compile_dfg_expr is fuel-invariant above the structural bound: the recursion
     descends only into strictly-smaller arg positions, so any two fuels above a
     node's position agree.  Canonicalises compile calls to a single fuel. *)
  Lemma compile_fuel_irrel_gen (act: tfs_action sched) a_idx buffers
        (tainted: list nid_t) (dfacts: list gfact) :
    forall n,
      1 <= n ->
      n < length (graph (build_dfg ctx act)) ->
      forall f1 f2 (pi: list lit),
        n < f1 -> n < f2 ->
        compile_dfg_expr_aux ctx bneeds tainted dfacts pi f1 a_idx
          (build_dfg ctx act) n buffers
        = compile_dfg_expr_aux ctx bneeds tainted dfacts pi f2 a_idx
          (build_dfg ctx act) n buffers.
  Proof.
    intros n. induction n as [n IH] using (well_founded_induction lt_wf).
    intros Hn1 Hnlen f1 f2 pi Hf1 Hf2.
    destruct f1 as [| f1']; [ lia | ].
    destruct f2 as [| f2']; [ lia | ].
    set (dfg := build_dfg ctx act) in *.
    cbn [compile_dfg_expr_aux].
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
      assert (Hrec : forall x (p: list lit), In x (get_args ctx node) ->
                compile_dfg_expr_aux ctx bneeds tainted dfacts p f1' a_idx dfg x buffers
                = compile_dfg_expr_aux ctx bneeds tainted dfacts p f2' a_idx dfg x buffers).
      { intros x p Hx. destruct (Harg x Hx) as [Hx1 Hx2].
        apply (IH x Hx2 Hx1 (Nat.lt_trans _ _ _ Hx2 Hnlen)); lia. }
      destruct (op node) as [c | v | v | op1 arg | op1 arg1 arg2 | arg | cnd tid eid | slat sa | dov dn den | siv sn sen | ja jb | ] eqn:Hop.
      + reflexivity.
      + reflexivity.
      + destruct v; reflexivity.
      + assert (Hain : In arg (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        rewrite (Hrec arg pi Hain). reflexivity.
      + assert (Ha1 : In arg1 (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        assert (Ha2 : In arg2 (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; left; reflexivity).
        rewrite (Hrec arg1 pi Ha1), (Hrec arg2 pi Ha2). reflexivity.
      + assert (Hain : In arg (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        rewrite (Hrec arg pi Hain). reflexivity.
      + assert (Hcin : In cnd (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        assert (Htin : In tid (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; left; reflexivity).
        assert (Hein : In eid (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; right; left; reflexivity).
        rewrite (Hrec cnd pi Hcin), (Hrec tid (ppath tainted dfacts pi cnd true) Htin),
                (Hrec eid (ppath tainted dfacts pi cnd false) Hein). reflexivity.
      + (* DFG_Stall: one argument, same shape as DFG_Unary / DFG_Resize. *)
        assert (Hain : In sa (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        rewrite (Hrec sa pi Hain). reflexivity.
      + (* SPIKE 2b: DFG_Drive, same shape again. *)
        assert (Hain : In dn (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        rewrite (Hrec dn pi Hain). reflexivity.
      + (* DFG_Sample -- the fuel only reaches the token, and the value half
           does not mention it. *)
        assert (Hain : In sn (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        rewrite (Hrec sn pi Hain). reflexivity.
      + (* DFG_Join: both arguments, for the validity half only. *)
        assert (Hain : In ja (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        assert (Hbin : In jb (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; left; reflexivity).
        rewrite (Hrec ja pi Hain), (Hrec jb pi Hbin). reflexivity.
      + exfalso. apply (node_op_not_empty act n Hn1 Hnlen). exact Hop.
  Qed.

  Lemma compile_fuel_irrel (act: tfs_action sched) a_idx buffers :
    forall n,
      1 <= n ->
      n < length (graph (build_dfg ctx act)) ->
      forall f1 f2,
        n < f1 -> n < f2 ->
        compile_dfg_expr ctx bneeds f1 a_idx (build_dfg ctx act) n buffers
        = compile_dfg_expr ctx bneeds f2 a_idx (build_dfg ctx act) n buffers.
  Proof.
    intros n Hn1 Hnlen f1 f2 Hf1 Hf2.
    exact (compile_fuel_irrel_gen act a_idx buffers _ _ n Hn1 Hnlen f1 f2 [] Hf1 Hf2).
  Qed.

  (* A stall carries no value, whether or not it is buffered: the buffered
     branch returns [tf_const 0] because the register holds its COUNTER, and the
     op branch returns [tf_const 0] because the answer arrives at the sample. *)
  Lemma compile_stall_value
        (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var)
                (outputs_var := o_var) (ips_var := p_var))
        tainted dfacts a_idx n lat arg :
    op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Stall lat arg ->
    forall fuel pi bufs, 0 < fuel ->
      fst (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx dfg n bufs)
      = tf_const 0.
  Proof.
    intros Hop fuel. destruct fuel as [| fuel]; [ intros; lia |].
    intros pi bufs _. cbn [compile_dfg_expr_aux].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |].
    - destruct (index_of_nat _ m) as [n_idx |]; [| reflexivity].
      cbv beta iota. rewrite Hop. reflexivity.
    - cbv beta iota. rewrite Hop.
      destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx dfg arg bufs).
      reflexivity.
  Qed.

  (* A stall's compiled VALIDITY is its argument's, unchanged: the stall itself
     contributes the wait, which [compile_dfg_buffers] counts in the register. *)
  Lemma compile_stall_valid
        (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var)
                (outputs_var := o_var) (ips_var := p_var))
        tainted dfacts a_idx (n: nid_t) lat arg
        (bufs: list (nid_t * (nat * sz_t))) pi fuel :
    op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Stall lat arg ->
    BitsToLists.list_assoc bufs n = None ->
    0 < fuel ->
    snd (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx dfg n bufs)
    = snd (compile_dfg_expr_aux ctx bneeds tainted dfacts pi (pred fuel) a_idx dfg arg bufs).
  Proof.
    intros Hop Hbuf Hf. destruct fuel as [| fuel]; [ lia |]. cbn [Init.Nat.pred].
    cbn [compile_dfg_expr_aux].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:E;
      [ exfalso; rewrite Hbuf in E; congruence |].
    cbv beta iota. rewrite Hop.
    destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx dfg arg bufs).
    reflexivity.
  Qed.

  (* Same step at a sample: its VALIDITY is its token.s, which is where the
     round trip decouples value from validity. *)
  Lemma compile_sample_valid
        (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var)
                (outputs_var := o_var) (ips_var := p_var))
        tainted dfacts a_idx (n: nid_t) p tok en
        (bufs: list (nid_t * (nat * sz_t))) pi fuel :
    op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Sample p tok en ->
    BitsToLists.list_assoc bufs n = None ->
    0 < fuel ->
    snd (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx dfg n bufs)
    = snd (compile_dfg_expr_aux ctx bneeds tainted dfacts pi (pred fuel) a_idx dfg tok bufs).
  Proof.
    intros Hop Hbuf Hf. destruct fuel as [| fuel]; [ lia |]. cbn [Init.Nat.pred].
    cbn [compile_dfg_expr_aux].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:E;
      [ exfalso; rewrite Hbuf in E; congruence |].
    cbv beta iota. rewrite Hop.
    destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx dfg tok bufs).
    reflexivity.
  Qed.

  (* And at a drive: the request is as valid as the argument it carries. *)
  Lemma compile_drive_valid
        (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var)
                (outputs_var := o_var) (ips_var := p_var))
        tainted dfacts a_idx (n: nid_t) p arg en
        (bufs: list (nid_t * (nat * sz_t))) pi fuel :
    op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Drive p arg en ->
    BitsToLists.list_assoc bufs n = None ->
    0 < fuel ->
    snd (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx dfg n bufs)
    = snd (compile_dfg_expr_aux ctx bneeds tainted dfacts pi (pred fuel) a_idx dfg arg bufs).
  Proof.
    intros Hop Hbuf Hf. destruct fuel as [| fuel]; [ lia |]. cbn [Init.Nat.pred].
    cbn [compile_dfg_expr_aux].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:E;
      [ exfalso; rewrite Hbuf in E; congruence |].
    cbv beta iota. rewrite Hop. reflexivity.
  Qed.

  (* And the same step at a join: its validity is the AND the sequencing needs. *)
  Lemma compile_join_valid
        (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var)
                (outputs_var := o_var) (ips_var := p_var))
        tainted dfacts a_idx (n: nid_t) a b
        (bufs: list (nid_t * (nat * sz_t))) pi fuel :
    op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Join a b ->
    BitsToLists.list_assoc bufs n = None ->
    0 < fuel ->
    snd (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx dfg n bufs)
    = valid_expr_and ctx bneeds
        (snd (compile_dfg_expr_aux ctx bneeds tainted dfacts pi (pred fuel) a_idx dfg a bufs))
        (snd (compile_dfg_expr_aux ctx bneeds tainted dfacts pi (pred fuel) a_idx dfg b bufs)).
  Proof.
    intros Hop Hbuf Hf. destruct fuel as [| fuel]; [ lia |]. cbn [Init.Nat.pred].
    cbn [compile_dfg_expr_aux].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:E;
      [ exfalso; rewrite Hbuf in E; congruence |].
    cbv beta iota. rewrite Hop.
    destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx dfg a bufs).
    destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx dfg b bufs).
    reflexivity.
  Qed.

  (* THE JOIN HOLDS THE PORT.  A drive whose chain gate is an unbuffered join
     cannot pulse while the node that join waits on is invalid -- which is the
     sequencing [dataflow_ops] emits it for. *)
  Lemma drive_pulse_zero_of_join
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
        (n j h a b: nid_t) (ss: sched_sys_state) (input: sched_input_t) :
    chain_gate ctx (build_dfg ctx act) n = Some (j, h) ->
    node_op act j = DFG_Join a b ->
    BitsToLists.list_assoc
      (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) j = None ->
    0 < length (graph (build_dfg ctx act)) ->
    eval1 (snd (compile_dfg_expr ctx bneeds
                  (pred (length (graph (build_dfg ctx act)))) a_idx
                  (build_dfg ctx act) b
                  (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))) ss input
      = Bits.zero ->
    eval1 (drive_pulse act a_idx n) ss input = Bits.zero.
  Proof.
    intros Hcg Hj Hbuf Hf Hz.
    apply (drive_pulse_zero_of_vgate act a_idx n j h ss input Hcg).
    unfold node_op in Hj.
    rewrite (compile_join_valid _ _ _ a_idx j a b _ [] _ Hj Hbuf Hf).
    rewrite valid_and_eval, Hz. apply bits1_and_zero_r.
  Qed.

  (* One step of [compile_dfg_expr_aux]'s VALUE at a node that is not a stall:
     buffered, it is that node's own register.  Stated as a match rather than
     under hypotheses because [bufs] is typed at [nid_t] here and at [nat]
     inside the compiler -- convertible, but [rewrite] will not bridge them. *)
  Lemma compile_buffered_value
        (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var)
                (outputs_var := o_var) (ips_var := p_var))
        tainted dfacts a_idx n bufs :
    match op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}) with
    | DFG_Stall _ _ => False | _ => True end ->
    forall fuel pi, 0 < fuel ->
      fst (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx dfg n bufs)
      = match BitsToLists.list_assoc bufs n with
        | Some (m, _) =>
            match index_of_nat
                    (Datatypes.length (nth (index_to_nat a_idx) bneeds [])) m with
            | Some n_idx' => tf_svar (tf_dfg_b a_idx n_idx')
            | None => tf_const 0
            end
        | None =>
            fst (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx dfg n bufs)
        end.
  Proof.
    intros Hns fuel. destruct fuel as [| fuel]; [ intros; lia |].
    intros pi _.
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:E; [| reflexivity].
    cbn [compile_dfg_expr_aux]. rewrite E. cbv beta iota.
    destruct (index_of_nat _ m) as [n_idx' |]; [| reflexivity].
    cbv beta iota.
    destruct (op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}));
      cbn [fst]; try reflexivity; destruct Hns.
  Qed.

  (* A buffered node.s VALIDITY is its own bit, stall or not. *)
  Lemma compile_buffered_valid
        (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var)
                (outputs_var := o_var) (ips_var := p_var))
        tainted dfacts a_idx n bufs m msz n_idx' fuel pi :
    BitsToLists.list_assoc bufs n = Some (m, msz) ->
    index_of_nat (Datatypes.length (nth (index_to_nat a_idx) bneeds [])) m
      = Some n_idx' ->
    0 < fuel ->
    snd (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx dfg n bufs)
    = tf_svar (tf_dfg_v a_idx n_idx').
  Proof.
    intros Hbuf Hidx Hf. destruct fuel as [| fuel]; [ lia |].
    cbn [compile_dfg_expr_aux]. rewrite Hbuf. cbv beta iota.
    rewrite Hidx. cbv beta iota.
    destruct (op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}));
      reflexivity.
  Qed.

  (* A chain gate that is BUFFERED speaks through its validity register, which
     is what lifts [drive_pulse_zero_of_join] off the unbuffered case. *)
  Lemma drive_pulse_zero_of_gate_reg
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
        (n g h m msz: nid_t)
        (n_idx : Vect.index (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])))
        (ss: sched_sys_state) (input: sched_input_t) :
    chain_gate ctx (build_dfg ctx act) n = Some (g, h) ->
    BitsToLists.list_assoc
      (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) g = Some (m, msz) ->
    index_of_nat (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) m
      = Some n_idx ->
    0 < length (graph (build_dfg ctx act)) ->
    (fst ss).[tf_dfg_v a_idx n_idx] = Bits.zero ->
    eval1 (drive_pulse act a_idx n) ss input = Bits.zero.
  Proof.
    intros Hcg Hbuf Hidx Hf Hz.
    apply (drive_pulse_zero_of_vgate act a_idx n g h ss input Hcg).
    rewrite (compile_buffered_valid _ _ _ a_idx g _ m msz n_idx _ [] Hbuf Hidx Hf).
    rewrite eval1_svar_v. exact Hz.
  Qed.

  (* The join.s own validity from the SAMPLE it waits on: a sample is always
     buffered, so what the join ANDs in is that sample.s validity register. *)
  Lemma join_gate_zero_of_prev
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
        (g m prev m0 msz: nid_t)
        (n_idx : Vect.index (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])))
        (ss: sched_sys_state) (input: sched_input_t) :
    node_op act g = DFG_Join m prev ->
    BitsToLists.list_assoc
      (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) g = None ->
    BitsToLists.list_assoc
      (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) prev = Some (m0, msz) ->
    index_of_nat (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) m0
      = Some n_idx ->
    (fst ss).[tf_dfg_v a_idx n_idx] = Bits.zero ->
    1 < length (graph (build_dfg ctx act)) ->
    eval1 (snd (compile_dfg_expr ctx bneeds (length (graph (build_dfg ctx act))) a_idx
                  (build_dfg ctx act) g
                  (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))) ss input
    = Bits.zero.
  Proof.
    intros Hg Hgnb Hpb Hidx Hz Hf.
    assert (HA : 0 < length (graph (build_dfg ctx act))) by lia.
    assert (HB : 0 < pred (length (graph (build_dfg ctx act)))) by lia.
    unfold node_op in Hg.
    rewrite (compile_join_valid _ _ _ a_idx g m prev _ [] _ Hg Hgnb HA).
    rewrite valid_and_eval.
    rewrite (compile_buffered_valid _ _ _ a_idx prev _ m0 msz n_idx _ [] Hpb Hidx HB).
    rewrite eval1_svar_v, Hz. apply bits1_and_zero_r.
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
  (* ---- the buffer table as a lookup: keys are distinct, filters agree ---- *)

  (* A filter that keeps every entry under key [x] is invisible to a lookup of
     [x].  Generic in [K] so both lookups share one [EqDec]. *)
  Lemma list_assoc_filter {K} `{EqDec K} {A} (q: K * A -> bool) (l: list (K * A)) (x: K) :
    (forall e, In e l -> fst e = x -> q e = true) ->
    BitsToLists.list_assoc (filter q l) x = BitsToLists.list_assoc l x.
  Proof.
    intro Hq. induction l as [| [k v] l IH]; cbn [filter]; [ reflexivity |].
    assert (Hrest : forall e, In e l -> fst e = x -> q e = true)
      by (intros e He Hfe; apply Hq; [ right; exact He | exact Hfe ]).
    destruct (q (k, v)) eqn:Hqk; cbn [BitsToLists.list_assoc];
      destruct (eq_dec x k) as [Hxk | Hxk].
    - reflexivity.
    - exact (IH Hrest).
    - exfalso. rewrite (Hq (k, v) (or_introl eq_refl) (eq_sym Hxk)) in Hqk.
      discriminate Hqk.
    - exact (IH Hrest).
  Qed.

  Lemma list_assoc_none_key {K} `{EqDec K} {A} (l: list (K * A)) k :
    BitsToLists.list_assoc l k = None -> ~ In k (map fst l).
  Proof.
    induction l as [| [k0 v0] l IH]; [ intros _ [] |].
    cbn [BitsToLists.list_assoc map fst].
    destruct (eq_dec k k0) as [-> | Hne]; [ discriminate |].
    intros Hn [Heq | Hin]; [ apply Hne; symmetry; exact Heq | exact (IH Hn Hin) ].
  Qed.

  Lemma list_assoc_key_none {K} `{EqDec K} {A} (l: list (K * A)) k :
    ~ In k (map fst l) -> BitsToLists.list_assoc l k = None.
  Proof.
    induction l as [| [k0 v0] l IH]; [ reflexivity |].
    cbn [BitsToLists.list_assoc map fst]. intro Hn.
    destruct (eq_dec k k0) as [-> | Hne];
      [ exfalso; apply Hn; left; reflexivity |].
    apply IH. intro Hin. apply Hn. right. exact Hin.
  Qed.

  (* A sample.s GATE is exactly its stall.s validity bit: the stall is buffered
     -- it IS the counter -- so the walk stops one node in. *)
  Lemma sample_gate_is_stall_reg
        (act: tfs_action sched) a_idx n_idx (p: p_var) (tok: nid_t) en m msz t_idx :
    node_op act (vreg_nid a_idx n_idx) = DFG_Sample p tok en ->
    tok <> vreg_nid a_idx n_idx ->
    BitsToLists.list_assoc
      (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) tok = Some (m, msz) ->
    index_of_nat (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) m
      = Some t_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    buf_gate act a_idx n_idx = tf_svar (tf_dfg_v a_idx t_idx).
  Proof.
    intros Hop Hne Hassoc Hidx Hf.
    assert (Hnone : BitsToLists.list_assoc
                      (filter (fun '(b_nid, _) =>
                                 negb (Nat.eqb b_nid (vreg_nid a_idx n_idx)))
                         (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))
                      (vreg_nid a_idx n_idx) = None).
    { apply list_assoc_key_none. intro Hin.
      apply in_map_iff in Hin. destruct Hin as [[k v] [Hk Hmem]].
      cbn [fst] in Hk. subst k.
      apply filter_In in Hmem. destruct Hmem as [_ Hq].
      rewrite Nat.eqb_refl in Hq. discriminate Hq. }
    assert (Htok : BitsToLists.list_assoc
                     (filter (fun '(b_nid, _) =>
                                negb (Nat.eqb b_nid (vreg_nid a_idx n_idx)))
                        (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))
                     tok = Some (m, msz)).
    { rewrite list_assoc_filter; [ exact Hassoc |].
      intros [k v] _ Hfe. cbn [fst] in Hfe. subst k.
      apply negb_true_iff, Nat.eqb_neq. exact Hne. }
    assert (HA : 0 < length (graph (build_dfg ctx act))) by lia.
    assert (HB : 0 < pred (length (graph (build_dfg ctx act)))) by lia.
    unfold node_op in Hop.
    rewrite (compile_sample_valid _ _ _ a_idx _ p tok en _ [] _ Hop Hnone HA).
    exact (compile_buffered_valid _ _ _ a_idx tok _ m msz t_idx _ [] Htok Hidx HB).
  Qed.

  (* And a stall.s GATE is the validity of the node it waits on -- the drive,
     or the ordering join when the call was sequenced. *)
  Lemma stall_gate_walks
        (act: tfs_action sched) a_idx t_idx (l hd: nid_t) :
    node_op act (vreg_nid a_idx t_idx) = DFG_Stall l hd ->
    hd <> vreg_nid a_idx t_idx ->
    0 < length (graph (build_dfg ctx act)) ->
    buf_gate act a_idx t_idx
    = snd (compile_dfg_expr ctx bneeds (pred (length (graph (build_dfg ctx act)))) a_idx
             (build_dfg ctx act) hd
             (filter (fun '(b_nid, _) => negb (Nat.eqb b_nid (vreg_nid a_idx t_idx)))
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))).
  Proof.
    intros Hop Hne Hf.
    assert (Hnone : BitsToLists.list_assoc
                      (filter (fun '(b_nid, _) =>
                                 negb (Nat.eqb b_nid (vreg_nid a_idx t_idx)))
                         (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))
                      (vreg_nid a_idx t_idx) = None).
    { apply list_assoc_key_none. intro Hin.
      apply in_map_iff in Hin. destruct Hin as [[k v] [Hk Hmem]].
      cbn [fst] in Hk. subst k.
      apply filter_In in Hmem. destruct Hmem as [_ Hq].
      rewrite Nat.eqb_refl in Hq. discriminate Hq. }
    unfold node_op in Hop.
    exact (compile_stall_valid _ _ _ a_idx _ l hd _ [] _ Hop Hnone Hf).
  Qed.

  Lemma list_assoc_nodup_in {K} `{EqDec K} {A} (l: list (K * A)) k v :
    NoDup (map fst l) -> In (k, v) l -> BitsToLists.list_assoc l k = Some v.
  Proof.
    induction l as [| [k0 v0] l IH]; [ intros _ [] |].
    cbn [map fst BitsToLists.list_assoc]. intros Hnd Hin.
    inversion Hnd as [| x xs Hnotin Hnd2]; subst.
    destruct (eq_dec k k0) as [-> | Hne].
    - destruct Hin as [Heq | Hin]; [ injection Heq; intros; subst; reflexivity |].
      exfalso. apply Hnotin, in_map_iff.
      exists (k0, v). split; [ reflexivity | exact Hin ].
    - destruct Hin as [Heq | Hin];
        [ injection Heq as -> _; contradiction | exact (IH Hnd2 Hin) ].
  Qed.

  Lemma nodup_map_fst_filter {K A} (p: K * A -> bool) (l: list (K * A)) :
    NoDup (map fst l) -> NoDup (map fst (filter p l)).
  Proof.
    induction l as [| [k v] l IH]; [ intro; constructor |].
    cbn [filter map fst]. intro Hnd.
    inversion Hnd as [| x xs Hnotin Hnd2]; subst.
    destruct (p (k, v)); [| exact (IH Hnd2) ].
    cbn [map fst]. constructor; [| exact (IH Hnd2) ].
    intro Hin. apply Hnotin.
    apply in_map_iff in Hin. destruct Hin as [[k' v'] [Hk Hmem]].
    apply filter_In in Hmem. destruct Hmem as [Hmem _].
    apply in_map_iff. exists (k', v'). split; [ exact Hk | exact Hmem ].
  Qed.

  (* [require_buffer] is a [nodup], and [get_sizes_and_idx] keeps its keys. *)
  Lemma slot_keys_nodup (act: tfs_action sched) a_idx :
    act_idx_aligned act a_idx ->
    NoDup (map fst (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])).
  Proof.
    intro Halign.
    rewrite (buffer_slot_eq act a_idx Halign), gsi_map_fst.
    unfold require_buffer. apply NoDup_nodup.
  Qed.

  (* Two slots naming the same node are the same slot: the table's keys are
     distinct, so a nid pins its position. *)
  Lemma vreg_nid_inj (act: tfs_action sched) a_idx n_idx m_idx :
    act_idx_aligned act a_idx ->
    vreg_nid a_idx n_idx = vreg_nid a_idx m_idx -> n_idx = m_idx.
  Proof.
    intros Halign Heq. apply index_to_nat_injective.
    apply (proj1 (NoDup_nth _ 0) (slot_keys_nodup act a_idx Halign)).
    - rewrite map_length. apply index_to_nat_bounded.
    - rewrite map_length. apply index_to_nat_bounded.
    - unfold vreg_nid in Heq.
      rewrite (map_nth fst _ (0, (0, 0)) (index_to_nat n_idx)),
              (map_nth fst _ (0, (0, 0)) (index_to_nat m_idx)).
      exact Heq.
  Qed.

  (* A sample's reference IS its register: the table keeps it, so the recursion
     stops at the slot rather than inlining to the port. *)
  Lemma sample_ref_is_register (act: tfs_action sched) a_idx n_idx :
    act_idx_aligned act a_idx ->
    is_sample_of act (vreg_nid a_idx n_idx) = true ->
    forall (pi: list lit) fuel, vreg_nid a_idx n_idx < fuel ->
      compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
        (vreg_nid a_idx n_idx) (sample_bufs act a_idx)
      = (tf_svar (tf_dfg_b a_idx n_idx), tf_svar (tf_dfg_v a_idx n_idx)).
  Proof.
    intros Halign Hsam pi fuel Hfuel.
    destruct (BitsToLists.list_assoc (sample_bufs act a_idx)
                (vreg_nid a_idx n_idx)) as [[q qsz] |] eqn:Hq;
      [| exfalso; exact (sample_is_buffered act a_idx _ Halign Hsam Hq) ].
    pose proof (wla_in _ _ _ Hq) as Hin.
    unfold sample_bufs in Hin. apply filter_In in Hin. destruct Hin as [Hin _].
    assert (Hlt : q < length
              (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])).
    { rewrite (buffer_slot_eq act a_idx Halign), gsi_length.
      apply (gsi_idx_bound (build_dfg ctx act) _ (vreg_nid a_idx n_idx) q qsz).
      rewrite <- (buffer_slot_eq act a_idx Halign). exact Hin. }
    destruct (index_of_nat_bounded Hlt) as [q_idx Hq_idx].
    assert (Hqv : vreg_nid a_idx q_idx = vreg_nid a_idx n_idx)
      by (apply (vreg_nid_of_entry act a_idx _ q qsz q_idx Halign Hin Hq_idx)).
    pose proof (vreg_nid_inj act a_idx q_idx n_idx Halign Hqv) as ->.
    destruct fuel as [| f]; [ lia |].
    cbn [compile_dfg_expr_aux]. rewrite Hq, Hq_idx. cbv beta iota.
    unfold is_sample_of, node_op in Hsam.
    destruct (op (nth (vreg_nid a_idx n_idx) (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}));
      try discriminate Hsam.
    reflexivity.
  Qed.

  (* Every sample has a SLOT, so it is named by some [vreg_nid]. *)
  Lemma sample_index (act: tfs_action sched) a_idx n :
    act_idx_aligned act a_idx ->
    is_sample_of act n = true ->
    exists n_idx, vreg_nid a_idx n_idx = n.
  Proof.
    intros Halign Hsam.
    destruct (BitsToLists.list_assoc (sample_bufs act a_idx) n) as [[q qsz] |] eqn:Hq;
      [| exfalso; exact (sample_is_buffered act a_idx n Halign Hsam Hq) ].
    pose proof (wla_in _ _ _ Hq) as Hin.
    unfold sample_bufs in Hin. apply filter_In in Hin. destruct Hin as [Hin _].
    assert (Hlt : q < length
              (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])).
    { rewrite (buffer_slot_eq act a_idx Halign), gsi_length.
      apply (gsi_idx_bound (build_dfg ctx act) _ n q qsz).
      rewrite <- (buffer_slot_eq act a_idx Halign). exact Hin. }
    destruct (index_of_nat_bounded Hlt) as [q_idx Hq_idx].
    exists q_idx.
    exact (vreg_nid_of_entry act a_idx n q qsz q_idx Halign Hin Hq_idx).
  Qed.

  (* ==================================================================== *)

  Definition valid_settled
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (ss: sched_sys_state) (input: sched_input_t) : Prop :=
    forall n_idx,
      (* A2 debt 2: a stall's register holds its COUNTER, and no compiled
         expression reads it as a value, so settledness says nothing there. *)
      stall_lat_of act (vreg_nid a_idx n_idx) = None ->
      (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
      (fst ss).[tf_dfg_b a_idx n_idx]
      = eval_st (tf_dfg_b a_idx n_idx)
          (node_ref_expr act a_idx (vreg_nid a_idx n_idx)) ss input.

  (* The third conjunct: the assignment that refreshes a set bit is itself up.
     Uniform over stalls and plain buffers, which is what makes monotonicity a
     one-liner rather than an argument about earlier cycles. *)
  Definition valid_gates
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (ss: sched_sys_state) (input: sched_input_t) : Prop :=
    forall n_idx,
      (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
      eval_st (tf_dfg_v a_idx n_idx) (buf_valid_next act a_idx n_idx) ss input
      = Bits.ones 1.

  (* SUBSTITUTION, gated by VALIDITY: wherever a node's compiled validity fires,
     its value agrees with the buffer-free one.  An untainted Phi validates
     exactly the branch [tf_expr_if] selects, so it reads no unsettled one. *)
  Lemma compile_subst_valid_gen
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
        (ss: sched_sys_state) (input: sched_input_t) :
    act_idx_aligned act a_idx ->
    valid_settled act a_idx ss input ->
    forall bufs,
      (forall e, In e bufs ->
         In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
      (* the reference keeps the SAMPLE buffers, so [bufs] must keep them too:
         a sample read through a buffer on one side and off the wire on the
         other would compare a latched answer against the live port *)
      (forall x, BitsToLists.list_assoc bufs x = None ->
                 BitsToLists.list_assoc (sample_bufs act a_idx) x = None) ->
      (forall x m msz, BitsToLists.list_assoc bufs x = Some (m, msz) ->
                 is_sample_of act x = true ->
                 BitsToLists.list_assoc (sample_bufs act a_idx) x = Some (m, msz)) ->
      forall fuel n szB (pi: list lit),
        1 <= n ->
        n < length (graph (build_dfg ctx act)) ->
        n < fuel ->
        szB = sz (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}) ->
        eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                      n bufs)) ss input = Bits.ones 1 ->
        tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
          (fst (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act) n bufs))
          ss input
        = tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
          (fst (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act) n (sample_bufs act a_idx)))
          ss input.
  Proof.
    intros Halign Hinv bufs Hsub Hsam_sub Hsam_same fuel.
    induction fuel as [| fuel IH];
      intros n szB pi Hn1 Hnlen Hnfuel HszB Hval; [ lia | ].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:Hla.
    - (* buffered leaf: its validity bit is the one that fired *)
      rewrite (compile_fuel_irrel_gen act a_idx (sample_bufs act a_idx) _ _ n Hn1 Hnlen (S fuel)
                 (length (graph (build_dfg ctx act))) pi Hnfuel Hnlen).
      cbn [compile_dfg_expr_aux] in Hval |- *. rewrite Hla in Hval |- *.
      cbv beta iota in Hval |- *.
      assert (Hin_slot : In (n, (m, msz))
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))
        by (apply Hsub, wla_in, Hla).
      assert (Hin_gsi : In (n, (m, msz))
                (get_sizes_and_idx ctx (build_dfg ctx act)
                   (require_buffer ctx (build_dfg ctx act)
                      (calc_target_cycle cost_limit
                         (calc_backward_cost ctx cost_limit (build_dfg ctx act))))))
        by (rewrite <- (buffer_slot_eq act a_idx Halign); exact Hin_slot).
      assert (Hlt : m < length
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])).
      { rewrite (buffer_slot_eq act a_idx Halign), gsi_length.
        exact (gsi_idx_bound _ _ n m msz Hin_gsi). }
      destruct (index_of_nat_bounded Hlt) as [n_idx' Hn_idx'].
      rewrite Hn_idx' in Hval |- *. cbv beta iota in Hval |- *.
      (* Both arms of the buffered branch publish the SAME validity register;
         only the value differs, and a stall's is [tf_const 0]. *)
      destruct (op (nth n (graph (build_dfg ctx act))
                      {| nid := 0; op := DFG_Empty; sz := 0 |})) eqn:Hopn;
        cbn [fst] in *; cbn [snd] in Hval.
      all: try (assert (Hmi : index_to_nat n_idx' = m)
                  by (apply index_to_nat_of_nat; exact Hn_idx');
                assert (Hvn : vreg_nid a_idx n_idx' = n) by
                  (unfold vreg_nid; rewrite Hmi, (buffer_slot_eq act a_idx Halign);
                   rewrite (gsi_entry_at _ _ n m msz Hin_gsi); reflexivity);
                assert (Hsz : ss_sz (tf_dfg_b a_idx n_idx') = szB) by
                  (rewrite (buffer_register_node_size act a_idx n_idx' Halign), Hvn;
                   symmetry; exact HszB);
                rewrite eval1_svar_v in Hval;
                assert (Hns : stall_lat_of act (vreg_nid a_idx n_idx') = None) by
                  (unfold stall_lat_of, node_op; rewrite Hvn, Hopn; reflexivity);
                assert (Hset := Hinv n_idx' Hns Hval);
                rewrite <- Hsz, eval_svar_same, Hset, Hvn;
                unfold node_ref_expr;
                rewrite (compile_fst_pi_irrel _ _ a_idx (build_dfg ctx act)
                           (sample_bufs act a_idx)
                           (length (graph (build_dfg ctx act))) n [] pi);
                reflexivity).
      (* the stall: neither side reads the register *)
      rewrite (compile_stall_value (build_dfg ctx act) _ _ a_idx n lat arg Hopn
                 (length (graph (build_dfg ctx act))) pi (sample_bufs act a_idx)
                 ltac:(lia)).
      reflexivity.
    - (* not buffered: split the validity along the op's structure *)
      cbn [compile_dfg_expr_aux BitsToLists.list_assoc] in Hval |- *.
      rewrite Hla in Hval |- *. rewrite (Hsam_sub n Hla).
      cbv beta iota in Hval |- *.
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
      assert (Hchild : forall x sx (p: list lit), In x (get_args ctx node) ->
                wsz (build_dfg ctx act) x sx ->
                eval1 (snd (compile_dfg_expr_at ctx bneeds p fuel a_idx
                              (build_dfg ctx act) x bufs)) ss input = Bits.ones 1 ->
                tf_eval_expr ss_sz si_sz oo_sz (szB := sx)
                  (fst (compile_dfg_expr_at ctx bneeds p fuel a_idx
                          (build_dfg ctx act) x bufs)) ss input
                = tf_eval_expr ss_sz si_sz oo_sz (szB := sx)
                  (fst (compile_dfg_expr_at ctx bneeds p fuel a_idx
                          (build_dfg ctx act) x (sample_bufs act a_idx))) ss input).
      { intros x sx p Hx Hwsz Hxv.
        destruct (Harg x Hx) as [Hx1 Hx2].
        destruct (wsz_node_sz act x sx Hwsz) as [Hxlen Hxsz].
        apply (IH x sx p Hx1 Hxlen ltac:(lia) (eq_sym Hxsz) Hxv). }
      pose proof (wfg_build_dfg act node Hnode_in) as Hfg.
      destruct (op node) as [c | v | v | op1 arg | op1 arg1 arg2 | arg | cnd tid eid | slat sa | dov dn den | siv sn sen | ja jb | ]
        eqn:Hop.
      + (* Const *) reflexivity.
      + (* Input *) reflexivity.
      + (* Var *) destruct v; reflexivity.
      + (* Unary: validity passes through *)
        assert (Hain : In arg (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    arg bufs) as [ae ve] eqn:E1.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    arg (sample_bufs act a_idx)) as [ae' ve'] eqn:E2.
        cbn [fst]. cbn [snd] in Hval.
        unfold node_args_sz in Hfg. rewrite Hop in Hfg.
        assert (Hav : eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                                    (build_dfg ctx act) arg bufs)) ss input
                      = Bits.ones 1) by (rewrite E1; cbn [snd]; exact Hval).
        destruct op1 as [| src].
        * pose proof (Hchild arg (sz node) pi Hain Hfg Hav) as Hc.
          rewrite E1, E2 in Hc. cbn [fst] in Hc.
          cbn [tf_eval_expr]. rewrite Hc. reflexivity.
        * pose proof (Hchild arg src pi Hain Hfg Hav) as Hc.
          rewrite E1, E2 in Hc. cbn [fst] in Hc.
          cbn [tf_eval_expr]. rewrite Hc. reflexivity.
      + (* Binary: validity is the AND of the two children's *)
        assert (Ha1in : In arg1 (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        assert (Ha2in : In arg2 (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; left; reflexivity).
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    arg1 bufs) as [a1e v1e] eqn:E1.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    arg2 bufs) as [a2e v2e] eqn:E2.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    arg1 (sample_bufs act a_idx)) as [a1e' v1e'] eqn:E3.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    arg2 (sample_bufs act a_idx)) as [a2e' v2e'] eqn:E4.
        cbn [fst]. cbn [snd] in Hval.
        rewrite valid_and_eval in Hval.
        destruct (bits1_and_split _ _ Hval) as [Hv1 Hv2].
        assert (Hav1 : eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                                     (build_dfg ctx act) arg1 bufs)) ss input
                       = Bits.ones 1) by (rewrite E1; cbn [snd]; exact Hv1).
        assert (Hav2 : eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                                     (build_dfg ctx act) arg2 bufs)) ss input
                       = Bits.ones 1) by (rewrite E2; cbn [snd]; exact Hv2).
        unfold node_args_sz in Hfg. rewrite Hop in Hfg.
        destruct op1 as [ | | | | | | szC cop | hz lz ];
          [ destruct Hfg as [Hf1 Hf2];
            pose proof (Hchild arg1 (sz node) pi Ha1in Hf1 Hav1) as Hc1;
            pose proof (Hchild arg2 (sz node) pi Ha2in Hf2 Hav2) as Hc2;
            rewrite E1, E3 in Hc1; rewrite E2, E4 in Hc2;
            cbn [fst] in Hc1, Hc2;
            cbn [tf_eval_expr]; rewrite Hc1, Hc2; reflexivity .. | | ].
        destruct Hfg as [Hf1 Hf2].
        pose proof (Hchild arg1 szC pi Ha1in Hf1 Hav1) as Hc1.
        pose proof (Hchild arg2 szC pi Ha2in Hf2 Hav2) as Hc2.
        rewrite E1, E3 in Hc1. rewrite E2, E4 in Hc2.
        cbn [fst] in Hc1, Hc2.
        cbn [tf_eval_expr]. rewrite Hc1, Hc2. reflexivity.
        (* tf_concat *)
        destruct Hfg as [Hf1 Hf2].
        pose proof (Hchild arg1 hz pi Ha1in Hf1 Hav1) as Hk1.
        pose proof (Hchild arg2 lz pi Ha2in Hf2 Hav2) as Hk2.
        rewrite E1, E3 in Hk1. rewrite E2, E4 in Hk2.
        cbn [fst] in Hk1, Hk2.
        cbn [tf_eval_expr]. rewrite Hk1, Hk2. reflexivity.
      + (* Resize: validity passes through *)
        assert (Hain : In arg (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    arg bufs) as [ae ve] eqn:E1.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    arg (sample_bufs act a_idx)) as [ae' ve'] eqn:E2.
        cbn [fst]. cbn [snd] in Hval.
        destruct (Harg arg Hain) as [Hx1 Hx2].
        assert (Hav : eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                                    (build_dfg ctx act) arg bufs)) ss input
                      = Bits.ones 1) by (rewrite E1; cbn [snd]; exact Hval).
        pose proof (IH arg (sz (nth arg (graph (build_dfg ctx act))
                                  {| nid := 0; op := DFG_Empty; sz := 0 |})) pi
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
        (* the branch paths only matter to [Hchild], which is path-polymorphic *)
        remember (ppath_at act pi cnd true) as pt eqn:Hpt. clear Hpt.
        remember (ppath_at act pi cnd false) as pe eqn:Hpe. clear Hpe.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    cnd bufs) as [ce cv] eqn:Ec.
        destruct (compile_dfg_expr_at ctx bneeds pt fuel a_idx
                    (build_dfg ctx act) tid bufs) as [te tv] eqn:Et.
        destruct (compile_dfg_expr_at ctx bneeds pe fuel a_idx
                    (build_dfg ctx act) eid bufs) as [ee ev] eqn:Ee.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    cnd (sample_bufs act a_idx)) as [ce' cv'] eqn:Ec'.
        destruct (compile_dfg_expr_at ctx bneeds pt fuel a_idx
                    (build_dfg ctx act) tid (sample_bufs act a_idx)) as [te' tv'] eqn:Et'.
        destruct (compile_dfg_expr_at ctx bneeds pe fuel a_idx
                    (build_dfg ctx act) eid (sample_bufs act a_idx)) as [ee' ev'] eqn:Ee'.
        cbn [fst]. cbn [snd] in Hval.
        unfold node_args_sz in Hfg. rewrite Hop in Hfg.
        destruct Hfg as [Hf1 [Hf2 Hf3]].
        (* criticality is decided per OCCURRENCE, from [cnd] and the path [pi] *)
        match type of Hval with context [if ?B then _ else _] => destruct B end.
        * (* critical: all three children are valid *)
          rewrite valid_and_eval, valid_and_eval in Hval.
          destruct (bits1_and_split _ _ Hval) as [Hte Hcv].
          destruct (bits1_and_split _ _ Hte) as [Htv Hev].
          assert (Hac : eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                                      (build_dfg ctx act) cnd bufs)) ss input
                        = Bits.ones 1) by (rewrite Ec; cbn [snd]; exact Hcv).
          assert (Hat : eval1 (snd (compile_dfg_expr_at ctx bneeds pt
                                      fuel a_idx (build_dfg ctx act) tid bufs)) ss input
                        = Bits.ones 1) by (rewrite Et; cbn [snd]; exact Htv).
          assert (Hae : eval1 (snd (compile_dfg_expr_at ctx bneeds pe
                                      fuel a_idx (build_dfg ctx act) eid bufs)) ss input
                        = Bits.ones 1) by (rewrite Ee; cbn [snd]; exact Hev).
          pose proof (Hchild cnd 1 pi Hcin Hf1 Hac) as Hcc.
          pose proof (Hchild tid (sz node) pt Htin Hf2 Hat) as Hct.
          pose proof (Hchild eid (sz node) pe Hein Hf3 Hae) as Hce.
          rewrite Ec, Ec' in Hcc. rewrite Et, Et' in Hct. rewrite Ee, Ee' in Hce.
          cbn [fst] in Hcc, Hct, Hce.
          cbn [tf_eval_expr]. rewrite Hcc, Hct, Hce. reflexivity.
        * (* non-critical: only the selected branch is known valid *)
          rewrite valid_and_eval in Hval.
          destruct (bits1_and_split _ _ Hval) as [Hcv Hif].
          assert (Hac : eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                                      (build_dfg ctx act) cnd bufs)) ss input
                        = Bits.ones 1) by (rewrite Ec; cbn [snd]; exact Hcv).
          pose proof (Hchild cnd 1 pi Hcin Hf1 Hac) as Hcc.
          rewrite Ec, Ec' in Hcc. cbn [fst] in Hcc.
          destruct (valid_if_eval_inv ce tv ev ss input Hif) as [Hthen Helse].
          cbn [tf_eval_expr]. rewrite Hcc.
          destruct (beq_dec (eval1 ce' ss input) Bits.zero) eqn:Hb.
          -- apply beq_dec_iff in Hb.
             assert (Hcz : eval1 ce ss input = Bits.zero) by (rewrite Hcc; exact Hb).
             assert (Hae : eval1 (snd (compile_dfg_expr_at ctx bneeds pe
                                         fuel a_idx (build_dfg ctx act) eid bufs)) ss input
                           = Bits.ones 1)
               by (rewrite Ee; cbn [snd]; exact (Helse Hcz)).
             pose proof (Hchild eid (sz node) pe Hein Hf3 Hae) as Hce.
             rewrite Ee, Ee' in Hce. cbn [fst] in Hce. exact Hce.
          -- assert (Hcnz : eval1 ce ss input <> Bits.zero).
             { rewrite Hcc. intro Hz. rewrite Hz, beq_dec_refl in Hb. discriminate. }
             assert (Hat : eval1 (snd (compile_dfg_expr_at ctx bneeds pt
                                         fuel a_idx (build_dfg ctx act) tid bufs)) ss input
                           = Bits.ones 1)
               by (rewrite Et; cbn [snd]; exact (Hthen Hcnz)).
             pose proof (Hchild tid (sz node) pt Htin Hf2 Hat) as Hct.
             rewrite Et, Et' in Hct. cbn [fst] in Hct. exact Hct.
      + (* DFG_Stall: carries no value, so both sides are [tf_const 0]. *)
        cbn [fst].
        repeat match goal with
        | |- context [compile_dfg_expr_aux ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j] =>
            destruct (compile_dfg_expr_aux a b c d e f g h i j)
        end.
        reflexivity.
      + (* DFG_Drive: value and validity both pass through. *)
        assert (Hain : In dn (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        unfold node_args_sz in Hfg. rewrite Hop in Hfg.
        exact (Hchild dn (sz node) pi Hain Hfg Hval).
      + (* DFG_Sample: only the validity passes through, the value [tf_ivar v]
           being the same with and without buffers.  The round trip's
           value/validity decoupling, discharged here. *)
        cbn [fst].
        repeat match goal with
        | |- context [compile_dfg_expr_aux ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j] =>
            destruct (compile_dfg_expr_aux a b c d e f g h i j)
        end.
        reflexivity.
      + (* DFG_Join: no value either. *)
        cbn [fst].
        repeat match goal with
        | |- context [compile_dfg_expr_aux ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j] =>
            destruct (compile_dfg_expr_aux a b c d e f g h i j)
        end.
        reflexivity.
      + (* Empty: impossible for a real node *)
        exfalso. apply (node_op_not_empty act n Hn1 Hnlen).
        unfold node in Hop. exact Hop.
  Qed.

  Lemma compile_subst_valid
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
        (ss: sched_sys_state) (input: sched_input_t) :
    act_idx_aligned act a_idx ->
    valid_settled act a_idx ss input ->
    forall bufs,
      (forall e, In e bufs ->
         In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
      (* the reference keeps the SAMPLE buffers, so [bufs] must keep them too:
         a sample read through a buffer on one side and off the wire on the
         other would compare a latched answer against the live port *)
      (forall x, BitsToLists.list_assoc bufs x = None ->
                 BitsToLists.list_assoc (sample_bufs act a_idx) x = None) ->
      (forall x m msz, BitsToLists.list_assoc bufs x = Some (m, msz) ->
                 is_sample_of act x = true ->
                 BitsToLists.list_assoc (sample_bufs act a_idx) x = Some (m, msz)) ->
      forall fuel n szB,
        1 <= n ->
        n < length (graph (build_dfg ctx act)) ->
        n < fuel ->
        szB = sz (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}) ->
        eval1 (snd (compile_dfg_expr ctx bneeds fuel a_idx (build_dfg ctx act)
                      n bufs)) ss input = Bits.ones 1 ->
        tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
          (fst (compile_dfg_expr ctx bneeds fuel a_idx (build_dfg ctx act) n bufs))
          ss input
        = tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
          (fst (compile_dfg_expr ctx bneeds fuel a_idx (build_dfg ctx act) n (sample_bufs act a_idx)))
          ss input.
  Proof.
    intros Halign Hinv bufs Hsub Hsam_sub Hsam_same fuel n szB.
    exact (compile_subst_valid_gen act a_idx ss input Halign Hinv bufs Hsub
             Hsam_sub Hsam_same fuel n szB []).
  Qed.

  (* A valid buffer's REFERENCE is itself valid -- every sample the reference
     reads has already latched.  Quantified over [pi], since only the VALUE of
     a node is path-independent (there is no [snd] twin of
     [compile_fst_pi_irrel]: [phi_crit] reads the path). *)
  Definition valid_refs
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (ss: sched_sys_state) (input: sched_input_t) : Prop :=
    forall n_idx (pi: list lit),
      (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
      eval1 (snd (compile_dfg_expr_at ctx bneeds pi
                    (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act)
                    (vreg_nid a_idx n_idx) (sample_bufs act a_idx))) ss input
      = Bits.ones 1.

  (* VALIDITY substitution: a validity that fires over [bufs] fires over the
     reference's table too.  The untainted-Phi case is where this needs
     [valid_settled]: the two tables give two different CONDITION expressions,
     and the branch that is known valid is the one the condition selects. *)
  Lemma compile_subst_ref_valid_gen
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
        (ss: sched_sys_state) (input: sched_input_t) :
    act_idx_aligned act a_idx ->
    valid_settled act a_idx ss input ->
    valid_refs act a_idx ss input ->
    forall bufs,
      (forall e, In e bufs ->
         In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
      (forall x, BitsToLists.list_assoc bufs x = None ->
                 BitsToLists.list_assoc (sample_bufs act a_idx) x = None) ->
      (forall x m msz, BitsToLists.list_assoc bufs x = Some (m, msz) ->
                 is_sample_of act x = true ->
                 BitsToLists.list_assoc (sample_bufs act a_idx) x = Some (m, msz)) ->
      forall fuel n (pi: list lit),
        1 <= n ->
        n < length (graph (build_dfg ctx act)) ->
        n < fuel ->
        eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                      n bufs)) ss input = Bits.ones 1 ->
        eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                      n (sample_bufs act a_idx))) ss input = Bits.ones 1.
  Proof.
    intros Halign Hinv Hrefs bufs Hsub Hsam_sub Hsam_same fuel.
    induction fuel as [| fuel IH]; intros n pi Hn1 Hnlen Hnfuel Hval; [ lia |].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:Hla.
    - (* buffered leaf: its validity bit is the one that fired *)
      cbn [compile_dfg_expr_aux] in Hval. rewrite Hla in Hval.
      cbv beta iota in Hval.
      assert (Hin_slot : In (n, (m, msz))
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))
        by (apply Hsub, wla_in, Hla).
      assert (Hin_gsi : In (n, (m, msz))
                (get_sizes_and_idx ctx (build_dfg ctx act)
                   (require_buffer ctx (build_dfg ctx act)
                      (calc_target_cycle cost_limit
                         (calc_backward_cost ctx cost_limit (build_dfg ctx act))))))
        by (rewrite <- (buffer_slot_eq act a_idx Halign); exact Hin_slot).
      assert (Hlt : m < length
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])).
      { rewrite (buffer_slot_eq act a_idx Halign), gsi_length.
        exact (gsi_idx_bound _ _ n m msz Hin_gsi). }
      destruct (index_of_nat_bounded Hlt) as [n_idx' Hn_idx'].
      rewrite Hn_idx' in Hval. cbv beta iota in Hval.
      assert (Hmi : index_to_nat n_idx' = m)
        by (apply index_to_nat_of_nat; exact Hn_idx').
      assert (Hvn : vreg_nid a_idx n_idx' = n)
        by (unfold vreg_nid; rewrite Hmi, (buffer_slot_eq act a_idx Halign);
            rewrite (gsi_entry_at _ _ n m msz Hin_gsi); reflexivity).
      (* both arms of the buffered branch publish the SAME validity register *)
      assert (Hv' : (fst ss).[tf_dfg_v a_idx n_idx'] = Bits.ones 1).
      { destruct (op (nth n (graph (build_dfg ctx act))
                        {| nid := 0; op := DFG_Empty; sz := 0 |}));
          cbn [snd] in Hval; rewrite eval1_svar_v in Hval; exact Hval. }
      rewrite (compile_fuel_irrel_gen act a_idx (sample_bufs act a_idx) _ _ n Hn1 Hnlen
                 (S fuel) (length (graph (build_dfg ctx act))) pi Hnfuel Hnlen).
      rewrite <- Hvn. exact (Hrefs n_idx' pi Hv').
    - (* not buffered: split the validity along the op's structure *)
      cbn [compile_dfg_expr_aux BitsToLists.list_assoc] in Hval |- *.
      rewrite Hla in Hval. rewrite (Hsam_sub n Hla).
      cbv beta iota in Hval |- *.
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
      assert (Hchild : forall x (p: list lit), In x (get_args ctx node) ->
                eval1 (snd (compile_dfg_expr_at ctx bneeds p fuel a_idx
                              (build_dfg ctx act) x bufs)) ss input = Bits.ones 1 ->
                eval1 (snd (compile_dfg_expr_at ctx bneeds p fuel a_idx
                              (build_dfg ctx act) x (sample_bufs act a_idx))) ss input
                = Bits.ones 1).
      { intros x p Hx Hxv.
        destruct (Harg x Hx) as [Hx1 Hx2].
        apply (IH x p Hx1 (Nat.lt_trans _ _ _ Hx2 Hnlen) ltac:(lia) Hxv). }
      pose proof (wfg_build_dfg act node Hnode_in) as Hfg.
      destruct (op node) as [c | v | v | op1 arg | op1 arg1 arg2 | arg | cnd tid eid | slat sa | dov dn den | siv sn sen | ja jb | ]
        eqn:Hop.
      + (* Const *) apply eval1_const1.
      + (* Input *) apply eval1_const1.
      + (* Var *) destruct v; apply eval1_const1.
      + (* Unary: validity passes through *)
        assert (Hain : In arg (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    arg bufs) as [ae ve] eqn:E1.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    arg (sample_bufs act a_idx)) as [ae' ve'] eqn:E2.
        cbn [snd] in Hval |- *.
        pose proof (Hchild arg pi Hain ltac:(rewrite E1; cbn [snd]; exact Hval)) as Hc.
        rewrite E2 in Hc. cbn [snd] in Hc. exact Hc.
      + (* Binary: validity is the AND of the two children's *)
        assert (Ha1in : In arg1 (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        assert (Ha2in : In arg2 (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; left; reflexivity).
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    arg1 bufs) as [a1e v1e] eqn:E1.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    arg2 bufs) as [a2e v2e] eqn:E2.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    arg1 (sample_bufs act a_idx)) as [a1e' v1e'] eqn:E3.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    arg2 (sample_bufs act a_idx)) as [a2e' v2e'] eqn:E4.
        cbn [snd] in Hval |- *.
        rewrite valid_and_eval in Hval.
        destruct (bits1_and_split _ _ Hval) as [Hv1 Hv2].
        pose proof (Hchild arg1 pi Ha1in ltac:(rewrite E1; cbn [snd]; exact Hv1)) as Hc1.
        pose proof (Hchild arg2 pi Ha2in ltac:(rewrite E2; cbn [snd]; exact Hv2)) as Hc2.
        rewrite E3 in Hc1. rewrite E4 in Hc2. cbn [snd] in Hc1, Hc2.
        rewrite valid_and_eval, Hc1, Hc2. vm_compute. reflexivity.
      + (* Resize: validity passes through *)
        assert (Hain : In arg (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    arg bufs) as [ae ve] eqn:E1.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    arg (sample_bufs act a_idx)) as [ae' ve'] eqn:E2.
        cbn [snd] in Hval |- *.
        pose proof (Hchild arg pi Hain ltac:(rewrite E1; cbn [snd]; exact Hval)) as Hc.
        rewrite E2 in Hc. cbn [snd] in Hc. exact Hc.
      + (* Phi: the selected branch, and the two tables must SELECT alike *)
        assert (Hcin : In cnd (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        assert (Htin : In tid (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; left; reflexivity).
        assert (Hein : In eid (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; right; left; reflexivity).
        unfold node_args_sz in Hfg. rewrite Hop in Hfg.
        destruct Hfg as [Hf1 [Hf2 Hf3]].
        (* the condition agrees in VALUE across the two tables *)
        destruct (Harg cnd Hcin) as [Hc1 Hc2].
        destruct (wsz_node_sz act cnd 1 Hf1) as [Hclen Hcsz].
        pose proof (compile_subst_valid_gen act a_idx ss input Halign Hinv bufs Hsub
                      Hsam_sub Hsam_same fuel cnd 1 pi Hc1 Hclen ltac:(lia)
                      (eq_sym Hcsz)) as Hcondval.
        remember (ppath_at act pi cnd true) as pt eqn:Hpt. clear Hpt.
        remember (ppath_at act pi cnd false) as pe eqn:Hpe. clear Hpe.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    cnd bufs) as [ce cv] eqn:Ec.
        destruct (compile_dfg_expr_at ctx bneeds pt fuel a_idx
                    (build_dfg ctx act) tid bufs) as [te tv] eqn:Et.
        destruct (compile_dfg_expr_at ctx bneeds pe fuel a_idx
                    (build_dfg ctx act) eid bufs) as [ee ev] eqn:Ee.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    cnd (sample_bufs act a_idx)) as [ce' cv'] eqn:Ec'.
        destruct (compile_dfg_expr_at ctx bneeds pt fuel a_idx
                    (build_dfg ctx act) tid (sample_bufs act a_idx)) as [te' tv'] eqn:Et'.
        destruct (compile_dfg_expr_at ctx bneeds pe fuel a_idx
                    (build_dfg ctx act) eid (sample_bufs act a_idx)) as [ee' ev'] eqn:Ee'.
        cbn [snd] in Hval |- *. cbn [fst] in Hcondval.
        match type of Hval with context [if ?B then _ else _] => destruct B end.
        * (* critical: all three children are valid *)
          rewrite valid_and_eval, valid_and_eval in Hval.
          destruct (bits1_and_split _ _ Hval) as [Hte Hcv].
          destruct (bits1_and_split _ _ Hte) as [Htv Hev].
          pose proof (Hchild cnd pi Hcin ltac:(rewrite Ec; cbn [snd]; exact Hcv)) as Hac.
          pose proof (Hchild tid pt Htin ltac:(rewrite Et; cbn [snd]; exact Htv)) as Hat.
          pose proof (Hchild eid pe Hein ltac:(rewrite Ee; cbn [snd]; exact Hev)) as Hae.
          rewrite Ec' in Hac. rewrite Et' in Hat. rewrite Ee' in Hae.
          cbn [snd] in Hac, Hat, Hae.
          rewrite valid_and_eval, valid_and_eval, Hac, Hat, Hae.
          vm_compute. reflexivity.
        * (* non-critical: only the branch the condition selects *)
          rewrite valid_and_eval in Hval.
          destruct (bits1_and_split _ _ Hval) as [Hcv Hif].
          pose proof (Hchild cnd pi Hcin ltac:(rewrite Ec; cbn [snd]; exact Hcv)) as Hac.
          rewrite Ec' in Hac. cbn [snd] in Hac.
          destruct (valid_if_eval_inv ce tv ev ss input Hif) as [Hthen Helse].
          specialize (Hcondval ltac:(cbn [snd]; exact Hcv)).
          cbn [fst] in Hcondval.
          rewrite valid_and_eval, Hac.
          rewrite (valid_if_eval_sel ce' tv' ev' ss input).
          -- vm_compute. reflexivity.
          -- intro Hnz.
             pose proof (Hchild tid pt Htin
               ltac:(rewrite Et; cbn [snd]; apply Hthen;
                     rewrite Hcondval; exact Hnz)) as Hct.
             rewrite Et' in Hct. cbn [snd] in Hct. exact Hct.
          -- intro Hz.
             pose proof (Hchild eid pe Hein
               ltac:(rewrite Ee; cbn [snd]; apply Helse;
                     rewrite Hcondval; exact Hz)) as Hce.
             rewrite Ee' in Hce. cbn [snd] in Hce. exact Hce.
      + (* DFG_Stall: the validity is the argument's *)
        assert (Hain : In sa (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    sa bufs) as [ae ve] eqn:E1.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    sa (sample_bufs act a_idx)) as [ae' ve'] eqn:E2.
        cbn [snd] in Hval |- *.
        pose proof (Hchild sa pi Hain ltac:(rewrite E1; cbn [snd]; exact Hval)) as Hc.
        rewrite E2 in Hc. cbn [snd] in Hc. exact Hc.
      + (* DFG_Drive: value and validity both pass through *)
        assert (Hain : In dn (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        exact (Hchild dn pi Hain Hval).
      + (* DFG_Sample: the validity is the token's *)
        assert (Hain : In sn (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    sn bufs) as [ae ve] eqn:E1.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    sn (sample_bufs act a_idx)) as [ae' ve'] eqn:E2.
        cbn [snd] in Hval |- *.
        pose proof (Hchild sn pi Hain ltac:(rewrite E1; cbn [snd]; exact Hval)) as Hc.
        rewrite E2 in Hc. cbn [snd] in Hc. exact Hc.
      + (* DFG_Join: the AND of the two *)
        assert (Ha1in : In ja (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        assert (Ha2in : In jb (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; left; reflexivity).
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    ja bufs) as [a1e v1e] eqn:E1.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    jb bufs) as [a2e v2e] eqn:E2.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    ja (sample_bufs act a_idx)) as [a1e' v1e'] eqn:E3.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    jb (sample_bufs act a_idx)) as [a2e' v2e'] eqn:E4.
        cbn [snd] in Hval |- *.
        rewrite valid_and_eval in Hval.
        destruct (bits1_and_split _ _ Hval) as [Hv1 Hv2].
        pose proof (Hchild ja pi Ha1in ltac:(rewrite E1; cbn [snd]; exact Hv1)) as Hc1.
        pose proof (Hchild jb pi Ha2in ltac:(rewrite E2; cbn [snd]; exact Hv2)) as Hc2.
        rewrite E3 in Hc1. rewrite E4 in Hc2. cbn [snd] in Hc1, Hc2.
        rewrite valid_and_eval, Hc1, Hc2. vm_compute. reflexivity.
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

  (* SETTLE BOUND.  Buffers rank by NODE ID (args_lt_fwd), so a buffer caching
     node [n] settles by cycle [n] and the run is bounded by the graph size.
     The target cycle is NOT a rank: two buffers can share one. *)
  Definition settle_bound (act: tfs_action sched) : nat :=
    node_rank act (length (graph (build_dfg ctx act))).

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
                (calc_target_cycle cost_limit (calc_backward_cost ctx cost_limit (build_dfg ctx act))) n)
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

  (* GATEWAY: the compiled done signal is [tf_dfg_done] assigned the combined
     validity over EXACTLY the per-output validity exprs, at the aligned
     action's DFG, full fuel and require_buffer slot list. *)
  Lemma done_exprs_concrete (act: tfs_action sched) a_idx :
    act_idx_aligned act a_idx ->
    exists rest,
      fst (Contract.tfs_schedule sched act)
      = tf_assign (tfs_done_signal sched)
          (combine_valid_exprs ctx bneeds
             (map (fun nid =>
                     snd (compile_dfg_expr ctx bneeds
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
    unfold sched, tfs_schedule, tfs_schedule_bn, Contract.tfs_schedule, tfs_done_signal, done_signal.
    unfold schedule. cbv zeta. cbn [fst].
    unfold compile_dfg_valid. cbv zeta.
    rewrite Halign2.
    rewrite index_of_nat_to_nat.
    rewrite Hnth_dfg.
    eexists. reflexivity.
  Qed.

  (* Structural exposure of the buffer-write tail of the always-ops list: after
     the done-flag head come the buffer writes, and after THOSE the drive
     writes -- one register per IP, live in every action's always half. *)
  Lemma buffer_ops_concrete (act: tfs_action sched) a_idx :
    act_idx_aligned act a_idx ->
    exists done_e,
      fst (Contract.tfs_schedule sched act)
      = done_e ::
        compile_dfg_buffers ctx bneeds (index_to_nat a_idx) (build_dfg ctx act)
          (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])
        ++ compile_dfg_drives ctx bneeds (index_to_nat a_idx) (build_dfg ctx act)
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
    unfold sched, tfs_schedule, tfs_schedule_bn, Contract.tfs_schedule.
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
        (ss: sched_sys_state) (input: sched_input_t) :
    act_idx_aligned act a_idx ->
    ~ done_set (sched_step act ss input) ->
    let buffers := nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [] in
    let entry := nth (index_to_nat n_idx) buffers (0, (0, 0)) in
    let n := fst entry in
    let buffers' := filter (fun '(b_nid, _) => negb (Nat.eqb b_nid n)) buffers in
    let compiled := compile_dfg_expr ctx bneeds
                      (length (graph (build_dfg ctx act))) a_idx
                      (build_dfg ctx act) n buffers' in
    let sz := snd (snd entry) in
    (fst (sched_step act ss input)).[tf_dfg_b a_idx n_idx]
      = eval_st (tf_dfg_b a_idx n_idx)
          (buf_value_expr act a_idx n_idx sz (fst compiled) (snd compiled) n) ss input
    /\
    (fst (sched_step act ss input)).[tf_dfg_v a_idx n_idx]
      = eval_st (tf_dfg_v a_idx n_idx)
          (buf_valid_expr act a_idx n_idx sz (snd compiled) n) ss input.
  Proof.
    intros Halign Hnd. cbv zeta.
    pose proof (compile_dfg_buffers_entry act a_idx n_idx Halign) as Hmem.
    cbv zeta in Hmem.
    match goal with
    | |- context [buf_valid_expr _ _ _ _ (snd ?compiled) _] =>
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
    assert (Hvalue_ops : In (tf_assign (tf_dfg_b a_idx n_idx)
                               (buf_value_expr act a_idx n_idx
                                  (snd (snd (nth (index_to_nat n_idx)
                                     (nth (index_to_nat a_idx) bneeds []) (0, (0, 0)))))
                                  expr valid (vreg_nid a_idx n_idx)))
              (fst (Contract.tfs_schedule sched act))).
    { rewrite Hops. right. apply in_or_app. left. exact Hvalue. }
    assert (Hvalid_ops : In (tf_assign (tf_dfg_v a_idx n_idx)
                               (buf_valid_expr act a_idx n_idx
                                  (snd (snd (nth (index_to_nat n_idx)
                                     (nth (index_to_nat a_idx) bneeds []) (0, (0, 0)))))
                                  valid (vreg_nid a_idx n_idx)))
              (fst (Contract.tfs_schedule sched act))).
    { rewrite Hops. right. apply in_or_app. left. exact Hvalid. }
    split; rewrite sched_step_getst, (cycle_updates_not_done act ss input Hnd);
      unfold find_st_val.
    - rewrite (find_st_update_unique_assign _ _ _ _ _ Hnd_always Hvalue_ops).
      reflexivity.
    - rewrite (find_st_update_unique_assign _ _ _ _ _ Hnd_always Hvalid_ops).
      reflexivity.
  Qed.

  (* On a pre-done cycle, port [p]'s request register reads exactly what
     [compile_dfg_drives] emits for it. *)
  Lemma drive_after_cycle
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit))) (p: p_var)
        (ss: sched_sys_state) (input: sched_input_t) :
    act_idx_aligned act a_idx ->
    ~ done_set (sched_step act ss input) ->
    (fst (sched_step act ss input)).[tf_dfg_ov p]
    = eval_st (tf_dfg_ov p) (drive_value_expr act a_idx p) ss input.
  Proof.
    intros Halign Hnd.
    destruct (buffer_ops_concrete act a_idx Halign) as [done_e Hops].
    assert (Hnd_always : tfs_ops_no_duplicates
              (fst (Contract.tfs_schedule sched act))).
    { pose proof (tfs_schedule_no_duplicates sched act) as Hnd_all.
      unfold tfs_ops_no_duplicates in *. rewrite flat_map_app in Hnd_all.
      apply (NoDup_app_l _ _ Hnd_all). }
    assert (Hin : In (tf_assign (tf_dfg_ov p) (drive_value_expr act a_idx p))
                     (fst (Contract.tfs_schedule sched act))).
    { rewrite Hops. right. apply in_or_app. right.
      exact (compile_dfg_drives_entry act a_idx p). }
    rewrite sched_step_getst, (cycle_updates_not_done act ss input Hnd).
    unfold find_st_val.
    rewrite (find_st_update_unique_assign _ _ _ _ _ Hnd_always Hin).
    reflexivity.
  Qed.

  (* THE PORT HOLDS: on a pre-done cycle with no drive on [p] pulsing, the
     request payload on the wire is the one it already carried. *)
  Lemma drive_payload_hold
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit))) (p: p_var)
        (ss: sched_sys_state) (input: sched_input_t) :
    act_idx_aligned act a_idx ->
    ~ done_set (sched_step act ss input) ->
    (forall n, In n (drive_nodes ctx (build_dfg ctx act) p) ->
       eval1 (drive_pulse act a_idx n) ss input = Bits.zero) ->
    drive_payload (sched_step act ss input) p = drive_payload ss p.
  Proof.
    intros Halign Hnd Hdown.
    rewrite (drive_payload_slice p (sched_step act ss input)).
    rewrite (drive_after_cycle act a_idx p ss input Halign Hnd).
    rewrite drive_value_expr_split. cbn [tf_eval_expr].
    rewrite slice_convert_eq by (cbn; lia).
    rewrite slice_app_lo.
    exact (drive_payload_expr_hold act a_idx p ss input Hdown).
  Qed.

  (* THE PORT TAKES: the latest pulsing drive on [p] puts its own argument on
     the wire.  [drive_nodes] is latest first, so [pre] is what came after it. *)
  Lemma drive_payload_take
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit))) (p: p_var)
        (pre post: list nid_t) (n: nid_t)
        (ss: sched_sys_state) (input: sched_input_t) :
    act_idx_aligned act a_idx ->
    ~ done_set (sched_step act ss input) ->
    drive_nodes ctx (build_dfg ctx act) p = pre ++ n :: post ->
    (forall m, In m pre -> eval1 (drive_pulse act a_idx m) ss input = Bits.zero) ->
    eval1 (drive_pulse act a_idx n) ss input <> Bits.zero ->
    drive_payload (sched_step act ss input) p
    = tf_eval_expr ss_sz si_sz oo_sz (szB := ip_req_sz (tfs_spec_ip ctx p))
        (fst (compile_dfg_expr ctx bneeds (length (graph (build_dfg ctx act))) a_idx
                (build_dfg ctx act) n
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))) ss input.
  Proof.
    intros Halign Hnd Hsplit Hpre Hn.
    rewrite (drive_payload_slice p (sched_step act ss input)).
    rewrite (drive_after_cycle act a_idx p ss input Halign Hnd).
    rewrite drive_value_expr_split. cbn [tf_eval_expr].
    rewrite slice_convert_eq by (cbn; lia).
    rewrite slice_app_lo.
    unfold drive_payload_expr. rewrite Hsplit.
    exact (eval_pulse_fold_take act a_idx _ _ pre post n _ ss input Hpre Hn).
  Qed.

  (* A sample's buffer holds once its validity bit reads ones: the latch arm is
     [if valid && !v then expr else b], and [!v] is zero. *)
  Lemma sample_buffer_frozen
        (act: tfs_action sched) a_idx n_idx (ss: sched_sys_state) (input: sched_input_t) :
    act_idx_aligned act a_idx ->
    ~ done_set (sched_step act ss input) ->
    is_sample_of act (vreg_nid a_idx n_idx) = true ->
    (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
    (fst ss).[tf_dfg_b a_idx n_idx]
    = (fst (sched_step act ss input)).[tf_dfg_b a_idx n_idx].
  Proof.
    intros Halign Hnd Hsam Hv.
    pose proof (buffer_after_cycle act a_idx n_idx ss input Halign Hnd) as Hba.
    cbv zeta in Hba. destruct Hba as [Hvalue _]. rewrite Hvalue.
    change (fst (nth (index_to_nat n_idx)
                   (nth (index_to_nat a_idx) bneeds []) (0, (0, 0))))
      with (vreg_nid a_idx n_idx).
    unfold buf_value_expr.
    destruct (stall_lat_of act (vreg_nid a_idx n_idx)) as [l |] eqn:Hst.
    { exfalso. unfold stall_lat_of, is_sample_of in Hst, Hsam.
      destruct (node_op act (vreg_nid a_idx n_idx)); discriminate. }
    rewrite Hsam. cbn [tf_eval_expr]. rewrite !convert_same.
    (* the validity bit comes FROM the goal, and then the guard reads zero *)
    match goal with
    | |- context [ Bits.neg ?x ] => replace x with (Bits.ones 1) by (symmetry; exact Hv)
    end.
    rewrite bits1_and_not_ones, beq_dec_refl. reflexivity.
  Qed.

  (* A validity bit that RISES says its gate fired on the cycle before: the
     stall arm ANDs the gate in, and every other arm IS the gate. *)
  Lemma buffer_valid_gate
        (act: tfs_action sched) a_idx n_idx (ss: sched_sys_state) (input: sched_input_t) :
    act_idx_aligned act a_idx ->
    ~ done_set (sched_step act ss input) ->
    (fst (sched_step act ss input)).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
    eval1 (buf_gate act a_idx n_idx) ss input = Bits.ones 1.
  Proof.
    intros Halign Hnd Hv.
    pose proof (buffer_after_cycle act a_idx n_idx ss input Halign Hnd) as Hba.
    cbv zeta in Hba. destruct Hba as [_ Hvalid].
    rewrite Hvalid in Hv.
    change (fst (nth (index_to_nat n_idx)
                   (nth (index_to_nat a_idx) bneeds []) (0, (0, 0))))
      with (vreg_nid a_idx n_idx) in Hv.
    unfold buf_valid_expr in Hv.
    destruct (stall_lat_of act (vreg_nid a_idx n_idx)) as [l |] eqn:Hst;
      [| exact Hv ].
    cbn [tf_eval_expr] in Hv.
    exact (proj1 (bits1_and_split _ _ Hv)).
  Qed.

  (* The downward twin, along the run: a validity bit that starts down and
     whose gate never rises stays down. *)
  Lemma valid_zero_run
        (act: tfs_action sched) a_idx n_idx (input: input_t)
        (ss0: sched_sys_state) (K: nat) :
    act_idx_aligned act a_idx ->
    (fst ss0).[tf_dfg_v a_idx n_idx] = Bits.zero ->
    (forall i, 1 <= i <= K -> ~ done_set (run_n i act input ss0)) ->
    (forall j, j < K ->
       eval1 (buf_gate act a_idx n_idx) (run_n j act input ss0)
         (sched_input input (run_n j act input ss0)) <> Bits.ones 1) ->
    forall k, k <= K ->
      (fst (run_n k act input ss0)).[tf_dfg_v a_idx n_idx] = Bits.zero.
  Proof.
    intros Halign Hz Hnd Hgate k HkK.
    destruct k as [| k]; [ cbn [run_n]; exact Hz |].
    change (run_n (S k) act input ss0)
      with (sched_step act (run_n k act input ss0)
              (sched_input input (run_n k act input ss0))).
    destruct (bits1_cases
                ((fst (sched_step act (run_n k act input ss0)
                         (sched_input input (run_n k act input ss0))))
                   .[tf_dfg_v a_idx n_idx])) as [Hones | Hzero]; [| exact Hzero ].
    exfalso. apply (Hgate k ltac:(lia)).
    exact (buffer_valid_gate act a_idx n_idx (run_n k act input ss0)
             (sched_input input (run_n k act input ss0)) Halign
             ltac:(apply (Hnd (S k)); lia) Hones).
  Qed.

  (* A bit that is up stays up: the register takes exactly the expression
     [valid_gates] says is up. *)
  Lemma validity_monotone_step
        (act: tfs_action sched) a_idx n_idx (ss: sched_sys_state) (input: sched_input_t) :
    act_idx_aligned act a_idx ->
    ~ done_set (sched_step act ss input) ->
    valid_gates act a_idx ss input ->
    (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
    (fst (sched_step act ss input)).[tf_dfg_v a_idx n_idx] = Bits.ones 1.
  Proof.
    intros Halign Hnd Hg Hv.
    pose proof (buffer_after_cycle act a_idx n_idx ss input Halign Hnd) as Hba.
    cbv zeta in Hba. destruct Hba as [_ Hvalid]. rewrite Hvalid.
    exact (Hg n_idx Hv).
  Qed.

  (* And its value stays put.  A plain buffer recomputes to the same reference
     it already holds, a sample has latched, and a saturated counter holds. *)
  Lemma buffer_frozen_step
        (act: tfs_action sched) a_idx n_idx (ss: sched_sys_state) (input: sched_input_t) :
    act_idx_aligned act a_idx ->
    ~ done_set (sched_step act ss input) ->
    valid_settled act a_idx ss input ->
    valid_gates act a_idx ss input ->
    (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
    (fst ss).[tf_dfg_b a_idx n_idx]
    = (fst (sched_step act ss input)).[tf_dfg_b a_idx n_idx].
  Proof.
    intros Halign Hnd Hset Hg Hv.
    destruct (vreg_nid_node_range act a_idx n_idx Halign) as [Hn1 Hnlen].
    pose proof (Hg n_idx Hv) as Hgv.
    pose proof (buffer_after_cycle act a_idx n_idx ss input Halign Hnd) as Hba.
    cbv zeta in Hba. destruct Hba as [Hvalue _]. rewrite Hvalue.
    change (fst (nth (index_to_nat n_idx)
                   (nth (index_to_nat a_idx) bneeds []) (0, (0, 0))))
      with (vreg_nid a_idx n_idx).
    unfold buf_valid_expr in Hgv.
    destruct (stall_lat_of act (vreg_nid a_idx n_idx)) as [l |] eqn:Hst.
    - (* a stall: the count has saturated, and a saturated counter holds *)
      destruct (stall_counter_wide act a_idx n_idx l Halign Hst) as [_ Hwide].
      cbn [tf_eval_expr] in Hgv. rewrite !convert_same in Hgv.
      destruct (bits1_and_split _ _ Hgv) as [_ Hcmp].
      assert (Hreg : (fst ss).[tf_dfg_b a_idx n_idx]
                     = Bits.of_nat (ss_sz (tf_dfg_b a_idx n_idx)) (pred l)).
      { revert Hcmp.
        match goal with
        | |- context [ @beq_dec ?T ?E ?c ?d ] =>
            replace c with ((fst ss).[tf_dfg_b a_idx n_idx]) by reflexivity;
            destruct (@beq_dec T E ((fst ss).[tf_dfg_b a_idx n_idx]) d) eqn:Hb
        end.
        - intros _. exact (proj1 (beq_dec_iff _ _ _) Hb).
        - intro Hc. exfalso. revert Hc. vm_compute. discriminate. }
      assert (Hcnt : Bits.to_nat ((fst ss).[tf_dfg_b a_idx n_idx]) = pred l)
        by (rewrite Hreg; apply Bits.to_nat_of_nat; exact Hwide).
      apply (bits_to_nat_inj (ss_sz (tf_dfg_b a_idx n_idx))).
      rewrite (stall_counter_step act a_idx n_idx ss input l _ _ Hst Hwide
                 ltac:(lia)).
      rewrite (proj2 (Nat.eqb_eq _ _) Hcnt). cbn [negb].
      rewrite Bool.andb_false_r. reflexivity.
    - destruct (is_sample_of act (vreg_nid a_idx n_idx)) eqn:Hsam.
      + (* a sample: it has already latched *)
        pose proof (sample_buffer_frozen act a_idx n_idx ss input Halign Hnd Hsam Hv)
          as Hfz.
        rewrite Hvalue in Hfz.
        change (fst (nth (index_to_nat n_idx)
                       (nth (index_to_nat a_idx) bneeds []) (0, (0, 0))))
          with (vreg_nid a_idx n_idx) in Hfz.
        exact Hfz.
      + (* a plain buffer: it recomputes the reference it already holds *)
        unfold buf_value_expr. rewrite Hst, Hsam.
        rewrite (Hset n_idx Hst Hv). unfold node_ref_expr. symmetry.
        apply (compile_subst_valid act a_idx ss input Halign Hset
                 (filter (fun '(b_nid, _) =>
                            negb (Nat.eqb b_nid (vreg_nid a_idx n_idx)))
                    (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))).
        * intros e He. exact (proj1 (proj1 (filter_In _ e _) He)).
        * intros x Hx. apply list_assoc_key_none. intro Hin.
          apply in_map_iff in Hin. destruct Hin as [[x' v'] [Hxx Hmem]].
          cbn [fst] in Hxx. subst x'.
          unfold sample_bufs in Hmem. apply filter_In in Hmem.
          destruct Hmem as [Hmem Hsx].
          destruct (Nat.eq_dec x (vreg_nid a_idx n_idx)) as [-> | Hne];
            [ rewrite Hsx in Hsam; discriminate |].
          apply (list_assoc_none_key _ _ Hx), in_map_iff.
          exists (x, v'). split; [ reflexivity |].
          apply filter_In. split; [ exact Hmem |].
          apply negb_true_iff, Nat.eqb_neq. exact Hne.
        * intros x m msz Hx Hsx. apply list_assoc_nodup_in.
          -- unfold sample_bufs. apply nodup_map_fst_filter.
             exact (slot_keys_nodup act a_idx Halign).
          -- unfold sample_bufs. apply filter_In. split; [| exact Hsx ].
             exact (proj1 (proj1 (filter_In _ _ _) (wla_in _ _ _ Hx))).
        * exact Hn1.
        * exact Hnlen.
        * exact Hnlen.
        * apply buffer_register_node_size. exact Halign.
        * exact Hgv.
  Qed.

  (* A stall's next-validity, read in both directions: it fires exactly when the
     gate is up AND the count has reached [pred l]. *)
  Lemma stall_valid_next_inv
        (act: tfs_action sched) a_idx n_idx (ss: sched_sys_state)
        (input: sched_input_t) l gate :
    stall_lat_of act (vreg_nid a_idx n_idx) = Some l ->
    pred l < pow2 (ss_sz (tf_dfg_b a_idx n_idx)) ->
    eval_st (tf_dfg_v a_idx n_idx)
      (buf_valid_expr act a_idx n_idx (ss_sz (tf_dfg_b a_idx n_idx)) gate
         (vreg_nid a_idx n_idx)) ss input = Bits.ones 1 ->
    eval1 gate ss input = Bits.ones 1
    /\ (fst ss).[tf_dfg_b a_idx n_idx]
       = Bits.of_nat (ss_sz (tf_dfg_b a_idx n_idx)) (pred l).
  Proof.
    intros Hst Hwide Hv. unfold buf_valid_expr in Hv. rewrite Hst in Hv.
    cbn [tf_eval_expr] in Hv. rewrite !convert_same in Hv.
    destruct (bits1_and_split _ _ Hv) as [Hg Hcmp].
    split; [ exact Hg |]. revert Hcmp.
    match goal with
    | |- context [ @beq_dec ?T ?E ?c ?d ] =>
        replace c with ((fst ss).[tf_dfg_b a_idx n_idx]) by reflexivity;
        destruct (@beq_dec T E ((fst ss).[tf_dfg_b a_idx n_idx]) d) eqn:Hb
    end.
    - intros _. exact (proj1 (beq_dec_iff _ _ _) Hb).
    - intro Hc. exfalso. revert Hc. vm_compute. discriminate.
  Qed.

  Lemma stall_valid_next_ones
        (act: tfs_action sched) a_idx n_idx (ss: sched_sys_state)
        (input: sched_input_t) l gate :
    stall_lat_of act (vreg_nid a_idx n_idx) = Some l ->
    eval1 gate ss input = Bits.ones 1 ->
    (fst ss).[tf_dfg_b a_idx n_idx]
      = Bits.of_nat (ss_sz (tf_dfg_b a_idx n_idx)) (pred l) ->
    eval_st (tf_dfg_v a_idx n_idx)
      (buf_valid_expr act a_idx n_idx (ss_sz (tf_dfg_b a_idx n_idx)) gate
         (vreg_nid a_idx n_idx)) ss input = Bits.ones 1.
  Proof.
    intros Hst Hg Hreg. unfold buf_valid_expr. rewrite Hst.
    cbn [tf_eval_expr]. rewrite !convert_same.
    match goal with
    | |- context [ @beq_dec ?T ?E ?c ?d ] =>
        replace c with ((fst ss).[tf_dfg_b a_idx n_idx]) by reflexivity
    end.
    match goal with
    | |- context [ beq_dec _ ?d ] =>
        assert (Hr2 : (fst ss).[tf_dfg_b a_idx n_idx] = d)
          by (rewrite Hreg; reflexivity)
    end.
    rewrite Hr2, beq_dec_refl.
    match goal with
    | |- context [ Bits.and ?g _ ] =>
        replace g with (Bits.ones 1) by (symmetry; exact Hg)
    end.
    vm_compute. reflexivity.
  Qed.

  (* A saturated counter holds its value across a pre-done cycle. *)
  Lemma stall_saturated_step
        (act: tfs_action sched) a_idx n_idx (ss: sched_sys_state)
        (input: sched_input_t) l :
    act_idx_aligned act a_idx ->
    ~ done_set (sched_step act ss input) ->
    stall_lat_of act (vreg_nid a_idx n_idx) = Some l ->
    (fst ss).[tf_dfg_b a_idx n_idx]
      = Bits.of_nat (ss_sz (tf_dfg_b a_idx n_idx)) (pred l) ->
    (fst (sched_step act ss input)).[tf_dfg_b a_idx n_idx]
      = Bits.of_nat (ss_sz (tf_dfg_b a_idx n_idx)) (pred l).
  Proof.
    intros Halign Hnd Hst Hreg.
    destruct (stall_counter_wide act a_idx n_idx l Halign Hst) as [_ Hwide].
    assert (Hcnt : Bits.to_nat ((fst ss).[tf_dfg_b a_idx n_idx]) = pred l)
      by (rewrite Hreg; apply Bits.to_nat_of_nat; exact Hwide).
    pose proof (buffer_after_cycle act a_idx n_idx ss input Halign Hnd) as Hba.
    cbv zeta in Hba. destruct Hba as [Hvalue _]. rewrite Hvalue.
    change (fst (nth (index_to_nat n_idx)
                   (nth (index_to_nat a_idx) bneeds []) (0, (0, 0))))
      with (vreg_nid a_idx n_idx).
    apply (bits_to_nat_inj (ss_sz (tf_dfg_b a_idx n_idx))).
    rewrite (stall_counter_step act a_idx n_idx ss input l _ _ Hst Hwide
               ltac:(lia)).
    rewrite (proj2 (Nat.eqb_eq _ _) Hcnt). cbn [negb].
    rewrite Bool.andb_false_r, Hcnt. symmetry.
    apply Bits.to_nat_of_nat. exact Hwide.
  Qed.

  (* Specialisation to one pre-done cycle: the reference is stable wherever its
     own validity fires, since the samples it reads have already latched. *)
  Lemma compile_nobuf_step_stable
        (act: tfs_action sched) a_idx (ss: sched_sys_state) (input: input_t) :
    act_idx_aligned act a_idx ->
    ~ done_set (sched_step act ss (sched_input input ss)) ->
    forall fuel n szB,
      n < length (graph (build_dfg ctx act)) ->
      eval1 (snd (compile_dfg_expr ctx bneeds fuel a_idx (build_dfg ctx act)
                    n (sample_bufs act a_idx))) ss (sched_input input ss)
        = Bits.ones 1 ->
      tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
        (fst (compile_dfg_expr ctx bneeds fuel a_idx (build_dfg ctx act) n (sample_bufs act a_idx)))
        (sched_step act ss (sched_input input ss))
        (sched_input input (sched_step act ss (sched_input input ss)))
      = tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
        (fst (compile_dfg_expr ctx bneeds fuel a_idx (build_dfg ctx act) n (sample_bufs act a_idx)))
        ss (sched_input input ss).
  Proof.
    intros Halign Hnd fuel n szB Hnlen Hval. symmetry.
    apply (compile_nobuf_state_indep act a_idx (sched_input input ss)
             (sched_input input (sched_step act ss (sched_input input ss)))
             ss (sched_step act ss (sched_input input ss))).
    - exact Halign.
    - intro s. symmetry.
      exact (sched_step_preserves_svar act ss (sched_input input ss) s Hnd).
    - intro o. symmetry.
      exact (sched_step_preserves_ovar act ss (sched_input input ss) o Hnd).
    - intro v. reflexivity.
    - intros n_idx Hsam Hv.
      exact (sample_buffer_frozen act a_idx n_idx ss (sched_input input ss)
               Halign Hnd Hsam Hv).
    - exact Hnlen.
    - exact Hval.
  Qed.

  (* The ungated value saturation -- [buffers_settled], [compile_subst_gen],
     [compile_subst], [buffers_settled_run] -- lived here and is GONE.  Nothing
     consumed it: correctness goes through the VALIDITY-gated [valid_settled],
     and progress through [valids_ones_run].  V4 would have made it expensive to
     keep, since a sample's buffer latches and an ungated rank has to carry a
     "no sample latches this cycle" obligation that the gated version gets for
     free from validity monotonicity.  Removed rather than re-proved. *)

  (* VALIDITY substitution: if every buffer register caching an id below [bound]
     reads all-ones, then so does the compiled validity expression of any node
     at or below [bound].  Ranked by [node_rank]. *)
  Lemma compile_valid_ones_gen
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
        (ss: sched_sys_state) (input: sched_input_t) :
    act_idx_aligned act a_idx ->
    forall bound,
    (forall n_idx, node_rank act (vreg_nid a_idx n_idx) < bound ->
       (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1) ->
    forall bufs,
      (forall e, In e bufs ->
         In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
      forall fuel n (pi: list lit),
        1 <= n ->
        n < length (graph (build_dfg ctx act)) ->
        n < fuel ->
        node_rank act n <= bound ->
        (BitsToLists.list_assoc bufs n = None \/ node_rank act n < bound) ->
        eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                      n bufs)) ss input = Bits.ones 1.
  Proof.
    intros Halign bound Hvalid bufs Hsub fuel.
    induction fuel as [| fuel IH]; intros n pi Hn1 Hnlen Hnfuel Hnb Hself; [ lia | ].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:Hla.
    - (* buffered leaf: read the validity register, valid by hypothesis *)
      assert (Hnlt : node_rank act n < bound)
        by (destruct Hself as [Hnone | Hlt2]; [ congruence | exact Hlt2 ]).
      cbn [compile_dfg_expr_aux]. rewrite Hla. cbv beta iota.
      assert (Hin_slot : In (n, (m, msz))
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))
        by (apply Hsub, wla_in, Hla).
      assert (Hin_gsi : In (n, (m, msz))
                (get_sizes_and_idx ctx (build_dfg ctx act)
                   (require_buffer ctx (build_dfg ctx act)
                      (calc_target_cycle cost_limit
                         (calc_backward_cost ctx cost_limit (build_dfg ctx act))))))
        by (rewrite <- (buffer_slot_eq act a_idx Halign); exact Hin_slot).
      assert (Hlt : m < length
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])).
      { rewrite (buffer_slot_eq act a_idx Halign), gsi_length.
        exact (gsi_idx_bound _ _ n m msz Hin_gsi). }
      destruct (index_of_nat_bounded Hlt) as [n_idx' Hn_idx'].
      rewrite Hn_idx'. cbv beta iota.
      assert (Hmi : index_to_nat n_idx' = m)
        by (apply index_to_nat_of_nat; exact Hn_idx').
      assert (Hvn : vreg_nid a_idx n_idx' = n).
      { unfold vreg_nid. rewrite Hmi, (buffer_slot_eq act a_idx Halign).
        rewrite (gsi_entry_at _ _ n m msz Hin_gsi). reflexivity. }
      (* both arms of the buffered branch publish the same validity register *)
      destruct (op (nth n (graph (build_dfg ctx act))
                      {| nid := 0; op := DFG_Empty; sz := 0 |}));
        cbn [snd]; rewrite eval1_svar_v; apply Hvalid; rewrite Hvn; exact Hnlt.
    - (* not buffered: the validity is built from the args' validities *)
      cbn [compile_dfg_expr_aux]. rewrite Hla. cbv beta iota.
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
      assert (Hchild : forall x (p: list lit), In x (get_args ctx node) ->
                eval1 (snd (compile_dfg_expr_at ctx bneeds p fuel a_idx
                              (build_dfg ctx act) x bufs)) ss input = Bits.ones 1).
      { intros x p Hx. destruct (Harg x Hx) as [Hx1 Hx2].
        apply (IH x p Hx1 (Nat.lt_trans _ _ _ Hx2 Hnlen));
          [ lia
          | apply Nat.lt_le_incl; exact (node_rank_child act x n bound Hx2 Hnb)
          | right; exact (node_rank_child act x n bound Hx2 Hnb) ]. }
      destruct (op node) as [c | v | v | op1 arg | op1 arg1 arg2 | arg | cnd tid eid | slat sa | dov dn den | siv sn sen | ja jb | ]
        eqn:Hop.
      + cbn [snd]. apply eval1_const1.
      + cbn [snd]. apply eval1_const1.
      + destruct v; cbn [snd]; apply eval1_const1.
      + assert (Hain : In arg (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        pose proof (Hchild arg pi Hain) as Ha.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    arg bufs) as [ae ve] eqn:E1.
        cbn [snd] in Ha |- *. exact Ha.
      + assert (Ha1in : In arg1 (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        assert (Ha2in : In arg2 (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; left; reflexivity).
        pose proof (Hchild arg1 pi Ha1in) as Hv1.
        pose proof (Hchild arg2 pi Ha2in) as Hv2.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    arg1 bufs) as [a1e v1e] eqn:E1.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    arg2 bufs) as [a2e v2e] eqn:E2.
        cbn [snd] in Hv1, Hv2 |- *.
        rewrite valid_and_eval, Hv1, Hv2. apply Bits.and_ones_l.
      + assert (Hain : In arg (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        pose proof (Hchild arg pi Hain) as Ha.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    arg bufs) as [ae ve] eqn:E1.
        cbn [snd] in Ha |- *. exact Ha.
      + assert (Hcin : In cnd (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        assert (Htin : In tid (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; left; reflexivity).
        assert (Hein : In eid (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; right; left; reflexivity).
        pose proof (Hchild cnd pi Hcin) as Hcv.
        remember (ppath_at act pi cnd true) as pt eqn:Hpt. clear Hpt.
        remember (ppath_at act pi cnd false) as pe eqn:Hpe. clear Hpe.
        pose proof (Hchild tid pt Htin) as Htv.
        pose proof (Hchild eid pe Hein) as Hev.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    cnd bufs) as [ce cv] eqn:Ec.
        destruct (compile_dfg_expr_at ctx bneeds pt fuel a_idx
                    (build_dfg ctx act) tid bufs) as [te tv] eqn:Et.
        destruct (compile_dfg_expr_at ctx bneeds pe fuel a_idx
                    (build_dfg ctx act) eid bufs) as [ee ev] eqn:Ee.
        cbn [snd] in Hcv, Htv, Hev |- *.
        match goal with |- context [if ?B then _ else _] => destruct B end.
        * rewrite valid_and_eval, valid_and_eval, Htv, Hev, Hcv.
          rewrite Bits.and_ones_l. apply Bits.and_ones_l.
        * rewrite valid_and_eval, Hcv, Bits.and_ones_l.
          apply (valid_if_eval ce tv ev _ input Htv Hev).
      + (* DFG_Stall: validity passes through unchanged here.  A counting stall
           delays it, so this lemma restates over a cycle index rather than
           holding pointwise. *)
        assert (Hain : In sa (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        pose proof (Hchild sa pi Hain) as Ha.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    sa bufs) as [ae ve] eqn:E1.
        cbn [snd] in Ha |- *. exact Ha.
      + (* SPIKE 2b: DFG_Drive, validity passes through. *)
        assert (Hain : In dn (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        pose proof (Hchild dn pi Hain) as Ha.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    dn bufs) as [ae ve] eqn:E1.
        cbn [snd] in Ha |- *. exact Ha.
      + (* SPIKE 2b: DFG_Sample -- its validity IS the token's, by construction
           in compile_dfg_expr_aux, so this passes through too. *)
        assert (Hain : In sn (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        pose proof (Hchild sn pi Hain) as Ha.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    sn bufs) as [ae ve] eqn:E1.
        cbn [snd] in Ha |- *. exact Ha.
      + (* DFG_Join: its validity is the AND of its two arguments. *)
        assert (Hain : In ja (get_args ctx node))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        assert (Hbin : In jb (get_args ctx node))
          by (unfold get_args; rewrite Hop; right; left; reflexivity).
        pose proof (Hchild ja pi Hain) as Ha.
        pose proof (Hchild jb pi Hbin) as Hb2.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    ja bufs) as [ae ve] eqn:E1.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    jb bufs) as [be be2] eqn:E2.
        cbn [snd] in Ha, Hb2 |- *.
        rewrite valid_and_eval, Ha, Hb2. reflexivity.
      + exfalso. apply (node_op_not_empty act n Hn1 Hnlen).
        unfold node in Hop. exact Hop.
  Qed.

  Lemma compile_valid_ones
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
        (ss: sched_sys_state) (input: sched_input_t) :
    act_idx_aligned act a_idx ->
    forall bound,
    (forall n_idx, node_rank act (vreg_nid a_idx n_idx) < bound ->
       (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1) ->
    forall bufs,
      (forall e, In e bufs ->
         In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
      forall fuel n,
        1 <= n ->
        n < length (graph (build_dfg ctx act)) ->
        n < fuel ->
        node_rank act n <= bound ->
        (BitsToLists.list_assoc bufs n = None \/ node_rank act n < bound) ->
        eval1 (snd (compile_dfg_expr ctx bneeds fuel a_idx (build_dfg ctx act)
                      n bufs)) ss input = Bits.ones 1.
  Proof.
    intros Halign bound Hvalid bufs Hsub fuel n.
    exact (compile_valid_ones_gen act a_idx ss input Halign bound Hvalid bufs Hsub
             fuel n []).
  Qed.

  (* A stall's counter along a pre-done run: with its gate up from cycle [r],
     the counter reads [pred l] from cycle [r + pred l] on.  This is A2 debt 3,
     and it is what licenses the weight [node_rank] gives a stall. *)
  Lemma stall_counter_run
        (act: tfs_action sched) a_idx n_idx (input: input_t)
        (ss0: sched_sys_state) l r K :
    act_idx_aligned act a_idx ->
    stall_lat_of act (vreg_nid a_idx n_idx) = Some l ->
    (fst ss0).[tf_dfg_b a_idx n_idx] = Bits.zero ->
    (forall i, 1 <= i <= K -> ~ done_set (run_n i act input ss0)) ->
    (forall j, r <= j < K ->
       eval1 (buf_gate act a_idx n_idx) (run_n j act input ss0)
         (sched_input input (run_n j act input ss0)) = Bits.ones 1) ->
    forall k, r + pred l <= k <= K ->
      Bits.to_nat ((fst (run_n k act input ss0)).[tf_dfg_b a_idx n_idx]) = pred l.
  Proof.
    intros Halign Hst Hzero Hnd Hadv.
    destruct (stall_counter_wide act a_idx n_idx l Halign Hst) as [Hl Hwide].
    apply (counter_saturates (ss_sz (tf_dfg_b a_idx n_idx)) (pred l) r K
             (fun j => (fst (run_n j act input ss0)).[tf_dfg_b a_idx n_idx])
             (fun j => if beq_dec
                            (eval1 (buf_gate act a_idx n_idx)
                               (run_n j act input ss0)
                               (sched_input input (run_n j act input ss0)))
                            Bits.zero
                       then false else true)).
    - exact Hwide.
    - cbn [run_n]. rewrite Hzero.
      change (@Bits.zero (ss_sz (tf_dfg_b a_idx n_idx)))
        with (Bits.of_nat (ss_sz (tf_dfg_b a_idx n_idx)) 0).
      apply Bits.to_nat_of_nat. lia.
    - intros j HjK Hinv. cbn beta in Hinv |- *.
      change (run_n (S j) act input ss0)
        with (sched_step act (run_n j act input ss0)
                (sched_input input (run_n j act input ss0))).
      pose proof (buffer_after_cycle act a_idx n_idx (run_n j act input ss0)
                    (sched_input input (run_n j act input ss0)) Halign
                    ltac:(apply (Hnd (S j)); lia)) as Hba.
      cbv zeta in Hba. destruct Hba as [Hvalb _]. rewrite Hvalb.
      apply (stall_counter_step act a_idx n_idx _ _ l _ _ Hst Hwide Hinv).
    - intros j Hj. cbn beta. rewrite (Hadv j Hj).
      destruct (beq_dec (Bits.ones 1) Bits.zero) eqn:E; [| reflexivity].
      exfalso. apply ones1_neq_zero. exact (proj1 (beq_dec_iff _ _ _) E).
  Qed.

  (* SATURATION (validity).  After [k] pre-done cycles, every buffer whose node
     ranks below [k] reads all-ones.  The rank is WEIGHTED: a stall's buffer
     counts, and its validity rises [lat] cycles after its argument's, so the
     induction needs every earlier cycle rather than the previous one. *)
  Lemma valids_ones_run :
    forall (act: tfs_action sched) a_idx (input: input_t)
           (ss0: sched_sys_state) (K: nat),
      act_idx_aligned act a_idx ->
      (forall x, zeroed_at_start x -> (fst ss0).[x] = Bits.zero) ->
      (forall i, 1 <= i <= K -> ~ done_set (run_n i act input ss0)) ->
      forall k, k <= K ->
      forall n_idx,
        node_rank act (vreg_nid a_idx n_idx) < k ->
        (fst (run_n k act input ss0)).[tf_dfg_v a_idx n_idx] = Bits.ones 1.
  Proof.
    intros act a_idx input ss0 K Halign Hzero Hnd.
    assert (main : forall bnd j, j <= bnd -> j <= K -> forall n_idx,
              node_rank act (vreg_nid a_idx n_idx) < j ->
              (fst (run_n j act input ss0)).[tf_dfg_v a_idx n_idx] = Bits.ones 1).
    { intro bnd. induction bnd as [| m IH]; intros j Hjm HjK n_idx Hlt; [ lia |].
      destruct (Nat.eq_dec j (S m)) as [-> | Hne]; [| apply (IH j); lia ].
      destruct (vreg_nid_node_range act a_idx n_idx Halign) as [Hn1 Hnlen].
      assert (Hstep : ~ done_set (sched_step act (run_n m act input ss0)
                        (sched_input input (run_n m act input ss0))))
        by (apply (Hnd (S m)); lia).
      pose proof (buffer_after_cycle act a_idx n_idx (run_n m act input ss0)
                    (sched_input input (run_n m act input ss0)) Halign Hstep) as Hba.
      cbv zeta in Hba. destruct Hba as [_ Hval].
      change (run_n (S m) act input ss0)
        with (sched_step act (run_n m act input ss0)
                (sched_input input (run_n m act input ss0))).
      rewrite Hval.
      (* the buffer lemmas hand the node id over UNFOLDED; fold it once, so the
         rank hypotheses and the stall lemmas speak of the same term *)
      change (fst (nth (index_to_nat n_idx)
                     (nth (index_to_nat a_idx) bneeds []) (0, (0, 0))))
        with (vreg_nid a_idx n_idx).
      unfold buf_valid_expr.
      (* the node id comes FROM the goal: [vreg_nid] is a definition and a
         written-out copy of it matches nothing the buffer lemmas produced *)
      match goal with
      | |- context [ stall_lat_of act ?nn ] =>
          destruct (stall_lat_of act nn) as [l |] eqn:Hst
      end.
      - (* a stall: the gate is up, and the counter has reached [pred l] *)
        assert (Hnode : In (nth (vreg_nid a_idx n_idx) (graph (build_dfg ctx act))
                              {| nid := 0; op := DFG_Empty; sz := 0 |})
                           (graph (build_dfg ctx act)))
          by (apply nth_In; exact Hnlen).
        pose proof Hst as Hst0. unfold stall_lat_of, node_op in Hst0.
        match type of Hst0 with
        | match ?o with _ => _ end = _ =>
            destruct o as [cn|iv|dv|uop ua|bop b1 b2|ra|pc pt pe|slat sarg
                          |dp da den|sp stok sen|ja jb|] eqn:Hop
        end; try discriminate Hst0.
        injection Hst0 as Hslat. subst slat.
        assert (Hargin : In sarg (get_args ctx
                   (nth (vreg_nid a_idx n_idx) (graph (build_dfg ctx act))
                      {| nid := 0; op := DFG_Empty; sz := 0 |})))
          by (unfold get_args; rewrite Hop; left; reflexivity).
        pose proof (build_dfg_args_pos act) as [_ [Hargpos _]].
        pose proof (Hargpos _ Hnode sarg Hargin) as Hs1.
        pose proof (args_lt_fwd act _ Hnode sarg Hargin) as Hslt.
        rewrite (node_nid_at act _ Hnlen) in Hslt.
        assert (Hslen : sarg < length (graph (build_dfg ctx act))) by lia.
        pose proof (node_rank_stall act (vreg_nid a_idx n_idx) sarg l Hst Hslt) as Hrk.
        (* the gate IS the argument's validity, up from the argument's rank on *)
        assert (Hgate : forall j, S (node_rank act sarg) <= j <= m ->
                  eval1 (buf_gate act a_idx n_idx) (run_n j act input ss0)
                    (sched_input input (run_n j act input ss0)) = Bits.ones 1).
        { intros j Hj.
          rewrite (compile_stall_valid (build_dfg ctx act) _ _ a_idx _ _ sarg _ []
                     (length (graph (build_dfg ctx act))) Hop
                     (list_assoc_filter_out _ _) ltac:(lia)).
          rewrite (compile_fuel_irrel act a_idx _ sarg Hs1 Hslen
                     (pred (length (graph (build_dfg ctx act))))
                     (length (graph (build_dfg ctx act))) ltac:(lia) Hslen).
          apply (compile_valid_ones act a_idx (run_n j act input ss0)
                   (sched_input input (run_n j act input ss0)) Halign j
                   (IH j ltac:(lia) ltac:(lia))).
          + intros e He. exact (proj1 (proj1 (filter_In _ e _) He)).
          + exact Hs1.
          + exact Hslen.
          + exact Hslen.
          + lia.
          + right. lia. }
        assert (Hcnt : Bits.to_nat
                  ((fst (run_n m act input ss0)).[tf_dfg_b a_idx n_idx]) = pred l).
        { apply (stall_counter_run act a_idx n_idx input ss0 l
                   (S (node_rank act sarg)) m Halign Hst
                   (Hzero (tf_dfg_b a_idx n_idx) I)
                   ltac:(intros i Hi; apply Hnd; lia)).
          - intros j Hj. apply Hgate. lia.
          - lia. }
        destruct (stall_counter_wide act a_idx n_idx l Halign Hst) as [_ Hwide].
        cbn [tf_eval_expr]. rewrite !convert_same.
        (* [cbn] rebuilds the register read under a second type annotation;
           put the statement's form back before rewriting with [Hcnt]. *)
        match goal with
        | |- context [ @beq_dec ?T ?E ?c ?d ] =>
            replace c with
              ((fst (run_n m act input ss0)).[tf_dfg_b a_idx n_idx]) by reflexivity
        end.
        (* the width comes from the goal too: [Bits.to_nat] carries it as an
           implicit, and a second copy of it breaks the rewrite *)
        match goal with
        | |- context [ beq_dec _ ?d ] =>
            assert (Hreg : (fst (run_n m act input ss0)).[tf_dfg_b a_idx n_idx] = d)
        end.
        { apply (bits_to_nat_inj (ss_sz (tf_dfg_b a_idx n_idx))).
          rewrite Hcnt. symmetry. apply Bits.to_nat_of_nat. exact Hwide. }
        rewrite Hreg, beq_dec_refl.
        (* and the gate, which the AND now needs as well *)
        match goal with
        | |- context [ Bits.and ?g _ ] =>
            replace g with (Bits.ones 1)
              by (symmetry; exact (Hgate m ltac:(lia)))
        end.
        vm_compute. reflexivity.
      - (* every other node: the compiled validity of its own expression *)
        apply (compile_valid_ones act a_idx (run_n m act input ss0)
                 (sched_input input (run_n m act input ss0)) Halign m
                 (IH m (Nat.le_refl m) ltac:(lia))).
        + intros e He. exact (proj1 (proj1 (filter_In _ e _) He)).
        + exact Hn1.
        + exact Hnlen.
        + exact Hnlen.
        + lia.
        + left. apply list_assoc_filter_out. }
    intros k HkK n_idx Hlt. exact (main k k (Nat.le_refl k) HkK n_idx Hlt).
  Qed.


  (* SOUND semantic core (Phase 2): a done cycle exists by S (settle_bound).
     Either done fired earlier, which yields an earlier witness, or every buffer
     settled and validated by settle_bound and the combined validity fires. *)
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
      apply (compile_valid_ones act a_idx _ _ Halign (settle_bound act)
               (valids_ones_run act a_idx input ss0 (settle_bound act) Halign
                  (proj2 (proj2 Hstart)) (fun i Hi => Hno i (proj2 Hi))
                  (settle_bound act) (Nat.le_refl _))
               _ (fun e He => He)
               (length (graph (build_dfg ctx act))) nd Hnd1 Hndlt Hndlt);
        unfold settle_bound;
        [ apply Nat.lt_le_incl | right ]; apply node_rank_mono; exact Hndlt.
  Qed.

  (* PHASE 2 (progress): a FIRST done cycle exists, the least N <= S
     (settle_bound act) at which done fires (well-ordering over the decidable
     [done_set (run_n k ...)]), so "not done before N" holds by construction. *)
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

  Lemma cycle_updates_done (act: tfs_action sched) (ss: sched_sys_state) (input: sched_input_t) :
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
    cbn [app]. destruct u as [| var val | var val];
      cbn [find_st_update] in *.
    - apply IH, Hnone.
    - destruct (eq_dec var x); [ reflexivity | apply IH, Hnone ].
    - apply IH, Hnone.
  Qed.

  Lemma find_out_update_app_None x (ups1 ups2: list (tf_update ss_sz oo_sz)) :
    find_out_update sched x ups1 = None ->
    find_out_update sched x (ups1 ++ ups2) = find_out_update sched x ups2.
  Proof.
    induction ups1 as [| u ups1 IH]; intro Hnone; [ reflexivity |].
    cbn [app]. destruct u as [| var val | var val];
      cbn [find_out_update] in *.
    - apply IH, Hnone.
    - apply IH, Hnone.
    - destruct (eq_dec var x); [ discriminate | apply IH, Hnone ].
  Qed.

  Lemma find_out_update_app_r_None x (ups1 ups2: list (tf_update ss_sz oo_sz)) :
    find_out_update sched x ups2 = None ->
    find_out_update sched x (ups1 ++ ups2) = find_out_update sched x ups1.
  Proof.
    induction ups1 as [| u ups1 IH]; intro Hnone; [ exact Hnone |].
    cbn [app]. destruct u as [| var val | var val];
      cbn [find_out_update] in *.
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
    In v (reset_states ctx bneeds) -> v <> tf_dfg_s s.
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
    assert (Hrs: tfs_reset_states sched = reset_states ctx bneeds) by reflexivity.
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
    - destruct op as [| dst rhs | dst rhs | ip dst rhs]; [ | | | destruct ip ].
      + apply IH; [ exact Hnd | exact Hin ].
      + apply IH; [ cbn [app] in Hnd; inversion Hnd; assumption | exact Hin ].
      + inversion Hnd as [| tag tags Hnot Htail]; subst tag tags.
        destruct (eq_dec dst x) as [Hdx | Hdx].
        * subst dst. exfalso. apply Hnot. apply in_flat_map.
          exists (tf_output x e). split; [ exact Hin |]. cbn [In]. left. reflexivity.
        * rewrite find_out_update_skip_head.
          -- apply IH; [ exact Htail | exact Hin ].
          -- intros [rhs' Heq]; inversion Heq; contradiction.
  Qed.

  (* --- concrete shape of the done-branch op list --- *)

  Lemma final_ops_concrete (act: tfs_action sched) a_idx :
    act_idx_aligned act a_idx ->
    snd (Contract.tfs_schedule sched act)
    = map (fun '(var, n) =>
             let '(expr, _) := compile_dfg_expr ctx bneeds
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
    unfold sched, tfs_schedule, tfs_schedule_bn, Contract.tfs_schedule. unfold schedule.
    cbv zeta. cbn [snd]. unfold compile_dfg_aux. cbv zeta.
    rewrite Halign2, index_of_nat_to_nat, Hnth_dfg. reflexivity.
  Qed.

  Local Notation act_slot a_idx :=
    (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []).

  (* The compiled expression the done branch writes for a var_map entry. *)
  Local Notation vm_expr act a_idx n :=
    (fst (compile_dfg_expr ctx bneeds (length (graph (build_dfg ctx act)))
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
    (* E1: op_assigns_st gained a tf_call disjunct; the done half emits only
       tf_assign / tf_output, so the extra branch dies by inversion. *)
    destruct var as [sv' | ov]; subst op;
      intros [e He]; inversion He; subst.
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
    (* the done half emits only tf_assign / tf_output, so the call disjunct of
       [op_writes_out] dies by inversion *)
    destruct var as [sv | ov']; subst op;
      intros [e He]; inversion He; subst.
    apply (Hno n). exact Hvm.
  Qed.

  (* --- READOUT: a done cycle commits the compiled var_map expressions --- *)

  Lemma sched_step_done_svar (act: tfs_action sched) a_idx (ss: sched_sys_state)
        (input: sched_input_t) (sv: s_var) (n: nat) :
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
        (input: sched_input_t) (ov: o_var) (n: nat) :
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
        (ss: sched_sys_state) (input: sched_input_t) (sv: s_var) :
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
        (ss: sched_sys_state) (input: sched_input_t) (ov: o_var) :
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

  Local Notation find_st_update_app_Some := (find_st_update_app_Some_gen sched).

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
    In (tf_dfg_v a_idx n_idx) (reset_states ctx bneeds).
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
      (ss: sched_sys_state) (input: sched_input_t) :
    done_set (sched_step act ss input) ->
    (fst (sched_step act ss input)).[tf_dfg_v a_idx n_idx] = Bits.zero.
  Proof.
    intro Hdone.
    rewrite sched_step_getst, (cycle_updates_done act ss input Hdone).
    unfold find_st_val.
    rewrite (find_st_update_app_Some _ _ _ _ (reset_updates_v a_idx n_idx)).
    reflexivity.
  Qed.

  (* THE INVARIANT (Phase 3b): from a state with clear validity bits, at EVERY
     cycle a buffer whose validity bit is set holds its settled value.  A done
     cycle clears the bits, so no "not yet done" hypothesis is needed. *)
  (* THE INVARIANT (Phase 3b), all three conjuncts at once.  They go together:
     settledness crosses a cycle only if the reference's validity is up, that
     validity substitutes onto the reference's table only if the VALUES agree,
     and both lean on the gate still being up. *)
  Lemma valid_settled_run :
    forall (act: tfs_action sched) a_idx (input: input_t)
           (ss0: sched_sys_state) (k: nat),
      act_idx_aligned act a_idx ->
      (forall n_idx, (fst ss0).[tf_dfg_v a_idx n_idx] = Bits.zero) ->
      valid_gates act a_idx (run_n k act input ss0)
        (sched_input input (run_n k act input ss0))
      /\ valid_refs act a_idx (run_n k act input ss0)
           (sched_input input (run_n k act input ss0))
      /\ valid_settled act a_idx (run_n k act input ss0)
           (sched_input input (run_n k act input ss0)).
  Proof.
    intros act a_idx input ss0 k Halign Hz0.
    induction k as [| k IH].
    - split; [| split ].
      + intros m Hv. exfalso. cbn [run_n] in Hv.
        rewrite Hz0 in Hv. apply ones1_neq_zero. symmetry. exact Hv.
      + intros m pi Hv. exfalso. cbn [run_n] in Hv.
        rewrite Hz0 in Hv. apply ones1_neq_zero. symmetry. exact Hv.
      + intros m Hns Hv. exfalso. cbn [run_n] in Hv.
        rewrite Hz0 in Hv. apply ones1_neq_zero. symmetry. exact Hv.
    - destruct IH as [IHg [IHr IHs]].
      set (ssk := run_n k act input ss0) in *.
      change (run_n (S k) act input ss0)
        with (sched_step act ssk (sched_input input ssk)).
      destruct (done_set_dec (sched_step act ssk (sched_input input ssk)))
        as [Hd | Hnd].
      + (* a done cycle clears every validity bit *)
        split; [| split ].
        * intros m Hv. exfalso.
          rewrite (sched_step_done_v act a_idx m ssk
                     (sched_input input ssk) Hd) in Hv.
          apply ones1_neq_zero. symmetry. exact Hv.
        * intros m pi Hv. exfalso.
          rewrite (sched_step_done_v act a_idx m ssk
                     (sched_input input ssk) Hd) in Hv.
          apply ones1_neq_zero. symmetry. exact Hv.
        * intros m Hns Hv. exfalso.
          rewrite (sched_step_done_v act a_idx m ssk
                     (sched_input input ssk) Hd) in Hv.
          apply ones1_neq_zero. symmetry. exact Hv.
      + (* a pre-done cycle *)
        assert (Hmono : forall m,
                  (fst ssk).[tf_dfg_v a_idx m] = Bits.ones 1 ->
                  (fst (sched_step act ssk (sched_input input ssk))).[tf_dfg_v a_idx m]
                  = Bits.ones 1)
          by (intros m Hx; exact (validity_monotone_step act a_idx m ssk
                (sched_input input ssk) Halign Hnd IHg Hx)).
        assert (Hfroz : forall m,
                  (fst ssk).[tf_dfg_v a_idx m] = Bits.ones 1 ->
                  (fst ssk).[tf_dfg_b a_idx m]
                  = (fst (sched_step act ssk (sched_input input ssk))).[tf_dfg_b a_idx m])
          by (intros m Hx; exact (buffer_frozen_step act a_idx m ssk
                (sched_input input ssk) Halign Hnd IHs IHg Hx)).
        assert (Hgk : forall m,
                  (fst (sched_step act ssk (sched_input input ssk))).[tf_dfg_v a_idx m]
                    = Bits.ones 1 ->
                  eval1 (buf_gate act a_idx m) ssk (sched_input input ssk)
                  = Bits.ones 1)
          by (intros m Hx; exact (buffer_valid_gate act a_idx m ssk
                (sched_input input ssk) Halign Hnd Hx)).
        assert (Hnk : forall m,
                  (fst (sched_step act ssk (sched_input input ssk))).[tf_dfg_v a_idx m]
                    = Bits.ones 1 ->
                  eval_st (tf_dfg_v a_idx m) (buf_valid_next act a_idx m)
                    ssk (sched_input input ssk) = Bits.ones 1).
        { intros m Hx.
          pose proof (buffer_after_cycle act a_idx m ssk (sched_input input ssk)
                        Halign Hnd) as Hba.
          cbv zeta in Hba. destruct Hba as [_ Hvalid].
          rewrite Hvalid in Hx. exact Hx. }
        (* a sample below a node is in the table with that node's slot removed *)
        assert (Hrest : forall m x, x < vreg_nid a_idx m ->
                  is_sample_of act x = true ->
                  BitsToLists.list_assoc
                    (filter (fun '(b_nid, _) =>
                               negb (Nat.eqb b_nid (vreg_nid a_idx m)))
                       (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))
                    x <> None).
        { intros m x Hx Hsx.
          destruct (BitsToLists.list_assoc (sample_bufs act a_idx) x) as [e |] eqn:He;
            [| exfalso; exact (sample_is_buffered act a_idx x Halign Hsx He) ].
          pose proof (wla_in _ _ _ He) as Hin.
          unfold sample_bufs in Hin. apply filter_In in Hin. destruct Hin as [Hin _].
          intro Hno. apply (list_assoc_none_key _ _ Hno), in_map_iff.
          exists (x, e). split; [ reflexivity |].
          apply filter_In. split; [ exact Hin |].
          apply negb_true_iff, Nat.eqb_neq. lia. }
        (* the reference's validity at [ssk], for every bit up after the step *)
        assert (Hrk : forall m pi,
                  is_sample_of act (vreg_nid a_idx m) = false ->
                  (fst (sched_step act ssk (sched_input input ssk))).[tf_dfg_v a_idx m]
                    = Bits.ones 1 ->
                  eval1 (snd (compile_dfg_expr_at ctx bneeds pi
                                (length (graph (build_dfg ctx act))) a_idx
                                (build_dfg ctx act) (vreg_nid a_idx m)
                                (sample_bufs act a_idx)))
                    ssk (sched_input input ssk) = Bits.ones 1).
        { intros m pi Hsam Hx.
          destruct (vreg_nid_node_range act a_idx m Halign) as [Hn1 Hnlen].
          apply (compile_valid_path_mono act a_idx ssk (sched_input input ssk)
                   (sample_bufs act a_idx) _ _ [] pi ltac:(intros y [])).
          - apply (compile_subst_ref_valid_gen act a_idx ssk (sched_input input ssk)
                     Halign IHs IHr
                     (filter (fun '(b_nid, _) =>
                                negb (Nat.eqb b_nid (vreg_nid a_idx m)))
                        (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))).
            + intros e He. exact (proj1 (proj1 (filter_In _ e _) He)).
            + intros x Hx2. apply list_assoc_key_none. intro Hin.
              apply in_map_iff in Hin. destruct Hin as [[x' v'] [Hxx Hmem]].
              cbn [fst] in Hxx. subst x'.
              unfold sample_bufs in Hmem. apply filter_In in Hmem.
              destruct Hmem as [Hmem Hsx].
              destruct (Nat.eq_dec x (vreg_nid a_idx m)) as [-> | Hne];
                [ rewrite Hsx in Hsam; discriminate |].
              apply (list_assoc_none_key _ _ Hx2), in_map_iff.
              exists (x, v'). split; [ reflexivity |].
              apply filter_In. split; [ exact Hmem |].
              apply negb_true_iff, Nat.eqb_neq. exact Hne.
            + intros x q qsz Hx2 Hsx. apply list_assoc_nodup_in.
              * unfold sample_bufs. apply nodup_map_fst_filter.
                exact (slot_keys_nodup act a_idx Halign).
              * unfold sample_bufs. apply filter_In. split; [| exact Hsx ].
                exact (proj1 (proj1 (filter_In _ _ _) (wla_in _ _ _ Hx2))).
            + exact Hn1.
            + exact Hnlen.
            + exact Hnlen.
            + exact (Hgk m Hx). }
        (* a validity that fires at [ssk] fires after the step *)
        assert (Hstv : forall bufs,
                  (forall e, In e bufs ->
                     In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
                  forall fuel n pi,
                    n < length (graph (build_dfg ctx act)) ->
                    (forall x, x < n -> is_sample_of act x = true ->
                       BitsToLists.list_assoc bufs x <> None) ->
                    eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                                  (build_dfg ctx act) n bufs))
                      ssk (sched_input input ssk) = Bits.ones 1 ->
                    eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                                  (build_dfg ctx act) n bufs))
                      (sched_step act ssk (sched_input input ssk))
                      (sched_input input (sched_step act ssk (sched_input input ssk)))
                    = Bits.ones 1).
        { intros bufs Hsub.
          apply (compile_valid_state_indep_gen act a_idx (sched_input input ssk)
                   (sched_input input (sched_step act ssk (sched_input input ssk)))
                   ssk (sched_step act ssk (sched_input input ssk)) _ _ bufs Halign
                   ltac:(intro s; symmetry;
                         exact (sched_step_preserves_svar act ssk
                                  (sched_input input ssk) s Hnd))
                   ltac:(intro o; symmetry;
                         exact (sched_step_preserves_ovar act ssk
                                  (sched_input input ssk) o Hnd))
                   ltac:(intro v; reflexivity)
                   Hsub ltac:(intros m _ Hx; exact (Hfroz m Hx)) Hmono). }
        split; [| split ].
        * (* the gate is still up *)
          intros m Hv.
          destruct (vreg_nid_node_range act a_idx m Halign) as [Hn1 Hnlen].
          assert (Hgate' : eval1 (buf_gate act a_idx m)
                             (sched_step act ssk (sched_input input ssk))
                             (sched_input input
                                (sched_step act ssk (sched_input input ssk)))
                           = Bits.ones 1).
          { apply (Hstv (filter (fun '(b_nid, _) =>
                     negb (Nat.eqb b_nid (vreg_nid a_idx m)))
                     (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])));
              [ intros e He; exact (proj1 (proj1 (filter_In _ e _) He))
              | exact Hnlen | exact (Hrest m) | exact (Hgk m Hv) ]. }
          destruct (stall_lat_of act (vreg_nid a_idx m)) as [l |] eqn:Hst.
          -- destruct (stall_counter_wide act a_idx m l Halign Hst) as [_ Hwide].
             destruct (stall_valid_next_inv act a_idx m ssk (sched_input input ssk)
                         l _ Hst Hwide (Hnk m Hv)) as [_ Hreg].
             exact (stall_valid_next_ones act a_idx m
                      (sched_step act ssk (sched_input input ssk))
                      (sched_input input
                         (sched_step act ssk (sched_input input ssk)))
                      l _ Hst Hgate'
                      (stall_saturated_step act a_idx m ssk (sched_input input ssk)
                         l Halign Hnd Hst Hreg)).
          -- unfold buf_valid_expr. rewrite Hst. exact Hgate'.
        * (* the reference's validity is still up *)
          intros m pi Hv.
          destruct (vreg_nid_node_range act a_idx m Halign) as [_ Hnlen].
          destruct (is_sample_of act (vreg_nid a_idx m)) eqn:Hsam.
          -- (* a sample IS its own reference, and its bit is up *)
             rewrite (sample_ref_is_register act a_idx m Halign Hsam pi _ Hnlen).
             cbn [snd]. rewrite eval1_svar_v. exact Hv.
          -- apply (Hstv (sample_bufs act a_idx));
               [ intros e He; exact (proj1 (proj1 (filter_In _ e _) He))
               | exact Hnlen
               | intros x _ Hx; exact (sample_is_buffered act a_idx x Halign Hx)
               | exact (Hrk m pi Hsam Hv) ].
        * (* and the register still holds the reference's value *)
          intros m Hns Hv.
          destruct (vreg_nid_node_range act a_idx m Halign) as [Hn1 Hnlen].
          pose proof (buffer_after_cycle act a_idx m ssk (sched_input input ssk)
                        Halign Hnd) as Hba.
          cbv zeta in Hba. destruct Hba as [Hvalue _].
          unfold node_ref_expr.
          destruct (is_sample_of act (vreg_nid a_idx m)) eqn:Hsam.
          -- (* a sample IS its own reference *)
             rewrite (sample_ref_is_register act a_idx m Halign Hsam []
                        (length (graph (build_dfg ctx act))) Hnlen).
             cbn [fst]. rewrite eval_svar_same. reflexivity.
          -- rewrite Hvalue.
             change (fst (nth (index_to_nat m)
                            (nth (index_to_nat a_idx) bneeds []) (0, (0, 0))))
               with (vreg_nid a_idx m).
             unfold buf_value_expr. rewrite Hns, Hsam.
             rewrite (compile_nobuf_step_stable act a_idx ssk input Halign Hnd
                        (length (graph (build_dfg ctx act))) (vreg_nid a_idx m)
                        _ Hnlen (Hrk m [] Hsam Hv)).
             apply (compile_subst_valid act a_idx ssk (sched_input input ssk)
                      Halign IHs
                      (filter (fun '(b_nid, _) =>
                                 negb (Nat.eqb b_nid (vreg_nid a_idx m)))
                         (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))).
             ++ intros e He. exact (proj1 (proj1 (filter_In _ e _) He)).
             ++ intros x Hx2. apply list_assoc_key_none. intro Hin.
                apply in_map_iff in Hin. destruct Hin as [[x' v'] [Hxx Hmem]].
                cbn [fst] in Hxx. subst x'.
                unfold sample_bufs in Hmem. apply filter_In in Hmem.
                destruct Hmem as [Hmem Hsx].
                destruct (Nat.eq_dec x (vreg_nid a_idx m)) as [-> | Hne];
                  [ rewrite Hsx in Hsam; discriminate |].
                apply (list_assoc_none_key _ _ Hx2), in_map_iff.
                exists (x, v'). split; [ reflexivity |].
                apply filter_In. split; [ exact Hmem |].
                apply negb_true_iff, Nat.eqb_neq. exact Hne.
             ++ intros x q qsz Hx2 Hsx. apply list_assoc_nodup_in.
                ** unfold sample_bufs. apply nodup_map_fst_filter.
                   exact (slot_keys_nodup act a_idx Halign).
                ** unfold sample_bufs. apply filter_In. split; [| exact Hsx ].
                   exact (proj1 (proj1 (filter_In _ _ _) (wla_in _ _ _ Hx2))).
             ++ exact Hn1.
             ++ exact Hnlen.
             ++ exact Hnlen.
             ++ apply buffer_register_node_size. exact Halign.
             ++ pose proof (Hnk m Hv) as Hx.
                unfold buf_valid_expr in Hx. rewrite Hns in Hx. exact Hx.
  Qed.

  (* ==================================================================== *)
  (* Phase 3c: glue.                                                      *)
  (* ==================================================================== *)

  (* Reading the mapped-back state at a spec variable is reading its tf_dfg_s slot. *)
  Lemma getenv_maps_from (env: sched_st_env) (sv: s_var) :
    getenv ContextEnv (maps_from ctx bneeds env) sv = env.[tf_dfg_s sv].
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
    pose proof (dataflow_ops_fg (tfs_spec_action_ops ctx act) []
                  {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |}
                  Hempty Hemvsz Hemfg (fun x Hx => match Hx with end)) as Hop.
    destruct (dataflow_ops ctx [] (tfs_spec_action_ops ctx act)
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
        (ss: sched_sys_state) (input: sched_input_t) n :
    act_idx_aligned act a_idx ->
    done_set (sched_step act ss input) ->
    In n (map snd (var_map (build_dfg ctx act))) ->
    eval1 (snd (compile_dfg_expr ctx bneeds
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
    assert (Hstep : ~ done_set (sched_step act (run_n M act input ss0)
                      (sched_input input (run_n M act input ss0))))
      by (apply (Hnd (S M)); lia).
    change (run_n (S M) act input ss0)
      with (sched_step act (run_n M act input ss0)
              (sched_input input (run_n M act input ss0))).
    rewrite (sched_step_preserves_svar act _ _ sv Hstep).
    apply IH. intros i Hi. apply Hnd. lia.
  Qed.

  Lemma run_preserves_ovar (act: tfs_action sched) (input: input_t)
        (ss0: sched_sys_state) (M: nat) :
    (forall i, 1 <= i <= M -> ~ done_set (run_n i act input ss0)) ->
    forall ov, (snd (run_n M act input ss0)).[ov] = (snd ss0).[ov].
  Proof.
    induction M as [| M IH]; intros Hnd ov; [ reflexivity |].
    assert (Hstep : ~ done_set (sched_step act (run_n M act input ss0)
                      (sched_input input (run_n M act input ss0))))
      by (apply (Hnd (S M)); lia).
    change (run_n (S M) act input ss0)
      with (sched_step act (run_n M act input ss0)
              (sched_input input (run_n M act input ss0))).
    rewrite (sched_step_preserves_ovar act _ _ ov Hstep).
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

  (* Every member of [drive_nodes] is a drive on that port. *)
  Lemma drive_nodes_spec (act: tfs_action sched) (p: p_var) (n: nid_t) :
    In n (drive_nodes ctx (build_dfg ctx act) p) ->
    n < length (graph (build_dfg ctx act))
    /\ exists a en, node_op act n = DFG_Drive p a en.
  Proof.
    unfold drive_nodes.
    match goal with
    | |- In n (fold_left ?F _ _) -> _ =>
        assert (Hgen : forall g (acc: list nid_t),
                  In n (fold_left F g acc) ->
                  In n acc \/
                  exists nd, In nd g /\ nid nd = n /\
                             exists a en, op nd = DFG_Drive p a en)
    end.
    { intro g. induction g as [| nd g IH]; intros acc Hin; cbn [fold_left] in Hin.
      - left. exact Hin.
      - destruct (IH _ Hin) as [Hacc | [nd' [Hnd' [Hid Hop]]]].
        + destruct (op nd) eqn:Ho; try (left; exact Hacc).
          destruct (eq_dec p0 p) as [Heq | Hne]; [| left; exact Hacc].
          destruct Hacc as [Heqn | Hacc]; [| left; exact Hacc].
          right. exists nd. split; [ left; reflexivity |].
          split; [ exact Heqn |]. subst p0. eauto.
        + right. exists nd'. split; [ right; exact Hnd' |].
          split; [ exact Hid | exact Hop ]. }
    intro Hin.
    destruct (Hgen _ [] Hin) as [H0 | [nd [Hnd [Hid Hop]]]]; [ destruct H0 |].
    destruct (node_at_nid act nd Hnd) as [Hlt Hnth].
    rewrite Hid in Hlt, Hnth.
    split; [ exact Hlt |]. unfold node_op. rewrite Hnth. exact Hop.
  Qed.

  (* And every drive on the port is in it. *)
  Lemma drive_nodes_complete (act: tfs_action sched) (p: p_var) (n a: nid_t) en :
    n < length (graph (build_dfg ctx act)) ->
    node_op act n = DFG_Drive p a en ->
    In n (drive_nodes ctx (build_dfg ctx act) p).
  Proof.
    intros Hlt Hop. unfold drive_nodes.
    match goal with
    | |- In n (fold_left ?F _ _) =>
        assert (Hmono : forall g (acc: list nid_t) x, In x acc -> In x (fold_left F g acc));
        [ | assert (Hgen : forall g (acc: list nid_t) nd,
                      In nd g -> (exists b e, op nd = DFG_Drive p b e) ->
                      In (nid nd) (fold_left F g acc)) ]
    end.
    { intro g. induction g as [| nd g IH]; intros acc x Hx; cbn [fold_left]; [ exact Hx |].
      apply IH. destruct (op nd); try exact Hx.
      match goal with
      | |- context [ if ?X then _ else _ ] => destruct X
      end; [ right; exact Hx | exact Hx ]. }
    { intro g. induction g as [| nd0 g IH]; intros acc nd Hin Hop';
        cbn [fold_left]; [ destruct Hin |].
      destruct Hin as [-> | Hin]; [| apply IH; assumption ].
      apply Hmono. destruct Hop' as [b [e Ho]]. rewrite Ho.
      match goal with
      | |- context [ if ?X then _ else _ ] => destruct X as [_ | Hne]
      end; [ left; reflexivity | exfalso; apply Hne; reflexivity ]. }
    pose proof (node_nid_at act n Hlt) as Hnid.
    pose proof (Hgen (graph (build_dfg ctx act)) []
                  (nth n (graph (build_dfg ctx act))
                     {| nid := 0; op := DFG_Empty; sz := 0 |})
                  (nth_In _ _ Hlt)
                  ltac:(exists a, en; exact Hop)) as Hres.
    rewrite Hnid in Hres. exact Hres.
  Qed.

  (* A sample.s own drive is one of the port.s drives. *)
  Lemma sample_drive_in_drive_nodes (act: tfs_action sched) n d p tok en :
    node_op act n = DFG_Sample p tok en ->
    sample_drive act n = Some d ->
    In d (drive_nodes ctx (build_dfg ctx act) p).
  Proof.
    intros Hn Hd.
    destruct (sample_drive_op act n d p tok en Hn Hd) as [a [en' Hop]].
    apply (drive_nodes_complete act p d a en').
    - apply node_op_range. rewrite Hop. discriminate.
    - exact Hop.
  Qed.

  (* THE JOIN, as the port argument reads it: it waits on a SAMPLE of the
     drive.s own port, under a guard the drive could share. *)
  Lemma join_waits_on_sample (act: tfs_action sched) (j d prev: nid_t) :
    node_op act j = DFG_Join d prev ->
    exists (p: p_var) arg en tok en',
      node_op act d = DFG_Drive p arg en
      /\ node_op act prev = DFG_Sample p tok en'
      /\ guards_disjoint en en' = false.
  Proof.
    intro Hop.
    assert (Hlt : j < length (graph (build_dfg ctx act)))
      by (apply node_op_range; rewrite Hop; discriminate).
    destruct (joins_sequence_build_dfg act
                (nth j (graph (build_dfg ctx act))
                   {| nid := 0; op := DFG_Empty; sz := 0 |}) d prev
                (nth_In _ _ Hlt) Hop)
      as [p [arg [en [tok [en' [nd [ns [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]]]]]]]].
    exists p, arg, en, tok, en'.
    destruct (node_at_nid act nd H1) as [_ Hnth1].
    destruct (node_at_nid act ns H4) as [_ Hnth4].
    rewrite H2 in Hnth1. rewrite H5 in Hnth4.
    unfold node_op. rewrite Hnth1, Hnth4.
    split; [ exact H3 | split; [ exact H6 | exact H7 ] ].
  Qed.

  (* A join and a stall both sit at their argument.s successor, so a drive
     that has an ordering join cannot also carry a stall of its own. *)
  Lemma join_nid_succ (act: tfs_action sched) j d prev :
    node_op act j = DFG_Join d prev -> j = S d.
  Proof.
    intro Hop.
    assert (Hlt : j < length (graph (build_dfg ctx act)))
      by (apply node_op_range; rewrite Hop; discriminate).
    pose proof (succ_args_build_dfg act
                  (nth j (graph (build_dfg ctx act))
                     {| nid := 0; op := DFG_Empty; sz := 0 |})
                  (nth_In _ _ Hlt)) as [Hj _].
    rewrite (node_nid_at act j Hlt) in Hj.
    exact (Hj d prev Hop).
  Qed.

  Lemma stall_nid_succ (act: tfs_action sched) t l a :
    node_op act t = DFG_Stall l a -> t = S a.
  Proof.
    intro Hop.
    assert (Hlt : t < length (graph (build_dfg ctx act)))
      by (apply node_op_range; rewrite Hop; discriminate).
    pose proof (succ_args_build_dfg act
                  (nth t (graph (build_dfg ctx act))
                     {| nid := 0; op := DFG_Empty; sz := 0 |})
                  (nth_In _ _ Hlt)) as [_ Hs].
    rewrite (node_nid_at act t Hlt) in Hs.
    exact (Hs l a Hop).
  Qed.

  Lemma no_stall_on_joined (act: tfs_action sched) j d prev t l :
    node_op act j = DFG_Join d prev -> node_op act t = DFG_Stall l d -> False.
  Proof.
    intros Hj Ht.
    pose proof (join_nid_succ act j d prev Hj) as Hjn.
    pose proof (stall_nid_succ act t l d Ht) as Htn.
    subst j. subst t. rewrite Hj in Ht. discriminate Ht.
  Qed.

  (* So a drive that HAS an ordering join has that join as its chain gate:
     [chain_gate] only looks for a stall on the drive first, and there is none. *)
  Lemma chain_gate_is_join (act: tfs_action sched) (d j prev g h: nid_t) :
    node_op act j = DFG_Join d prev ->
    chain_gate ctx (build_dfg ctx act) d = Some (g, h) ->
    exists prev', node_op act g = DFG_Join d prev'.
  Proof.
    intros Hj Hcg. unfold chain_gate in Hcg. cbv zeta in Hcg.
    destruct (find (fun nd => match op nd with
                              | DFG_Stall _ a => Nat.eqb a d
                              | _ => false
                              end) (graph (build_dfg ctx act))) as [nd |] eqn:Ef1.
    - exfalso. apply find_some in Ef1. destruct Ef1 as [Hin Hp]. cbv beta in Hp.
      destruct (op nd) as [ c | iv | v2 | uop a | bop a1 a2 | a | cd t e
                          | slat sa | dov dn den | siv sn sen | ja jb | ] eqn:Eo;
        try discriminate Hp.
      apply Nat.eqb_eq in Hp. subst sa.
      destruct (node_at_nid act nd Hin) as [_ Hnth].
      apply (no_stall_on_joined act j d prev (nid nd) slat Hj).
      unfold node_op. rewrite Hnth. exact Eo.
    - destruct (find (fun nd => match op nd with
                                | DFG_Join a _ => Nat.eqb a d
                                | _ => false
                                end) (graph (build_dfg ctx act))) as [j2 |] eqn:Ef2;
        [| discriminate Hcg ].
      destruct (find (fun nd => match op nd with
                                | DFG_Stall _ a => Nat.eqb a (nid j2)
                                | _ => false
                                end) (graph (build_dfg ctx act))) as [nd2 |] eqn:Ef3;
        [| discriminate Hcg ].
      injection Hcg as Hg Hh.
      apply find_some in Ef2. destruct Ef2 as [Hin2 Hp2]. cbv beta in Hp2.
      destruct (op j2) as [ c | iv | v2 | uop a | bop a1 a2 | a | cd t e
                          | slat sa | dov dn den | siv sn sen | ja jb | ] eqn:Eo2;
        try discriminate Hp2.
      apply Nat.eqb_eq in Hp2. subst ja.
      destruct (node_at_nid act j2 Hin2) as [_ Hnth2].
      exists jb. unfold node_op. rewrite <- Hg. rewrite Hnth2. exact Eo2.
  Qed.

  Lemma join_has_stall (act: tfs_action sched) j d prev :
    node_op act j = DFG_Join d prev ->
    exists t l, node_op act t = DFG_Stall l j.
  Proof.
    intro Hop.
    assert (Hlt : j < length (graph (build_dfg ctx act)))
      by (apply node_op_range; rewrite Hop; discriminate).
    destruct (joins_stalled_build_dfg act
                (nth j (graph (build_dfg ctx act))
                   {| nid := 0; op := DFG_Empty; sz := 0 |})
                d prev (nth_In _ _ Hlt) Hop) as [t [l [Ht Htop]]].
    rewrite (node_nid_at act j Hlt) in Htop.
    destruct (node_at_nid act t Ht) as [_ Hnth].
    exists (nid t), l. unfold node_op. rewrite Hnth. exact Htop.
  Qed.

  (* With [ip_lat_pos] every join carries a stall, so a drive that has a join
     has a chain gate at all -- which is what the port argument assumed. *)
  Lemma chain_gate_some (act: tfs_action sched) m j prev :
    node_op act j = DFG_Join m prev ->
    exists g h, chain_gate ctx (build_dfg ctx act) m = Some (g, h).
  Proof.
    intro Hj. unfold chain_gate. cbv zeta.
    destruct (find (fun nd => match op nd with
                              | DFG_Stall _ a => Nat.eqb a m
                              | _ => false
                              end) (graph (build_dfg ctx act))) as [nd |] eqn:Ef1;
      [ exists m, (nid nd); reflexivity |].
    destruct (find (fun nd => match op nd with
                              | DFG_Join a _ => Nat.eqb a m
                              | _ => false
                              end) (graph (build_dfg ctx act))) as [j2 |] eqn:Ef2.
    - apply find_some in Ef2. destruct Ef2 as [Hin2 Hp2]. cbv beta in Hp2.
      destruct (op j2) as [ c | iv | v2 | uop a1 | bop a1 a2 | a1 | cd t1 e1
                          | slat sa | dov dn den | siv sn sen | ja jb | ] eqn:Eo2;
        try discriminate Hp2.
      apply Nat.eqb_eq in Hp2. subst ja.
      destruct (node_at_nid act j2 Hin2) as [_ Hnth2].
      assert (Hj2 : node_op act (nid j2) = DFG_Join m jb)
        by (unfold node_op; rewrite Hnth2; exact Eo2).
      destruct (join_has_stall act (nid j2) m jb Hj2) as [t [l Ht]].
      destruct (find (fun nd => match op nd with
                                | DFG_Stall _ a => Nat.eqb a (nid j2)
                                | _ => false
                                end) (graph (build_dfg ctx act))) as [nd2 |] eqn:Ef3;
        [ exists (nid j2), (nid nd2); reflexivity |].
      exfalso.
      assert (Htlt : t < length (graph (build_dfg ctx act)))
        by (apply node_op_range; rewrite Ht; discriminate).
      pose proof (find_none _ _ Ef3
                    (nth t (graph (build_dfg ctx act))
                       {| nid := 0; op := DFG_Empty; sz := 0 |})
                    (nth_In _ _ Htlt)) as Hn. cbv beta in Hn.
      unfold node_op in Ht. rewrite Ht in Hn. rewrite Nat.eqb_refl in Hn.
      discriminate Hn.
    - exfalso.
      assert (Hjlt : j < length (graph (build_dfg ctx act)))
        by (apply node_op_range; rewrite Hj; discriminate).
      pose proof (find_none _ _ Ef2
                    (nth j (graph (build_dfg ctx act))
                       {| nid := 0; op := DFG_Empty; sz := 0 |})
                    (nth_In _ _ Hjlt)) as Hn. cbv beta in Hn.
      unfold node_op in Hj. rewrite Hj in Hn. rewrite Nat.eqb_refl in Hn.
      discriminate Hn.
  Qed.

  Lemma sample_nid_succ (act: tfs_action sched) s (p: p_var) tok en :
    node_op act s = DFG_Sample p tok en -> s = S tok.
  Proof.
    intro Hop.
    assert (Hlt : s < length (graph (build_dfg ctx act)))
      by (apply node_op_range; rewrite Hop; discriminate).
    pose proof (ssucc_build_dfg act
                  (nth s (graph (build_dfg ctx act))
                     {| nid := 0; op := DFG_Empty; sz := 0 |})
                  (nth_In _ _ Hlt)) as Hss.
    pose proof (Hss p tok en Hop) as H.
    rewrite (node_nid_at act s Hlt) in H. exact H.
  Qed.

  (* What [sample_drive] stopped at: the drive itself, or the join above it. *)
  Lemma sample_drive_head_shape (act: tfs_action sched) (p: p_var) h d :
    sample_drive_head act p h = Some d ->
    (d = h /\ exists arg en, node_op act h = DFG_Drive p arg en)
    \/ (exists prev, node_op act h = DFG_Join d prev).
  Proof.
    unfold sample_drive_head.
    destruct (node_op act h) as [ c | iv | v2 | uop a1 | bop a1 a2 | a1 | cd t1 e1
                               | slat sa | dov dn den | siv sn sen | ja jb | ] eqn:Eh;
      try discriminate.
    - destruct ((tfs_spec_ips_eq_dec ctx).(eq_dec) dov p) as [-> | Hne];
        [| discriminate ].
      intro H. injection H as <-. left. split; [ reflexivity | exists dn, den; reflexivity ].
    - destruct (node_op act ja) as [ | | | | | | | | dov dn den | | | ] eqn:Ea;
        try discriminate.
      destruct ((tfs_spec_ips_eq_dec ctx).(eq_dec) dov p) as [-> | Hne];
        [| discriminate ].
      intro H. injection H as <-. right. exists jb. reflexivity.
  Qed.

  (* What sits strictly between a call.s drive and its sample: its ordering
     join and its stall, and nothing else. *)
  Lemma sample_chain_between (act: tfs_action sched) samp (p: p_var) tok en d i :
    node_op act samp = DFG_Sample p tok en ->
    sample_drive act samp = Some d ->
    d < i -> i < samp ->
    (exists l a, node_op act i = DFG_Stall l a)
    \/ (exists a b, node_op act i = DFG_Join a b).
  Proof.
    intros Hsamp Hsd Hdi His.
    pose proof (sample_nid_succ act samp p tok en Hsamp) as Hsm.
    unfold sample_drive in Hsd. rewrite Hsamp in Hsd.
    destruct (node_op act tok) as [ c | iv | v2 | uop a1 | bop a1 a2 | a1 | cd t1 e1
                                 | slat sa | dov dn den | siv sn sen | ja jb | ] eqn:Etok;
      try (destruct (sample_drive_head_shape act p tok d Hsd)
             as [[Hdh [ar [e2 Hh]]] | [prev Hh]];
           [ lia
           | pose proof (join_nid_succ act tok d prev Hh) as Ht;
             assert (i = tok) as -> by lia; right; exists d, prev; exact Hh ]).
    pose proof (stall_nid_succ act tok slat sa Etok) as Ht.
    destruct (sample_drive_head_shape act p sa d Hsd)
      as [[Hdh [ar [e2 Hh]]] | [prev Hh]].
    - assert (i = tok) as -> by lia. left. exists slat, sa. exact Etok.
    - pose proof (join_nid_succ act sa d prev Hh) as Hsa.
      assert (i = sa \/ i = tok) as [-> | ->] by lia;
        [ right; exists d, prev; exact Hh | left; exists slat, sa; exact Etok ].
  Qed.

  Lemma sample_drive_lt (act: tfs_action sched) samp (p: p_var) tok en d :
    node_op act samp = DFG_Sample p tok en ->
    sample_drive act samp = Some d -> d < samp.
  Proof.
    intros Hsamp Hsd.
    pose proof (sample_nid_succ act samp p tok en Hsamp) as Hsm.
    unfold sample_drive in Hsd. rewrite Hsamp in Hsd.
    destruct (node_op act tok) as [ c | iv | v2 | uop a1 | bop a1 a2 | a1 | cd t1 e1
                                 | slat sa | dov dn den | siv sn sen | ja jb | ] eqn:Etok;
      try (destruct (sample_drive_head_shape act p tok d Hsd)
             as [[Hdh [ar [e2 Hh]]] | [prev Hh]];
           [ lia
           | pose proof (join_nid_succ act tok d prev Hh) as Ht; lia ]).
    pose proof (stall_nid_succ act tok slat sa Etok) as Ht.
    destruct (sample_drive_head_shape act p sa d Hsd)
      as [[Hdh [ar [e2 Hh]]] | [prev Hh]]; [ lia |].
    pose proof (join_nid_succ act sa d prev Hh) as Hsa. lia.
  Qed.

  (* Nothing strictly between a call.s drive and its sample is a drive: the
     indices in between are its join and its stall. *)
  Lemma sample_chain_no_drive (act: tfs_action sched) samp (p: p_var) tok en d i :
    node_op act samp = DFG_Sample p tok en ->
    sample_drive act samp = Some d ->
    d < i -> i < samp ->
    forall q a e, node_op act i <> DFG_Drive q a e.
  Proof.
    intros Hsamp Hsd Hdi His q a e Hi.
    destruct (sample_chain_between act samp p tok en d i Hsamp Hsd Hdi His)
      as [[l [b Hb]] | [b1 [b2 Hb]]]; rewrite Hi in Hb; discriminate Hb.
  Qed.

  Lemma sample_chain_no_sample (act: tfs_action sched) samp (p: p_var) tok en d i :
    node_op act samp = DFG_Sample p tok en ->
    sample_drive act samp = Some d ->
    d < i -> i < samp ->
    forall q t2 e2, node_op act i <> DFG_Sample q t2 e2.
  Proof.
    intros Hsamp Hsd Hdi His q t2 e2 Hi.
    destruct (sample_chain_between act samp p tok en d i Hsamp Hsd Hdi His)
      as [[l [b Hb]] | [b1 [b2 Hb]]]; rewrite Hi in Hb; discriminate Hb.
  Qed.

  (* Two samples in program order: the later one.s call starts after the
     earlier sample, since nothing between a drive and its sample is one. *)
  Lemma sample_before_drive (act: tfs_action sched) (p q: p_var)
        samp tok en prev tok2 en2 d2 :
    node_op act samp = DFG_Sample p tok en ->
    node_op act prev = DFG_Sample q tok2 en2 ->
    sample_drive act prev = Some d2 ->
    samp < prev -> samp < d2.
  Proof.
    intros Hsamp Hprev Hsd2 Hlt.
    destruct (Nat.lt_ge_cases samp d2) as [Hok | Hge]; [ exact Hok |].
    exfalso.
    destruct (Nat.eq_dec samp d2) as [Heq | Hne].
    - destruct (sample_drive_op act prev d2 q tok2 en2 Hprev Hsd2) as [ar [e2 Hd2op]].
      rewrite Heq in Hsamp. congruence.
    - exact (sample_chain_no_sample act prev q tok2 en2 d2 samp Hprev Hsd2
               ltac:(lia) Hlt p tok en Hsamp).
  Qed.

  (* So a drive emitted after the call.s drive is emitted after its SAMPLE. *)
  Lemma drive_after_sample (act: tfs_action sched) (p: p_var) samp tok en d m q a e :
    node_op act samp = DFG_Sample p tok en ->
    sample_drive act samp = Some d ->
    node_op act m = DFG_Drive q a e ->
    d < m -> samp < m.
  Proof.
    intros Hsamp Hsd Hm Hlt.
    destruct (Nat.lt_ge_cases samp m) as [Hok | Hge]; [ exact Hok |].
    exfalso.
    destruct (Nat.eq_dec m samp) as [-> | Hne].
    - rewrite Hsamp in Hm. discriminate Hm.
    - exact (sample_chain_no_drive act samp p tok en d m Hsamp Hsd Hlt
               ltac:(lia) q a e Hm).
  Qed.

  (* THE SEQUENCING FACT, as the port argument reads it: a call that could see
     an earlier call.s answer on the same port is held behind it by a join. *)
  Lemma call_sequenced_join (act: tfs_action sched) (p: p_var) m arg en s tok en' :
    node_op act m = DFG_Drive p arg en ->
    node_op act s = DFG_Sample p tok en' ->
    s < m -> guards_disjoint en en' = false ->
    exists j prev, node_op act j = DFG_Join m prev /\ s <= prev.
  Proof.
    intros Hm Hs Hlt Hdis.
    assert (Hmlt : m < length (graph (build_dfg ctx act)))
      by (apply node_op_range; rewrite Hm; discriminate).
    assert (Hslt : s < length (graph (build_dfg ctx act)))
      by (apply node_op_range; rewrite Hs; discriminate).
    destruct (calls_main_build_dfg act p m arg en s tok en'
                (ex_intro _ _ (conj (nth_In _ _ Hmlt)
                                 (conj (node_nid_at act m Hmlt) Hm)))
                (ex_intro _ _ (conj (nth_In _ _ Hslt)
                                 (conj (node_nid_at act s Hslt) Hs))) Hlt Hdis)
      as [j [prev [Hj [Hjop Hle]]]].
    exists (nid j), prev.
    destruct (node_at_nid act j Hj) as [_ Hnth].
    split; [ unfold node_op; rewrite Hnth; exact Hjop | exact Hle ].
  Qed.

  (* ASSEMBLY: the chain gate of a drive emitted after this call.s sample is
     the ordering join, and that join waits on a sample at or after it. *)
  Lemma later_drive_gate
        (act: tfs_action sched) (p: p_var) samp tok en_s d m arg_m en_m g h :
    node_op act samp = DFG_Sample p tok en_s ->
    sample_drive act samp = Some d ->
    node_op act m = DFG_Drive p arg_m en_m ->
    d < m -> guards_disjoint en_m en_s = false ->
    chain_gate ctx (build_dfg ctx act) m = Some (g, h) ->
    exists prev,
      node_op act g = DFG_Join m prev
      /\ samp <= prev
      /\ exists q tok' en'', node_op act prev = DFG_Sample q tok' en''.
  Proof.
    intros Hsamp Hsd Hm Hlt Hdis Hcg.
    pose proof (drive_after_sample act p samp tok en_s d m p arg_m en_m
                  Hsamp Hsd Hm Hlt) as Hsm.
    destruct (call_sequenced_join act p m arg_m en_m samp tok en_s Hm Hsamp Hsm Hdis)
      as [j [prev [Hj Hle]]].
    destruct (chain_gate_is_join act m j prev g h Hj Hcg) as [prev' Hg].
    pose proof (join_nid_succ act j m prev Hj) as Hjn.
    pose proof (join_nid_succ act g m prev' Hg) as Hgn.
    assert (Hgj : g = j) by lia.
    assert (Hpp : prev' = prev) by congruence.
    subst prev'.
    exists prev. split; [ exact Hg | split; [ exact Hle |]].
    destruct (join_waits_on_sample act g m prev Hg)
      as [q [arg2 [en2 [tok2 [en3 [_ [Hps _]]]]]]].
    exists q, tok2, en3. exact Hps.
  Qed.

  (* And the same with no [chain_gate] hypothesis: it is [Some] because the
     join carries a stall. *)
  Lemma later_drive_gate_full
        (act: tfs_action sched) (p: p_var) samp tok en_s d m arg_m en_m :
    node_op act samp = DFG_Sample p tok en_s ->
    sample_drive act samp = Some d ->
    node_op act m = DFG_Drive p arg_m en_m ->
    d < m -> guards_disjoint en_m en_s = false ->
    exists g h prev,
      chain_gate ctx (build_dfg ctx act) m = Some (g, h)
      /\ node_op act g = DFG_Join m prev
      /\ samp <= prev
      /\ exists q tok' en'', node_op act prev = DFG_Sample q tok' en''.
  Proof.
    intros Hsamp Hsd Hm Hlt Hdis.
    pose proof (drive_after_sample act p samp tok en_s d m p arg_m en_m
                  Hsamp Hsd Hm Hlt) as Hsm.
    destruct (call_sequenced_join act p m arg_m en_m samp tok en_s Hm Hsamp Hsm Hdis)
      as [j [prev0 [Hj _]]].
    destruct (chain_gate_some act m j prev0 Hj) as [g [h Hcg]].
    destruct (later_drive_gate act p samp tok en_s d m arg_m en_m g h
                Hsamp Hsd Hm Hlt Hdis Hcg) as [prev [Hg [Hle Hps]]].
    exists g, h, prev. split; [ exact Hcg | split; [ exact Hg | split; [ exact Hle | exact Hps ] ] ].
  Qed.

  (* Strictly decreasing, as [drive_nodes] produces it. *)
  Inductive Desc : list nid_t -> Prop :=
  | Desc_nil : Desc []
  | Desc_cons : forall x l, Forall (fun y => y < x) l -> Desc l -> Desc (x :: l).

  (* The fold conses in graph order and a node.s id is its index, so the drives
     EMITTED LATER come first. *)
  Lemma drive_nodes_desc (act: tfs_action sched) (p: p_var) :
    Desc (drive_nodes ctx (build_dfg ctx act) p).
  Proof.
    unfold drive_nodes.
    match goal with
    | |- Desc (fold_left ?F _ _) =>
        assert (Hgen : forall (g: list dfg_node_t) (base: nat) (acc: list nid_t),
                  (forall i, i < length g ->
                     nid (nth i g {| nid := 0; op := DFG_Empty; sz := 0 |}) = base + i) ->
                  Desc acc ->
                  (forall m, In m acc -> m < base) ->
                  Desc (fold_left F g acc)
                  /\ (forall m, In m (fold_left F g acc) -> m < base + length g))
    end.
    { intro g. induction g as [| nd g IH]; intros base acc Hidx Hd Hlt.
      - cbn [fold_left length]. split; [ exact Hd |].
        intros m Hm. rewrite Nat.add_0_r. exact (Hlt m Hm).
      - assert (Hnd : nid nd = base).
        { specialize (Hidx 0 ltac:(cbn; lia)). cbn in Hidx. lia. }
        assert (Hidx' : forall i, i < length g ->
                  nid (nth i g {| nid := 0; op := DFG_Empty; sz := 0 |}) = S base + i).
        { intros i Hi. specialize (Hidx (S i) ltac:(cbn; lia)). cbn in Hidx. lia. }
        cbn [fold_left].
        match goal with
        | |- Desc (fold_left _ g ?A) /\ _ =>
            assert (HA : Desc A /\ (forall m, In m A -> m < S base))
        end.
        { destruct (op nd) eqn:Ho;
            try (split; [ exact Hd | intros m Hm; specialize (Hlt m Hm); lia ]).
          match goal with
          | |- context [ if ?X then _ else _ ] => destruct X
          end.
          - split.
            + constructor; [| exact Hd ]. apply Forall_forall. intros y Hy.
              rewrite Hnd. exact (Hlt y Hy).
            + intros m Hm. destruct Hm as [<- | Hm];
                [ lia | specialize (Hlt m Hm); lia ].
          - split; [ exact Hd | intros m Hm; specialize (Hlt m Hm); lia ]. }
        destruct HA as [HA1 HA2].
        destruct (IH (S base) _ Hidx' HA1 HA2) as [H1 H2].
        split; [ exact H1 |].
        intros m Hm. specialize (H2 m Hm). cbn [length]. lia. }
    refine (proj1 (Hgen (graph (build_dfg ctx act)) 0 [] _ Desc_nil _)).
    - intros i Hi. cbn [Nat.add]. exact (node_nid_at act i Hi).
    - intros m Hm. destruct Hm.
  Qed.

  Lemma desc_split (l: list nid_t) :
    Desc l -> forall pre n post, l = pre ++ n :: post -> forall m, In m pre -> n < m.
  Proof.
    intro Hd. induction Hd as [| x l Hall Hd IH]; intros pre n post Heq m Hm.
    - destruct pre; discriminate Heq.
    - destruct pre as [| a pre]; cbn [app] in Heq.
      + destruct Hm.
      + injection Heq as Hax Hl. subst x.
        destruct Hm as [<- | Hm].
        * rewrite Forall_forall in Hall. apply Hall. rewrite Hl.
          apply in_or_app. right. left. reflexivity.
        * exact (IH pre n post Hl m Hm).
  Qed.

  Lemma drive_nodes_split (act: tfs_action sched) (p: p_var) (n: nid_t) :
    In n (drive_nodes ctx (build_dfg ctx act) p) ->
    exists pre post,
      drive_nodes ctx (build_dfg ctx act) p = pre ++ n :: post
      /\ forall m, In m pre -> n < m.
  Proof.
    intro Hin. destruct (in_split _ _ Hin) as [pre [post Heq]].
    exists pre, post. split; [ exact Heq |].
    exact (desc_split _ (drive_nodes_desc act p) pre n post Heq).
  Qed.

  (* THE PORT CARRIES THIS CALL.S REQUEST.  [drive_nodes] is decreasing, so the
     only drives that can take the wire from [n] are those emitted AFTER it --
     which is exactly what the ordering join is there to hold back. *)
  Lemma drive_payload_take_later
        (act: tfs_action sched)
        (a_idx : Vect.index (length (buffer_needs ctx cost_limit))) (p: p_var)
        (n: nid_t) (ss: sched_sys_state) (input: sched_input_t) :
    act_idx_aligned act a_idx ->
    ~ done_set (sched_step act ss input) ->
    In n (drive_nodes ctx (build_dfg ctx act) p) ->
    (forall m, In m (drive_nodes ctx (build_dfg ctx act) p) -> n < m ->
       eval1 (drive_pulse act a_idx m) ss input = Bits.zero) ->
    eval1 (drive_pulse act a_idx n) ss input <> Bits.zero ->
    drive_payload (sched_step act ss input) p
    = tf_eval_expr ss_sz si_sz oo_sz (szB := ip_req_sz (tfs_spec_ip ctx p))
        (fst (compile_dfg_expr ctx bneeds (length (graph (build_dfg ctx act))) a_idx
                (build_dfg ctx act) n
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))) ss input.
  Proof.
    intros Halign Hnd Hin Hlater Hn.
    destruct (drive_nodes_split act p n Hin) as [pre [post [Heq Hgt]]].
    apply (drive_payload_take act a_idx p pre post n ss input Halign Hnd Heq);
      [| exact Hn ].
    intros m Hm. apply (Hlater m).
    - rewrite Heq. apply in_or_app. left. exact Hm.
    - exact (Hgt m Hm).
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
    fst (compile_dfg_expr ctx bneeds f a_idx (build_dfg ctx act) x (sample_bufs act a_idx))
    = node_ref_expr act a_idx x.
  Proof.
    intros H1 H2 H3. unfold node_ref_expr.
    rewrite (compile_fuel_irrel act a_idx (sample_bufs act a_idx) x H1 H2 f
               (length (graph (build_dfg ctx act))) H3 H2).
    reflexivity.
  Qed.

  (* [sample_bufs] keeps exactly the samples, so anything else is absent. *)
  Lemma not_sample_not_in_sample_bufs (act: tfs_action sched) a_idx n :
    is_sample_of act n = false ->
    BitsToLists.list_assoc (sample_bufs act a_idx) n = None.
  Proof.
    intro Hs. apply list_assoc_key_none. intro Hin.
    apply in_map_iff in Hin. destruct Hin as [[x v] [Hx Hmem]].
    cbn [fst] in Hx. subst x.
    unfold sample_bufs in Hmem. apply filter_In in Hmem.
    destruct Hmem as [_ H]. rewrite Hs in H. discriminate.
  Qed.

  Lemma nre_unfold (act: tfs_action sched) a_idx n :
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    node_ref_expr act a_idx n
    = fst (compile_dfg_expr ctx bneeds (S n) a_idx (build_dfg ctx act) n (sample_bufs act a_idx)).
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
    cbn [compile_dfg_expr_aux].
    rewrite (not_sample_not_in_sample_bufs act a_idx n
              ltac:(unfold is_sample_of, node_op; rewrite Hop; reflexivity)).
    cbv beta iota. rewrite Hop. reflexivity.
  Qed.

  Lemma nre_input (act: tfs_action sched) a_idx n v :
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    op (nth n (graph (build_dfg ctx act))
          {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Input v ->
    node_ref_expr act a_idx n = tf_ivar (inl v).
  Proof.
    intros H1 H2 Hop. rewrite (nre_unfold act a_idx n H1 H2).
    cbn [compile_dfg_expr_aux].
    rewrite (not_sample_not_in_sample_bufs act a_idx n
              ltac:(unfold is_sample_of, node_op; rewrite Hop; reflexivity)).
    cbv beta iota. rewrite Hop. reflexivity.
  Qed.

  Lemma nre_svar (act: tfs_action sched) a_idx n sv :
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    op (nth n (graph (build_dfg ctx act))
          {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Var (DFG_SVar sv) ->
    node_ref_expr act a_idx n = tf_svar (tf_dfg_s sv).
  Proof.
    intros H1 H2 Hop. rewrite (nre_unfold act a_idx n H1 H2).
    cbn [compile_dfg_expr_aux].
    rewrite (not_sample_not_in_sample_bufs act a_idx n
              ltac:(unfold is_sample_of, node_op; rewrite Hop; reflexivity)).
    cbv beta iota. rewrite Hop. reflexivity.
  Qed.

  Lemma nre_ovar (act: tfs_action sched) a_idx n ov :
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    op (nth n (graph (build_dfg ctx act))
          {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Var (DFG_OVar ov) ->
    node_ref_expr act a_idx n = tf_ovar ov.
  Proof.
    intros H1 H2 Hop. rewrite (nre_unfold act a_idx n H1 H2).
    cbn [compile_dfg_expr_aux].
    rewrite (not_sample_not_in_sample_bufs act a_idx n
              ltac:(unfold is_sample_of, node_op; rewrite Hop; reflexivity)).
    cbv beta iota. rewrite Hop. reflexivity.
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
    cbn [compile_dfg_expr_aux].
    rewrite (not_sample_not_in_sample_bufs act a_idx n
              ltac:(unfold is_sample_of, node_op; rewrite Hop; reflexivity)).
    cbv beta iota. rewrite Hop.
    destruct (compile_dfg_expr ctx bneeds n a_idx (build_dfg ctx act) arg (sample_bufs act a_idx))
      as [ae av] eqn:E.
    cbn [fst]. f_equal.
    rewrite <- (nre_fuel act a_idx arg n Ha1 Ha2 Ha3), E. reflexivity.
  Qed.

  (* A stall carries NO value: the answer arrives at the sample, and the wait
     is the counter [compile_dfg_buffers] keeps. *)
  Lemma nre_stall (act: tfs_action sched) a_idx n lat arg :
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    op (nth n (graph (build_dfg ctx act))
          {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Stall lat arg ->
    node_ref_expr act a_idx n = tf_const 0.
  Proof.
    intros H1 H2 Hop.
    rewrite (nre_unfold act a_idx n H1 H2).
    cbn [compile_dfg_expr_aux].
    rewrite (not_sample_not_in_sample_bufs act a_idx n
              ltac:(unfold is_sample_of, node_op; rewrite Hop; reflexivity)).
    cbv beta iota. rewrite Hop.
    destruct (compile_dfg_expr ctx bneeds n a_idx (build_dfg ctx act) arg
                (sample_bufs act a_idx)).
    reflexivity.
  Qed.

  (* SPIKE 2b.  A drive's reference expression is its argument's -- it is the
     message on its way to the port, so it adds no logic. *)
  Lemma nre_drive (act: tfs_action sched) a_idx n p arg en :
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    op (nth n (graph (build_dfg ctx act))
          {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Drive p arg en ->
    node_ref_expr act a_idx n = node_ref_expr act a_idx arg.
  Proof.
    intros H1 H2 Hop.
    assert (Hain : In arg (get_args ctx (nth n (graph (build_dfg ctx act))
                                           {| nid := 0; op := DFG_Empty; sz := 0 |})))
      by (unfold get_args; rewrite Hop; left; reflexivity).
    destruct (node_args_range act n H1 H2 arg Hain) as [Ha1 Ha3].
    assert (Ha2 : arg < length (graph (build_dfg ctx act))) by lia.
    rewrite (nre_unfold act a_idx n H1 H2).
    cbn [compile_dfg_expr_aux].
    rewrite (not_sample_not_in_sample_bufs act a_idx n
              ltac:(unfold is_sample_of, node_op; rewrite Hop; reflexivity)).
    cbv beta iota. rewrite Hop.
    destruct (compile_dfg_expr ctx bneeds n a_idx (build_dfg ctx act) arg (sample_bufs act a_idx))
      as [ae av] eqn:E.
    cbn [fst].
    rewrite <- (nre_fuel act a_idx arg n Ha1 Ha2 Ha3), E. reflexivity.
  Qed.

  (* A sample's reference expression is its REGISTER, not the port: the table
     keeps every sample, so the recursion stops at the slot.  The port carries
     an answer only until the next call on it, which is why. *)
  Lemma nre_sample (act: tfs_action sched) a_idx n_idx :
    act_idx_aligned act a_idx ->
    is_sample_of act (vreg_nid a_idx n_idx) = true ->
    node_ref_expr act a_idx (vreg_nid a_idx n_idx)
    = tf_svar (tf_dfg_b a_idx n_idx).
  Proof.
    intros Halign Hsam.
    destruct (vreg_nid_node_range act a_idx n_idx Halign) as [_ Hnlen].
    unfold node_ref_expr.
    rewrite (sample_ref_is_register act a_idx n_idx Halign Hsam []
               (length (graph (build_dfg ctx act))) Hnlen).
    reflexivity.
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
    cbn [compile_dfg_expr_aux].
    rewrite (not_sample_not_in_sample_bufs act a_idx n
              ltac:(unfold is_sample_of, node_op; rewrite Hop; reflexivity)).
    cbv beta iota. rewrite Hop.
    destruct (compile_dfg_expr ctx bneeds n a_idx (build_dfg ctx act) arg (sample_bufs act a_idx))
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
    cbn [compile_dfg_expr_aux].
    rewrite (not_sample_not_in_sample_bufs act a_idx n
              ltac:(unfold is_sample_of, node_op; rewrite Hop; reflexivity)).
    cbv beta iota. rewrite Hop.
    destruct (compile_dfg_expr ctx bneeds n a_idx (build_dfg ctx act) a1 (sample_bufs act a_idx))
      as [e1 v1] eqn:E1.
    destruct (compile_dfg_expr ctx bneeds n a_idx (build_dfg ctx act) a2 (sample_bufs act a_idx))
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
    (* compile_fst_phi normalises the branches back to the empty path *)
    rewrite (compile_fst_phi act a_idx (sample_bufs act a_idx) n n cnd tid eid
               (not_sample_not_in_sample_bufs act a_idx n
                  ltac:(unfold is_sample_of, node_op; rewrite Hop; reflexivity)) Hop).
    f_equal.
    - apply (nre_fuel act a_idx cnd n Hpc Hbc Hlc).
    - apply (nre_fuel act a_idx tid n Hpt Hbt Hlt).
    - apply (nre_fuel act a_idx eid n Hpe Hbe Hle).
  Qed.

  (* ==================================================================== *)
  (* PHASE 3d, STEP 2: the DENOTATION of a graph node, and the bridge from  *)
  (* a node EMITTED by the builder to its position in the exported graph.   *)
  (* ==================================================================== *)

  (* The buffer-free value of forward-graph node [n], demanded at width [szB],
     in scheduler state [ss].  This is what [dfg_action_semantics] talks about. *)
  Definition nval (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (ss: sched_sys_state) (input: sched_input_t) (szB: nat) (n: nid_t) : bits_t szB :=
    tf_eval_expr ss_sz si_sz oo_sz (szB := szB) (node_ref_expr act a_idx n) ss input.

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
        (input: sched_input_t) F (s s': wst) sv id :
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
        (input: sched_input_t) F (s s': wst) ov id :
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

  (* The three facts about a [DFG_Var v] node in the EXPORTED graph that the
     semantic cases need, independent of how the node got there: [get_var] may
     reuse one that is already in the graph instead of emitting a fresh one. *)
  Definition var_node_at (act: tfs_action sched) (v: @dfg_vars_t s_var o_var)
      (id: nid_t) : Prop :=
    1 <= id
    /\ id < length (graph (build_dfg ctx act))
    /\ op (nth id (graph (build_dfg ctx act))
             {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Var v.

  Lemma emit_var_node_at (act: tfs_action sched) F (s s': wst) v id :
    exports act F ->
    0 < length (graph s) ->
    emit ctx (DFG_Var v) (dfg_var_size ctx v) s = (id, s') ->
    wgmono s' F ->
    var_node_at act v id.
  Proof.
    intros HF Hne Hem Hg.
    destruct (emitted_node_at act F s s' (DFG_Var v) (dfg_var_size ctx v) id
                HF Hne Hem Hg) as [H1 [H2 [H3 _]]].
    split; [ exact H1 | split; [ exact H2 | exact H3 ] ].
  Qed.

  Lemma in_var_node_at (act: tfs_action sched) F (s: wst) v id :
    exports act F ->
    In {| nid := id; op := DFG_Var v; sz := dfg_var_size ctx v |} (graph s) ->
    1 <= id ->
    wgmono s F ->
    var_node_at act v id.
  Proof.
    intros HF Hin Hpos Hg.
    pose proof (in_graph_fwd act F _ HF (Hg _ Hin)) as Hin'.
    destruct (node_at_nid act _ Hin') as [Hlt Hnth].
    cbn [nid] in Hlt, Hnth.
    split; [ exact Hpos | split; [ exact Hlt | rewrite Hnth; reflexivity ] ].
  Qed.

  Lemma nval_var_svar (act: tfs_action sched) a_idx (ss: sched_sys_state)
        (input: sched_input_t) sv id :
    var_node_at act (DFG_SVar sv) id ->
    nval act a_idx ss input (s_sz sv) id = (fst ss).[tf_dfg_s sv].
  Proof.
    intros [H1 [H2 H3]].
    unfold nval. rewrite (nre_svar act a_idx id sv H1 H2 H3).
    exact (eval_svar_same (tf_dfg_s sv) ss input).
  Qed.

  Lemma nval_var_ovar (act: tfs_action sched) a_idx (ss: sched_sys_state)
        (input: sched_input_t) ov id :
    var_node_at act (DFG_OVar ov) id ->
    nval act a_idx ss input (o_sz ov) id = (snd ss).[ov].
  Proof.
    intros [H1 [H2 H3]].
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

  (* var_map effects of the two updating steps, stated with [In] so no [eq_dec]
     instance appears in a statement: the one Coq elaborates need not match
     [ensure_var]'s syntactically, which breaks [destruct]/[reflexivity]. *)
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

  (* [get_var] either reuses an existing ASSIGNMENT or falls through to
     [read_var] -- a read is not an assignment, so it must not enter
     [var_map]. *)
  Lemma get_var_cases (v: dvar) (s: wst) id s' :
    get_var ctx v s = (id, s') ->
    (In (v, id) (var_map s) /\ s' = s)
    \/ (read_var ctx v s = (id, s') /\ forall n, ~ In (v, n) (var_map s)).
  Proof.
    unfold get_var, bind, get_state.
    destruct (BitsToLists.list_assoc (var_map s) v) as [id0 |] eqn:E; intro H.
    - unfold ret in H. injection H as H1 H2. subst id0. subst s'.
      apply wla_in in E. left. split; [ exact E | reflexivity ].
    - right. split; [ exact H | intro n; exact (list_assoc_None_notin (var_map s) v E n) ].
  Qed.

  (* Book-keeping about [emit] that the semantic induction needs at every node. *)
  Lemma emit_vm (o: @dfg_op_t s_var i_var o_var p_var) size (s: wst) id s' :
    emit ctx o size s = (id, s') -> var_map s' = var_map s.
  Proof. rewrite emit_red. intro H. injection H as _ <-. reflexivity. Qed.

  (* A read never records anything: either it reuses a node (state untouched)
     or it only grows the graph. *)
  Lemma read_var_vmap (v: dvar) (s: wst) id s' :
    read_var ctx v s = (id, s') -> var_map s' = var_map s.
  Proof.
    intro H. destruct (read_var_cases v s id s' H) as [[_ [_ ->]] | Hem].
    - reflexivity.
    - exact (emit_vm _ _ s id s' Hem).
  Qed.

  Lemma emit_gmono (o: @dfg_op_t s_var i_var o_var p_var) size (s: wst) id s' :
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
            (ss: sched_sys_state) (input: input_t) (sinput: sched_input_t)
            (sp0: src_sys_state) (F: wst).
    Hypothesis HF  : exports act F.
    Hypothesis Hss : forall sv, (fst ss).[tf_dfg_s sv] = (fst sp0).[sv].
    Hypothesis Hoo : forall ov, (snd ss).[ov] = (snd sp0).[ov].
    Hypothesis Hali : act_idx_aligned act a_idx.
    (* the scheduled input carries the source's, plus the IP responses *)
    Hypothesis Hsin : forall v, sinput (inl v) = input v.
    (* THE ROUND TRIP: a sample.s register holds the IP.s answer to the
       request its OWN drive sent. *)
    Hypothesis Hrt : forall n_idx p tok en av,
      node_op act (vreg_nid a_idx n_idx) = DFG_Sample p tok en ->
      sample_req act (vreg_nid a_idx n_idx) = Some av ->
      (fst ss).[tf_dfg_b a_idx n_idx]
      = convert (ip_fn (tfs_spec_ip ctx p)
          (tf_eval_expr ss_sz si_sz oo_sz
             (szB := ip_req_sz (tfs_spec_ip ctx p))
             (node_ref_expr act a_idx av) ss sinput)).

    Local Notation NV szB n := (nval act a_idx ss sinput szB n).

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
      - rewrite (nval_fresh_svar act a_idx ss sinput F s s' sv id HF Hne Hev Hg).
        exact (Hss sv).
      - rewrite (nval_fresh_ovar act a_idx ss sinput F s s' ov id HF Hne Hev Hg).
        exact (Hoo ov).
    Qed.

    (* Same, for the node [read_var] hands back -- whether it emitted it or
       reused one that was already in the graph. *)
    Lemma nval_read (s s': wst) (v: dvar) id :
      0 < length (graph s) ->
      read_var ctx v s = (id, s') -> wgmono s' F ->
      NV (dfg_var_size ctx v) id = src_get sp0 v.
    Proof.
      intros Hne Her Hg.
      assert (Hat : var_node_at act v id).
      { destruct (read_var_cases v s id s' Her) as [[Hin [Hpos Hss']] | Hem].
        - subst s'. exact (in_var_node_at act F s v id HF Hin Hpos Hg).
        - exact (emit_var_node_at act F s s' v id HF Hne Hem Hg). }
      destruct v as [sv | ov]; cbn [src_get dfg_var_size].
      - rewrite (nval_var_svar act a_idx ss sinput sv id Hat). exact (Hss sv).
      - rewrite (nval_var_ovar act a_idx ss sinput ov id Hat). exact (Hoo ov).
    Qed.

    (* [get_var] returns a node denoting the CURRENT source value: either the
       binding existed, or the read node holds the initial value, which the
       frame condition makes the current one.  A read leaves [var_map] alone. *)
    Lemma get_var_sem (s s': wst) (v: dvar) id sp :
      0 < length (graph s) ->
      get_var ctx v s = (id, s') ->
      wgmono s' F ->
      sem_inv s sp ->
      sem_inv s' sp /\ NV (dfg_var_size ctx v) id = src_get sp v.
    Proof.
      intros Hne Hgv Hg [Hsem Hfr].
      destruct (get_var_cases v s id s' Hgv) as [[Hin ->] | [Her Hnotin]].
      - split; [ split; assumption | exact (Hsem v id Hin) ].
      - pose proof (nval_read s s' v id Hne Her Hg) as Hfresh.
        assert (Hval : NV (dfg_var_size ctx v) id = src_get sp v)
          by (rewrite Hfresh; symmetry; exact (Hfr v Hnotin)).
        pose proof (read_var_vmap v s id s' Her) as Hvm.
        split; [ | exact Hval ]. split.
        + intros v' n' Hin. rewrite Hvm in Hin. exact (Hsem v' n' Hin).
        + intros v' Hno. apply Hfr. intros n Hin. apply (Hno n).
          rewrite Hvm. exact Hin.
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
            cbn [tf_eval_expr]. rewrite Hsin. reflexivity.
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
            cbn [tf_eval_expr]. rewrite Hsin. apply convert_same.
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
        destruct bop as [ | | | | | | szC cop | hz lz ].
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
        split;
        [ apply (sem_inv_vm s2 s'); [ exact (emit_vm _ _ _ _ _ Hde) | exact Hsem2 ]
        | unfold nval in Hv1, Hv2 |- *;
          rewrite (nre_binary act a_idx id (tf_cmp szC cop) id1 id2 R1 R2 Rop);
          cbn [tf_eval_expr]; rewrite Hv1, Hv2; reflexivity ].
        (* tf_concat: e1 is compiled at hz and e2 at lz.  Every other binary op
           compiles both operands at ONE width, which is why this case cannot
           share the tactic above. *)
        cbn [dataflow_expr] in Hde. unfold bind in Hde.
        pose proof (dataflow_expr_sz e1 hz s Hinv Hvsz) as Hsz1.
        destruct (dataflow_expr ctx e1 hz s) as [id1 s1] eqn:Ee1.
        destruct Hsz1 as [Hg1 [Hn1 [Hp1 [Hq1 Hz1]]]].
        pose proof (dataflow_expr_sz e2 lz s1 Hp1 Hq1) as Hsz2.
        destruct (dataflow_expr ctx e2 lz s1) as [id2 s2] eqn:Ee2.
        destruct Hsz2 as [Hg2 [Hn2 [Hp2 [Hq2 Hz2]]]].
        cbv beta in Hde.
        assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Hg1 Hne).
        assert (Hne2 : 0 < length (graph s2)) by exact (gne_gmono s1 s2 Hg2 Hne1).
        assert (Hg2F : wgmono s2 F)
          by exact (wgmono_trans s2 s' F (emit_gmono _ _ _ _ _ Hde) Hg').
        assert (Hg1F : wgmono s1 F) by exact (wgmono_trans s1 s2 F Hg2 Hg2F).
        destruct (IH1 hz s s1 id1 sp Hne Hinv Hvsz Ee1 Hg1F Hsem) as [Hsem1 Hv1].
        destruct (IH2 lz s1 s2 id2 sp Hne1 Hp1 Hq1 Ee2 Hg2F Hsem1) as [Hsem2 Hv2].
        destruct (emitted_node_at act F s2 s' (DFG_Binary (tf_concat hz lz) id1 id2)
                    szE id HF Hne2 Hde Hg') as [R1 [R2 [Rop _]]].
        split;
        [ apply (sem_inv_vm s2 s'); [ exact (emit_vm _ _ _ _ _ Hde) | exact Hsem2 ]
        | unfold nval in Hv1, Hv2 |- *;
          rewrite (nre_binary act a_idx id (tf_concat hz lz) id1 id2 R1 R2 Rop);
          cbn [tf_eval_expr]; rewrite Hv1, Hv2; reflexivity ].
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
         tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
           (tf_expr_if (node_ref_expr act a_idx cond_id) E1 E2) ss sinput
         = if b then tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E2 ss sinput
                else tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E1 ss sinput) ->
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
         tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
           (tf_expr_if (node_ref_expr act a_idx cond_id) E1 E2) ss sinput
         = if b then tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E2 ss sinput
                else tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E1 ss sinput) ->
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
         tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
           (tf_expr_if (node_ref_expr act a_idx cond_id) E1 E2) ss sinput
         = if b then tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E2 ss sinput
                else tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E1 ss sinput) ->
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
      tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tf_ops_base tf_nop) sp input = (fst sp, snd sp).
    Proof. reflexivity. Qed.

    Lemma ops_run_assign (dst: s_var) e (sp: src_sys_state) :
      tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tf_ops_base (tf_assign dst e)) sp input
      = (ContextEnv.(putenv) (fst sp) dst
           (tf_eval_expr s_sz i_sz o_sz (szB := s_sz dst) e sp input), snd sp).
    Proof. reflexivity. Qed.

    (* THE DENOTATION at the spec level, in this file's R form: a call assigns its
       destination the value of its RESPONSE port, with the argument [e] absent
       from the right-hand side. *)
    (* V4: a call is ONE source update, the IP applied to the request.  The
       request port is the scheduler's own register and no declared output. *)
    Lemma ops_run_call (ip: p_var) (dst: s_var) e (sp: src_sys_state) :
      tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tf_ops_base (tf_call ip dst e)) sp input
      = (ContextEnv.(putenv) (fst sp) dst
           (convert (ip_fn (tfs_spec_ip ctx ip)
              (tf_eval_expr s_sz i_sz o_sz
                 (szB := ip_req_sz (tfs_spec_ip ctx ip)) e sp input))),
         snd sp).
    Proof. reflexivity. Qed.

    Lemma ops_run_output (dst: o_var) e (sp: src_sys_state) :
      tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tf_ops_base (tf_output dst e)) sp input
      = (fst sp, ContextEnv.(putenv) (snd sp) dst
           (tf_eval_expr s_sz i_sz o_sz (szB := o_sz dst) e sp input)).
    Proof. reflexivity. Qed.

    Lemma ops_run_cons o1 o2 (sp: src_sys_state) :
      tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tf_ops_cons o1 o2) sp input
      = tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) o2 (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) o1 sp input) input.
    Proof.
      unfold tf_ops_run. cbn [tf_ops_updates].
      destruct (tf_ops_updates s_sz i_sz o_sz (tfs_spec_ip ctx) o1 sp input) as [u1 sp1].
      cbn [snd].
      destruct (tf_ops_updates s_sz i_sz o_sz (tfs_spec_ip ctx) o2 sp1 input) as [u2 sp2].
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
      forall (ops: @tf_ops s_var i_var o_var p_var) (en: list (nid_t * bool))
             (s: wst) sp,
        0 < length (graph s) -> winv s -> wvsz s -> wfg s ->
        (forall x, In x (map fst en) -> wnidwf s x) ->
        sem_inv s sp ->
        let (u, s') := dataflow_ops ctx en ops s in
        wgmono s' F -> sem_inv s' (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) ops sp input).
    Proof.
      induction ops as [op | op1 IHops1 op2 IHops2 | cond op1 IHops1 op2 IHops2];
        intros en s sp Hne Hinv Hvsz Hfg Hen Hsem.
      - destruct op as [ | dst expr | dst expr | ip dst expr ].
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
        + (* THE ROUND TRIP.  [dataflow_ops] emits arg -> drive -> (join) ->
             stall -> sample and binds [dst] to the SAMPLE, whose reference IS
             its register; [Hrt] says that register holds the IP's answer to
             this call's own request. *)
          simpl.
          rewrite (bind_red (get_state ctx) _ s _ _ (get_state_red s)).
          pose proof (dataflow_expr_fg expr (ip_req_sz (tfs_spec_ip ctx ip)) s
                        Hinv Hvsz Hfg) as Ha.
          destruct (dataflow_expr ctx expr (ip_req_sz (tfs_spec_ip ctx ip)) s)
            as [arg_id sa] eqn:Ea.
          destruct Ha as [Ga [Na [Pa [Qa [Sa Fa]]]]].
          rewrite (bind_red (dataflow_expr ctx expr (ip_req_sz (tfs_spec_ip ctx ip)))
                     _ s _ _ Ea).
          destruct (emit ctx (DFG_Drive ip arg_id en)
                      (ip_req_sz (tfs_spec_ip ctx ip)) sa) as [drive_id sd] eqn:Ed.
          rewrite (bind_red (emit ctx (DFG_Drive ip arg_id en)
                               (ip_req_sz (tfs_spec_ip ctx ip))) _ sa _ _ Ed).
          destruct (match last_sample ctx s ip en with
                    | None => ret ctx drive_id
                    | Some prev => emit ctx (DFG_Join drive_id prev) 1
                    end sd) as [head_id sh] eqn:Eh.
          rewrite (bind_red _ _ sd _ _ Eh).
          destruct (stall_chain ctx (ip_lat (tfs_spec_ip ctx ip)) head_id sh)
            as [stall_id s1] eqn:Es1.
          rewrite (bind_red (stall_chain ctx (ip_lat (tfs_spec_ip ctx ip)) head_id)
                     _ sh _ _ Es1).
          destruct (emit ctx (DFG_Sample ip stall_id en)
                      (dfg_var_size ctx (DFG_SVar dst)) s1) as [samp_id s2] eqn:Esm.
          rewrite (bind_red (emit ctx (DFG_Sample ip stall_id en)
                               (dfg_var_size ctx (DFG_SVar dst))) _ s1 _ _ Esm).
          pose proof (set_var_vm_head (DFG_SVar dst) samp_id s2) as Hhead.
          pose proof (set_var_vm_keep (DFG_SVar dst) samp_id s2) as Hkeep.
          pose proof (set_var_vm_inv2 (DFG_SVar dst) samp_id s2) as Hminv.
          destruct (set_var ctx (DFG_SVar dst) samp_id s2) as [u s'] eqn:Es.
          cbn [snd] in Hhead, Hkeep, Hminv.
          intro Hg'.
          (* --- the graph grows along the chain, so each emit lands in [F] --- *)
          assert (Gd : wgmono sa sd) by exact (emit_gmono _ _ _ _ _ Ed).
          assert (Gh : wgmono sd sh).
          { revert Eh. destruct (last_sample ctx s ip en) as [prev |].
            - intro E. exact (emit_gmono _ _ _ _ _ E).
            - unfold ret. intro E. injection E as _ <-. apply wgmono_refl. }
          assert (Gt : wgmono sh s1).
          { revert Es1. unfold stall_chain.
            destruct (ip_lat (tfs_spec_ip ctx ip)) as [| l].
            - unfold ret. intro E. injection E as _ <-. apply wgmono_refl.
            - intro E. exact (emit_gmono _ _ _ _ _ E). }
          assert (Gm : wgmono s1 s2) by exact (emit_gmono _ _ _ _ _ Esm).
          assert (Gs : wgmono s2 s').
          { intros n Hn.
            replace (graph s') with (graph s2);
              [ exact Hn | rewrite <- (set_var_graph (DFG_SVar dst) samp_id s2), Es;
                           reflexivity ]. }
          assert (GmF : wgmono s2 F) by (eapply wgmono_trans; [ exact Gs | exact Hg' ]).
          assert (Gt1F : wgmono s1 F) by (eapply wgmono_trans; [ exact Gm | exact GmF ]).
          assert (GhF : wgmono sh F) by (eapply wgmono_trans; [ exact Gt | exact Gt1F ]).
          assert (GdF : wgmono sd F) by (eapply wgmono_trans; [ exact Gh | exact GhF ]).
          assert (GaF : wgmono sa F) by (eapply wgmono_trans; [ exact Gd | exact GdF ]).
          (* --- and the nodes it records --- *)
          assert (Hnea : 0 < length (graph sa)) by exact (gne_gmono s sa Ga Hne).
          assert (Hned : 0 < length (graph sd)) by exact (gne_gmono sa sd Gd Hnea).
          assert (Hneh : 0 < length (graph sh)) by exact (gne_gmono sd sh Gh Hned).
          assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono sh s1 Gt Hneh).
          destruct (emitted_node_at act F s1 s2 (DFG_Sample ip stall_id en)
                      (dfg_var_size ctx (DFG_SVar dst)) samp_id HF Hne1 Esm GmF)
            as [Msm1 [Msm2 [MsmOp MsmSz]]].
          (* the head is the drive, or the ordering join in front of it -- and
             either way it is no stall, which is what pins the token's arm *)
          destruct (emitted_node_at act F sa sd (DFG_Drive ip arg_id en)
                      (ip_req_sz (tfs_spec_ip ctx ip)) drive_id HF Hnea Ed GdF)
            as [_ [_ [MdrOp _]]].
          assert (Hhd : sample_req_head act head_id = Some arg_id
                        /\ match node_op act head_id with
                           | DFG_Stall _ _ => False | _ => True end).
          { revert Eh. destruct (last_sample ctx s ip en) as [prev |].
            - intro E.
              destruct (emitted_node_at act F sd sh (DFG_Join drive_id prev) 1
                          head_id HF Hned E GhF) as [_ [_ [MjnOp _]]].
              unfold sample_req_head, node_op. rewrite MjnOp.
              split; [ rewrite MdrOp; reflexivity | exact I ].
            - unfold ret. intro E. injection E as <- _.
              unfold sample_req_head, node_op. rewrite MdrOp.
              split; [ reflexivity | exact I ]. }
          destruct Hhd as [Hhd1 Hhd2].
          assert (Hreq : sample_req act samp_id = Some arg_id).
          { unfold sample_req, node_op. rewrite MsmOp.
            revert Es1. unfold stall_chain.
            destruct (ip_lat (tfs_spec_ip ctx ip)) as [| l].
            - unfold ret. intro E. injection E as <- _.
              revert Hhd2 Hhd1. unfold node_op.
              destruct (op (nth head_id (graph (build_dfg ctx act))
                              {| nid := 0; op := DFG_Empty; sz := 0 |}));
                try (intros _ H; exact H).
              intros [].
            - intro E.
              destruct (emitted_node_at act F sh s1 (DFG_Stall (S l) head_id)
                          (counter_sz (S l)) stall_id HF Hneh E Gt1F)
                as [_ [_ [MstOp _]]].
              unfold node_op. rewrite MstOp. exact Hhd1. }
          (* --- the semantics --- *)
          destruct (dataflow_expr_sem expr (ip_req_sz (tfs_spec_ip ctx ip)) s sa
                      arg_id sp Hne Hinv Hvsz Ea GaF Hsem) as [[Hvm1 Hfr1] Hval].
          assert (Hvm2 : var_map s2 = var_map sa).
          { rewrite (emit_vm _ _ _ _ _ Esm).
            assert (Hs1 : var_map s1 = var_map sh).
            { revert Es1. unfold stall_chain.
              destruct (ip_lat (tfs_spec_ip ctx ip)) as [| l].
              - unfold ret. intro E. injection E as _ <-. reflexivity.
              - intro E. exact (emit_vm _ _ _ _ _ E). }
            rewrite Hs1.
            assert (Hsh : var_map sh = var_map sd).
            { revert Eh. destruct (last_sample ctx s ip en) as [prev |].
              - intro E. exact (emit_vm _ _ _ _ _ E).
              - unfold ret. intro E. injection E as _ <-. reflexivity. }
            rewrite Hsh. exact (emit_vm _ _ _ _ _ Ed). }
          (* the sample's reference IS its register, and [Hrt] reads it *)
          assert (Hsampv : is_sample_of act samp_id = true)
            by (unfold is_sample_of, node_op; rewrite MsmOp; reflexivity).
          destruct (sample_index act a_idx samp_id Hali Hsampv) as [n_idx Hvn].
          assert (Hbsz : ss_sz (tf_dfg_b a_idx n_idx)
                         = dfg_var_size ctx (DFG_SVar dst))
            by (rewrite (buffer_register_node_size act a_idx n_idx Hali), Hvn;
                exact MsmSz).
          assert (Hsamp : NV (dfg_var_size ctx (DFG_SVar dst)) samp_id
                          = convert (ip_fn (tfs_spec_ip ctx ip)
                              (NV (ip_req_sz (tfs_spec_ip ctx ip)) arg_id))).
          { unfold nval. rewrite <- Hvn.
            rewrite (nre_sample act a_idx n_idx Hali
                       ltac:(rewrite Hvn; exact Hsampv)).
            rewrite <- Hbsz, eval_svar_same.
            exact (Hrt n_idx ip stall_id en arg_id
                     ltac:(unfold node_op; rewrite Hvn, MsmOp; reflexivity)
                     ltac:(rewrite Hvn; exact Hreq)). }
          rewrite ops_run_call. split.
          * intros v n Hin.
            destruct (Hminv v n Hin) as [[Hv Hn] | [Hin0 Hnv]].
            -- subst v. subst n. rewrite (src_get_put_s_eq sp dst _).
               rewrite Hsamp, Hval. reflexivity.
            -- rewrite (src_get_put_s_neq sp dst _ v Hnv).
               apply Hvm1. rewrite <- Hvm2. exact Hin0.
          * intros v Hno.
            assert (Hnv : v <> DFG_SVar dst).
            { intro He. subst v. exact (Hno samp_id Hhead). }
            rewrite (src_get_put_s_neq sp dst _ v Hnv).
            apply Hfr1. intros n Hin. apply (Hno n).
            apply (Hkeep v n); [ rewrite Hvm2; exact Hin | exact Hnv ].
      - (* sequential composition *)
        cbn [dataflow_ops].
        pose proof (dataflow_ops_fg op1 en s Hinv Hvsz Hfg Hen) as Fa.
        pose proof (IHops1 en s sp Hne Hinv Hvsz Hfg Hen Hsem) as H1.
        destruct (dataflow_ops ctx en op1 s) as [u1 s1] eqn:E1.
        destruct Fa as [G1 [P1 [Q1 Ff1]]].
        rewrite (bind_red (dataflow_ops ctx en op1) _ s _ _ E1).
        assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 G1 Hne).
        assert (Hen1 : forall x, In x (map fst en) -> wnidwf s1 x)
          by (intros x Hx; eapply wnidwf_gmono; [ apply Hen, Hx | exact G1 ]).
        pose proof (dataflow_ops_fg op2 en s1 P1 Q1 Ff1 Hen1) as Fb.
        pose proof (fun Hs =>
                      IHops2 en s1 (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) op1 sp input)
                        Hne1 P1 Q1 Ff1 Hen1 Hs) as H2.
        destruct (dataflow_ops ctx en op2 s1) as [u2 s2] eqn:E2.
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
        assert (Hen_t : forall x, In x (map fst ((cond_id, true) :: en)) -> wnidwf s1 x).
        { intros x Hx. cbn [map In] in Hx. destruct Hx as [<- | Hx]; [ exact Nc |].
          eapply wnidwf_gmono; [ apply Hen, Hx | exact Gc ]. }
        pose proof (dataflow_ops_fg op1 ((cond_id, true) :: en) s1 Pc Qc Fc Hen_t) as Ft.
        pose proof (fun Hs => IHops1 ((cond_id, true) :: en) s1 sp Hne1 Pc Qc Fc Hen_t Hs) as Ht.
        destruct (dataflow_ops ctx ((cond_id, true) :: en) op1 s1) as [ut s_then] eqn:Et.
        destruct Ft as [Gthen [Pthen [Qthen Fthen]]].
        rewrite (bind_red (dataflow_ops ctx ((cond_id, true) :: en) op1) _ s1 _ _ Et).
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
        assert (Hen_e : forall x, In x (map fst ((cond_id, false) :: en)) ->
                          wnidwf sR x).
        { assert (Gs1R : wgmono s1 sR)
            by (eapply wgmono_trans; [ exact Gthen | exact Gthen_sR ]).
          intros x Hx. cbn [map In] in Hx.
          destruct Hx as [<- | Hx];
            [ eapply wnidwf_gmono; [ exact Nc | exact Gs1R ]
            | eapply wnidwf_gmono;
              [ apply Hen, Hx
              | eapply wgmono_trans; [ exact Gc | exact Gs1R ] ] ]. }
        pose proof (dataflow_ops_fg op2 ((cond_id, false) :: en) sR PsR QsR FsR Hen_e) as Fe.
        pose proof (fun Hs => IHops2 ((cond_id, false) :: en) sR sp HneR PsR QsR FsR Hen_e Hs) as Hels.
        destruct (dataflow_ops ctx ((cond_id, false) :: en) op2 sR) as [ue s_else] eqn:Ee.
        destruct Fe as [Gelse [Pelse [Qelse Felse]]].
        rewrite (bind_red (dataflow_ops ctx ((cond_id, false) :: en) op2) _ sR _ _ Ee).
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
                       tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
                         (tf_expr_if (node_ref_expr act a_idx cond_id) E1 E2) ss sinput
                       = if B then tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E2 ss sinput
                              else tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E1 ss sinput)
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
      dataflow_ops ctx [] (tfs_spec_action_ops ctx act)
        {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |}
        = (tt, Fin)
      /\ exports act Fin
      /\ var_map (build_dfg ctx act) = var_map Fin.
  Proof.
    unfold exports, build_dfg.
    destruct (dataflow_ops ctx [] (tfs_spec_action_ops ctx act)
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
        (sp: src_sys_state) (ss: sched_sys_state)
        (input: input_t) (sinput: sched_input_t) :
    act_idx_aligned act a_idx ->
    (forall v, sinput (inl v) = input v) ->
    (forall n_idx p tok en av,
       node_op act (vreg_nid a_idx n_idx) = DFG_Sample p tok en ->
       sample_req act (vreg_nid a_idx n_idx) = Some av ->
       (fst ss).[tf_dfg_b a_idx n_idx]
       = convert (ip_fn (tfs_spec_ip ctx p)
           (tf_eval_expr ss_sz si_sz oo_sz
              (szB := ip_req_sz (tfs_spec_ip ctx p))
              (node_ref_expr act a_idx av) ss sinput))) ->
    (forall sv, (fst ss).[tf_dfg_s sv] = (fst sp).[sv]) ->
    (forall ov, (snd ss).[ov] = (snd sp).[ov]) ->
    let sp1 := tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act) sp input in
    (forall sv n, In (DFG_SVar sv, n) (var_map (build_dfg ctx act)) ->
        eval_st (tf_dfg_s sv)
          (fst (compile_dfg_expr ctx bneeds
                  (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n (sample_bufs act a_idx)))
          ss sinput
        = (fst sp1).[sv])
    /\ (forall ov n, In (DFG_OVar ov, n) (var_map (build_dfg ctx act)) ->
        eval_out ov
          (fst (compile_dfg_expr ctx bneeds
                  (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n (sample_bufs act a_idx)))
          ss sinput
        = (snd sp1).[ov])
    /\ (forall sv, (forall n, ~ In (DFG_SVar sv, n) (var_map (build_dfg ctx act))) ->
        (fst sp1).[sv] = (fst sp).[sv])
    /\ (forall ov, (forall n, ~ In (DFG_OVar ov, n) (var_map (build_dfg ctx act))) ->
        (snd sp1).[ov] = (snd sp).[ov]).
  Proof.
    intros Halign Hsinp Hrtp Hs Ho.
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
    pose proof (dataflow_ops_sem act a_idx ss input sinput sp Fin Hgr Hs Ho
                  Halign Hsinp Hrtp
                  (tfs_spec_action_ops ctx act) []
                  {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |}
                  sp Hne0 Hempty Hemvsz Hemfg ltac:(intros x [])
                  (sem_inv_empty act a_idx ss sinput sp
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
      let sp1 := tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act) sp0 input in
      maps_from ctx bneeds (fst (run_n N act input ss0)) = fst sp1 /\
      snd (run_n N act input ss0) = snd sp1.
  Proof.
    intros act sp0 ss0 input N [Hout0 [Hst0 Hzero0]] Hbefore Hdone.
    destruct (exists_act_idx act) as [a_idx Halign].
    (* N = 0 is impossible: start_rel clears the done flag *)
    destruct N as [| M].
    { exfalso. apply Hdone. cbn [run_n]. apply (Hzero0 (tfs_done_signal sched) I). }
    set (ssM := run_n M act input ss0) in *.
    change (run_n (S M) act input ss0)
      with (sched_step act ssM (sched_input input ssM)) in *.
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
    assert (Hinv : valid_settled act a_idx ssM (sched_input input ssM)).
    { destruct (valid_settled_run act a_idx input ss0 M Halign
                  ltac:(intro n_idx; apply (Hzero0 (tf_dfg_v a_idx n_idx) I)))
        as [_ [_ Hinv]]. exact Hinv. }
    (* drop the buffers from any var_map node's compiled expression *)
    assert (Hdrop : forall v n szB,
              In (v, n) (var_map (build_dfg ctx act)) ->
              szB = dfg_var_size ctx v ->
              tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
                (fst (compile_dfg_expr ctx bneeds
                        (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n
                        (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])))
                ssM (sched_input input ssM)
              = tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
                (fst (compile_dfg_expr ctx bneeds
                        (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n (sample_bufs act a_idx)))
                ssM (sched_input input ssM)).
    { intros v n szB Hin HszB.
      assert (Hmem : In n (map snd (var_map (build_dfg ctx act))))
        by (apply (in_map snd _ (v, n)); exact Hin).
      destruct (var_map_node_range act n Hmem) as [Hn1 Hnlen].
      apply (compile_subst_valid act a_idx ssM (sched_input input ssM)
               Halign Hinv).
      - intros e He. exact He.
      - intros x Hx. apply list_assoc_key_none. intro Hin2.
        apply in_map_iff in Hin2. destruct Hin2 as [[x2 v2] [Hxx Hmem2]].
        cbn [fst] in Hxx. subst x2.
        unfold sample_bufs in Hmem2. apply filter_In in Hmem2.
        apply (list_assoc_none_key _ _ Hx), in_map_iff.
        exists (x, v2). split; [ reflexivity | exact (proj1 Hmem2) ].
      - intros x m msz Hx Hsx. apply list_assoc_nodup_in.
        + unfold sample_bufs. apply nodup_map_fst_filter.
          exact (slot_keys_nodup act a_idx Halign).
        + unfold sample_bufs. apply filter_In.
          split; [ exact (wla_in _ _ _ Hx) | exact Hsx ].
      - exact Hn1.
      - exact Hnlen.
      - exact Hnlen.
      - rewrite HszB. symmetry. exact (var_map_entry_size act v n Hin).
      - exact (sched_step_done_valid act a_idx ssM (sched_input input ssM) n Halign Hdone Hmem). }
    (* the one obligation left in this file: a sample.s register holds the IP.s
       answer to the request its own drive sent. *)
    destruct (dfg_action_semantics act a_idx sp0 ssM input (sched_input input ssM)
                Halign ltac:(intro v; reflexivity) Hrt_obligation Hs Ho)
      as [Hsem_s [Hsem_o [Hfix_s Hfix_o]]].
    split.
    - apply equiv_eq. unfold equiv. intro sv.
      rewrite getenv_maps_from.
      destruct (find_pair_dec eq_dec (var_map (build_dfg ctx act)) (DFG_SVar sv))
        as [[n Hn] | Hno].
      + rewrite (sched_step_done_svar act a_idx ssM (sched_input input ssM) sv n Halign Hdone Hn).
        rewrite (Hdrop (DFG_SVar sv) n (ss_sz (tf_dfg_s sv)) Hn eq_refl).
        exact (Hsem_s sv n Hn).
      + rewrite (sched_step_done_svar_untouched act a_idx ssM (sched_input input ssM) sv Halign Hdone Hno).
        rewrite (Hfix_s sv Hno). exact (Hs sv).
    - apply equiv_eq. unfold equiv. intro ov.
      destruct (find_pair_dec eq_dec (var_map (build_dfg ctx act)) (DFG_OVar ov))
        as [[n Hn] | Hno].
      + rewrite (sched_step_done_ovar act a_idx ssM (sched_input input ssM) ov n Halign Hdone Hn).
        rewrite (Hdrop (DFG_OVar ov) n (oo_sz ov) Hn eq_refl).
        exact (Hsem_o ov n Hn).
      + rewrite (sched_step_done_ovar_untouched act a_idx ssM (sched_input input ssM) ov Halign Hdone Hno).
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
        let sp1 := tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act) sp0 input in
        maps_from ctx bneeds (fst (run_n N act input ss0)) = fst sp1 /\
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
