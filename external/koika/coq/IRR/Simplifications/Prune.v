Require Import Koika.IRR.Interpretation.
Require Import Koika.IRR.Operations.
Require Import Koika.BitsToLists.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.KoikaForm.Types.
Require Import Koika.IRR.IRR.
Require Import Koika.Utils.EqDec.
Require Import Koika.Utils.Maps.
Require Import Koika.Utils.Environments.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section Prune.
  Context {pos_t reg_t ext_fn_t rule_name_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {ext_fn_t_eq_dec: EqDec ext_fn_t}.
  Context {REnv: Env reg_t}.
  Context (R: reg_t -> type).
  Context (Sigma: ext_fn_t -> ExternalSignature).
  Local Definition ext_funs_defs := forall f: ext_fn_t, val -> val.
  Local Definition UREnv := REnv.(env_t) (fun _ => val).
  Context (r: UREnv).
  Context (sigma: ext_funs_defs).
  Local Definition sact := sact (ext_fn_t := ext_fn_t) (reg_t := reg_t).
  Local Definition eval_sact := eval_sact r sigma.
  Local Definition wf_sf := wf_sf (rule_name_t := rule_name_t) R Sigma.
  Hypothesis WTRENV: Wt.wt_renv R REnv r.
  Context {
    wt_sigma:
    forall ufn vc, wt_val (arg1Sig (Sigma ufn)) vc
    -> wt_val (retSig (Sigma ufn)) (sigma ufn vc)
  }.

  Definition prune_irrelevant_aux (sf: @IRR reg_t ext_fn_t rule_name_t) reg v :=
    sf
      <| final_values := [(reg, v)] |>
      <| vars :=
           filter_ptree (vars sf) (PTree.empty _) (useful_vars_for_var sf v) |>.

  Definition prune_irrelevant (sf: IRR) reg :=
    match list_assoc (final_values sf) reg with
    | Some v => Some (prune_irrelevant_aux sf reg v)
    | None => None
    end.

  Fixpoint pos_union_2 (l1 l2 : list positive) : list positive :=
    match l2 with
    | h::t =>
      if in_dec Pos.eq_dec h l1 then pos_union_2 l1 t
      else h::(pos_union_2 l1 t)
    | nil => l1
    end.

  Lemma in_l1_in_pos_union_2_l:
    forall l1 l2 a, In a l1 -> In a (pos_union_2 l1 l2).
  Proof.
    induction l2; simpl; intros; eauto.
    destr; auto. right; eauto.
  Qed.

  Lemma pos_union_2_correct:
    forall l1 l2 a, In a (pos_union_2 l1 l2) <-> In a l1 \/ In a l2.
  Proof.
    intros. split; intro.
    - induction l2; auto. simpl in H. destr_in H.
      destruct IHl2; auto. right; right; auto.
      destruct H. subst. right. left; auto.
      destruct IHl2; auto. right; right; auto.
    - destruct H.
      + eapply in_l1_in_pos_union_2_l. eauto.
      + revert H.
        induction l2; simpl; intros; eauto. easy.
        destruct H as [EQ | IN]. subst.
        destr; simpl; auto.
        eapply in_l1_in_pos_union_2_l; eauto.
        destr; simpl; auto.
  Qed.

  Lemma NoDup_pos_union_2:
    forall l1 l2, NoDup l1 -> NoDup l2 -> NoDup (pos_union_2 l1 l2).
  Proof.
    intros.
    induction l2; eauto.
    inv H0. apply IHl2 in H4.
    simpl. destr.
    constructor; auto.
    intro IN.
    eapply pos_union_2_correct in IN. destruct IN; auto.
  Qed.

  Definition pos_union (l : list (list positive)) : list positive :=
    List.fold_right (pos_union_2) [] l.

  Lemma NoDup_pos_union:
    forall (l : list (list positive)),
    Forall (@NoDup positive) l -> NoDup (pos_union l).
  Proof.
    induction l; intro; simpl; auto.
    - constructor.
    - inv H. apply NoDup_pos_union_2; auto.
  Qed.

  Lemma pos_union_correct:
    forall e l, In e (pos_union l) <-> exists ll, In ll l /\ In e ll.
  Proof.
    intros. split; intro.
    - induction l.
      + simpl in H. destruct H.
      + simpl in H. apply pos_union_2_correct in H. destruct H.
        * exists a. split; auto. left. reflexivity.
        * apply IHl in H. destruct H. exists x. destruct H. split; auto.
          right. auto.
    - induction l.
      + destruct H. destruct H. inv H.
      + simpl in *. apply pos_union_2_correct.
        destruct H. destruct H. destruct H.
        * subst. left. auto.
        * right.
          assert (exists ll, In ll l /\ In e ll). { exists x. split; auto. }
          apply IHl in H1. auto.
  Qed.

  Definition prune_irrelevant_l
    (sf: @IRR reg_t ext_fn_t rule_name_t) (regs: list reg_t)
  :=
    let reg_vars_list :=
      list_options_to_list (List.map (list_assoc (final_values sf)) regs)
    in
    let reachable_vars_list := List.map (useful_vars_for_var sf) reg_vars_list in
    let reachable_vars := pos_union reachable_vars_list in {|
      final_values :=
        List.filter
          (fun x => if in_dec eq_dec (fst x) regs then true else false)
          (final_values sf);
      vars := filter_ptree (vars sf) (PTree.empty _) reachable_vars;
      debug_log := debug_log sf;
      read1_values := read1_values sf;
    |}.

  Lemma Forall_map_2:
    forall {A B} (P: B -> Prop) f (l: list A),
    (forall (x: A), P (f x)) -> Forall P (List.map f l).
  Proof.
    induction l; intros; simpl.
    - constructor.
    - constructor; auto.
  Qed.

  Lemma wf_sf_prune_irrelevant_l:
    forall sf regs, wf_sf sf -> wf_sf (prune_irrelevant_l sf regs).
  Proof.
    intros.
    eapply wf_sf_filter_ptree. 5: reflexivity.
    - eapply NoDup_pos_union. apply Forall_map_2.
      unfold useful_vars_for_var.
      intros; eapply nodup_reachable_vars_aux; eauto. apply H. constructor.
    - intros.
      apply pos_union_correct.
      apply pos_union_correct in IN.
      destruct IN as (ll & INll & INv).
      exists ll; split; auto.
      apply in_map_iff in INll. destruct INll as (x & EQ & INll).
      intros; eapply reachable_vars_aux_ok in REACH.
      eauto.
      eauto. eauto. 2: subst. 2: reflexivity.
      apply H. simpl; easy. lia. eauto. eauto.
    - eauto.
    - simpl. intros.
      erewrite list_assoc_filter2 in H0.
      2: instantiate (1 :=
           fun k => if in_dec eq_dec k regs then true else false
          ); simpl; reflexivity.
      simpl in H0.
      destr_in H0. congruence.
      destr_in Heqb. 2: simpl in Heqb; congruence.
      clear Heqb.
      split. auto.
      apply pos_union_correct.
      eexists; split.
      rewrite in_map_iff.
      eexists; split. reflexivity. apply Sact.filter_map_In.
      eexists; split. reflexivity.
      rewrite in_map_iff. eexists; split. eauto. auto.
      unfold useful_vars_for_var.
      eapply reachable_vars_aux_in. lia.
  Qed.

  Lemma wf_sf_prune_irrelevant_aux:
    forall sf reg v, list_assoc (final_values sf) reg = Some v
    -> wf_sf sf
    -> wf_sf (prune_irrelevant_aux sf reg v).
  Proof.
    intros.
    eapply wf_sf_filter_ptree. 5: reflexivity.
    eapply nodup_reachable_vars_aux; eauto. apply H0. constructor.
    intros; eapply reachable_vars_aux_ok. eauto. eauto. 2: reflexivity.
    apply H0. simpl; easy. lia. eauto. eauto. eauto. auto.
    simpl. intros. destr_in H1; inv H1. rewrite H. split; auto.
  Qed.

  Lemma sf_eqf_prune_irrelevant_aux:
    forall sf reg v, list_assoc (final_values sf) reg = Some v
    -> wf_sf sf
    -> sf_eq_restricted
         R Sigma r sigma [reg] sf (prune_irrelevant_aux sf reg v).
  Proof.
    intros. eapply sf_eqr_filter. 6: reflexivity.
    apply nodup_reachable_vars_aux; eauto. apply H0. constructor.
    intros; eapply reachable_vars_aux_ok; eauto. apply H0. reflexivity.
    easy. auto. simpl. intros ? [|[]]. subst.
    destr. simpl. intros. repeat destr_in H1; inv H1. split; auto.
  Qed.

  Lemma sf_eqf_prune_irrelevant_l:
    forall sf regs, wf_sf sf
    -> sf_eq_restricted R Sigma r sigma regs sf (prune_irrelevant_l sf regs).
  Proof.
    intros. eapply sf_eqr_filter. 6: reflexivity.
    - eapply NoDup_pos_union. apply Forall_map_2.
      unfold useful_vars_for_var.
      intros; eapply nodup_reachable_vars_aux; eauto. apply H. constructor.
    - intros.
      apply pos_union_correct.
      apply pos_union_correct in IN.
      destruct IN as (ll & INll & INv).
      exists ll; split; auto.
      apply in_map_iff in INll. destruct INll as (x & EQ & INll).
      intros; eapply reachable_vars_aux_ok in REACH.
      eauto.
      eauto. eauto. 2: subst. 2: reflexivity.
      apply H. simpl; easy. lia. eauto. eauto.
    - apply H.
    - simpl. intros.
      erewrite list_assoc_filter2.
      2: instantiate (1:=fun k => if in_dec eq_dec k regs then true else false);
         simpl; reflexivity. simpl.
      destruct in_dec; try congruence. simpl. auto.
    - simpl. intros.
      erewrite list_assoc_filter2 in H0.
      2: instantiate (1:=fun k => if in_dec eq_dec k regs then true else false);
         simpl; reflexivity.
      simpl in H0.
      destr_in H0. congruence.
      destr_in Heqb. 2: simpl in Heqb; congruence.
      clear Heqb.
      split. auto.
      apply pos_union_correct.
      eexists; split.
      rewrite in_map_iff.
      eexists; split. reflexivity. apply Sact.filter_map_In.
      eexists; split. reflexivity.
      rewrite in_map_iff. eexists; split. eauto. auto.
      unfold useful_vars_for_var.
      eapply reachable_vars_aux_in. lia.
  Qed.

  Lemma prune_irrelevant_interp_cycle_ok:
    forall
      reg sf sf' (WF: wf_sf sf) (PRUNE: prune_irrelevant sf reg = Some sf'),
    getenv REnv (interp_cycle r sigma sf) reg
    = getenv REnv (interp_cycle r sigma sf') reg.
  Proof.
    intros.
    unfold prune_irrelevant in PRUNE. destr_in PRUNE; inv PRUNE.
    eapply sf_eqr_interp_cycle_ok; eauto.
    - eapply wf_sf_prune_irrelevant_aux; eauto.
    - eapply sf_eqf_prune_irrelevant_aux; eauto.
    - simpl; auto.
  Qed.

  Lemma prune_irrelevant_l_interp_cycle_ok:
    forall regs sf sf' (WF: wf_sf sf) (PRUNE: prune_irrelevant_l sf regs = sf'),
    forall reg,
      In reg regs ->
      getenv REnv (interp_cycle r sigma sf) reg
      = getenv REnv (interp_cycle r sigma sf') reg.
  Proof.
    intros. subst.
    eapply sf_eqr_interp_cycle_ok; eauto.
    - eapply wf_sf_prune_irrelevant_l; eauto.
    - eapply sf_eqf_prune_irrelevant_l; eauto.
  Qed.
End Prune.
