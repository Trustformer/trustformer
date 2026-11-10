Require Import Koika.IRR.Interpretation.
Require Import Koika.IRR.Operations.
Require Import Koika.BitsToLists.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.KoikaForm.Types.
Require Import Koika.IRR.Direction.
Require Import Koika.IRR.IRR.
Require Import Koika.Utils.EqDec.
Require Import Koika.Utils.Maps.
Require Import Koika.Utils.Environments.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section ReplaceSubact.
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
  Local Definition wt_sact := @wt_sact _ _ R Sigma.
  Local Definition interp_sact := @interp_sact _ _ _ r sigma.
  Local Definition wf_sf := wf_sf (rule_name_t := rule_name_t) R Sigma.
  Hypothesis WTRENV: Wt.wt_renv R REnv r.
  Context {
      wt_sigma:
      forall ufn vc, wt_val (arg1Sig (Sigma ufn)) vc
                     -> wt_val (retSig (Sigma ufn)) (sigma ufn vc)
    }.

  Fixpoint subact_at_position (s: sact) (p: position) : option sact :=
    match p with
    | [] => Some s
    | branch1::p =>
      match s with
      | SUnop ufn a => subact_at_position a p
      | SBinop ufn a b => subact_at_position a p
      | SExternalCall ufn a => subact_at_position a p
      | SIf a b c => subact_at_position a p
      | _ => None
      end
    | branch2::p =>
      match s with
      | SBinop ufn a b => subact_at_position b p
      | SIf a b c => subact_at_position b p
      | _ => None
      end
    | branch3::p =>
      match s with
      | SIf a b c => subact_at_position c p
      | _ => None
      end
    end.

  Fixpoint replace_at_position
    (s: sact) (p: position) (v: sact) : sact :=
    match p with
    | [] => v
    | branch1::p =>
      match s with
      | SUnop ufn a => let a := replace_at_position a p v in (SUnop ufn a)
      | SBinop ufn a b => let a := replace_at_position a p v in (SBinop ufn a b)
      | SExternalCall ufn a =>
        let a := replace_at_position a p v in (SExternalCall ufn a)
      | SIf a b c => let a := replace_at_position a p v in (SIf a b c)
      | _ => s
      end
    | branch2::p =>
      match s with
      | SBinop ufn a b => let b := replace_at_position b p v in (SBinop ufn a b)
      | SIf a b c => let b := replace_at_position b p v in (SIf a b c)
      | _ => s
      end
    | branch3::p =>
      match s with
      | SIf a b c => let c := replace_at_position c p v in (SIf a b c)
      | _ => s
      end
    end.

  Definition replace_at_positions s ps v :=
    fold_left (fun acc pos => replace_at_position acc pos v) ps s.

  Definition replace_subact_in_vars
    (vars: PTree.t (type * sact)) (positions: PTree.t (list position))
    (v: sact)
  :=
    PTree.map
      (fun k '(t, ua) =>
        let poss :=
          match PTree.get k positions with
          | Some l => l
          | _ => []
          end
        in
        (t, replace_at_positions ua poss v))
      vars.

  Definition replace_subact
    (sf: IRR (rule_name_t := rule_name_t)) (positions: PTree.t (list position)) (v: sact)
  : IRR :=
    sf <| vars := replace_subact_in_vars (vars sf) positions v |>.

  Lemma wt_unop_determ:
    forall u t t1, wt_unop u t t1
    -> forall t2, wt_unop u t t2
    -> t1 = t2.
  Proof. intros. inv H; inv H0; auto. congruence. congruence. Qed.

  Lemma wt_binop_determ:
    forall u t t' t1, wt_binop u t t' t1
    -> forall t2, wt_binop u t t' t2
    -> t1 = t2.
  Proof. intros. inv H; inv H0; auto. Qed.

  Lemma wt_sact_determ:
    forall vvs s t1, wt_sact vvs s t1
    -> forall t2, wt_sact vvs s t2
    -> t1 = t2.
  Proof.
    induction 1; simpl; intros; eauto.
    - inv H0. congruence.
    - inv H0. eapply wt_val_determ; eauto.
    - inv H2. eauto.
    - inv H1; eauto. apply IHwt_sact in H4. subst.
      eapply wt_unop_determ; eauto.
    - inv H2; eauto.
      apply IHwt_sact1 in H6. apply IHwt_sact2 in H8.
      subst. eapply wt_binop_determ; eauto.
    - inv H0. auto.
    - inv H. auto.
  Qed.

  Lemma wt_sact_replace_at_position:
    forall
      vvs s p subact (SAP: subact_at_position s p = Some subact) t
      (WT: wt_sact vvs s t) rep tn,
    wt_sact vvs subact tn
    -> wt_sact vvs rep tn
    -> wt_sact vvs (replace_at_position s p rep) t.
  Proof.
    induction s; simpl; intros; eauto.
    - repeat destr_in SAP; inv SAP.
      exploit wt_sact_determ. apply WT. apply H. intros ->. auto.
    - repeat destr_in SAP; inv SAP.
      exploit wt_sact_determ. apply WT. apply H. intros ->. auto.
    - repeat destr_in SAP; inv SAP.
      + exploit wt_sact_determ. apply WT. apply H. intros ->. auto.
      + inv WT. econstructor; eauto. eapply IHs1; eauto.
      + inv WT. econstructor; eauto. eapply IHs2; eauto.
      + inv WT. econstructor; eauto. eapply IHs3; eauto.
    - repeat destr_in SAP; inv SAP.
      + exploit wt_sact_determ. apply WT. apply H. intros ->. auto.
      + inv WT. econstructor; eauto. eapply IHs; eauto.
    - repeat destr_in SAP; inv SAP.
      + exploit wt_sact_determ. apply WT. apply H. intros ->. auto.
      + inv WT. econstructor; eauto. eapply IHs1; eauto.
      + inv WT. econstructor; eauto. eapply IHs2; eauto.
    - repeat destr_in SAP; inv SAP.
      + exploit wt_sact_determ. apply WT. apply H. intros ->. auto.
      + inv WT. econstructor; eauto. eapply IHs; eauto.
    - repeat destr_in SAP; inv SAP.
      exploit wt_sact_determ. apply WT. apply H. intros ->. auto.
  Qed.

  Inductive prefix {A:Type}: list A -> list A -> Prop :=
  | prefix_nil_l: forall l, prefix [] l
  | prefix_cons: forall d l1 l2, prefix l1 l2 -> prefix (d::l1) (d::l2).

  Inductive no_prefix : list position -> Prop :=
  | no_prefix_nil: no_prefix []
  | no_prefix_cons:
    forall p l,
    (forall p', In p' l -> ~ prefix p p' /\ ~ prefix p' p)
    -> no_prefix l
    -> no_prefix (p::l).

  Lemma no_prefix_subact_at_position_same:
    forall p s v p',
    ~ prefix p p'
    -> ~ prefix p' p
    -> subact_at_position (replace_at_position s p v) p'
       = subact_at_position s p'.
  Proof.
    induction p; simpl; intros; eauto.
    elim H. constructor.
    destruct p'. elim H0. constructor.
    destruct s; simpl.
    - repeat destr; simpl; auto.
    - repeat destr; simpl; auto.
    - repeat destr; simpl; auto.
      eapply IHp.
      intro P; apply H; constructor; auto.
      intro P; apply H0; constructor; auto.
      eapply IHp.
      intro P; apply H; constructor; auto.
      intro P; apply H0; constructor; auto.
      eapply IHp.
      intro P; apply H; constructor; auto.
      intro P; apply H0; constructor; auto.
    - repeat destr; simpl; auto.
      eapply IHp.
      intro P; apply H; constructor; auto.
      intro P; apply H0; constructor; auto.
    - repeat destr; simpl; auto.
      eapply IHp.
      intro P; apply H; constructor; auto.
      intro P; apply H0; constructor; auto.
      eapply IHp.
      intro P; apply H; constructor; auto.
      intro P; apply H0; constructor; auto.
    - repeat destr; simpl; auto.
      eapply IHp.
      intro P; apply H; constructor; auto.
      intro P; apply H0; constructor; auto.
    - repeat destr; simpl; auto.
  Qed.

  Lemma wt_sact_replace_at_positions:
    forall
      vvs ps (NP: no_prefix ps) s tn subact
      (POSOK: forall p (IN: In p ps),
        subact_at_position s p = Some subact)
      (WWT: wt_sact vvs subact tn) t (WT: wt_sact vvs s t) rep
      (WTrep: wt_sact vvs rep tn),
    wt_sact vvs (replace_at_positions s ps rep) t.
  Proof.
    induction 1; simpl; intros; eauto.
    eapply IHNP.
    - intros.
      erewrite no_prefix_subact_at_position_same. eauto.
      eapply H; eauto. eapply H; eauto.
    - eauto.
    - eapply wt_sact_replace_at_position; eauto.
    - eauto.
  Qed.

  Lemma wt_sact_replace_at_positions_in_vars:
    forall
      vvs positions (NP: forall k ps, positions ! k = Some ps -> no_prefix ps)
      subact
      (POSOK: forall k t s ps,
        positions ! k = Some ps
        -> vvs ! k = Some (t, s)
        -> forall p (IN: In p ps),
        subact_at_position s p = Some subact)
      tn (WWT: wt_sact vvs subact tn) rep (WTrep: wt_sact vvs rep tn) s t
      (WT: wt_sact vvs s t),
    wt_sact (replace_subact_in_vars vvs positions rep) s t.
  Proof.
    intros vvs positions NP subact POSOK tn WWT rep WTrep.
    induction 1; simpl; intros; eauto.
    - econstructor. setoid_rewrite PTree.gmap. setoid_rewrite H. simpl. eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.

  Lemma interp_sact_replace_at_position:
    forall vvs,
    wt_vvs (Sigma:=Sigma) R vvs
    -> vvs_smaller_variables vvs
    -> forall a0 p subact tn rep, subact_at_position a0 p = Some subact
    -> wt_sact vvs subact tn
    -> wt_sact vvs rep tn
    -> (forall ov : val, interp_sact vvs subact ov <-> interp_sact vvs rep ov)
    -> forall t v, wt_sact vvs a0 t
    -> interp_sact vvs a0 v
    -> interp_sact vvs (replace_at_position a0 p rep) v.
  Proof.
    induction a0; simpl; intros; eauto.
    - repeat destr_in H1; inv H1. apply H4; auto.
    - repeat destr_in H1; inv H1. apply H4; auto.
    - inv H5. repeat destr_in H1; inv H1.
      + apply H4; auto.
      + inv H6; econstructor; eauto. eapply IHa0_1; eauto.
      + inv H6. econstructor; eauto. destr. eapply IHa0_2; eauto.
      + inv H6; econstructor; eauto. destr. eapply IHa0_3; eauto.
    - inv H5. repeat destr_in H1; inv H1.
      + apply H4; auto.
      + inv H6; econstructor; eauto. eapply IHa0; eauto.
    - inv H5. repeat destr_in H1; inv H1.
      + apply H4; auto.
      + inv H6; econstructor; eauto. eapply IHa0_1; eauto.
      + inv H6. econstructor; eauto. eapply IHa0_2; eauto.
    - inv H5. repeat destr_in H1; inv H1.
      + apply H4; auto.
      + inv H6; econstructor; eauto. eapply IHa0; eauto.
    - inv H5. repeat destr_in H1; inv H1. apply H4; auto.
  Qed.

  Lemma interp_sact_replace_at_position':
    forall vvs,
    wt_vvs (Sigma:=Sigma) R vvs
    -> vvs_smaller_variables vvs
    -> forall a0 p subact tn rep, subact_at_position a0 p = Some subact
    -> wt_sact vvs subact tn
    -> wt_sact vvs rep tn
    -> (forall ov : val, interp_sact vvs subact ov <-> interp_sact vvs rep ov)
    -> forall t v, wt_sact vvs a0 t
    -> interp_sact vvs (replace_at_position a0 p rep) v
    -> interp_sact vvs a0 v.
  Proof.
    induction a0; simpl; intros; eauto.
    - repeat destr_in H1; inv H1. apply H4; auto.
    - repeat destr_in H1; inv H1. apply H4; auto.
    - inv H5. repeat destr_in H1; inv H1.
      + apply H4; auto.
      + inv H6; econstructor; eauto. eapply IHa0_1; eauto.
      + inv H6. econstructor; eauto. destr. eapply IHa0_2; eauto.
      + inv H6; econstructor; eauto. destr. eapply IHa0_3; eauto.
    - inv H5. repeat destr_in H1; inv H1.
      + apply H4; auto.
      + inv H6; econstructor; eauto. eapply IHa0; eauto.
    - inv H5. repeat destr_in H1; inv H1.
      + apply H4; auto.
      + inv H6; econstructor; eauto. eapply IHa0_1; eauto.
      + inv H6. econstructor; eauto. eapply IHa0_2; eauto.
    - inv H5. repeat destr_in H1; inv H1.
      + apply H4; auto.
      + inv H6; econstructor; eauto. eapply IHa0; eauto.
    - inv H5. repeat destr_in H1; inv H1. apply H4; auto.
  Qed.

  Lemma interp_sact_replace_at_position_iff:
    forall vvs,
    wt_vvs (Sigma:=Sigma) R vvs
    -> vvs_smaller_variables vvs
    -> forall a0 p subact tn rep, subact_at_position a0 p = Some subact
    -> wt_sact vvs subact tn
    -> wt_sact vvs rep tn
    -> (forall ov : val, interp_sact vvs subact ov <-> interp_sact vvs rep ov)
    -> forall t v, wt_sact vvs a0 t
    -> interp_sact vvs (replace_at_position a0 p rep) v
       <-> interp_sact vvs a0 v.
  Proof.
    split; intros.
    eapply interp_sact_replace_at_position'; eauto.
    eapply interp_sact_replace_at_position; eauto.
  Qed.

  Lemma interp_sact_replace_at_positions:
    forall vvs,
    wt_vvs (Sigma:=Sigma) R vvs
    -> vvs_smaller_variables vvs
    -> forall subact tn rep, wt_sact vvs subact tn
    -> wt_sact vvs rep tn
    -> (forall ov : val, interp_sact vvs subact ov <-> interp_sact vvs rep ov)
    -> forall ps a0 t v, wt_sact vvs a0 t
    -> (forall p : position, In p ps -> subact_at_position a0 p = Some subact)
    -> no_prefix ps
    -> interp_sact vvs a0 v
       <-> interp_sact vvs (replace_at_positions a0 ps rep) v.
  Proof.
    induction ps; simpl; intros; eauto. tauto.
    rewrite <- IHps.
    rewrite interp_sact_replace_at_position_iff; eauto. tauto.
    eapply wt_sact_replace_at_position; eauto.
    - inv H6. intros.
      rewrite no_prefix_subact_at_position_same. eauto. apply H9. auto.
      apply H9; auto.
    - inv H6; auto.
  Qed.

  Lemma wt_vvs_replace_subact_in_vars:
    forall
      vvs positions v (WTVVS: wt_vvs (Sigma := Sigma) R vvs) tt subact
      (OLDTYPE: wt_sact  vvs subact tt) (NEWTYPE: wt_sact  vvs v tt)
      (SUBACT: forall ps p k t a,
        vvs ! k = Some (t, a)
        -> positions ! k = Some ps
        -> In p ps
        -> subact_at_position a p = Some subact)
      (NP: forall ps k, positions ! k = Some ps -> no_prefix ps),
    wt_vvs (Sigma:=Sigma) R (replace_subact_in_vars vvs positions v).
  Proof.
    intros.
    unfold wt_vvs. intros.
    setoid_rewrite Maps.PTree.gmap in H. unfold option_map in H.
    destr_in H. 2: inv H. destr_in H. inv H.
    destr.
    intros; eapply wt_sact_replace_at_positions; eauto.
    eapply wt_sact_replace_at_positions_in_vars; eauto.
    eapply wt_sact_replace_at_positions_in_vars; eauto.
    eapply WTVVS; eauto.
    eapply wt_sact_replace_at_positions_in_vars; eauto.
    simpl.
    eapply wt_sact_replace_at_positions_in_vars; eauto.
    eapply WTVVS; eauto.
  Qed.

  Lemma var_in_sact_replace_at_position:
    forall a p b v,
    var_in_sact (replace_at_position a p b) v
    -> var_in_sact a v \/ var_in_sact b v.
  Proof.
    induction a; simpl; intros; eauto.
    - repeat destr_in H; eauto.
    - repeat destr_in H; eauto.
    - repeat destr_in H; eauto.
      inv H.
      edestruct IHa1; eauto. left; eapply var_in_if_cond; eauto.
      left; eapply var_in_if_true; eauto.
      left; eapply var_in_if_false; eauto.
      inv H.
      left; eapply var_in_if_cond; eauto.
      edestruct IHa2; eauto. left; eapply var_in_if_true; eauto.
      left; eapply var_in_if_false; eauto.
      inv H.
      left; eapply var_in_if_cond; eauto.
      left; eapply var_in_if_true; eauto.
      edestruct IHa3; eauto. left; eapply var_in_if_false; eauto.
    - repeat destr_in H; eauto.
      inv H.
      edestruct IHa; eauto. left; eapply var_in_sact_unop; eauto.
    - repeat destr_in H; eauto.
      inv H.
      edestruct IHa1; eauto. left; eapply var_in_sact_binop_1; eauto.
      left; eapply var_in_sact_binop_2; eauto.
      inv H.
      left; eapply var_in_sact_binop_1; eauto.
      edestruct IHa2; eauto. left; eapply var_in_sact_binop_2; eauto.
    - repeat destr_in H; eauto.
      inv H.
      edestruct IHa; eauto. left; eapply var_in_sact_external; eauto.
    - repeat destr_in H; eauto.
  Qed.

  Lemma var_in_sact_replace_at_positions:
    forall ps a b v,
    var_in_sact (replace_at_positions a ps b) v
    -> var_in_sact a v \/ var_in_sact b v.
  Proof.
    induction ps; simpl; intros; eauto.
    eapply IHps in H. destruct H; auto.
    edestruct var_in_sact_replace_at_position; eauto.
  Qed.

  Lemma subact_at_position_var_in_sact:
    forall s p s' v,
    subact_at_position s p = Some s'
    -> var_in_sact s' v
    -> var_in_sact s v.
  Proof.
    induction s; simpl; intros; eauto; repeat destr_in H; inv H; eauto.
    eapply var_in_if_cond; eauto.
    eapply var_in_if_true; eauto.
    eapply var_in_if_false; eauto.
    eapply var_in_sact_unop; eauto.
    eapply var_in_sact_binop_1; eauto.
    eapply var_in_sact_binop_2; eauto.
    eapply var_in_sact_external; eauto.
  Qed.

  Lemma vsv_replace_subact_in_vars:
    forall
      vvs positions v (VSV: vvs_smaller_variables vvs) tt subact
      (OLDTYPE: wt_sact  vvs subact tt) (NEWTYPE: wt_sact  vvs v tt)
      (SUBACT: forall ps p k t a,
        vvs ! k = Some (t, a)
        -> positions ! k = Some ps
        -> In p ps
        -> subact_at_position a p = Some subact)
      (SMALLER: forall var, var_in_sact v var -> var_in_sact subact var),
    vvs_smaller_variables (replace_subact_in_vars vvs positions v).
  Proof.
    intros.
    red. intros.
    setoid_rewrite Maps.PTree.gmap in H. unfold option_map in H.
    destr_in H. 2: inv H. inv H. destr_in H2. inv H2.
    edestruct var_in_sact_replace_at_positions. eauto. eapply VSV; eauto.
    eapply SMALLER in H.
    destr_in H0.
    2:{ simpl in *. eauto. }
    destruct l. simpl in H0; eauto.
    exploit SUBACT; eauto. left; reflexivity. intro EQ.
    eapply subact_at_position_var_in_sact in EQ.
    eapply VSV in EQ. 2: eauto. apply EQ. auto.
  Qed.

  Lemma interp_sact_var_iff:
    forall vvs var vv t s,
    vvs ! var = Some (t,s)
    -> interp_sact vvs (SVar var) vv <-> interp_sact vvs s vv.
  Proof.
    split.
    intro A; inv A. rewrite H in H1; inv H1. apply H2.
    intros; econstructor; eauto.
  Qed.

  Lemma sap_reach:
    forall (vvs: PTree.t (type * sact)) a1 a2,
    forall v, reachable_var vvs a1 v
    -> (forall v, var_in_sact a1 v -> var_in_sact a2 v)
    -> reachable_var vvs a2 v.
  Proof.
    induction 1; simpl; intros; eauto.
    - eapply var_in_sact_reachable; eauto. apply H. constructor.
    - trim (H1 x). constructor. eapply reachable_vars_in_sact2. 2: eauto.
      auto. auto.
    - eapply IHreachable_var. intros; eapply H0. eapply var_in_if_cond; eauto.
    - eapply IHreachable_var. intros; eapply H0. eapply var_in_if_true; eauto.
    - eapply IHreachable_var. intros; eapply H0. eapply var_in_if_false; eauto.
    - eapply IHreachable_var. intros; eapply H0.
      eapply var_in_sact_binop_1; eauto.
    - eapply IHreachable_var. intros; eapply H0.
      eapply var_in_sact_binop_2; eauto.
    - eapply IHreachable_var. intros; eapply H0. eapply var_in_sact_unop; eauto.
    - eapply IHreachable_var. intros; eapply H0.
      eapply var_in_sact_external; eauto.
  Qed.

  Lemma interp_sact_replace_subact:
    forall
      vvs positions (NP: forall k ps, positions ! k = Some ps -> no_prefix ps)
      subact
      (POSOK: forall k t s ps,
        positions ! k = Some ps
        -> vvs ! k = Some (t, s)
        -> forall p (IN: In p ps), subact_at_position s p = Some subact)
      tn (WWT: wt_sact vvs subact tn) rep (WTrep: wt_sact vvs rep tn)
      (WTvvs: wt_vvs (Sigma:=Sigma) R vvs) (VSV: vvs_smaller_variables vvs)
      (SAME1: forall ov, interp_sact vvs subact ov <-> interp_sact vvs rep ov)
      (SMALLER: forall var, var_in_sact rep var -> var_in_sact subact var)
      a n (LT: forall v, reachable_var vvs a v -> (v < n)%positive) t
      (WT: wt_sact vvs a t),
    forall vv,
    interp_sact vvs a vv
    <-> interp_sact (replace_subact_in_vars vvs positions rep) a vv.
  Proof.
    intros vvs positions NP subact POSOK tn WWT rep WTrep WTvvs VSV SAME1.
    intros SMALLER a n.
    change n with (projT1 (existT (fun _ => sact) n a)).
    change a with (projT2 (existT (fun _ => sact) n a)) at 1 3 4 5.
    generalize (existT (fun _ => sact) n a).
    clear n a. intro s. pattern s.
    eapply well_founded_induction.
    apply wf_order_sact. clear s.
    intros x IH BELOW t WTs vv.
    assert (IH2:
      forall a0,
      size_sact a0 < size_sact (projT2 x)
      -> (forall v0, reachable_var vvs a0 v0 -> (v0 < projT1 x)%positive)
      -> forall t (WT: wt_sact vvs a0 t), forall vv,
      interp_sact vvs a0 vv
      <-> interp_sact (replace_subact_in_vars vvs positions rep) a0 vv
    ). {
      intros. eapply (IH (existT _ (projT1 x) a0)).
      red. destruct x. apply Relation_Operators.right_lex. simpl in H.  auto.
      simpl. auto. simpl. auto. simpl. eauto.
    }
    destruct x; simpl in *.
    destruct s; simpl in *.
    - inv WTs.
      rewrite interp_sact_var_iff. 2: eauto.
      rewrite interp_sact_var_iff.
      2: setoid_rewrite PTree.gmap; setoid_rewrite H0; simpl; eauto.
      destr. 2: simpl. destruct l.
      simpl.
      {
        eapply (IH (existT _ var s)). red. apply Relation_Operators.left_lex.
        apply BELOW. constructor.
        simpl. eapply reachable_var_aux_below_get; eauto.
        simpl. eapply WTvvs; eauto.
      }
      2: {
        eapply (IH (existT _ var s)). red.
        apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl. eapply reachable_var_aux_below_get; eauto.
        simpl. eapply WTvvs; eauto.
      }
      erewrite <- interp_sact_replace_at_positions; eauto.
      eapply (IH (existT _ var s)); simpl; eauto.
      red. apply Relation_Operators.left_lex. apply BELOW. econstructor.
      apply (reachable_var_aux_below_get _ VSV _ _ _ H0). eapply WTvvs; eauto.
      eapply wt_vvs_replace_subact_in_vars. 4: intros; eapply POSOK; eauto.
      all: eauto.
      eapply vsv_replace_subact_in_vars. 4: intros; eapply POSOK; eauto.
      all: eauto.
      2: eapply wt_sact_replace_at_positions_in_vars; eauto.
      intros; eapply wt_sact_replace_at_positions_in_vars.
      2: eapply POSOK; eauto.
      all: eauto.
      2: intros; eapply wt_sact_replace_at_positions_in_vars.
      3: eapply POSOK; eauto. all: eauto. 2: eapply WTvvs; eauto.
      intros. exploit POSOK; eauto. left; reflexivity. intro SAP.
      generalize (fun v => subact_at_position_var_in_sact _ _ _ v SAP).
      intro SAPVIS.
      erewrite <- (IH (existT _ var subact)); simpl; eauto.
      2: red. 2: eapply Relation_Operators.left_lex. 2: apply BELOW.
      2: constructor.
      erewrite <- (IH (existT _ var rep)); simpl; eauto.
      red. eapply Relation_Operators.left_lex. apply BELOW. constructor.
      intros.
      eapply sap_reach in H; eauto.
      eapply sap_reach in H; eauto.
      eapply reachable_var_aux_below_get; eauto.
      intros.
      eapply sap_reach in H; eauto.
      eapply reachable_var_aux_below_get; eauto.
    - intros. split; intro A; inv A; econstructor.
    - inv WTs.
      intros.
      split; intro A; inv A.
      + econstructor.
        eapply (IH2 s1). lia. intros; eapply BELOW.
        eapply reachable_var_if_cond; eauto. eauto. eauto.
        eapply (IH2 (if b then s2 else s3)).
        destr; lia. intros; eapply BELOW. destr_in H.
        eapply reachable_var_if_true; eauto.
        eapply reachable_var_if_false; eauto.
        destr; eauto. eauto.
      + econstructor.
        eapply (IH2 s1). lia. intros; eapply BELOW.
        eapply reachable_var_if_cond; eauto. eauto. eauto.
        eapply (IH2 (if b then s2 else s3)).
        destr; lia. intros; eapply BELOW. destr_in H.
        eapply reachable_var_if_true; eauto.
        eapply reachable_var_if_false; eauto.
        destr; eauto. eauto.
    - inv WTs; intros.
      split; intro A; inv A; econstructor; eauto.
      eapply (IH2 s). lia. intros; eapply BELOW.
      eapply reachable_var_unop; eauto. eauto. eauto.
      eapply (IH2 s). lia. intros; eapply BELOW.
      eapply reachable_var_unop; eauto. eauto. eauto.
    - inv WTs; intros.
      split; intro A; inv A; econstructor; eauto.
      eapply (IH2 s1). lia. intros; eapply BELOW.
      eapply reachable_var_binop1; eauto. eauto. eauto.
      eapply (IH2 s2). lia. intros; eapply BELOW.
      eapply reachable_var_binop2; eauto. eauto. eauto.
      eapply (IH2 s1). lia. intros; eapply BELOW.
      eapply reachable_var_binop1; eauto. eauto. eauto.
      eapply (IH2 s2). lia. intros; eapply BELOW.
      eapply reachable_var_binop2; eauto. eauto. eauto.
    - inv WTs; intros.
      split; intro A; inv A; econstructor; eauto.
      eapply (IH2 s). lia. intros; eapply BELOW.
      eapply reachable_var_externalCall; eauto. eauto. eauto.
      eapply (IH2 s). lia. intros; eapply BELOW.
      eapply reachable_var_externalCall; eauto. eauto. eauto.
    - intros. split; intro A; inv A; econstructor.
  Qed.

  Lemma interp_sact_replace_subact_iff:
    forall
      vvs positions (NP: forall k ps, positions ! k = Some ps -> no_prefix ps)
      subact
      (POSOK: forall k t s ps,
        positions ! k = Some ps
        -> vvs ! k = Some (t, s)
        -> forall p (IN: In p ps), subact_at_position s p = Some subact)
      tn (WWT: wt_sact vvs subact tn) rep (WTrep: wt_sact vvs rep tn)
      (WTvvs: wt_vvs (Sigma:=Sigma) R vvs) (VSV: vvs_smaller_variables vvs)
      (SAME1: forall ov,
        interp_sact vvs subact ov <-> interp_sact vvs rep ov)
      (SMALLER: forall var, var_in_sact rep var -> var_in_sact subact var) a t
      (WT: wt_sact vvs a t),
    forall vv, interp_sact vvs a vv
    <-> interp_sact (replace_subact_in_vars vvs positions rep) a vv.
  Proof.
    intros; eapply interp_sact_replace_subact; eauto.
    intros; eapply reachable_var_aux_below; eauto.
    intros. eapply wt_sact_valid_vars; eauto. apply vvs_range_max_var.
  Qed.

  Record subact_ok vvs positions subact rep :=
    {
      so_np: forall k ps, positions ! k = Some ps -> no_prefix ps;
      so_posok: forall k t s ps,
        positions ! k = Some ps ->
        vvs ! k = Some (t, s) ->
        forall p (IN: In p ps),
          subact_at_position s p = Some subact;
      so_tn: type;
      so_wt_subact: wt_sact vvs subact so_tn;
      so_wt_rep: wt_sact vvs rep so_tn;
      so_interp: forall ov,
        interp_sact vvs subact ov <-> interp_sact vvs rep ov;
      so_smaller: forall var, var_in_sact rep var -> var_in_sact subact var;
    }.

  Lemma subact_ok_interp_sact_replace_subact:
    forall vvs positions subact rep
           (SO: subact_ok vvs positions subact rep)
           (WTvvs: wt_vvs (Sigma:=Sigma) R  vvs)
           (VSV: vvs_smaller_variables vvs)
           a t (WT: wt_sact vvs a t),
    forall vv,
      interp_sact vvs a vv <->
        interp_sact (replace_subact_in_vars vvs positions rep) a vv.
  Proof.
    intros. inv SO.
    intros; eapply interp_sact_replace_subact_iff; eauto.
  Qed.

  Lemma wf_sf_replace_subact':
    forall sf positions subact rep,
      subact_ok (vars sf) positions subact rep ->
      wf_sf sf -> wf_sf (replace_subact sf positions rep).
  Proof.
    intros sf positions subact rep SO WF.
    destruct WF. destruct SO.
    split.
    - simpl. eapply wt_vvs_replace_subact_in_vars; auto. apply so_wt_subact0. all: eauto.
    - eapply vsv_replace_subact_in_vars; auto. apply so_wt_subact0. all: eauto.
    - simpl. intros. eapply wt_sact_replace_at_positions_in_vars; eauto.
      eapply wf_sf_final; eauto.
  Qed.

  Lemma sf_eq_replace_subact:
    forall sf
           (WFSF: wf_sf sf)
           positions subact rep
           (SO: subact_ok (vars sf) positions subact rep),
      sf_eq R Sigma r sigma sf (replace_subact sf positions rep).
  Proof.
    intros.
    split.
    - reflexivity.
    - intros. eapply subact_ok_interp_sact_replace_subact; eauto. apply WFSF.  apply WFSF.
    - simpl. intros.
      split. intro A; inv A. econstructor.
      setoid_rewrite PTree.gmap. unfold option_map. setoid_rewrite H1. eauto.
      intro A; inv A.
      setoid_rewrite PTree.gmap in H1. unfold option_map in H1.
      destr_in H1; inv H1. destr_in H2. inv H2. econstructor; eauto.
  Qed.

  Lemma replace_subact_interp_cycle_ok':
    forall
      sf
      (WFSF: wf_sf sf)
      positions subact rep
      (SO: subact_ok (vars sf) positions subact rep) reg,
      getenv REnv (interp_cycle r sigma sf) reg
      = getenv REnv (interp_cycle r sigma (replace_subact sf positions rep)) reg.
  Proof.
    intros.
    eapply sf_eq_interp_cycle_ok; eauto.
    - eapply wf_sf_replace_subact' in WFSF; eauto.
    - eapply sf_eq_replace_subact; eauto.
  Qed.

  Lemma subact_ok_set:
    forall vvs positions subact rep k ps,
    subact_ok vvs positions subact rep ->
    no_prefix ps ->
    (forall t s, vvs ! k = Some (t, s) -> forall p, In p ps -> subact_at_position s p = Some subact) ->
    subact_ok vvs (PTree.set k ps positions) subact rep.
  Proof.
    intros vvs positions subact rep k ps SO NP SAP; inv SO; econstructor; eauto.
    - intros. rewrite PTree.gsspec in H. destr_in H; eauto. inv H. auto.
    - intros. rewrite PTree.gsspec in H. destr_in H; eauto. inv H. eauto.
  Qed.

Lemma subact_at_pos_refl: forall (x: sact),
    subact_at_position x [] = Some x.
Proof.
  induction x; simpl; intros; reflexivity.
Qed.

Lemma subact_at_pos_rev_refl: forall (x: sact),
    subact_at_position x (List.rev []) = Some x.
Proof.
  intros; simpl; eapply subact_at_pos_refl.
Qed.

Lemma subact_at_pos_trans:
  forall (s: sact) p1 s1 p2 s2,
    subact_at_position s p1 = Some s1 ->
    subact_at_position s1 p2 = Some s2 ->
    subact_at_position s (p1 ++ p2) = Some s2.
Proof.
  induction s; simpl; intros;
    repeat destr_in H; inv H; simpl in *; eauto.
Qed.

Lemma subact_at_pos_unop1:
  forall s pos ufn a,
    subact_at_position s (List.rev pos) = Some (SUnop ufn a) ->
    subact_at_position s (List.rev (branch1 :: pos)) = Some a.
Proof.
  intros. simpl. erewrite subact_at_pos_trans. 2: eauto. eauto. simpl.
  apply subact_at_pos_refl.
Qed.

Lemma subact_at_pos_extcall1:
  forall s pos ufn a,
    subact_at_position s (List.rev pos) = Some (SExternalCall ufn a) ->
    subact_at_position s (List.rev (branch1 :: pos)) = Some a.
Proof.
  intros. simpl. erewrite subact_at_pos_trans. 2: eauto. eauto. simpl.
  apply subact_at_pos_refl.
Qed.

Lemma subact_at_pos_binop1:
  forall s pos ufn a1 a2,
    subact_at_position s (List.rev pos) = Some (SBinop ufn a1 a2) ->
    subact_at_position s (List.rev (branch1 :: pos)) = Some a1.
Proof.
  intros. simpl. erewrite subact_at_pos_trans. 2: eauto. eauto. simpl.
  apply subact_at_pos_refl.
Qed.

Lemma subact_at_pos_binop2:
  forall s pos ufn a1 a2,
    subact_at_position s (List.rev pos) = Some (SBinop ufn a1 a2) ->
    subact_at_position s (List.rev (branch2 :: pos)) = Some a2.
Proof.
  intros. simpl. erewrite subact_at_pos_trans. 2: eauto. eauto. simpl.
  apply subact_at_pos_refl.
Qed.


Lemma subact_at_pos_if1:
  forall s pos a1 a2 a3,
    subact_at_position s (List.rev pos) = Some (SIf a1 a2 a3) ->
    subact_at_position s (List.rev (branch1 :: pos)) = Some a1.
Proof.
  intros. simpl. erewrite subact_at_pos_trans. 2: eauto. eauto. simpl.
  apply subact_at_pos_refl.
Qed.

Lemma subact_at_pos_if2:
  forall s pos a1 a2 a3,
    subact_at_position s (List.rev pos) = Some (SIf a1 a2 a3) ->
    subact_at_position s (List.rev (branch2 :: pos)) = Some a2.
Proof.
  intros. simpl. erewrite subact_at_pos_trans. 2: eauto. eauto. simpl.
  apply subact_at_pos_refl.
Qed.

Lemma subact_at_pos_if3:
  forall s pos a1 a2 a3,
    subact_at_position s (List.rev pos) = Some (SIf a1 a2 a3) ->
    subact_at_position s (List.rev (branch3 :: pos)) = Some a3.
Proof.
  intros. simpl. erewrite subact_at_pos_trans. 2: eauto. eauto. simpl.
  apply subact_at_pos_refl.
Qed.

Lemma no_prefix_one a:
  no_prefix [a].
Proof.
  repeat constructor. easy. easy.
Qed.

Definition search_subterm_propP needle (haystack: sact) pos ps :=
  no_prefix (List.map (fun l => List.rev l) ps)
  /\ Forall (fun v => subact_at_position haystack (rev v) = Some needle) ps
  /\ Forall (fun p => exists x, p = x ++ pos) ps.

Definition search_subterm_prop needle (haystack: sact) pos :=
  sigT (search_subterm_propP needle haystack pos).

Definition ssprop_one (pos: position) needle (haystack: sact)
  (Ppos: subact_at_position haystack (rev pos) = Some needle ) : search_subterm_prop needle haystack pos.
Proof.
  exists [pos]. split. apply no_prefix_one. split. constructor; auto.
  constructor; auto. exists nil; reflexivity.
Defined.

Definition ssprop_nil needle (haystack: sact) pos : search_subterm_prop needle haystack pos.
Proof.
  exists []. split. apply no_prefix_nil. constructor; auto.
Defined.

Lemma prefix_app:
  forall {A:Type} (l: list A) l1 l2,
    prefix (l ++ l1) (l ++ l2) -> prefix l1 l2.
Proof.
  induction l; simpl; intros; eauto.
  inv H. eauto.
Qed.

Lemma no_prefix_app:
  forall l1,
    no_prefix l1 ->
    forall l2,
      no_prefix l2 ->
      forall (P1 P2: position -> Prop),
        (forall x: position, P1 x -> P2 x -> False) ->
        (forall x y, P1 x -> P2 y -> ~ prefix x y /\ ~ prefix y x) ->
      Forall P1 l1 ->
      Forall P2 l2 ->
      no_prefix (l1 ++ l2).
Proof.
  induction 1; simpl; intros l2 NP2 P1 P2 P12 PNP Fl1 Fl2; eauto.
  inv Fl1. constructor; eauto.
  intros. apply in_app_iff in H1. destruct H1.
  edestruct H. apply H1. auto.
  eapply PNP; eauto.
  rewrite Forall_forall in Fl2; apply Fl2 in H1. auto.
Qed.

Lemma no_prefix_app2:
  forall pos l1,
    no_prefix l1 ->
    forall l2,
      no_prefix l2 ->
      Forall (fun p => exists x, p = rev pos ++ branch1 :: x) l1 ->
      Forall (fun p => exists x, p = rev pos ++ branch2 :: x) l2 ->
      no_prefix (l1 ++ l2).
Proof.
  intros. eapply no_prefix_app. auto. auto. 3-4: eauto.
  all: simpl.
  intros x (x0 & EQ) (x1 & EQ'). subst. apply app_inv_head in EQ'. congruence.
  intros x y (x0 & EQ) (x1 & EQ'). subst.
  split; intro A.
  apply prefix_app in A. inv A.
  apply prefix_app in A. inv A.
Qed.

Lemma no_prefix_app3:
  forall pos l1,
    no_prefix l1 ->
    forall l2,
      no_prefix l2 ->
    forall l3,
      no_prefix l3 ->
      Forall (fun p => exists x, p = rev pos ++ branch1 :: x) l1 ->
      Forall (fun p => exists x, p = rev pos ++ branch2 :: x) l2 ->
      Forall (fun p => exists x, p = rev pos ++ branch3 :: x) l3 ->
      no_prefix (l1 ++ l2 ++ l3).
Proof.
  intros. eapply no_prefix_app. auto.
  eapply no_prefix_app. auto. auto. 3-4,7: eauto.
  all: simpl.
  intros x (x0 & EQ) (x1 & EQ'). subst. apply app_inv_head in EQ'. congruence.
  intros x y (x0 & EQ) (x1 & EQ'). subst.
  split; intro A.
  apply prefix_app in A. inv A.
  apply prefix_app in A. inv A.
  instantiate (1:= fun x => exists x0, x = rev pos ++ branch2 :: x0 \/ x = rev pos ++ branch3 :: x0).
  all: simpl.
  intros x (x0 & EQ) (x1 & EQ'). subst.
  destruct EQ' as [EQ'|EQ']; apply app_inv_head in EQ'; congruence.
  intros x y (x0 & EQ) (x1 & EQ'). subst.
  destruct EQ' as [EQ'|EQ']; split; intro A; subst;
    apply prefix_app in A; inv A.
  apply Forall_app; split; eapply Forall_impl. 2: apply H3. 3: apply H4.
  intros a (x & EQ); eauto.
  intros a (x & EQ); eauto.
Qed.

Definition sprop_unop needle pos a ps1
  (p1: search_subterm_propP needle a (branch1 :: pos) ps1):
  search_subterm_propP needle a pos ps1.
Proof.
  destruct p1 as (d1 & d2 & d3).
  split;[|split]; auto.
  eapply Forall_impl. 2: apply d3. simpl. intros aa (x & EQ). subst. exists (x ++ branch1 :: nil); simpl; auto. rewrite <- app_assoc. reflexivity.
Qed.

Definition sprop_binop needle pos a ps1 ps2
  (p1: search_subterm_propP needle a (branch1 :: pos) ps1)
  (p2: search_subterm_propP needle a (branch2 :: pos) ps2):
  search_subterm_propP needle a pos (ps1 ++ ps2).
Proof.
  destruct p1 as (d1 & d2 & d3).
  destruct p2 as (e1 & e2 & e3).
  split;[|split].
  -  rewrite List.map_app. eapply no_prefix_app2. eauto. eauto.
     rewrite Forall_forall in d3 |- *. intros x IN.
     rewrite in_map_iff in IN. destruct IN as (x0 & EQ & IN). subst.
     destruct (d3 _ IN) as (x1 & EQ). subst. rewrite rev_app_distr. simpl. rewrite <- app_assoc. simpl. eauto.
     rewrite Forall_forall in e3 |- *. intros x IN.
     rewrite in_map_iff in IN. destruct IN as (x0 & EQ & IN). subst.
     destruct (e3 _ IN) as (x1 & EQ). subst. rewrite rev_app_distr. simpl. rewrite <- app_assoc. simpl. eauto.
  - apply Forall_app. split; eauto.
  - apply Forall_app. split; eauto.
    + eapply Forall_impl. 2: apply d3. simpl. intros aa (x & EQ). subst. exists (x ++ branch1 :: nil); simpl; auto. rewrite <- app_assoc. reflexivity.
    + eapply Forall_impl. 2: apply e3. simpl. intros aa (x & EQ). subst. exists (x ++ branch2 :: nil); simpl; auto. rewrite <- app_assoc. reflexivity.
Qed.

Definition sprop_if needle pos a ps1 ps2 ps3
  (p1: search_subterm_propP needle a (branch1 :: pos) ps1)
  (p2: search_subterm_propP needle a (branch2 :: pos) ps2)
  (p3: search_subterm_propP needle a (branch3 :: pos) ps3):
  search_subterm_propP needle a pos (ps1 ++ ps2 ++ ps3).
Proof.
  destruct p1 as (d1 & d2 & d3).
  destruct p2 as (e1 & e2 & e3).
  destruct p3 as (f1 & f2 & f3).
  split;[|split].
  - rewrite ! List.map_app.
    eapply no_prefix_app3; eauto.
    + rewrite Forall_forall in d3 |- *. intros x IN.
      rewrite in_map_iff in IN. destruct IN as (x0 & EQ & IN). subst.
      destruct (d3 _ IN) as (x1 & EQ). subst. rewrite rev_app_distr. simpl. rewrite <- app_assoc. simpl. eauto.
    + rewrite Forall_forall in e3 |- *. intros x IN.
      rewrite in_map_iff in IN. destruct IN as (x0 & EQ & IN). subst.
      destruct (e3 _ IN) as (x1 & EQ). subst. rewrite rev_app_distr. simpl. rewrite <- app_assoc. simpl. eauto.
    + rewrite Forall_forall in f3 |- *. intros x IN.
      rewrite in_map_iff in IN. destruct IN as (x0 & EQ & IN). subst.
      destruct (f3 _ IN) as (x1 & EQ). subst. rewrite rev_app_distr. simpl. rewrite <- app_assoc. simpl. eauto.
  - apply Forall_app; split; auto.
    apply Forall_app; split; auto.
  - apply Forall_app; split; auto.
    2: apply Forall_app; split; auto.
    + eapply Forall_impl. 2: apply d3. simpl. intros aa (x & EQ). subst. exists (x ++ branch1 :: nil); simpl; auto. rewrite <- app_assoc. reflexivity.
    + eapply Forall_impl. 2: apply e3. simpl. intros aa (x & EQ). subst. exists (x ++ branch2 :: nil); simpl; auto. rewrite <- app_assoc. reflexivity.
    + eapply Forall_impl. 2: apply f3. simpl. intros aa (x & EQ). subst. exists (x ++ branch3 :: nil); simpl; auto. rewrite <- app_assoc. reflexivity.
Qed.


Definition ptree_forall {A: Type} (P: positive -> A -> Prop) (t: Maps.PTree.t A) :=
  forall k v, Maps.PTree.get k t = Some v -> P k v.

Lemma ptree_set_prop {A: Type} (t: Maps.PTree.t A) P
  (FA: ptree_forall P t)
  k v
  (PKV: P k v):
  ptree_forall P (Maps.PTree.set k v t).
Proof.
  unfold ptree_forall in *.
  intros.
  rewrite Maps.PTree.gsspec in H. destr_in H; eauto. inv H. auto.
Qed.

Lemma ptree_forall_empty {A: Type} P:
  ptree_forall P (Maps.PTree.empty A).
Proof.
  unfold ptree_forall. intros. rewrite Maps.PTree.gempty in H. congruence.
Qed.

Definition ssearch_in_elemsT (needle: sact) (l: list (positive * (type * sact))) :=
  sigT (fun v : list (positive * list position) =>
          Forall2 (fun '(k, (t, a)) '(k1, ps) =>
                     k = k1 /\ search_subterm_propP needle a [] ps
            ) l v
    ).

Definition ssearch_in_elemsT_nil  (needle: sact) :
  ssearch_in_elemsT needle [].
Proof.
  exists []. constructor.
Defined.


Lemma search_subterm_prop_to_nil (needle: sact) a pos ps:
  search_subterm_propP needle a pos ps ->
  search_subterm_propP needle a [] ps.
Proof.
  intros (A & B & C).
  repeat split; auto.
  rewrite Forall_forall. intros; eexists; rewrite app_nil_r; eauto.
Qed.

Definition ssearch_in_elemsT_cons (needle: sact) l k t pos a:
  ssearch_in_elemsT needle l ->
  search_subterm_prop needle a pos ->
  ssearch_in_elemsT needle ((k,(t,a))::l).
Proof.
  intros (pss & PSS) (ps & PS).
  exists ((k,ps)::pss). constructor. split. apply eq_refl.
  eapply search_subterm_prop_to_nil; eauto. apply PSS.
Defined.


Fixpoint ptree_of_elements {A: Type} (l: list (positive * A)) :=
  match l with
    [] => Maps.PTree.empty A
  | (k,v)::r => Maps.PTree.set k v (ptree_of_elements r)
  end.


Lemma forall2_elems:
  forall {A B: Type}
         (l1: list (positive * A))
         (l2: list (positive * B)) P,
    Forall2 (fun '(k, a) '(k1,v) => k = k1 /\ P a v) l1 l2 ->
    NoDup (List.map fst l1) ->
    let res := ptree_of_elements l2 in
    forall k ps a,
      In (k, a) l1 ->
      Maps.PTree.get k res = Some ps ->
      P a ps.
Proof.
  induction 1; simpl; intros; eauto. easy.
  destr_in H3.
  rewrite Maps.PTree.gsspec in H3.
  destruct x. destruct H. subst. simpl in H1. inv H1.
  destr_in H3.
  - inv H3. destruct H2 as [C|C]. inv C. auto.
    elim H6. change p with (fst (p, a)). apply in_map. auto.
  - destruct H2. inv H. congruence.
    eauto.
Qed.


Lemma forall2_elems':
  forall {A B: Type}
         (l1: Maps.PTree.t A)
         (l2: list (positive * B)) P,
    Forall2 (fun '(k, a) '(k1,v) => k = k1 /\ P a v) (Maps.PTree.elements l1) l2 ->
    let res := ptree_of_elements l2 in
    forall k ps a,
      Maps.PTree.get k l1 = Some a ->
      Maps.PTree.get k res = Some ps ->
      P a ps.
Proof.
  intros.
  eapply forall2_elems; eauto.
  apply Maps.PTree.elements_keys_norepet.
  apply Maps.PTree.elements_correct; auto.
Qed.


Lemma forall2_elems'':
  forall {A B C: Type}
         (l1: Maps.PTree.t (C * A))
         (l2: list (positive * B)) P,
    Forall2 (fun '(k, (t, a)) '(k1,v) => k = k1 /\ P a v) (Maps.PTree.elements l1) l2 ->
    let res := ptree_of_elements l2 in
    forall k ps t a,
      Maps.PTree.get k l1 = Some (t, a) ->
      Maps.PTree.get k res = Some ps ->
      P a ps.
Proof.
  intros.
  eapply forall2_elems' with (P := fun '(t,a) v => P a v) in H0. eauto.
  2: eauto.
  eapply Wt.Forall2_impl. eauto. simpl. intros. destruct x. destruct p0,y.
  destruct H4. subst. split; auto.
Qed.

Lemma ptree_of_elements_get:
  forall {A: Type} (l: list (positive * A)) k v,
  (ptree_of_elements l) ! k = Some v ->
  In (k,v) l.
Proof.
  induction l; simpl; intros; eauto.
  rewrite PTree.gempty in H. congruence.
  destruct a.
  rewrite PTree.gsspec in H. destr_in H; auto. inv H. auto.
Qed.

Lemma forall2_in_exr:
  forall {A B: Type} (P: A -> B -> Prop) l1 l2,
    Forall2 P l1 l2 -> forall y,
      In y l2 ->
      exists x, In x l1 /\ P x y.
Proof.
  induction 1; simpl; intros; eauto. easy.
  destruct H1. subst. eauto.
  edestruct IHForall2; eauto. destruct H2; eauto.
Qed.

Lemma forall2_in_exl:
  forall {A B: Type} (P: A -> B -> Prop) l1 l2,
    Forall2 P l1 l2 -> forall x,
      In x l1 ->
      exists y, In y l2 /\ P x y.
Proof.
  induction 1; simpl; intros; eauto. easy.
  destruct H1. subst. eauto.
  edestruct IHForall2; eauto. destruct H2; eauto.
Qed.

Lemma interp_sact_iff_from_implies:
  forall vvs (WTV: wt_vvs R (Sigma:=Sigma) vvs) (VSV: vvs_smaller_variables vvs),
  forall t a1 a2,
    wt_sact vvs a1 t ->
    (forall ov, interp_sact vvs a1 ov -> interp_sact vvs a2 ov) ->
    (forall ov, interp_sact vvs a1 ov <-> interp_sact vvs a2 ov).
Proof.
  intros.
  split; auto.
  intros.
  edestruct @wt_sact_interp as (x & IS & WTv). eauto. eauto. eauto. eauto. apply vvs_range_max_var. apply H.
  exploit @interp_sact_determ. apply H1. apply H0. apply IS. intro; subst. auto.
Qed.

Lemma subact_ok_ltac:
        forall l1 l2 subact,
          Forall2
            (fun '(k, (ty, a)) '(k1, ps) =>
               k = k1 /\
                 (fun '(_, a0) (ps0 : list (list Direction.direction)) =>
                    search_subterm_propP subact a0 [] ps0) (ty, a) ps) (Maps.PTree.elements l1) l2 ->
          forall rep tn,
            wt_sact l1 subact tn ->
            wt_sact l1 rep tn ->
            (forall ov, interp_sact l1 subact ov <-> interp_sact l1 rep ov) ->
            (forall v, var_in_sact rep v -> var_in_sact subact v) ->
            subact_ok l1 (ptree_of_elements (List.map (fun '(k,ps) => (k, List.map (fun l => rev l) ps)) l2))
              subact rep.
Proof.
  intros.
  econstructor.
  - intros k ps GET. apply ptree_of_elements_get in GET.
    apply in_map_iff in GET.
    destruct GET as (x & EQ & IN). destruct x. inv EQ.
    edestruct @forall2_in_exr as (x & IN' & PP). apply H. eauto. simpl in PP.
    destruct x. destruct p0. destruct PP. subst.
    destruct H5 as (A & B & C).
    auto.
  - intros k t s ps GET. apply ptree_of_elements_get in GET.
    apply in_map_iff in GET.
    destruct GET as (x & EQ & IN). destruct x. inv EQ.
    intros GET p INl.
    edestruct @forall2_in_exr as (x & IN' & PP). apply H. eauto. simpl in PP.
    destruct x. destruct p1. destruct PP. subst.
    generalize (PTree.elements_complete _ _ _ IN'). rewrite GET. intro A; inv A.
    destruct H5 as (A & B & C).
    apply in_map_iff in INl.
    destruct INl as (x & EQ & INl).
    rewrite Forall_forall in B. apply B in INl. subst. auto.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
Qed.

Lemma subact_ok_ltac_1var:
  forall l1 subact k t a ps,
    l1 ! k = Some (t, a) ->
    search_subterm_propP subact a [] ps ->
    forall rep tn,
      wt_sact l1 subact tn ->
      wt_sact l1 rep tn ->
      (forall ov, interp_sact l1 subact ov <-> interp_sact l1 rep ov) ->
      (forall v, var_in_sact rep v -> var_in_sact subact v) ->
      subact_ok l1 (PTree.set k (List.map (fun v => rev v) ps) (PTree.empty _)) subact rep.
Proof.
  intros.
  econstructor.
  - intros kk pss GET. rewrite PTree.gsspec, PTree.gempty in GET.
    destr_in GET; inv GET. destruct H0. auto.
  - intros k0 t0 s ps0 GET. rewrite PTree.gsspec, PTree.gempty in GET.
    destr_in GET; inv GET.
    intros GET p INl. rewrite H in GET. inv GET.
    destruct H0 as (A & B & C).
    apply in_map_iff in INl.
    destruct INl as (x & EQ & INl).
    rewrite Forall_forall in B. apply B in INl. subst. auto.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
Qed.
End ReplaceSubact.
