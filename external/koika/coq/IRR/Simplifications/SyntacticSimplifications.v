Require Import Koika.KoikaForm.Untyped.UntypedSemantics.
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

Section SimplifySIfs.
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

  Definition simplify_sif_sact (ua: sact) : sact :=
    match ua with
    | SIf cond (SVar x) (SVar y) => if Pos.eqb x y then (SVar x) else ua
    | SIf cond (SConst (Bits [x])) (SConst (Bits [y])) =>
      if Bool.eqb x y then (SConst (Bits [x])) else ua
    | _ => ua
    end.

  Definition simplify_sifs (v: var_value_map) :=
    Maps.PTree.map (fun _ '(t, a) => (t, simplify_sif_sact a)) v.

  Definition simplify_sifs_sf (sf: IRR (rule_name_t := rule_name_t)) :=
    sf <| vars := simplify_sifs (vars sf) |>.

  Lemma simplify_sif_sact_correct:
    forall vvs (WTV: wt_vvs R (Sigma:=Sigma) vvs) n a res t,
    wt_sact (Sigma:=Sigma) R vvs a t
    -> eval_sact vvs a n = Some res
    -> eval_sact vvs (simplify_sif_sact a) n = Some res.
  Proof.
    intros.
    destruct a; auto.
    simpl. destruct a2; auto. destruct a3; auto. destr; auto.
    rewrite Pos.eqb_eq in Heqb. subst.
    destruct n; auto.
    simpl in H0. inv H.
    destruct (eval_sact vvs a1 n); try (inversion H0; fail).
    destruct v; try (inversion H0; fail).
    destruct v; try (inversion H0; fail).
    destruct v; try (inversion H0; fail).
    simpl in H0.
    destruct b; eapply eval_sact_more_fuel; try eapply Nat.le_succ_diag_r; auto.
    (* SIf x T T, SIf x F F *)
    repeat (destruct v; eauto). destruct a3; eauto.
    repeat (destruct v; eauto). destr.
    rewrite Bool.eqb_true_iff in Heqb1. subst.
    destruct n; auto.
    eapply eval_sact_more_fuel; try eapply Nat.le_succ_diag_r; auto.
    simpl in H0.
    destruct (eval_sact vvs a1 n); try (inversion H0; fail).
    repeat (destruct v; try (inversion H0; fail)).
    simpl in H0. destruct b; eauto.
  Qed.

  Lemma wt_simplify_sif_sact:
    forall vss a t,
    wt_sact R (Sigma:=Sigma) vss a t
    -> wt_sact R (Sigma:=Sigma) vss (simplify_sif_sact a) t.
  Proof.
    intros.
    destruct a; auto.
    simpl. destruct a2; auto. destruct a3; auto. destr; auto.
    rewrite Pos.eqb_eq in Heqb. subst.
    inv H. auto.
    repeat destr. inv H. auto.
  Qed.

  Lemma simplify_sif_sact_wt_sact_ok':
    forall vvs a t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
    wt_sact (Sigma := Sigma) R vvs (simplify_sif_sact a) t.
  Proof. apply wt_simplify_sif_sact. Qed.

  Lemma simplify_sifs_wt_sact_ok:
    forall vvs s t (WTS: wt_sact (Sigma := Sigma) R (simplify_sifs vvs) s t),
    wt_sact (Sigma := Sigma) R vvs s t.
  Proof.
    intros.
    induction WTS; try (econstructor; eauto; fail).
    unfold simplify_sifs in H.
    rewrite Maps.PTree.gmap in H. unfold option_map in H.
    destr_in H. destruct p.
    - apply Some_inj in H. apply pair_inj in H. destruct H. subst.
      econstructor. eauto.
    - easy.
  Qed.

  Lemma simplify_sifs_wt_sact_ok':
    forall vvs s t (WTS: wt_sact (Sigma := Sigma) R vvs s t),
    wt_sact (Sigma := Sigma) R (simplify_sifs vvs) s t.
  Proof.
    intros.
    induction WTS; econstructor; eauto.
    unfold simplify_sifs.
    setoid_rewrite Maps.PTree.gmap.
    unfold option_map. setoid_rewrite H. easy.
  Qed.

  Lemma simplify_sifs_wtvvs_ok':
    forall vvs (WTVVS: wt_vvs (Sigma := Sigma) R vvs),
    wt_vvs (Sigma := Sigma) R (simplify_sifs vvs).
  Proof.
    intros. unfold wt_vvs. intros.
    apply simplify_sifs_wt_sact_ok'.
    unfold simplify_sifs in H.
    rewrite Maps.PTree.gmap in H. unfold option_map in H.
    destr_in H. destruct p.
    - apply Some_inj in H. apply pair_inj in H. destruct H. subst t0.
      inv H0. apply simplify_sif_sact_wt_sact_ok'; eauto.
    - easy.
  Qed.

  Lemma simplify_sif_sact_reachable_vars_ok:
    forall vvs s v (RV: reachable_var vvs (simplify_sif_sact s) v),
    reachable_var vvs s v.
  Proof.
    intros. destruct s; auto.
    destruct s2; auto. destruct s3; auto. simpl in *.
    destr_in RV; auto.
    rewrite Pos.eqb_eq in Heqb. subst.
    inv RV.
    - apply reachable_var_if_true. constructor.
    - apply reachable_var_if_true. econstructor; eauto.
    - repeat (destruct v0; auto). repeat (destruct s3; auto).
      repeat (destruct v0; auto).
      simpl in *. destr_in RV; auto. inv RV.
  Qed.

  Lemma simplify_sif_sact_interp_sact_ok':
    forall a v vvs (WTVVS: wt_vvs (Sigma := Sigma) R vvs) t
      (WTS: wt_sact (Sigma := Sigma) R vvs a t)
      (VVSSV: vvs_smaller_variables vvs),
    interp_sact (sigma := sigma) REnv r vvs a v
    -> interp_sact (sigma := sigma) REnv r vvs (simplify_sif_sact a) v.
  Proof.
    intros.
    eapply interp_sact_do_eval_sact in H; eauto.
    unfold do_eval_sact in H.
    eapply eval_sact_interp_sact.
    erewrite simplify_sif_sact_correct; eauto.
  Qed.

  Lemma simplify_sif_sact_var_in_sact_ok':
    forall s v (VIS: var_in_sact (simplify_sif_sact s) v),
    var_in_sact s v.
  Proof.
    intros.
    intros. destruct s; auto.
    destruct s2; auto. destruct s3; auto. simpl in *.
    destr_in VIS; auto.
    apply var_in_if_true. auto.
    repeat (destruct v0; auto). repeat (destruct s3; auto).
    repeat (destruct v0; auto).
    simpl in *. destr_in VIS; auto. inv VIS.
  Qed.

  Lemma simplify_sifs_vvssv_ok':
    forall vvs (VVSSV: vvs_smaller_variables vvs),
    vvs_smaller_variables (simplify_sifs vvs).
  Proof.
    intros.
    unfold vvs_smaller_variables in *. intros.
    unfold simplify_sifs in H.
    rewrite Maps.PTree.gmap in H. unfold option_map in H.
    destr_in H. destruct p.
    - apply Some_inj in H. apply pair_inj in H. destruct H. subst t0.
      eapply VVSSV; eauto. inv H1.
      apply simplify_sif_sact_var_in_sact_ok'. eauto.
    - easy.
  Qed.

  Lemma simplify_sifs_interp_sact_ok':
    forall vvs a v (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
      (VVSSV: vvs_smaller_variables vvs)
      (EV_INIT: interp_sact (sigma := sigma) REnv r vvs a v),
    interp_sact (sigma := sigma) REnv r (simplify_sifs vvs) a v.
  Proof.
    intros.
    induction EV_INIT; try (econstructor; eauto; fail).
    econstructor.
    - unfold simplify_sifs. setoid_rewrite Maps.PTree.gmap.
      unfold option_map. setoid_rewrite H.
      f_equal.
    - eapply simplify_sif_sact_interp_sact_ok'; eauto.
      + apply simplify_sifs_wtvvs_ok'. eauto.
      + apply simplify_sifs_wt_sact_ok'. eauto.
      + apply simplify_sifs_vvssv_ok'. eauto.
  Qed.

  Lemma simplify_sifs_ok:
    forall
      fuel vvs a res (EV_INIT: eval_sact vvs a fuel = Some res)
      (WTVVS: wt_vvs (Sigma := Sigma) R vvs) t
      (WTS: wt_sact (Sigma := Sigma) R vvs a t),
    eval_sact (simplify_sifs vvs) a fuel = Some res.
  Proof.
    induction fuel; simpl; intros; eauto.
    Transparent eval_sact.
    destruct a; simpl in *.
    - unfold opt_bind in EV_INIT. repeat destr_in EV_INIT; inv EV_INIT.
      setoid_rewrite PTree.gmap. setoid_rewrite Heqo. simpl.
      erewrite IHfuel. eauto. eapply simplify_sif_sact_correct; eauto. auto.
      eapply wt_simplify_sif_sact; eauto.
    - congruence.
    - unfold opt_bind in EV_INIT. destr_in EV_INIT; inv EV_INIT.
      erewrite IHfuel. 2: eauto. simpl.
      destr_in H0; inv H0.
      destr_in H1; inv H1.
      destr_in H0; inv H0.
      rewrite H1.
      inv WTS.
      destr_in H1; (erewrite IHfuel; eauto).
      auto. inv WTS. eauto.
    - unfold opt_bind in EV_INIT. destr_in EV_INIT; inv EV_INIT.
      inv WTS.
      erewrite IHfuel. 2: eauto. simpl. auto. auto. eauto.
    - unfold opt_bind in EV_INIT. destr_in EV_INIT; inv EV_INIT.
      destr_in H0; inv H0.
      inv WTS.
      erewrite IHfuel; eauto.
      erewrite IHfuel; eauto. simpl. auto.
    - unfold opt_bind in EV_INIT. destr_in EV_INIT; inv EV_INIT.
      inv WTS.
      erewrite IHfuel. 2: eauto. simpl. auto. auto. eauto.
    - auto.
  Qed.

  Lemma simplify_sif_sact_interp_sact_ok:
    forall
      vvs (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
      (VVSSV: vvs_smaller_variables vvs) a v
      (EV_INIT: interp_sact (sigma := sigma) REnv r vvs (simplify_sif_sact a) v)
      t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
    interp_sact (sigma := sigma) REnv r vvs a v.
  Proof.
    intros. destruct a; auto.
    destruct a2; auto. destruct a3; auto. simpl in *.
    destr_in EV_INIT; auto.
    rewrite Pos.eqb_eq in Heqb. subst.
    inv WTS.
    eapply wt_sact_interp_bool in H2; eauto.
    2: eapply vvs_range_max_var.
    destruct H2. destruct x; eapply interp_sact_if; eauto.
    repeat (destruct v0; auto). repeat (destruct a3; auto).
    repeat (destruct v0; auto).
    simpl in *. destr_in EV_INIT; auto. rewrite eqb_true_iff in Heqb1. subst.
    inv WTS. eapply wt_sact_interp_bool in H2; eauto.
    2: eapply vvs_range_max_var. destruct H2.
    econstructor; eauto. destruct x; eauto.
  Qed.

  Lemma simplify_sifs_interp_sact_ok:
    forall
      vvs (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
      (VVSSV: vvs_smaller_variables vvs) a v
      (EV_INIT: interp_sact (sigma := sigma) REnv r (simplify_sifs vvs) a v) t
      (WTS: wt_sact (Sigma := Sigma) R vvs a t),
    interp_sact (sigma := sigma) REnv r vvs a v.
  Proof.
    induction 3; simpl; intros; inv WTS.
    - setoid_rewrite PTree.gmap in H. setoid_rewrite H1 in H. simpl in H. inv H.
      econstructor; eauto.
      eapply simplify_sif_sact_interp_sact_ok; eauto.
      eapply IHEV_INIT.
      eapply wt_simplify_sif_sact; eauto.
    - econstructor.
    - econstructor. eauto.
      eapply IHEV_INIT2. destr; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.

  Lemma simplify_sifs_reachable_var_ok:
    forall vvs v (VVSSV: vvs_smaller_variables vvs) a,
    reachable_var (simplify_sifs vvs) a v
    -> reachable_var vvs a v.
  Proof.
    induction 2; simpl; intros; eauto.
    - econstructor.
    - setoid_rewrite PTree.gmap in H. unfold option_map in H.
      repeat destr_in H; inv H.
      econstructor; eauto.
      eapply simplify_sif_sact_reachable_vars_ok. auto.
    - eapply reachable_var_if_cond; eauto.
    - eapply reachable_var_if_true; eauto.
    - eapply reachable_var_if_false; eauto.
    - eapply reachable_var_binop1; eauto.
    - eapply reachable_var_binop2; eauto.
    - eapply reachable_var_unop; eauto.
    - constructor; auto.
  Qed.

  Lemma sf_eq_simplify_sifs_sf sf:
    wf_sf sf -> sf_eq R Sigma r sigma sf (simplify_sifs_sf sf).
  Proof.
    unfold simplify_sifs_sf. intros. inv H. constructor; auto.
    intros. simpl.
    split; intros.
    eapply simplify_sifs_interp_sact_ok'; eauto.
    inversion H1. subst.
    unfold simplify_sifs in H3. rewrite PTree.gmap in H3.
    unfold option_map in H3. repeat destr_in H3; inv H3.
    eapply simplify_sifs_interp_sact_ok; eauto.
    econstructor. eauto.
    simpl. intros.
    eapply simplify_sifs_wt_sact_ok'; eauto.
    eapply simplify_sifs_wt_sact_ok; eauto.
  Qed.

  Lemma wf_sf_simplify_sifs_sf:
    forall sf, wf_sf sf -> wf_sf (simplify_sifs_sf sf).
  Proof.
    destruct 1; constructor.
    eapply simplify_sifs_wtvvs_ok'; eauto.
    eapply simplify_sifs_vvssv_ok'; eauto.
    simpl. intros.
    eapply wf_sf_final in H.
    eapply simplify_sifs_wt_sact_ok'. auto.
  Qed.

  Lemma simplify_sifs_sf_interp_cycle_ok:
    forall reg sf,
    wf_sf sf
    -> getenv REnv (interp_cycle r sigma sf) reg
    = getenv REnv (interp_cycle r sigma (simplify_sifs_sf sf)) reg.
  Proof.
    intros.
    eapply sf_eq_interp_cycle_ok; eauto.
    - apply wf_sf_simplify_sifs_sf; auto.
    - apply sf_eq_simplify_sifs_sf. auto.
  Qed.
End SimplifySIfs.
