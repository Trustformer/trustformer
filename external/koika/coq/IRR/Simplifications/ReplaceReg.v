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

Section ReplaceReg.
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

  Fixpoint replace_reg_in_sact (ua: sact) (from: reg_t) (to: val) : sact :=
    match ua with
    | SBinop ufn a1 a2 =>
      SBinop
        ufn (replace_reg_in_sact a1 from to)
        (replace_reg_in_sact a2 from to)
    | SUnop ufn a1 => SUnop ufn (replace_reg_in_sact a1 from to)
    | SVar v => SVar v
    | SIf cond tb fb =>
      SIf
        (replace_reg_in_sact cond from to)
        (replace_reg_in_sact tb from to)
        (replace_reg_in_sact fb from to)
    | SConst c => SConst c
    | SExternalCall ufn a => SExternalCall ufn (replace_reg_in_sact a from to)
    | SReg r => if eq_dec r from then SConst to else SReg r
    end.

  Definition replace_reg_in_vars
    (vars: var_value_map) (from: reg_t) (to: val)
  : var_value_map :=
    PTree.map
      (fun _ '(t, ua) => (t, replace_reg_in_sact ua from to))
      vars.

  Definition replace_reg (sf: IRR (rule_name_t := rule_name_t)) (from: reg_t) (to: val)
  : IRR :=
    sf <| vars := replace_reg_in_vars (vars sf) from to |>.

  Lemma eval_sact_replace_reg:
    forall vvs idx v', getenv REnv r idx = v'
    -> forall fuel a,
    eval_sact vvs a fuel = eval_sact vvs (replace_reg_in_sact a idx v') fuel.
  Proof.
    induction fuel; simpl; intros; eauto.
    destruct a; simpl; intros; auto; repeat (rewrite <- ! IHfuel; now eauto).
    destruct eq_dec; subst; auto.
  Qed.

  Lemma eval_sact_replace_reg_vars:
    forall vvs idx v', getenv REnv r idx = v'
    -> forall fuel a,
    eval_sact vvs a fuel = eval_sact (replace_reg_in_vars vvs idx v') a fuel.
  Proof.
    induction fuel; simpl; intros; eauto.
    destruct a; simpl; intros; auto; repeat (rewrite <- ! IHfuel; now eauto).
    setoid_rewrite PTree.gmap. unfold option_map.
    unfold opt_bind. repeat destr. setoid_rewrite Heqo in Heqo0. inv Heqo0.
    rewrite <- IHfuel.  apply eval_sact_replace_reg.  auto.
    setoid_rewrite Heqo in Heqo0. inv Heqo0.
    setoid_rewrite Heqo in Heqo0. inv Heqo0.
  Qed.

  Lemma eval_sact_replace_reg_sact_vars:
    forall vvs idx v', getenv REnv r idx = v'
    -> forall fuel a,
    eval_sact vvs a fuel
    = eval_sact
        (replace_reg_in_vars vvs idx v') (replace_reg_in_sact a idx v') fuel.
  Proof.
    intros; rewrite <- eval_sact_replace_reg_vars, <- eval_sact_replace_reg;
      eauto.
  Qed.

  Lemma var_in_replace_reg:
    forall i v s v',
    var_in_sact (replace_reg_in_sact s i v) v' -> var_in_sact s v'.
  Proof.
    induction s; simpl; intros; eauto.
    - inv H.
      + apply IHs1 in H4. apply var_in_if_cond. eauto.
      + apply IHs2 in H4. apply var_in_if_true. eauto.
      + apply IHs3 in H4. apply var_in_if_false. eauto.
    - inv H. econstructor. eauto.
    - inv H.
      + eapply IHs1 in H4. apply var_in_sact_binop_1. eauto.
      + eapply IHs2 in H4. apply var_in_sact_binop_2. eauto.
    - inv H. apply IHs in H3. econstructor. eauto.
    - destruct (eq_dec idx i).
      + inv H.
      + inv H.
  Qed.

  Lemma wt_sact_replace_reg:
    forall vvs a i v t, wt_sact (Sigma:=Sigma) R vvs a t
    -> wt_val (R i) v
    -> wt_sact (Sigma:=Sigma) R vvs (replace_reg_in_sact a i v) t.
  Proof.
    induction a; simpl; intros; eauto; try (inv H; econstructor; eauto).
    inv H. destr; eauto. subst. constructor; auto.
    constructor.
  Qed.

  Lemma wt_sact_replace_reg_in_vars:
    forall vvs a i v t, wt_sact (Sigma:=Sigma) R vvs a t
    -> wt_val (R i) v
    -> wt_sact (Sigma:=Sigma) R (replace_reg_in_vars vvs i v) a t.
  Proof.
    induction a; simpl; intros; eauto.
    inv H. econstructor; eauto. setoid_rewrite PTree.gmap. setoid_rewrite H2.
    simpl; eauto.
    inv H; econstructor; eauto.
    inv H; econstructor; eauto.
    inv H; econstructor; eauto.
    inv H; econstructor; eauto.
    inv H; econstructor; eauto.
    inv H; econstructor; eauto.
  Qed.

  Lemma interp_sact_replace_reg' :
    forall sf idx v a t res,
    vvs_smaller_variables (vars sf)
    -> wt_sact (Sigma:=Sigma) R (vars sf) a t
    -> getenv REnv r idx = v
    -> interp_sact (sigma:=sigma) REnv r (vars sf) a res
    <-> interp_sact (sigma:=sigma) REnv r (vars (replace_reg sf idx v)) a res.
  Proof.
    intros.
    eapply interp_eval_iff; eauto. {
      simpl. red; intros. unfold replace_reg_in_vars in H2.
      rewrite PTree.gmap in H2. unfold option_map in H2; destr_in H2; inv H2.
      destr_in H5. inv H5.
      apply H in Heqo. apply Heqo.
      apply var_in_replace_reg in H3; auto.
    }
    simpl. eapply wt_sact_replace_reg_in_vars; eauto. subst. apply WTRENV.
    exists 0; intros.
    apply eval_sact_replace_reg_vars. auto.
  Qed.

  Lemma replace_reg_in_vars_wt_sact_vvs_ok':
    forall vvs v reg s t (WTV: wt_val (R reg) v)
      (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
      (WTS: wt_sact (Sigma := Sigma) R vvs s t),
    wt_sact (Sigma := Sigma) R (replace_reg_in_vars vvs reg v) s t.
  Proof.
    intros.
    induction WTS; econstructor; eauto.
    setoid_rewrite Maps.PTree.gmap. unfold option_map.
    setoid_rewrite H. easy.
  Qed.

  Lemma wt_vvs_replace_reg_in_vars:
    forall vvs v reg (WTV: wt_val (R reg) v)
      (WTVVS: wt_vvs (Sigma := Sigma) R vvs),
    wt_vvs (Sigma := Sigma) R (replace_reg_in_vars vvs reg v).
  Proof.
    intros.
    unfold wt_vvs. intros.
    setoid_rewrite Maps.PTree.gmap in H. unfold option_map in H.
    unfold wt_vvs in WTVVS.
    repeat destr_in H; inv H.
    apply wt_sact_replace_reg; eauto.
    apply WTVVS in Heqo.
    apply replace_reg_in_vars_wt_sact_vvs_ok'; eauto.
  Qed.

  Lemma vsv_replace_reg_in_vars:
    forall vvs v reg
      (VSV: vvs_smaller_variables vvs),
      vvs_smaller_variables (replace_reg_in_vars vvs reg v).
  Proof.
    intros.
    red. intros.
    setoid_rewrite Maps.PTree.gmap in H. unfold option_map in H.
    repeat destr_in H; inv H.
    apply var_in_replace_reg in H0. eauto.
  Qed.

  Lemma replace_reg_in_vars_ok:
    forall (vvs : var_value_map) (VSV: vvs_smaller_variables vvs)
           (idx : reg_t) (v' : val) v a t (WT: wt_sact R (Sigma:=Sigma) vvs a t)
    (WTVVS: wt_vvs R (Sigma:=Sigma) vvs),
    getenv REnv r idx = v'
    -> interp_sact (sigma := sigma) REnv r (replace_reg_in_vars vvs idx v') a v
    -> interp_sact (sigma := sigma) REnv r vvs a v.
  Proof.
    intros vvs VSV idx v' v a t WT WTVVS H.
    eapply interp_eval.
    eapply vsv_replace_reg_in_vars; eauto.
    auto.
    eapply replace_reg_in_vars_wt_sact_vvs_ok'. subst. apply WTRENV. auto.
    eauto. eauto.
    exists O; intros; symmetry; apply eval_sact_replace_reg_vars. auto.
  Qed.

  Lemma replace_reg_interp_inv:
    forall reg (vvs : PTree.t (type * IRR.sact)),
    wt_vvs (Sigma:=Sigma) R vvs
    -> vvs_smaller_variables vvs
    -> forall (a : sact) (v : val),
    interp_sact
      (sigma:=sigma) REnv r vvs (replace_reg_in_sact a reg (getenv REnv r reg))
      v
    -> forall t : type, wt_sact (Sigma:=Sigma) R vvs a t
    -> interp_sact (sigma:=sigma) REnv r vvs a v.
  Proof.
    induction a; simpl; intros; eauto.
    - inv H2. inv H1.
      econstructor; eauto.
      destr; eauto.
    - inv H2; inv H1. econstructor; eauto.
    - inv H2; inv H1. econstructor; eauto.
    - inv H2; inv H1. econstructor; eauto.
    - inv H2. destr_in H1. subst. inv H1. econstructor. eauto.
  Qed.

  Lemma replace_reg_interp:
    forall reg (vvs : PTree.t (type * IRR.sact)),
    wt_vvs (Sigma:=Sigma) R vvs
    -> vvs_smaller_variables vvs
    -> forall (a : sact) (v : val),
    interp_sact (sigma:=sigma) REnv r vvs a v
    -> forall t : type,
    wt_sact (Sigma:=Sigma) R vvs a t
    -> interp_sact
        (sigma:=sigma) REnv r vvs
        (replace_reg_in_sact a reg (getenv REnv r reg)) v.
  Proof.
    induction 3; simpl; intros; try now (econstructor; eauto).
    - inv H1. econstructor; eauto. destr; eauto.
    - inv H3. econstructor; eauto.
    - inv H2. econstructor; eauto.
    - inv H2. econstructor; eauto.
    - inv H1. destr; subst; econstructor.
  Qed.

  Lemma replace_reg_wt:
    forall reg vvs a t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
    wt_sact
      (Sigma := Sigma) R vvs (replace_reg_in_sact a reg (getenv REnv r reg)) t.
  Proof.
    induction 1; simpl; intros; try now (econstructor; eauto).
    destr; try (econstructor; eauto).
    subst. eauto.
  Qed.

  Lemma replace_reg_vis:
    forall
      reg a v'
      (VIS: var_in_sact (replace_reg_in_sact a reg (getenv REnv r reg)) v'),
    var_in_sact a v'.
  Proof.
    induction a; simpl; intros; eauto.
    - inv VIS.
      eapply var_in_if_cond; eauto.
      eapply var_in_if_true; eauto.
      eapply var_in_if_false; eauto.
    - inv VIS; econstructor; eauto.
    - inv VIS. econstructor; eauto.
      eapply var_in_sact_binop_2; eauto.
    - inv VIS; econstructor; eauto.
    - destr_in VIS; inv VIS.
  Qed.

  Lemma wf_sf_replace_reg:
    forall reg val sf,
    getenv REnv r reg = val -> wf_sf sf -> wf_sf (replace_reg sf reg val).
  Proof.
    intros.
    rewrite <- H.
    eapply wf_f.
    - apply replace_reg_wt.
    - apply replace_reg_vis.
    - auto.
  Qed.

  Lemma sf_eq_replace_reg:
    forall reg sf,
    wf_sf sf
    -> sf_eq R Sigma r sigma sf (replace_reg sf reg (getenv REnv r reg)).
  Proof.
    intros.
    eapply sf_eq_f.
    - eapply replace_reg_interp_inv.
    - intros; eapply replace_reg_interp; eauto.
    - apply replace_reg_wt.
    - apply replace_reg_vis.
    - auto.
  Qed.

  Lemma replace_reg_interp_cycle_ok:
    forall
      {reg} {reg2} {sf} {val} (REG_VAL: getenv REnv r reg2 = val)
      (WFSF: wf_sf sf),
    getenv REnv (interp_cycle r sigma sf) reg
    = getenv REnv (interp_cycle r sigma (replace_reg sf reg2 val)) reg.
  Proof.
    intros.
    eapply sf_eq_interp_cycle_ok; eauto.
    - eapply wf_sf_replace_reg in WFSF; eauto.
    - rewrite <- REG_VAL. apply sf_eq_replace_reg. auto.
  Qed.
End ReplaceReg.
