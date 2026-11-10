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

Section ReplaceVar.
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

  Definition replace_var_in_vars
    (vars: var_value_map) (from: positive) (to: sact)
  : var_value_map :=
    PTree.map
      (fun k '(t, ua) => (t, if eq_dec from k then to else ua))
      vars.

  Definition replace_var (sf: IRR (rule_name_t := rule_name_t)) (from: positive) (to: sact)
  : IRR :=
    sf <| vars := replace_var_in_vars (vars sf) from to |>.

  Lemma wt_sact_replace_var_in_vars:
    forall vvs a i v t tv,
    wt_sact (Sigma:=Sigma) R vvs a t
    -> wt_sact (Sigma:=Sigma) R vvs (SVar i) tv
    -> wt_sact (Sigma:=Sigma) R vvs v tv
    -> wt_sact (Sigma:=Sigma) R (replace_var_in_vars vvs i v) a t.
  Proof.
    induction a; simpl; intros; eauto.
    inv H. inv H0. econstructor; eauto. setoid_rewrite PTree.gmap.
    setoid_rewrite H3.
    simpl; eauto.
    inv H; econstructor; eauto.
    inv H; econstructor; eauto.
    inv H; econstructor; eauto.
    inv H; econstructor; eauto.
    inv H; econstructor; eauto.
    inv H; econstructor; eauto.
  Qed.

  Lemma interp_sact_replace_var:
    forall
      vvs (WTvvs: wt_vvs R (Sigma:=Sigma) vvs) (VSV: vvs_smaller_variables vvs)
      idx v
      (SAME1: forall ov,
       interp_sact (sigma:=sigma) REnv r vvs (SVar idx) ov
       <-> interp_sact (sigma:=sigma) REnv r vvs v ov)
      (SMALLER: forall var, reachable_var vvs v var -> (var < idx)%positive)
      (tt : type) (OLDTYPE: wt_sact R (Sigma:=Sigma) vvs (SVar idx) tt)
      (NEWTYPE: wt_sact R (Sigma:=Sigma) vvs v tt) a n
      (LT: forall v, reachable_var vvs a v -> (v < n)%positive) t
      (WT: wt_sact (Sigma:=Sigma) R vvs a t),
    forall vv,
    interp_sact (sigma:=sigma) REnv r vvs a vv
    <-> interp_sact (sigma:=sigma) REnv r (replace_var_in_vars vvs idx v) a vv.
  Proof.
    intros vvs WTvvs VSV idx v SAME1 SMALLER tt OLDTYPE NEWTYPE a n.
    change n with (projT1 (existT (fun _ => sact) n a)).
    change a with (projT2 (existT (fun _ => sact) n a)) at 1 3 4 5.
    generalize (existT (fun _ => sact) n a).
    clear n a. intro s. pattern s.
    eapply well_founded_induction.
    apply wf_order_sact. clear s.
    intros x IH BELOW t WTs.
    assert (
      IH2:
        forall a0,
        size_sact a0 < size_sact (projT2 x)
        -> (forall v0, reachable_var vvs a0 v0 -> (v0 < projT1 x)%positive)
        -> forall t (WT: wt_sact (Sigma:=Sigma) R vvs a0 t), forall vv,
          interp_sact (sigma:=sigma) REnv r vvs a0 vv
          <-> interp_sact
                (sigma:=sigma) REnv r (replace_var_in_vars vvs idx v) a0 vv
    ). {
      intros. eapply (IH (existT _ (projT1 x) a0)).
      red. destruct x. apply Relation_Operators.right_lex. simpl in H.  auto.
      simpl. auto. simpl. auto. simpl. eauto.
    }
    destruct x; simpl in *.
    destruct s; simpl in *.
    - inv WTs. intros.
      destruct (eq_dec idx var).
      + subst.
        Opaque eq_dec. intros.
        assert (
          interp_sact
            (sigma:=sigma) REnv r (replace_var_in_vars vvs var v) (SVar var) vv
          <-> interp_sact
                (sigma:=sigma) REnv r (replace_var_in_vars vvs var v) v vv
        ). {
          split.
          - intro A; inv A.
            setoid_rewrite PTree.gmap in H1. setoid_rewrite H0 in H1.
            simpl in H1. destr_in H1; try congruence.
          - intro; econstructor; eauto.
            setoid_rewrite PTree.gmap. setoid_rewrite H0. simpl. destr. eauto.
        } rewrite H.
        exploit (IH (existT _ var v)).
        red. apply Relation_Operators.left_lex. apply BELOW. econstructor.
        simpl.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ H0). auto. simpl.
        eauto. simpl. intro A; rewrite <- A. apply SAME1.
      + exploit (IH (existT _ var s)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ H0). auto. simpl.
        eapply WTvvs. eauto. simpl.
        assert (
          interp_sact (sigma:=sigma) REnv r vvs (SVar var) vv
          <-> interp_sact (sigma:=sigma) REnv r vvs s vv
        ). { split. intro A; inv A. congruence. intros; econstructor; eauto. }
        rewrite H. clear H.
        assert (
          interp_sact
            (sigma:=sigma) REnv r (replace_var_in_vars vvs idx v) (SVar var) vv
          <-> interp_sact
                (sigma:=sigma) REnv r (replace_var_in_vars vvs idx v) s vv
        ). {
          split.
          - intro A; inv A.
            setoid_rewrite PTree.gmap in H1. setoid_rewrite H0 in H1.
            simpl in H1. destr_in H1; try congruence.
          - intro; econstructor; eauto.
            setoid_rewrite PTree.gmap. setoid_rewrite H0. simpl. destr. eauto.
        }
        rewrite H. eauto.
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

  Lemma interp_sact_replace_var':
    forall
      vvs (WTvvs: wt_vvs R (Sigma:=Sigma) vvs) (VSV: vvs_smaller_variables vvs)
      idx v
      (SAME1: forall ov,
       interp_sact (sigma:=sigma) REnv r vvs (SVar idx) ov
       <-> interp_sact (sigma:=sigma) REnv r vvs v ov)
      (SMALLER: forall var, reachable_var vvs v var -> (var < idx)%positive)
      (tt : type) (OLDTYPE: wt_sact R (Sigma:=Sigma) vvs (SVar idx) tt)
      (NEWTYPE: wt_sact R (Sigma:=Sigma) vvs v tt) a t
      (WT: wt_sact (Sigma:=Sigma) R vvs a t),
    forall vv,
    interp_sact (sigma:=sigma) REnv r vvs a vv
    <-> interp_sact (sigma:=sigma) REnv r (replace_var_in_vars vvs idx v) a vv.
  Proof.
    intros.
    eapply interp_sact_replace_var; eauto.
    eapply reachable_var_aux_below. eauto.
    eapply wt_sact_valid_vars; eauto. apply vvs_range_max_var.
  Qed.

  Lemma wt_vvs_replace_var_in_vars:
    forall
      vvs v reg (WTVVS: wt_vvs (Sigma := Sigma) R vvs) tt
      (OLDTYPE: wt_sact (Sigma:=Sigma) R vvs (SVar reg) tt)
      (NEWTYPE: wt_sact (Sigma:=Sigma) R vvs v tt),
    wt_vvs (Sigma := Sigma) R (replace_var_in_vars vvs reg v).
  Proof.
    intros. inv OLDTYPE.
    unfold wt_vvs. intros.
    setoid_rewrite Maps.PTree.gmap in H. unfold option_map in H.
    destr_in H. 2: inv H. destr_in H. inv H.
    eapply wt_sact_replace_var_in_vars; eauto.
    - destr; eauto. subst. setoid_rewrite Heqo in H0; inv H0. auto.
    - econstructor; eauto.
  Qed.

  Lemma vsv_replace_var_in_vars:
    forall
      vvs v reg (VSV: vvs_smaller_variables vvs)
      (SMALLER: forall var, reachable_var vvs v var -> (var < reg)%positive),
    vvs_smaller_variables (replace_var_in_vars vvs reg v).
  Proof.
    intros.
    red. intros.
    setoid_rewrite Maps.PTree.gmap in H. unfold option_map in H.
    repeat destr_in H; inv H.
    eapply SMALLER. eapply var_in_sact_reachable; eauto. eapply VSV; eauto.
  Qed.

  Lemma wf_sf_replace_var':
    forall
      reg val sf tt (OLDTYPE: wt_sact (Sigma:=Sigma) R (vars sf) (SVar reg) tt)
      (NEWTYPE: wt_sact (Sigma:=Sigma) R (vars sf) val tt)
      (SMALLER: forall var : positive,
        reachable_var (vars sf) val var -> (var < reg)%positive),
    wf_sf sf -> wf_sf (replace_var sf reg val).
  Proof.
    intros reg val sf tt OLDTYPE NEWTYPE SMALLER WF.
    destruct WF.
    split.
    - simpl. eapply wt_vvs_replace_var_in_vars; eauto.
    - eapply vsv_replace_var_in_vars; eauto.
    - simpl. intros. eapply wt_sact_replace_var_in_vars; eauto.
  Qed.

  Lemma interp_sact_change_vvs:
    forall
      vvs1 (VSV1: vvs_smaller_variables vvs1) vvs2
      (VSV2: vvs_smaller_variables vvs2) a v
      (IS: interp_sact (sigma:=sigma) REnv r vvs1 a v) t
      (WT1: wt_sact (Sigma:=Sigma) R vvs1 a t)
      (WT2: wt_sact (Sigma:=Sigma) R vvs2 a t)
      (SMALLER:
        forall var, reachable_var vvs1 a var -> vvs1 ! var = vvs2 ! var),
    interp_sact (sigma:=sigma) REnv r vvs2 a v.
  Proof.
    intros.
    eapply interp_eval. 6: apply IS. all: eauto.
    exists O; intros. eapply eval_sact_reachable. intros; eapply SMALLER. auto.
  Qed.

  Lemma replace_var_interp_rev':
    forall
      sf idx v (WFSF: wf_sf sf)
      (INTERP: forall oldv,
       interp_sact (sigma:=sigma) REnv r (vars sf) (SVar idx) oldv
       -> interp_sact (sigma:=sigma) REnv r (vars sf) v oldv)
      tt (OLDTYPE: wt_sact (Sigma:=Sigma) R (vars sf) (SVar idx) tt),
    forall oldv,
    interp_sact (sigma:=sigma) REnv r (vars sf) v oldv
    -> interp_sact (sigma:=sigma) REnv r (vars sf) (SVar idx) oldv.
  Proof.
    intros.
    edestruct @wt_sact_interp' as (vv & IS & WTV). 6: apply OLDTYPE. all: eauto.
    apply WFSF. apply WFSF.
    eapply wt_sact_valid_vars; eauto. apply vvs_range_max_var.
    eapply INTERP in IS as IS2.
    exploit @interp_sact_determ. apply H. apply IS2. intro; subst. congruence.
  Qed.

  Lemma replace_var_interp_rev:
    forall
      sf idx v (WFSF: wf_sf sf)
      (INTERP: forall oldv,
       interp_sact (sigma:=sigma) REnv r (vars sf) (SVar idx) oldv
       -> interp_sact (sigma:=sigma) REnv r (vars sf) v oldv)
      tt (OLDTYPE: wt_sact (Sigma:=Sigma) R (vars sf) (SVar idx) tt),
    forall oldv,
    interp_sact (sigma:=sigma) REnv r (vars sf) v oldv
    <-> interp_sact (sigma:=sigma) REnv r (vars sf) (SVar idx) oldv.
  Proof.
    intros.
    split; intros; eauto.
    eapply replace_var_interp_rev'; eauto.
  Qed.

  Lemma sf_eq_replace_var:
    forall
      sf idx v (WFSF: wf_sf sf)
      (INTERP: forall oldv,
       interp_sact (sigma:=sigma) REnv r (vars sf) (SVar idx) oldv
       -> interp_sact (sigma:=sigma) REnv r (vars sf) v oldv)
      (SMALLER: forall var,
        reachable_var (vars sf) v var -> (var < idx)%positive)
      tt (OLDTYPE: wt_sact (Sigma:=Sigma) R (vars sf) (SVar idx) tt)
      (NEWTYPE: wt_sact (Sigma:=Sigma) R (vars sf) v tt),
    sf_eq R Sigma r sigma sf (replace_var sf idx v).
  Proof.
    intros.
    split.
    - reflexivity.
    - intros. eapply interp_sact_replace_var'; eauto. apply WFSF. apply WFSF.
      intros; symmetry; eapply replace_var_interp_rev; eauto.
    - simpl. intros.
      split.
      intros; eapply wt_sact_replace_var_in_vars; eauto.
      intro A; inv A.
      setoid_rewrite PTree.gmap in H1. unfold option_map in H1.
      destr_in H1; inv H1. destr_in H2. inv H2. econstructor; eauto.
  Qed.

  Lemma replace_var_interp_cycle_ok':
    forall
      {reg} {idx} {sf} {v} (WFSF: wf_sf sf)
      (INTERP:
        forall oldv,
        interp_sact (sigma:=sigma) REnv r (vars sf) (SVar idx) oldv
        -> interp_sact (sigma:=sigma) REnv r (vars sf) v oldv)
      (SMALLER:
        forall var, reachable_var (vars sf) v var -> (var < idx)%positive)
      tt (OLDTYPE: wt_sact (Sigma:=Sigma) R (vars sf) (SVar idx) tt)
      (NEWTYPE: wt_sact (Sigma:=Sigma) R (vars sf) v tt),
    getenv REnv (interp_cycle r sigma sf) reg
    = getenv REnv (interp_cycle r sigma (replace_var sf idx v)) reg.
  Proof.
    intros.
    eapply sf_eq_interp_cycle_ok; eauto.
    - eapply wf_sf_replace_var' in WFSF; eauto.
    - eapply sf_eq_replace_var; eauto.
  Qed.

  Record var_simpl vvs idx v := {
    vs_interp:
      forall oldv, interp_sact (sigma:=sigma) REnv r vvs (SVar idx) oldv
      -> interp_sact (sigma:=sigma) REnv r vvs v oldv;
    vs_smaller: forall var, reachable_var vvs v var -> ((var < idx)%positive);
    vs_type: type;
    vs_oldtype: wt_sact (Sigma:=Sigma) R vvs (SVar idx) vs_type;
    vs_newtype: wt_sact (Sigma:=Sigma) R vvs v vs_type
  }.

  Lemma wf_sf_replace_var:
    forall reg val sf (VS: var_simpl (vars sf) reg val),
    wf_sf sf -> wf_sf (replace_var sf reg val).
  Proof.
    intros reg val sf VS WFSF; inv VS; eapply wf_sf_replace_var'; eauto.
  Qed.

  Lemma replace_var_interp_cycle_ok:
    forall
      {reg} {idx} {sf} {v}
      (WFSF: wf_sf sf)
      (VS: var_simpl (vars sf) idx v),
    getenv REnv (interp_cycle r sigma sf) reg
    = getenv REnv (interp_cycle r sigma (replace_var sf idx v)) reg.
  Proof.
    intros. destruct VS.
    eapply replace_var_interp_cycle_ok'; eauto.
  Qed.
End ReplaceVar.
