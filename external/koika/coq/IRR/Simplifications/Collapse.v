Require Import Koika.IRR.Interpretation.
Require Import Koika.IRR.Operations.
Require Import Koika.IRR.Properties.
Require Import Koika.BitsToLists.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.KoikaForm.Types.
Require Import Koika.IRR.IRR.
Require Import Koika.Utils.EqDec.
Require Import Koika.Utils.Maps.
Require Import Koika.Utils.Environments.
Require Import Koika.IRR.Simplifications.Prune.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section Collapse.
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

  (* TODO Also inline elements referenced only once? *)

  Fixpoint collapse_sact
    (vvs : PTree.t (type * IRR.sact (ext_fn_t:=ext_fn_t)(reg_t:=reg_t)))
    (a : sact)
  :=
    match a with
    | SIf cond tb fb =>
      SIf (collapse_sact vvs cond) (collapse_sact vvs tb) (collapse_sact vvs fb)
    | SBinop ufn a1 a2 =>
      SBinop ufn (collapse_sact vvs a1) (collapse_sact vvs a2)
    | SUnop ufn a => SUnop ufn (collapse_sact vvs a)
    | SVar v =>
      match PTree.get v vvs with
      | Some (t, SVar v') => SVar v'
      | Some (t, SConst c) => SConst c
      | _ => a
      end
    | SExternalCall ufn s => SExternalCall ufn (collapse_sact vvs s)
    | _ => a
    end.

  (* Note that *)
  Definition collapse_sf (sf: IRR (rule_name_t := rule_name_t)) :=
    sf <| vars :=
      (* TODO Alternatively, fold and handle elements in order. That would
         remove the need for successive calls to collapse. *)
      Maps.PTree.map
        (fun _ '(t, a) => (t, collapse_sact (vars sf) a)) (vars sf) |>.

  Lemma collapse_wt:
    forall
      sf (WF: wf_sf sf) a t (WTS: wt_sact (Sigma := Sigma) R (vars sf) a t),
    wt_sact (Sigma := Sigma) R (vars sf) (collapse_sact (vars sf) a) t.
  Proof.
    induction 2; simpl; intros; try now (econstructor; eauto).
    rewrite H.
    destr; try now (econstructor; eauto).
    eapply wf_sf_wt; eauto.
    eapply wf_sf_wt; eauto.
  Qed.

  Lemma collapse_vis:
    forall vvs a v' (VIS: var_in_sact (collapse_sact vvs a) v'),
    reachable_var vvs a v'.
  Proof.
    induction a; simpl; intros; eauto; try now (inv VIS).
    - specialize (var_in_sact_reachable vvs (SVar var) v'). intros.
      repeat destr_in VIS; auto; clear H.
      subst.
      inv VIS.
      + econstructor; eauto. econstructor; eauto.
      + inv VIS.
    - inv VIS.
      eapply reachable_var_if_cond; eauto.
      eapply reachable_var_if_true; eauto.
      eapply reachable_var_if_false; eauto.
    - inv VIS; econstructor; eauto.
    - inv VIS. econstructor; eauto.
      eapply reachable_var_binop2; eauto.
    - inv VIS; econstructor; eauto.
  Qed.

  Lemma wf_collapse_sf: forall sf, wf_sf sf -> wf_sf (collapse_sf sf).
  Proof.
    intros; eapply wf_f_reachable.
    intros; eapply collapse_wt; eauto.
    intros; eapply collapse_vis; eauto. auto.
  Qed.

  Lemma collapse_interp_inv:
    forall vvs,
    wt_vvs (Sigma:=Sigma) R vvs
    -> vvs_smaller_variables vvs
    -> forall (a : sact) (v : val),
    interp_sact (sigma:=sigma) REnv r vvs (collapse_sact vvs a) v
    -> forall t : type,
    wt_sact (Sigma:=Sigma) R vvs a t
    -> interp_sact (sigma:=sigma) REnv r vvs a v.
  Proof.
    induction a; simpl; intros; eauto.
    - inv H2.
      rewrite H4 in H1.
      destr_in H1; auto; econstructor; eauto.
    - inv H2; inv H1. econstructor; eauto. destr; eauto.
    - inv H2; inv H1. econstructor; eauto.
    - inv H2; inv H1. econstructor; eauto.
    - inv H2; inv H1. econstructor; eauto.
  Qed.

  Lemma collapse_interp2:
    forall vvs,
      wt_vvs (Sigma:=Sigma) R vvs
    -> vvs_smaller_variables vvs
    -> forall n a v,
        (forall v, reachable_var vvs a v -> v < n)%positive ->
        interp_sact (sigma:=sigma) REnv r vvs a v ->
        forall t : type, wt_sact (Sigma:=Sigma) R vvs a t ->
                         interp_sact (sigma:=sigma) REnv r (PTree.map (fun _ '(t,a) => (t, collapse_sact vvs a)) vvs) (collapse_sact vvs a) v.
  Proof.
    intros vvs WTvvs VSV n a.
    change n with (projT1 (existT (fun _ => sact) n a)).
    change a with (projT2 (existT (fun _ => sact) n a)) at 1 3 4 5.
    generalize (existT (fun _ => sact) n a).
    clear n a. intro s. pattern s.
    eapply well_founded_induction.
    apply wf_order_sact. clear s.
    intros x IH v BELOW IS t0 WTs.
    assert (
      IH2:
        forall a0,
        size_sact a0 < size_sact (projT2 x)
        -> (forall v0, reachable_var vvs a0 v0 -> (v0 < projT1 x)%positive)
        -> forall v t,
        interp_sact (sigma:=sigma) REnv r vvs a0 v
        -> wt_sact (Sigma:=Sigma) R vvs a0 t
        -> interp_sact
             (sigma:=sigma) REnv r
             (PTree.map (fun _ '(t,a) => (t, collapse_sact vvs a)) vvs)
             (collapse_sact vvs a0) v
    ). {
      intros. eapply (IH (existT _ (projT1 x) a0)).
      red. destruct x. apply Relation_Operators.right_lex. simpl in H.  auto.
      simpl. auto. simpl. auto. simpl. eauto.
    }
    destruct x; simpl in *.
    inv IS.
    - simpl in *. rewrite H.
      destr.
      + inv H0. econstructor.
        rewrite PTree.gmap; setoid_rewrite H2. reflexivity.
        eapply (IH (existT _ var a0)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ H). intros.
        eapply H0. econstructor; eauto. simpl. auto.
        simpl. eauto.
      + inv H0; econstructor; eauto.
      + econstructor.
        rewrite PTree.gmap; setoid_rewrite H. reflexivity.
        simpl.
        inv H0.
        generalize (WTvvs _ _ _ H). intro WT. inv WT.
        econstructor.
        eapply (IH (existT _ var s1)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ H). intros.
        eapply H0. econstructor; eauto. simpl. eauto.
        simpl. eauto.
        destr.
        eapply (IH (existT _ var s2)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ H). intros.
        eapply H0. eapply reachable_var_if_true; eauto. simpl. eauto.
        simpl. eauto.
        eapply (IH (existT _ var s3)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ H). intros.
        eapply H0. eapply reachable_var_if_false; eauto. simpl. eauto.
        simpl. eauto.
      + econstructor.
        rewrite PTree.gmap; setoid_rewrite H. reflexivity.
        simpl.
        inv H0.
        generalize (WTvvs _ _ _ H). intro WT. inv WT.
        econstructor.
        eapply (IH (existT _ var s)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ H). intros.
        eapply H0. econstructor; eauto. simpl. eauto.
        simpl. eauto. auto.
      + econstructor.
        rewrite PTree.gmap; setoid_rewrite H. reflexivity.
        simpl.
        inv H0.
        generalize (WTvvs _ _ _ H). intro WT. inv WT.
        econstructor.
        eapply (IH (existT _ var s1)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ H). intros.
        eapply H0. eapply reachable_var_binop1; eauto. simpl. eauto.
        simpl. eauto. auto.
        simpl. eapply (IH (existT _ var s2)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ H). intros.
        eapply H0. eapply reachable_var_binop2; eauto. simpl. eauto.
        simpl. eauto. auto.
      + econstructor.
        rewrite PTree.gmap; setoid_rewrite H. reflexivity.
        simpl.
        inv H0.
        generalize (WTvvs _ _ _ H). intro WT. inv WT.
        econstructor.
        eapply (IH (existT _ var s)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ H). intros.
        eapply H0. eapply reachable_var_externalCall; eauto. simpl. eauto.
        simpl. eauto.
      + econstructor.
        rewrite PTree.gmap; setoid_rewrite H. reflexivity.
        simpl. inv H0. generalize (WTvvs _ _ _ H). intro WT. inv WT.
        econstructor.
    - simpl; constructor.
    - simpl.
      inv WTs.
      econstructor.
      eapply IH2. Transparent size_sact. simpl. lia.
      intros; eapply BELOW. eapply reachable_var_if_cond. eauto. eauto. eauto.
      destr.
      eapply IH2. simpl. lia.
      intros; eapply BELOW. eapply reachable_var_if_true. eauto. eauto. eauto.
      eapply IH2. simpl. lia.
      intros; eapply BELOW. eapply reachable_var_if_false. eauto. eauto. eauto.
    - simpl.
      inv WTs.
      econstructor.
      eapply IH2. simpl. lia.
      intros; eapply BELOW. eapply reachable_var_unop.
      eauto. eauto. eauto. eauto.
    - simpl.
      inv WTs.
      econstructor.
      eapply IH2. simpl. lia.
      intros; eapply BELOW. eapply reachable_var_binop1.
      eauto. eauto. eauto.
      eapply IH2. simpl. lia.
      intros; eapply BELOW. eapply reachable_var_binop2.
      auto. eauto. eauto. auto.
    - simpl.
      inv WTs.
      econstructor.
      eapply IH2. simpl. lia.
      intros; eapply BELOW. eapply reachable_var_externalCall.
      eauto. eauto. eauto.
    - simpl; constructor.
  Qed.

  Lemma collapse_interp_inv2:
    forall vvs,
    wt_vvs (Sigma:=Sigma) R vvs
    -> vvs_smaller_variables vvs
    -> forall n a v, (forall v, reachable_var vvs a v -> v < n)%positive
    -> interp_sact
         (sigma:=sigma) REnv r
         (PTree.map (fun _ '(t,a) => (t, collapse_sact vvs a)) vvs)
         (collapse_sact vvs a) v
    -> forall t : type, wt_sact (Sigma:=Sigma) R vvs a t
    -> interp_sact (sigma:=sigma) REnv r vvs a v.
  Proof.
    intros vvs WTvvs VSV n a.
    change n with (projT1 (existT (fun _ => sact) n a)).
    change a with (projT2 (existT (fun _ => sact) n a)) at 1 3 4 5.
    generalize (existT (fun _ => sact) n a).
    clear n a. intro s. pattern s.
    eapply well_founded_induction.
    apply wf_order_sact. clear s.
    intros x IH v BELOW IS t0 WTs.
    assert (
      IH2:
        forall a0,
        size_sact a0 < size_sact (projT2 x)
        -> (forall v0, reachable_var vvs a0 v0 -> (v0 < projT1 x)%positive)
        -> forall v t,
        interp_sact
          (sigma:=sigma) REnv r
          (PTree.map (fun _ '(t,a) => (t, collapse_sact vvs a)) vvs)
          (collapse_sact vvs a0) v
        -> wt_sact (Sigma:=Sigma) R vvs a0 t
        -> interp_sact (sigma:=sigma) REnv r vvs a0 v
    ). {
      intros. eapply (IH (existT _ (projT1 x) a0)).
      red. destruct x. apply Relation_Operators.right_lex. simpl in H.  auto.
      simpl. auto. simpl. auto. simpl. eauto.
    }
    destruct x; simpl in *.
    destruct s; simpl in *.
    - inv WTs. rewrite H0 in IS. econstructor. eauto.
      destr_in IS; subst.
      + inv IS.
        rewrite PTree.gmap in H1. unfold option_map in H1.
        repeat destr_in H1; inv H1.
        econstructor. eauto.
        eapply (IH (existT _ var s)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ Heqo). auto.
        generalize (reachable_var_aux_below_get _ VSV _ _ _ H0). intros.
        trim (H var0). constructor. specialize (H1 _ H3). lia.
        simpl. auto. simpl; eauto.
      + inv IS. constructor.
      + inv IS.
        generalize (WTvvs _ _ _ H0). intro WT; inv WT.
        rewrite PTree.gmap in H1. setoid_rewrite H0 in H1. simpl in H1. inv H1.
        inv H2.
        econstructor.
        eapply (IH (existT _ var s0_1)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        intros; eapply (reachable_var_aux_below_get _ VSV _ _ _ H0).
        eapply reachable_var_if_cond; eauto. simpl. eauto. simpl. eauto.
        destr.
        eapply (IH (existT _ var s0_2)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        intros; eapply (reachable_var_aux_below_get _ VSV _ _ _ H0).
        eapply reachable_var_if_true; eauto. simpl. eauto. simpl. eauto.
        eapply (IH (existT _ var s0_3)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        intros; eapply (reachable_var_aux_below_get _ VSV _ _ _ H0).
        eapply reachable_var_if_false; eauto. simpl. eauto. simpl. eauto.
      + inv IS.
        generalize (WTvvs _ _ _ H0). intro WT; inv WT.
        rewrite PTree.gmap in H1. setoid_rewrite H0 in H1. simpl in H1. inv H1.
        inv H2.
        econstructor.
        eapply (IH (existT _ var s0)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        intros; eapply (reachable_var_aux_below_get _ VSV _ _ _ H0).
        eapply reachable_var_unop; eauto. simpl. eauto. simpl. eauto. auto.
      + inv IS.
        generalize (WTvvs _ _ _ H0). intro WT; inv WT.
        rewrite PTree.gmap in H1. setoid_rewrite H0 in H1. simpl in H1. inv H1.
        inv H2. econstructor.
        eapply (IH (existT _ var s0_1)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl. intros; eapply (reachable_var_aux_below_get _ VSV _ _ _ H0).
        eapply reachable_var_binop1; eauto. simpl. eauto. simpl. eauto.
        eapply (IH (existT _ var s0_2)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl. intros; eapply (reachable_var_aux_below_get _ VSV _ _ _ H0).
        eapply reachable_var_binop2; eauto. simpl. eauto. simpl. eauto. auto.
      + inv IS.
        generalize (WTvvs _ _ _ H0). intro WT; inv WT.
        rewrite PTree.gmap in H1. setoid_rewrite H0 in H1. simpl in H1. inv H1.
        inv H2. econstructor.
        eapply (IH (existT _ var s0)).
        red. apply Relation_Operators.left_lex. apply BELOW. constructor.
        simpl.
        intros; eapply (reachable_var_aux_below_get _ VSV _ _ _ H0).
        eapply reachable_var_externalCall; eauto. simpl. eauto. simpl. eauto.
      + inv IS.
        generalize (WTvvs _ _ _ H0). intro WT; inv WT.
        rewrite PTree.gmap in H1. setoid_rewrite H0 in H1. simpl in H1. inv H1.
        inv H2. econstructor.
    - inv IS. constructor.
    - inv IS. inv WTs.
      econstructor.
      eapply IH2. lia. intros; eapply BELOW.
      eapply reachable_var_if_cond; eauto. eauto. eauto.
      destr.
      eapply IH2. lia. intros; eapply BELOW.
      eapply reachable_var_if_true; eauto. eauto. eauto.
      eapply IH2. lia. intros; eapply BELOW.
      eapply reachable_var_if_false; eauto. eauto. eauto.
    - inv IS. inv WTs.
      econstructor.
      eapply IH2. lia. intros; eapply BELOW.
      eapply reachable_var_unop; eauto. eauto. eauto. auto.
    - inv IS. inv WTs.
      econstructor.
      eapply IH2. lia. intros; eapply BELOW.
      eapply reachable_var_binop1; eauto. eauto. eauto.
      eapply IH2. lia. intros; eapply BELOW.
      eapply reachable_var_binop2; eauto. eauto. eauto. auto.
    - inv IS. inv WTs.
      econstructor.
      eapply IH2. lia. intros; eapply BELOW.
      eapply reachable_var_externalCall; eauto. eauto. eauto.
    - inv IS. constructor.
  Qed.

  Lemma sf_eq_collapse_sf:
    forall sf, wf_sf sf -> sf_eq R Sigma r sigma sf (collapse_sf sf).
  Proof.
    intros sf WF.
    constructor.
    - simpl. auto.
    - generalize (wf_collapse_sf _ WF). intro A; inv WF; inv A.
      intros. inv H0.
      split; intro A.
      + inv A. rewrite H2 in H1; inv H1.
        econstructor. setoid_rewrite PTree.gmap.
        setoid_rewrite H2. simpl. reflexivity.
        eapply collapse_interp2. eauto. eauto.
        eapply reachable_var_aux_below; eauto.
        eapply wf_sf_vvs. eauto. auto. eauto.
      + inv A.
        setoid_rewrite PTree.gmap in H1. setoid_rewrite H2 in H1.
        simpl in H1. inv H1.
        econstructor. eauto.
        eapply collapse_interp_inv2. eauto. eauto.
        eapply reachable_var_aux_below; eauto.
        eapply wf_sf_vvs. eauto. auto. eauto.
    - intros. simpl.
      split. eapply f_wt_sact_ok'; eauto.
      intro A; inv A.
      rewrite PTree.gmap in H1.
      unfold option_map in H1; repeat destr_in H1; inv H1.
      econstructor. eauto.
  Qed.

  Lemma collapse_prune_interp_cycle_ok:
    forall reg sf sf',
    wf_sf sf
    -> prune_irrelevant (collapse_sf sf) reg = Some sf'
    -> getenv REnv (interp_cycle r sigma sf) reg
    = getenv REnv (interp_cycle r sigma sf') reg.
  Proof.
    intros.
    unfold prune_irrelevant in H0. destr_in H0; inv H0.
    eapply sf_eqr_interp_cycle_ok; eauto.
    - eapply wf_sf_prune_irrelevant_aux.
      + eauto.
      + eapply wf_collapse_sf. auto.
    - eapply sf_eq_sf_eq_restricted_trans.
      2: apply sf_eqf_prune_irrelevant_aux.
      + apply sf_eq_collapse_sf. auto.
      + auto.
      + apply wf_collapse_sf. auto.
    - simpl; auto.
  Qed.

  Lemma collapse_interp_cycle_ok:
    forall reg sf sf',
    wf_sf sf
    -> collapse_sf sf = sf'
    -> getenv REnv (interp_cycle r sigma sf) reg
    = getenv REnv (interp_cycle r sigma sf') reg.
  Proof.
    intros. subst.
    eapply sf_eq_interp_cycle_ok; eauto.
    - eapply wf_collapse_sf. assumption.
    - eapply sf_eq_collapse_sf. assumption.
  Qed.
End Collapse.
