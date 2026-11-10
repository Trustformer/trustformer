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

Section ReplaceField.
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

  Fixpoint replace_field_in_sact
    (vars: var_value_map (ext_fn_t := ext_fn_t)) (ua: sact) (str: reg_t)
    (field: string) (value: val)
  : sact :=
    match ua with
    | SBinop ufn a1 a2 =>
      SBinop
        ufn (replace_field_in_sact vars a1 str field value)
        (replace_field_in_sact vars a2 str field value)
    | SUnop (PrimUntyped.UStruct1 (PrimUntyped.UGetField f)) (SVar v) =>
      match Maps.PTree.get v vars with
      | Some (_, SReg r) =>
        if beq_dec f field && beq_dec r str
        then SConst value
        else ua
      | _ => ua
      end
    | SUnop ufn a1 =>
      SUnop ufn (replace_field_in_sact vars a1 str field value)
    | SVar v => SVar v
    | SIf cond tb fb =>
      SIf
        (replace_field_in_sact vars cond str field value)
        (replace_field_in_sact vars tb str field value)
        (replace_field_in_sact vars fb str field value)
    | SConst c => ua
    | SReg r => ua
    | SExternalCall ufn a =>
      SExternalCall ufn (replace_field_in_sact vars a str field value)
    end.

  Definition replace_field
    (str: reg_t) (sf: IRR (rule_name_t := rule_name_t)) (field: string) (value: val)
  : IRR :=
    sf <|
      vars :=
        PTree.map
          (fun _ '(t, ua) =>
            (t, replace_field_in_sact (vars sf) ua str field value))
          (vars sf)
    |>.

  Lemma replace_field_interp_inv:
    forall str field (vvs : PTree.t (type * IRR.sact)) field_v,
    get_field (getenv REnv r str) field = Some field_v
    -> forall (a : sact) reg,
      interp_sact
        (sigma:=sigma) REnv r vvs
        (replace_field_in_sact vvs a str field field_v) reg
    -> forall t : type, wt_sact (Sigma:=Sigma) R vvs a t
    -> interp_sact (sigma:=sigma) REnv r vvs a reg.
  Proof.
    induction a; simpl; intros; eauto; inv H1.
    - inv H0.
      econstructor; eauto.
      destr; eauto.
    - destruct ufn1; try (inv H0; econstructor; eauto; fail).
      destruct fn; try (inv H0; econstructor; eauto; fail).
      destruct a; try (inv H0; econstructor; eauto; fail).
      destr_in H0; eauto; destr_in H0; destr_in H0; eauto.
      + inv H. econstructor; eauto.
        * destr_in H0; econstructor; eauto; econstructor.
        * destr_in H0.
          ** eapply andb_true_iff in Heqb. repeat (rewrite beq_dec_iff in Heqb).
             destruct Heqb. inv H0. eauto.
          ** inv H4. inv H6. inv H0. inv H5.
             inv H4; congruence.
    - inv H0. econstructor; eauto.
    - inv H0. econstructor; eauto.
  Qed.

  Lemma replace_field_interp:
    forall (vvs : PTree.t (type * IRR.sact)) str field field_v,
    wt_vvs (Sigma:=Sigma) R vvs
    -> vvs_smaller_variables vvs
    -> get_field (getenv REnv r str) field = Some field_v
    -> forall (a : sact) (v : val),
    interp_sact (sigma:=sigma) REnv r vvs a v
    -> forall t : type,
    wt_sact (Sigma:=Sigma) R vvs a t
    -> interp_sact
        (sigma:=sigma) REnv r vvs
        (replace_field_in_sact vvs a str field field_v) v.
  Proof.
    induction 4; simpl; intros; try now (econstructor; eauto).
    - inv H2. econstructor; eauto. destr; eauto.
    - inv H4.
      destruct ufn; try (econstructor; eauto).
      destruct fn; try (econstructor; eauto).
      destruct a; try (econstructor; eauto).
      inv H7. rewrite H5.
      destr; try (econstructor; eauto).
      destr.
      + eapply andb_true_iff in Heqb. repeat (rewrite beq_dec_iff in Heqb).
        inv Heqb.
        inv H2. rewrite H5 in H6. inv H6.
        inv H3. inv H7. rewrite H1 in H4. inv H4.
        econstructor.
      + econstructor; eauto.
    - inv H3. econstructor; eauto.
    - inv H3. econstructor; eauto.
  Qed.

  Lemma replace_field_wt:
    forall vvs a t (WTS: wt_sact (Sigma := Sigma) R vvs a t) str field field_v
      (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
      (VSV: vvs_smaller_variables vvs),
    get_field (getenv REnv r str) field = Some field_v
    -> wt_sact
         (Sigma := Sigma) R vvs (replace_field_in_sact vvs a str field field_v)
         t.
  Proof.
    induction 1; simpl; intros; try now (econstructor; eauto).
    destruct ufn; try (econstructor; eauto).
    destruct fn; try (econstructor; eauto).
    destruct a; try (econstructor; eauto).
    inv H. inv WTS.
    rewrite H1.
    destr; try (econstructor; econstructor; eauto). destr.
    - eapply andb_true_iff in Heqb. do 2 (rewrite beq_dec_iff in Heqb).
      inv Heqb.
      eapply IHWTS in H0 as HV.
      econstructor.
      eapply get_field_wt; eauto.
      + econstructor; eauto. econstructor.
      + eauto.
      + eauto.
    - econstructor; econstructor; eauto.
  Qed.

  Lemma replace_field_vis:
    forall vvs a v' str field field_v,
    get_field (getenv REnv r str) field = Some field_v
    -> var_in_sact (replace_field_in_sact vvs a str field field_v) v'
    -> reachable_var vvs a v'.
  Proof.
    induction a; simpl; intros; eauto.
    - eapply var_in_sact_reachable; eauto.
    - inv H0.
    - inv H0.
      eapply reachable_var_if_cond; eauto.
      eapply reachable_var_if_true; eauto.
      eapply reachable_var_if_false; eauto.
    - destr_in H0; try (inv H0; econstructor; eauto; fail).
      destr_in H0; try (inv H0; econstructor; eauto; fail).
      destruct a; try (inv H0; econstructor; eauto; fail).
      repeat (destr_in H0; try (inv H0; econstructor; eauto; fail)).
    - inv H0. econstructor; eauto.
      eapply reachable_var_binop2; eauto.
    - inv H0; econstructor; eauto.
    - inv H0; econstructor; eauto.
  Qed.

  Lemma wf_sf_replace_field:
    forall sf str field field_v,
    get_field (getenv REnv r str) field = Some field_v
    -> wf_sf sf
    -> wf_sf (replace_field str sf field field_v).
  Proof.
    intros.
    eapply wf_f_reachable; intros; eauto.
    - eapply replace_field_wt; eauto. apply H0. apply H0.
    - eapply replace_field_vis; eauto.
  Qed.

  Lemma replace_field_interp_inv2:
    forall vvs,
    wt_vvs (Sigma:=Sigma) R vvs
    -> vvs_smaller_variables vvs
    -> forall n a v rn field field_v, (forall v, reachable_var vvs a v -> v < n)%positive
    -> interp_sact
         (sigma:=sigma) REnv r
         (PTree.map (fun _ '(t,a) => (t, replace_field_in_sact vvs a rn field field_v)) vvs)
         (replace_field_in_sact vvs a rn field field_v) v
    -> get_field (getenv REnv r rn) field = Some field_v
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
    intros x IH v rn field field_v BELOW IS GF t0 WTs.
    assert (
      IH2:
        forall a0,
        size_sact a0 < size_sact (projT2 x)
        -> (forall v0, reachable_var vvs a0 v0 -> (v0 < projT1 x)%positive)
        -> forall v t,
        interp_sact
          (sigma:=sigma) REnv r
          (PTree.map (fun _ '(t,a) => (t, (replace_field_in_sact vvs a rn field field_v))) vvs)
          (replace_field_in_sact vvs a0 rn field field_v) v
        -> wt_sact (Sigma:=Sigma) R vvs a0 t
        -> interp_sact (sigma:=sigma) REnv r vvs a0 v
    ). {
      intros. eapply (IH (existT _ (projT1 x) a0)).
      red. destruct x. apply Relation_Operators.right_lex. simpl in H.  auto.
      simpl. auto. simpl. auto. simpl. eauto. eauto. eauto.
    }
    destruct x; simpl in *.
    destruct s; simpl in *.
    - inv WTs. inv IS.
      rewrite PTree.gmap in H1. unfold option_map in H1.
      repeat destr_in H1; inv H1.
      econstructor. eauto.
      eapply (IH (existT _ var s0)).
      red. apply Relation_Operators.left_lex. apply BELOW. constructor.
      simpl.
      generalize (reachable_var_aux_below_get _ VSV _ _ _ Heqo). auto.
      generalize (reachable_var_aux_below_get _ VSV _ _ _ H0). intros.
      setoid_rewrite H0 in Heqo; inv Heqo. apply H2. auto. eauto.
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
    - inv WTs.
      assert ( interp_sact (sigma:=sigma) REnv r
                 (PTree.map (fun (_ : positive) '(t, a) => (t, replace_field_in_sact vvs a rn field field_v)) vvs)
                 (SUnop ufn1 (replace_field_in_sact vvs s rn field field_v))
                 v -> interp_sact (sigma:=sigma) REnv r vvs (SUnop ufn1 s) v
             ). intro ISS. inv ISS. econstructor. eapply IH2; eauto. intros; eapply BELOW; eauto.
      econstructor; eauto. eauto.
      repeat destr_in IS; eauto. inv IS. simpl in *. clear H.
      econstructor. econstructor. eauto. econstructor. simpl.
      apply andb_true_iff in Heqb. destruct Heqb. apply beq_dec_iff in H. apply beq_dec_iff in H0. subst.
      auto.
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

  Lemma replace_field_interp2:
    forall vvs,
      wt_vvs (Sigma:=Sigma) R vvs
    -> vvs_smaller_variables vvs
    -> forall n a v,
      forall rn field field_v,
        (forall v, reachable_var vvs a v -> v < n)%positive ->
        interp_sact (sigma:=sigma) REnv r vvs a v ->
        get_field (getenv REnv r rn) field = Some field_v ->
        forall t : type,
          wt_sact (Sigma:=Sigma) R vvs a t ->
          interp_sact (sigma:=sigma) REnv r
            (PTree.map (fun _ '(t,a) => (t, (replace_field_in_sact vvs a rn field field_v))) vvs)
            (replace_field_in_sact vvs a rn field field_v) v.
  Proof.
    intros vvs WTvvs VSV n a.
    change n with (projT1 (existT (fun _ => sact) n a)).
    change a with (projT2 (existT (fun _ => sact) n a)) at 1 3 4 5.
    generalize (existT (fun _ => sact) n a).
    clear n a. intro s. pattern s.
    eapply well_founded_induction.
    apply wf_order_sact. clear s.
    intros x IH v rn field field_v BELOW IS GF t0 WTs.
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
             (PTree.map (fun _ '(t,a) => (t, replace_field_in_sact vvs a rn field field_v)) vvs)
             (replace_field_in_sact vvs a0 rn field field_v) v
    ). {
      intros. eapply (IH (existT _ (projT1 x) a0)).
      red. destruct x. apply Relation_Operators.right_lex. simpl in H.  auto.
      simpl. auto. simpl. auto. simpl. eauto. eauto.
    }
    destruct x; simpl in *.
    inv IS.
    - simpl in *.
      intros. econstructor. rewrite PTree.gmap.
      setoid_rewrite H. simpl. reflexivity.
      eapply (IH (existT _ var a)).
      red. apply Relation_Operators.left_lex. apply BELOW. constructor.
      simpl.
      generalize (reachable_var_aux_below_get _ VSV _ _ _ H). auto. simpl. auto. simpl. eauto. eauto.
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
       specialize (IH2 a). trim IH2. simpl. lia.
      trim IH2. intros; apply BELOW. econstructor; eauto.
      specialize (IH2 _ _ H H3).
      intros; repeat destr; try (econstructor; eauto; fail).
      inv H. rewrite Heqo in H2; inv H2. inv H4. simpl in H0.
      apply andb_true_iff in Heqb. destruct Heqb. apply beq_dec_iff in H. apply beq_dec_iff in H1. subst.
      rewrite GF in H0; inv H0. constructor.
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

  Lemma sf_eq_replace_field:
    forall sf str field field_v,
    get_field (getenv REnv r str) field = Some field_v
    -> wf_sf sf
    -> sf_eq R Sigma r sigma sf (replace_field str sf field field_v).
  Proof.
    intros sf str field field_v GF WF.
    constructor.
    - simpl. auto.
    - generalize (wf_sf_replace_field _ _ _ _ GF WF). intro A; inv WF; inv A.
      intros. inv H0.
      split; intro A.
      + inv A. rewrite H2 in H1; inv H1.
        econstructor. setoid_rewrite PTree.gmap.
        setoid_rewrite H2. simpl. reflexivity.
        eapply replace_field_interp2. eauto. eauto.
        eapply reachable_var_aux_below; eauto.
        eapply wf_sf_vvs. eauto. auto. eauto. eauto.
      + inv A.
        setoid_rewrite PTree.gmap in H1. setoid_rewrite H2 in H1.
        simpl in H1. inv H1.
        econstructor. eauto.
        eapply replace_field_interp_inv2. eauto. eauto.
        eapply reachable_var_aux_below; eauto.
        eapply wf_sf_vvs. eauto. apply H3. eauto. eauto.
    - intros. simpl.
      split. eapply f_wt_sact_ok'; eauto.
      intro A; inv A.
      rewrite PTree.gmap in H1.
      unfold option_map in H1; repeat destr_in H1; inv H1.
      econstructor. eauto.
  Qed.

  Lemma replace_field_interp_cycle_ok:
    forall {reg} {sf} {str} {field} {field_v} (WFSF: wf_sf sf),
    get_field (getenv REnv r str) field = Some field_v
    -> getenv REnv (interp_cycle r sigma sf) reg
    = getenv
        REnv (interp_cycle r sigma (replace_field str sf field field_v)) reg.
  Proof.
    intros.
    eapply sf_eq_interp_cycle_ok; eauto.
    - eapply wf_sf_replace_field in WFSF; eauto.
    - eapply sf_eq_replace_field; eauto.
  Qed.
End ReplaceField.
