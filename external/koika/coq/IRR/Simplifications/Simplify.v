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

Section Simplify.
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

  Fixpoint simplify_sact (ua: sact) : sact :=
    match ua with
    | SIf cond tb fb =>
      let cond' := simplify_sact cond in
      match eval_sact_no_vars r sigma cond' with
      | Some (Bits [true]) => simplify_sact tb
      | Some (Bits [false]) => simplify_sact fb
      | _ => SIf cond' (simplify_sact tb) (simplify_sact fb)
      end
    | SBinop ufn a1 a2 =>
      let a1' := simplify_sact a1 in
      match ufn with
      | PrimUntyped.UBits2 PrimUntyped.UAnd =>
        match eval_sact_no_vars r sigma a1' with
        | Some (Bits [false]) => const_false
        | Some (Bits [true]) => simplify_sact a2
        | _ =>
          let a2' := simplify_sact a2 in
          match eval_sact_no_vars r sigma a2' with
          | Some (Bits [false]) => const_false
          | Some (Bits [true]) => a1'
          | _ => SBinop ufn a1' a2'
          end
        end
      | PrimUntyped.UBits2 PrimUntyped.UOr =>
        match eval_sact_no_vars r sigma a1' with
        | Some (Bits [true]) => const_true
        | Some (Bits [false]) => simplify_sact a2
        | _ =>
          let a2' := simplify_sact a2 in
          match eval_sact_no_vars r sigma a2' with
          | Some (Bits [true]) => const_true
          | Some (Bits [false]) => a1'
          | _ => SBinop ufn a1' a2'
          end
        end
      | fn =>
        let a2' := simplify_sact a2 in
        match eval_sact_no_vars r sigma a1', eval_sact_no_vars r sigma a2' with
        | Some x, Some y =>
          match sigma2 fn x y with
          | Some r => SConst r
          | None => SBinop ufn a1' a2'
          end
        | _, _ => SBinop ufn a1' a2'
        end
      end
    | SUnop ufn a =>
      let a := simplify_sact a in
      match eval_sact_no_vars r sigma a with
      | Some x =>
        match sigma1 ufn x with
        | Some r => SConst r
        | None => SUnop ufn a
        end
      | None => SUnop ufn a
      end
    | SExternalCall ufn a => SExternalCall ufn (simplify_sact a)
    | SVar _ | SReg _ | SConst _ => ua
    end.

  Definition simplify_vars (v: var_value_map) :=
    Maps.PTree.map (fun _ '(t, a) => (t, simplify_sact a)) v.

  Definition simplify_sf (sf: IRR (rule_name_t := rule_name_t)) :=
    sf <| vars := simplify_vars (vars sf) |>.

  Lemma simplify_unop_cases:
    forall ufn a a',
    simplify_sact (SUnop ufn a) = a'
    -> forall ta tr vss, wt_unop ufn ta tr
    -> wt_sact (Sigma:=Sigma) R vss a ta
    -> (
      exists b x,
      eval_sact_no_vars r sigma (simplify_sact a) = Some b
      /\ sigma1 ufn b = Some x
      /\ a' = SConst x)
    \/ a' = SUnop ufn (simplify_sact a).
  Proof.
    intros. simpl in H. simpl.
    subst. destr. destr.
    - left. exists v, v0; split; auto.
    - right; auto.
    - right; auto.
  Qed.

  Lemma simplify_bnop_cases:
    forall ufn a1 a2 a' ,
    simplify_sact (SBinop ufn a1 a2) = a'
    -> a' = SBinop ufn (simplify_sact a1) (simplify_sact a2)
    \/ (ufn = PrimUntyped.UBits2 PrimUntyped.UAnd
        /\ ((eval_sact_no_vars r sigma (simplify_sact a1) = Some (Bits [true])
             /\ a' = simplify_sact a2)
            \/ (eval_sact_no_vars r sigma (simplify_sact a1) = Some (Bits [false])
                /\ a' = const_false)
            \/ (eval_sact_no_vars r sigma (simplify_sact a2) = Some (Bits [true])
                /\ a' = simplify_sact a1)
            \/ (eval_sact_no_vars r sigma (simplify_sact a2) = Some (Bits [false])
                /\ a' = const_false)))
    \/ (ufn = PrimUntyped.UBits2 PrimUntyped.UOr
        /\ ((eval_sact_no_vars r sigma (simplify_sact a1) = Some (Bits [true])
             /\ a' = const_true)
            \/ (eval_sact_no_vars r sigma (simplify_sact a1) = Some (Bits [false])
                /\ a' = simplify_sact a2)
            \/ (eval_sact_no_vars r sigma (simplify_sact a2) = Some (Bits [true])
                /\ a' = const_true)
            \/ (eval_sact_no_vars r sigma (simplify_sact a2) = Some (Bits [false])
                /\ a' = simplify_sact a1)))
  \/ (
      exists v1 v2 v,
      eval_sact_no_vars r sigma (simplify_sact a1) = Some v1
      /\ eval_sact_no_vars r sigma (simplify_sact a2) = Some v2
      /\ sigma2 ufn v1 v2 = Some v
      /\ a' = SConst v).
  Proof.
    intros. simpl in H. subst.
    repeat destr; intuition eauto; repeat right; do 3 eexists; repeat split;
      eauto.
  Qed.

  Lemma simplify_sact_correct:
    forall vvs (WTV: wt_vvs R (Sigma:=Sigma) vvs) n a res t,
    wt_sact (Sigma:=Sigma) R vvs a t
    -> eval_sact vvs a n = Some res
    -> eval_sact vvs (simplify_sact a) n = Some res.
  Proof.
    induction n; intros a res t WT EVAL; eauto.
    simpl in EVAL.
    unfold opt_bind in EVAL.
    repeat destr_in EVAL; inv EVAL; auto.
    - simpl. rewrite Heqo; eauto.
    - inv WT.
      simpl.
      destruct (eval_sact_no_vars r sigma (simplify_sact s1)) eqn:?.
      eapply eval_sact_eval_sact_no_vars in Heqo0; eauto. subst.
      transitivity (eval_sact vvs (simplify_sact s2) (S n)). reflexivity.
      exploit IHn. 2: apply H0. eauto. intro ES.
      exploit (
        eval_sact_more_fuel (reg_t := reg_t) (ext_fn_t := ext_fn_t)
        (REnv := REnv)
      ).
      apply ES.
      2: intro ES'; rewrite ES'. lia. eauto.
      erewrite IHn. 2-3: eauto. simpl.
      erewrite IHn; eauto.
    - inv WT.
      simpl.
      destruct (eval_sact_no_vars r sigma (simplify_sact s1)) eqn:?.
      eapply eval_sact_eval_sact_no_vars in Heqo0; eauto. subst.
      transitivity (eval_sact vvs (simplify_sact s3) (S n)). reflexivity.
      exploit IHn. 2: apply H0. eauto. intro ES.
      exploit (
        eval_sact_more_fuel (reg_t := reg_t) (ext_fn_t := ext_fn_t)
        (REnv := REnv)
      ).
      apply ES.
      2: intro ES'; rewrite ES'. lia. eauto.
      erewrite IHn. 2-3: eauto. simpl.
      erewrite IHn; eauto.
    - inv WT.
      edestruct (simplify_unop_cases ufn1 s _ eq_refl) as
        [(b & vv & EQ & ESNV & EQ')|EQ]; eauto.
      + rewrite EQ'. simpl.
        exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ).
        2: eauto. eapply IHn. eauto. eauto.
        intros ->.
        simpl. auto.
      + rewrite EQ. simpl. erewrite IHn; simpl; eauto.
    - inv WT.
      exploit (
        eval_sact_wt (reg_t := reg_t) (ext_fn_t := ext_fn_t) (REnv := REnv)
      ).
      5: apply Heqo. all: eauto.
      exploit (
        eval_sact_wt (reg_t := reg_t) (ext_fn_t := ext_fn_t) (REnv := REnv)
      ).
      5: apply Heqo0. all: eauto.
      intros WTv2 WTv1.
      exploit Wt.wt_binop_sigma1. eauto. eauto. eauto. eauto. intro WTres.
      eapply IHn in Heqo; eauto.
      eapply IHn in Heqo0; eauto.
      destruct (simplify_bnop_cases ufn2 s1 s2 _ eq_refl) as
        [EQ|[(ufneq & [(ESNV & EQ)|[(ESNV & EQ)|[(ESNV & EQ)|(ESNV & EQ)]]])
            |[(ufneq & [(ESNV & EQ)|[(ESNV & EQ)|[(ESNV & EQ)|(ESNV & EQ)]]])|
        (v1 & v2 & vv & ESNV1 & ESNV2 & SIGMA & EQ)]]]; rewrite EQ; clear EQ.
      + simpl. rewrite Heqo, Heqo0.  reflexivity.
      + exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ).
        apply Heqo. apply ESNV. intros ->.
        inv WTv1. inv H6.
        apply Sact.wt_val_bool in WTv2.
        apply Sact.wt_val_bool in WTres.
        destruct WTv2, WTres. subst.
        unfold eval_sact.
        erewrite eval_sact_more_fuel. 2: eauto. simpl. auto. lia.
      + exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ). apply Heqo. apply ESNV. intros ->.
        inv WTv1. inv H6.
        apply Sact.wt_val_bool in WTv2.
        apply Sact.wt_val_bool in WTres.
        destruct WTv2, WTres. subst.
        simpl. auto.
      + exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ). eauto. apply ESNV. eauto. intros ->.
        inv WTv2. inv H6.
        apply Sact.wt_val_bool in WTv1.
        apply Sact.wt_val_bool in WTres.
        destruct WTv1, WTres. subst.
        unfold eval_sact.
        erewrite eval_sact_more_fuel. 2: eauto. simpl.
        rewrite andb_true_r; auto. lia.
      + exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ). eauto. apply ESNV. eauto. intros ->.
        inv WTv2. inv H6.
        apply Sact.wt_val_bool in WTv1.
        apply Sact.wt_val_bool in WTres.
        destruct WTv1, WTres. subst.
        simpl. rewrite andb_false_r; auto.
      + exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ). 2: apply ESNV. eauto. intros ->.
        inv WTv1. inv H6.
        apply Sact.wt_val_bool in WTv2.
        apply Sact.wt_val_bool in WTres.
        destruct WTv2, WTres. subst. simpl; auto.
      + exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ). 2: apply ESNV. eauto. intros ->.
        inv WTv1. inv H6.
        apply Sact.wt_val_bool in WTv2.
        apply Sact.wt_val_bool in WTres.
        destruct WTv2, WTres. subst.
        unfold eval_sact.
        erewrite eval_sact_more_fuel. 2: eauto. simpl. auto. lia.
      + exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ). 2: apply ESNV. eauto. intros ->.
        inv WTv2. inv H6.
        apply Sact.wt_val_bool in WTv1.
        apply Sact.wt_val_bool in WTres.
        destruct WTv1, WTres. subst. simpl. rewrite orb_true_r; auto.
      + exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ). 2: apply ESNV. eauto. intros ->.
        inv WTv2. inv H6.
        apply Sact.wt_val_bool in WTv1.
        apply Sact.wt_val_bool in WTres.
        destruct WTv1, WTres. subst.
        unfold eval_sact.
        erewrite eval_sact_more_fuel. 2: eauto. simpl.
        rewrite orb_false_r; auto. lia.
      + exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ). 2: apply ESNV1. eauto. intros ->.
        exploit (
          eval_sact_eval_sact_no_vars (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
        ). 2: apply ESNV2. eauto. intros ->.
        rewrite H0 in SIGMA. inv SIGMA. simpl. eauto.
    - simpl. inv WT;  erewrite IHn; simpl; eauto.
  Qed.

  Lemma wt_simplify_sact:
    forall vss a t,
    wt_sact R (Sigma:=Sigma) vss a t
    -> wt_sact R (Sigma:=Sigma) vss (simplify_sact a) t.
  Proof.
    induction 1; simpl; intros; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - destr.
      exploit (
        eval_sact_no_vars_wt
          (reg_t := reg_t) (ext_fn_t := ext_fn_t) (REnv := REnv)
      ).
      eauto. eauto. 2: eauto. eauto.
      intro WT. apply Sact.wt_val_bool in WT. destruct WT; subst.
      destr.
      econstructor; eauto.
    - assert (
        wt_sact
          (Sigma:=Sigma) R vss
          match eval_sact_no_vars r sigma (simplify_sact a) with
          | Some x =>
            match sigma1 ufn x with
            | Some r => SConst r
            | None => SUnop ufn (simplify_sact a)
            end
          | None => SUnop ufn (simplify_sact a)
          end t'
      ). {
        destr.
        exploit (
          eval_sact_no_vars_wt
            (reg_t := reg_t) (ext_fn_t := ext_fn_t) (REnv := REnv)
        ).
        eauto. eauto. 2: eauto. eauto.
        intro WT.
        destr.
        econstructor; eauto.
        eapply Wt.wt_unop_sigma1; eauto.
        econstructor; eauto.
        econstructor; eauto.
      }
      destr; auto.
    - assert ( wt_sact (Sigma:=Sigma) R vss
                 match eval_sact_no_vars r sigma (simplify_sact a1) with
                 | Some x =>
                     match eval_sact_no_vars r sigma (simplify_sact a2) with
                     | Some y => match sigma2 ufn x y with
                                 | Some r0 => SConst r0
                                 | None => SBinop ufn (simplify_sact a1) (simplify_sact a2)
                                 end
                     | None => SBinop ufn (simplify_sact a1) (simplify_sact a2)
                     end
                 | None => SBinop ufn (simplify_sact a1) (simplify_sact a2)
                 end t').
      {
        destr.
        2: econstructor; eauto.
        destr.
        2: econstructor; eauto.
        exploit (
          eval_sact_no_vars_wt
            (reg_t := reg_t) (ext_fn_t := ext_fn_t) (REnv := REnv)
        ). eauto. eauto.
        2: apply Heqo. eauto.
        intro WT1.
        exploit (
          eval_sact_no_vars_wt
            (reg_t := reg_t) (ext_fn_t := ext_fn_t) (REnv := REnv)
        ). eauto. eauto.
        2: apply Heqo0. eauto.
        intro WT2.
        destr.
        2: econstructor; eauto.
        econstructor.
        eapply Wt.wt_binop_sigma1; eauto.
      }
      destr; auto.
      destr; auto.
      + clear H2. inv H1.
        destr.
        exploit (
          eval_sact_no_vars_wt
            (reg_t := reg_t) (ext_fn_t := ext_fn_t) (REnv := REnv)
        ). eauto. eauto.
        apply IHwt_sact1. eauto.
        intro WT1. inv WT1.
        destruct (eval_sact_no_vars r sigma (simplify_sact a2)) eqn:?.
        exploit (
          eval_sact_no_vars_wt
            (reg_t := reg_t) (ext_fn_t := ext_fn_t) (REnv := REnv)
        ). eauto. eauto.
        apply IHwt_sact2. eauto.
        intro WT2. inv WT2.
        destr. destr. econstructor; eauto. econstructor; eauto.
        simpl in H2; lia.
        destruct bs0. simpl in H2; lia. simpl in H2. destruct l.
        destr; eauto. constructor. constructor. auto.
        destruct bs0. simpl in H2; lia. simpl in H2.
        repeat destr; eauto; econstructor; eauto; constructor; auto.
        repeat destr; repeat econstructor; eauto.
        repeat destr; repeat econstructor; eauto.
        subst.
        exploit (
          eval_sact_no_vars_wt
            (reg_t := reg_t) (ext_fn_t := ext_fn_t) (REnv := REnv)
        ). eauto. eauto.
        apply IHwt_sact2. eauto.
        intro WT2. inv WT2.
        auto.
      + clear H2. inv H1.
        destr.
        exploit (
          eval_sact_no_vars_wt
            (reg_t := reg_t) (ext_fn_t := ext_fn_t) (REnv := REnv)
        ). eauto. eauto.
        apply IHwt_sact1. eauto.
        intro WT1. inv WT1.
        destruct (eval_sact_no_vars r sigma (simplify_sact a2)) eqn:?.
        exploit (
          eval_sact_no_vars_wt
            (reg_t := reg_t) (ext_fn_t := ext_fn_t) (REnv := REnv)
        ). eauto. eauto.
        apply IHwt_sact2. eauto.
        intro WT2. inv WT2.
        destr. destr. econstructor; eauto. econstructor; eauto.
        simpl in H2; lia.
        destruct bs0. simpl in H2; lia. simpl in H2. destruct l.
        destr; eauto. constructor. constructor. auto.
        destruct bs0. simpl in H2; lia. simpl in H2.
        repeat destr; eauto; econstructor; eauto; constructor; auto.
        repeat destr; repeat econstructor; eauto.
        repeat destr; repeat econstructor; eauto.
        subst.
        exploit (
          eval_sact_no_vars_wt
            (reg_t := reg_t) (ext_fn_t := ext_fn_t) (REnv := REnv)
        ). eauto. eauto.
        apply IHwt_sact2. eauto.
        intro WT2. inv WT2.
        auto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.

  Lemma simplify_sact_wt_sact_ok':
    forall vvs a t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
    wt_sact (Sigma := Sigma) R vvs (simplify_sact a) t.
  Proof. apply wt_simplify_sact. Qed.

  Lemma simplify_vars_wt_sact_ok:
    forall vvs s t (WTS: wt_sact (Sigma := Sigma) R (simplify_vars vvs) s t),
    wt_sact (Sigma := Sigma) R vvs s t.
  Proof.
    intros.
    induction WTS; try (econstructor; eauto; fail).
    unfold simplify_vars in H.
    rewrite Maps.PTree.gmap in H. unfold option_map in H.
    destr_in H. destruct p.
    - apply Some_inj in H. apply pair_inj in H. destruct H. subst.
      econstructor. eauto.
    - easy.
  Qed.

  Lemma simplify_vars_wt_sact_ok':
    forall vvs s t (WTS: wt_sact (Sigma := Sigma) R vvs s t),
    wt_sact (Sigma := Sigma) R (simplify_vars vvs) s t.
  Proof.
    intros.
    induction WTS; econstructor; eauto.
    unfold simplify_vars.
    setoid_rewrite Maps.PTree.gmap.
    unfold option_map. setoid_rewrite H. easy.
  Qed.

  Lemma simplify_vars_wtvvs_ok':
    forall vvs (WTVVS: wt_vvs (Sigma := Sigma) R vvs),
    wt_vvs (Sigma := Sigma) R (simplify_vars vvs).
  Proof.
    intros. unfold wt_vvs. intros.
    apply simplify_vars_wt_sact_ok'.
    unfold simplify_vars in H.
    rewrite Maps.PTree.gmap in H. unfold option_map in H.
    destr_in H. destruct p.
    - apply Some_inj in H. apply pair_inj in H. destruct H. subst t0.
      inv H0. apply simplify_sact_wt_sact_ok'; eauto.
    - easy.
  Qed.

  Lemma simplify_sact_reachable_vars_ok:
    forall vvs s v (RV: reachable_var vvs (simplify_sact s) v),
    reachable_var vvs s v.
  Proof.
    intros.
    induction s; simpl in *; eauto.
    - repeat (destr_in RV); eauto;
        try (
          inv RV;
          try (eapply reachable_var_if_cond; eauto; fail);
          try (eapply reachable_var_if_true; eauto; fail);
          try (eapply reachable_var_if_false; eauto; fail);
          fail); subst.
      + eapply IHs2 in RV. eapply reachable_var_if_true; eauto.
      + eapply IHs3 in RV. eapply reachable_var_if_false; eauto.
    - repeat (destr_in RV); econstructor; inv RV; eauto.
    - repeat (destr_in RV);
      try (eapply reachable_var_binop1; eauto; fail);
      try (eapply reachable_var_binop2; eauto; fail);
      try (
        inv RV;
        try (eapply reachable_var_binop1; eauto; fail);
        try (eapply reachable_var_binop2; eauto; fail);
        fail
      );
      subst.
    - inv RV. econstructor. eauto.
  Qed.

  Lemma simplify_sact_interp_sact_ok':
    forall a v vvs (WTVVS: wt_vvs (Sigma := Sigma) R vvs) t
      (WTS: wt_sact (Sigma := Sigma) R vvs a t)
      (VVSSV: vvs_smaller_variables vvs),
    interp_sact (sigma := sigma) REnv r vvs a v
    -> interp_sact (sigma := sigma) REnv r vvs (simplify_sact a) v.
  Proof.
    intros.
    eapply interp_sact_do_eval_sact in H; eauto.
    unfold do_eval_sact in H.
    eapply eval_sact_interp_sact.
    erewrite simplify_sact_correct; eauto.
  Qed.

  Lemma simplify_sact_var_in_sact_ok':
    forall s v (VIS: var_in_sact (simplify_sact s) v),
    var_in_sact s v.
  Proof.
    intros.
    induction s; try (eauto; fail).
    - simpl in VIS. repeat (destr_in VIS); try (
        inv VIS; try (apply var_in_if_cond; eauto; fail);
        try (apply var_in_if_true; eauto; fail);
        try (apply var_in_if_false; eauto; fail);
        fail).
      + apply var_in_if_true; eauto.
      + apply var_in_if_false; eauto.
    - simpl in VIS. repeat (destr_in VIS);
        (econstructor; eapply IHs; inv VIS; easy).
    - simpl in VIS. destr_in VIS;
      try (
        inv VIS;
        try (apply var_in_sact_binop_1; eauto; fail);
        try (apply var_in_sact_binop_2; eauto; fail);
        fail).
      repeat (destr_in VIS);
        try (apply var_in_sact_binop_1; eauto; fail);
        try (apply var_in_sact_binop_2; eauto; fail);
        try (
          inv VIS; try (apply var_in_sact_binop_1; eauto; fail);
          try (apply var_in_sact_binop_2; eauto; fail); fail).
      repeat (destr_in VIS);
        try (apply var_in_sact_binop_1; eauto; fail);
        try (apply var_in_sact_binop_2; eauto; fail);
        try (
          inv VIS; try (apply var_in_sact_binop_1; eauto; fail);
          try (apply var_in_sact_binop_2; eauto; fail); fail).
      repeat (destr_in VIS);
        try (apply var_in_sact_binop_1; eauto; fail);
        try (apply var_in_sact_binop_2; eauto; fail);
        try (
          inv VIS; try (apply var_in_sact_binop_1; eauto; fail);
          try (apply var_in_sact_binop_2; eauto; fail); fail).
      repeat (destr_in VIS);
        try (apply var_in_sact_binop_1; eauto; fail);
        try (apply var_in_sact_binop_2; eauto; fail);
        try (
          inv VIS; try (apply var_in_sact_binop_1; eauto; fail);
          try (apply var_in_sact_binop_2; eauto; fail); fail).
    - inv VIS. econstructor. eauto.
  Qed.

  Lemma simplify_vars_vvssv_ok':
    forall vvs (VVSSV: vvs_smaller_variables vvs),
    vvs_smaller_variables (simplify_vars vvs).
  Proof.
    intros.
    unfold vvs_smaller_variables in *. intros.
    unfold simplify_vars in H.
    rewrite Maps.PTree.gmap in H. unfold option_map in H.
    destr_in H. destruct p.
    - apply Some_inj in H. apply pair_inj in H. destruct H. subst t0.
      eapply VVSSV; eauto. inv H1.
      apply simplify_sact_var_in_sact_ok'. eauto.
    - easy.
  Qed.

  Lemma simplify_vars_interp_sact_ok':
    forall vvs a v (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
      (VVSSV: vvs_smaller_variables vvs)
      (EV_INIT: interp_sact (sigma := sigma) REnv r vvs a v),
    interp_sact (sigma := sigma) REnv r (simplify_vars vvs) a v.
  Proof.
    intros.
    induction EV_INIT; try (econstructor; eauto; fail).
    econstructor.
    - unfold simplify_vars. setoid_rewrite Maps.PTree.gmap.
      unfold option_map. setoid_rewrite H.
      f_equal.
    - eapply simplify_sact_interp_sact_ok'; eauto.
      + apply simplify_vars_wtvvs_ok'. eauto.
      + apply simplify_vars_wt_sact_ok'. eauto.
      + apply simplify_vars_vvssv_ok'. eauto.
  Qed.

  Lemma simplify_vars_ok:
    forall
      fuel vvs a res (EV_INIT: eval_sact vvs a fuel = Some res)
      (WTVVS: wt_vvs (Sigma := Sigma) R vvs) t
      (WTS: wt_sact (Sigma := Sigma) R vvs a t),
    eval_sact (simplify_vars vvs) a fuel = Some res.
  Proof.
    induction fuel; simpl; intros; eauto.
    Transparent eval_sact.
    destruct a; simpl in *.
    - unfold opt_bind in EV_INIT. repeat destr_in EV_INIT; inv EV_INIT.
      setoid_rewrite PTree.gmap. setoid_rewrite Heqo. simpl.
      erewrite IHfuel. eauto. eapply simplify_sact_correct; eauto. auto.
      eapply wt_simplify_sact; eauto.
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

  Lemma simplify_sact_interp_sact_ok:
    forall
      vvs (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
      (VVSSV: vvs_smaller_variables vvs) a v
      (EV_INIT: interp_sact (sigma := sigma) REnv r vvs (simplify_sact a) v)
      t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
    interp_sact (sigma := sigma) REnv r vvs a v.
  Proof.
    induction a; simpl; intros; eauto; inv WTS.
    - destr_in EV_INIT.
      exploit (
        eval_sact_no_vars_wt
          (reg_t := reg_t) (ext_fn_t := ext_fn_t) (REnv := REnv)
      ). 4: apply Heqo. all: eauto.
      apply wt_simplify_sact. eauto. intro WT. apply Sact.wt_val_bool in WT.
      destruct WT; subst.
      econstructor. eapply eval_sact_no_vars_interp in Heqo.
      eapply IHa1 in Heqo. eauto. eauto. destr; eauto.
      inv EV_INIT.
      econstructor; eauto.
      destr; eauto.
    - destr_in EV_INIT.
      destr_in EV_INIT.
      + inv EV_INIT.
        econstructor; eauto.
        eapply eval_sact_no_vars_interp in Heqo; eauto.
      + inv EV_INIT.
        econstructor; eauto.
      + inv EV_INIT.
        econstructor; eauto.
    - destruct (eval_sact_no_vars r sigma (simplify_sact a1)) eqn:?.
      exploit (
        eval_sact_no_vars_interp (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
      ).
      apply Heqo. intro IS1.
      destruct (eval_sact_no_vars r sigma (simplify_sact a2)) eqn:?.
      exploit (
        eval_sact_no_vars_interp (reg_t := reg_t) (ext_fn_t := ext_fn_t)
          (REnv := REnv)
      ).
      apply Heqo0. intro IS2.
      + destr_in EV_INIT.
        destr_in EV_INIT; inv EV_INIT.
        econstructor; eauto.
        econstructor; eauto.
        econstructor; eauto.
        assert (interp_sact (sigma:=sigma) REnv r vvs match sigma2 (PrimUntyped.UBits2 fn) v0 v1 with
                                        | Some r => SConst r
                                        | None => SBinop (PrimUntyped.UBits2 fn) (simplify_sact a1) (simplify_sact a2)
                                        end v ->
                sigma2 (PrimUntyped.UBits2 fn) v0 v1 = Some v
               ).
        clear EV_INIT.
        intros EV.
        destr_in EV. inv EV. auto. inv EV.
        generalize (interp_sact_determ _ _ _ _ _ IS1 _ H3).
        generalize (interp_sact_determ _ _ _ _ _ IS2 _ H7). congruence.
        destr_in EV_INIT; auto.
        simpl.
        inv H5.
        exploit @interp_sact_wt. eauto. eauto. eauto. auto. apply vvs_range_max_var. apply H2. eauto.
        exploit @interp_sact_wt. eauto. eauto. eauto. auto. apply vvs_range_max_var. apply H4. eauto.
        intros WT2 WT1. inv WT2; inv WT1. simpl in *.
        destr_in EV_INIT. destruct bs; [|simpl in H1; lia].
        inv EV_INIT.
        generalize (interp_sact_determ _ _ _ _ _ IS1 _ H6).
        generalize (interp_sact_determ _ _ _ _ _ IS2 _ H8).
        intros. subst. simpl in H9. inv H9. reflexivity.
        destruct bs; [simpl in H1; lia|].
        destruct l, bs; try (simpl in H1; lia).
        subst. simpl in *.
        destr_in EV_INIT. simpl.
        generalize (interp_sact_determ _ _ _ _ _ IS2 _ EV_INIT). congruence. inv EV_INIT. reflexivity.
        assert ( interp_sact (sigma:=sigma) REnv r vvs
                   (SBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) (simplify_sact a1) (simplify_sact a2)) v).
        repeat destr_in EV_INIT; eauto. clear EV_INIT. inv H0.
        generalize (interp_sact_determ _ _ _ _ _ IS1 _ H7).
        generalize (interp_sact_determ _ _ _ _ _ IS2 _ H9). intros; subst.
        simpl in H10. inv H10. simpl. auto.
        simpl.
        inv H5.
        exploit @interp_sact_wt. eauto. eauto. eauto. auto. apply vvs_range_max_var. apply H2. eauto.
        exploit @interp_sact_wt. eauto. eauto. eauto. auto. apply vvs_range_max_var. apply H4. eauto.
        intros WT2 WT1. inv WT2; inv WT1. simpl in *.
        destr_in EV_INIT. destruct bs; [|simpl in H1; lia].
        inv EV_INIT.
        generalize (interp_sact_determ _ _ _ _ _ IS1 _ H6).
        generalize (interp_sact_determ _ _ _ _ _ IS2 _ H8).
        intros. subst. simpl in H9. inv H9. reflexivity.
        destruct bs; [simpl in H1; lia|].
        destruct l, bs; try (simpl in H1; lia).
        subst. simpl in *.
        destr_in EV_INIT. simpl. inv EV_INIT. auto. simpl.
        generalize (interp_sact_determ _ _ _ _ _ IS2 _ EV_INIT). congruence.
        assert (interp_sact (sigma:=sigma) REnv r vvs
                   (SBinop (PrimUntyped.UBits2 PrimUntyped.UOr) (simplify_sact a1) (simplify_sact a2)) v).
        repeat destr_in EV_INIT; eauto. clear EV_INIT. inv H0.
        generalize (interp_sact_determ _ _ _ _ _ IS1 _ H7).
        generalize (interp_sact_determ _ _ _ _ _ IS2 _ H9). intros; subst.
        simpl in H10. inv H10. simpl. auto.
        destr_in EV_INIT; auto.
        econstructor. eauto. eauto.
        inv EV_INIT. auto.
        inv EV_INIT.
        generalize (interp_sact_determ _ _ _ _ _ IS1 _ H3).
        generalize (interp_sact_determ _ _ _ _ _ IS2 _ H7). intros; subst.
        econstructor; eauto.
        destr_in EV_INIT; auto.
        econstructor. eauto. eauto.
        inv EV_INIT. auto.
        inv EV_INIT.
        generalize (interp_sact_determ _ _ _ _ _ IS1 _ H3).
        generalize (interp_sact_determ _ _ _ _ _ IS2 _ H7). intros; subst.
        econstructor; eauto.
      + destr_in EV_INIT. inv EV_INIT.
        * generalize (interp_sact_determ _ _ _ _ _ IS1 _ H3). intro; subst.
          econstructor; eauto.
        * assert (interp_sact (sigma:=sigma) REnv r vvs (SBinop (PrimUntyped.UBits2 fn) (simplify_sact a1) (simplify_sact a2)) v ->
                  interp_sact (sigma:=sigma) REnv r vvs (SBinop (PrimUntyped.UBits2 fn) a1 a2) v
                 ).
          clear EV_INIT.
          intro IS. inv IS.
          generalize (interp_sact_determ _ _ _ _ _ IS1 _ H3). intro; subst.
          econstructor; eauto.
          repeat destr_in EV_INIT; eauto.
          clear H.
          inv H5. econstructor; eauto.
          exploit @interp_sact_wt. eauto. eauto. eauto. auto. apply vvs_range_max_var. apply H4. eauto.
          intro A; inv A.
          exploit @interp_sact_wt. eauto. eauto. eauto. auto. apply vvs_range_max_var. apply H2. eauto.
          intro A; inv A.
          simpl in H1. destruct bs; simpl in H1; try lia. destruct bs; simpl in H1; try lia.
          simpl. auto.
          clear H.
          inv H5. inv EV_INIT.
          exploit @wt_sact_interp. eauto. eauto. eauto. eauto. apply vvs_range_max_var. apply H4. intros (v2 & IS2 & WT2). inv WT2.
          econstructor; eauto.
          exploit @interp_sact_wt. eauto. eauto. eauto. auto. apply vvs_range_max_var. apply H2. eauto.
          intro A; inv A.
          simpl in H1. destruct bs; simpl in H1; try lia. destruct bs; simpl in H1; try lia.
          simpl. auto.
          clear H.
          inv H5. inv EV_INIT.
          exploit @wt_sact_interp. eauto. eauto. eauto. eauto. apply vvs_range_max_var. apply H4. intros (v2 & IS2 & WT2). inv WT2.
          econstructor; eauto.
          exploit @interp_sact_wt. eauto. eauto. eauto. auto. apply vvs_range_max_var. apply H2. eauto.
          intro A; inv A.
          simpl in H1. destruct bs; simpl in H1; try lia. destruct bs; simpl in H1; try lia.
          simpl. auto.
          clear H.
          inv H5. econstructor; eauto.
          exploit @interp_sact_wt. eauto. eauto. eauto. auto. apply vvs_range_max_var. apply H4. eauto.
          intro A; inv A.
          exploit @interp_sact_wt. eauto. eauto. eauto. auto. apply vvs_range_max_var. apply H2. eauto.
          intro A; inv A.
          simpl in H1. destruct bs; simpl in H1; try lia. destruct bs; simpl in H1; try lia.
          simpl. auto.
        * inv EV_INIT. generalize (interp_sact_determ _ _ _ _ _ IS1 _ H3). intro; subst.
          econstructor; eauto.
        * inv EV_INIT. generalize (interp_sact_determ _ _ _ _ _ IS1 _ H3). intro; subst.
          econstructor; eauto.
      + assert (interp_sact (sigma:=sigma) REnv r vvs (SBinop ufn2 (simplify_sact a1) (simplify_sact a2)) v ->
                interp_sact (sigma:=sigma) REnv r vvs (SBinop ufn2 a1 a2) v
               ).
        {
          clear EV_INIT.
          intro IS. inv IS.
          econstructor; eauto.
        }
        destr_in EV_INIT; auto.
        repeat destr_in EV_INIT; auto; clear H.
        econstructor; eauto.
        eapply IHa2.
        eapply eval_sact_no_vars_interp. eauto. eauto.
        exploit (
          eval_sact_no_vars_wt
            (reg_t := reg_t)  (ext_fn_t := ext_fn_t) (REnv := REnv)
        ).
        4: apply Heqo0. all: eauto. eapply wt_simplify_sact; eauto.
        exploit @interp_sact_wt. eauto. eauto. eauto. eauto. apply vvs_range_max_var. apply H2. eauto.
        intros WT1 WT2. inv H5. inv WT2. inv WT1.
        destruct bs; simpl in H0; try lia.
        destruct bs; simpl in H0; try lia.
        simpl. rewrite andb_true_r. auto.
        exploit @wt_sact_interp. eauto. eauto. eauto. eauto. apply vvs_range_max_var. apply H2. intros (vv1 & IS1 & WT1).
        econstructor; eauto.
        eapply IHa2.
        eapply eval_sact_no_vars_interp. eauto. eauto.
        exploit (
          eval_sact_no_vars_wt
            (reg_t := reg_t)  (ext_fn_t := ext_fn_t) (REnv := REnv)
        ).
        4: apply Heqo0. all: eauto. eapply wt_simplify_sact; eauto.
        intros WT2. inv H5. inv WT2. inv WT1.
        destruct bs; simpl in H0; try lia.
        destruct bs; simpl in H0; try lia.
        simpl. rewrite andb_false_r. inv EV_INIT. auto.
        exploit @wt_sact_interp. eauto. eauto. eauto. eauto. apply vvs_range_max_var. apply H2. intros (vv1 & IS1 & WT1).
        econstructor; eauto.
        eapply IHa2.
        eapply eval_sact_no_vars_interp. eauto. eauto.
        exploit (
          eval_sact_no_vars_wt
            (reg_t := reg_t)  (ext_fn_t := ext_fn_t) (REnv := REnv)
        ).
        4: apply Heqo0. all: eauto. eapply wt_simplify_sact; eauto.
        intros WT2. inv H5. inv WT2. inv WT1.
        destruct bs; simpl in H0; try lia.
        destruct bs; simpl in H0; try lia.
        simpl. rewrite orb_true_r. inv EV_INIT. auto.
        econstructor; eauto.
        eapply IHa2.
        eapply eval_sact_no_vars_interp. eauto. eauto.
        exploit (
          eval_sact_no_vars_wt
            (reg_t := reg_t)  (ext_fn_t := ext_fn_t) (REnv := REnv)
        ).
        4: apply Heqo0. all: eauto. eapply wt_simplify_sact; eauto.
        exploit @interp_sact_wt. eauto. eauto. eauto. eauto. apply vvs_range_max_var. apply H2. eauto.
        intros WT1 WT2. inv H5. inv WT2. inv WT1.
        destruct bs; simpl in H0; try lia.
        destruct bs; simpl in H0; try lia.
        simpl. rewrite orb_false_r. auto.
    - inv EV_INIT. econstructor; eauto.
  Qed.

  Lemma simplify_vars_interp_sact_ok:
    forall vvs
           (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
           (VVSSV: vvs_smaller_variables vvs)
           a v
           (EV_INIT: interp_sact (sigma := sigma) REnv r (simplify_vars vvs) a v)
           t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
      interp_sact (sigma := sigma) REnv r vvs a v.
  Proof.
    induction 3; simpl; intros; inv WTS.
    - setoid_rewrite PTree.gmap in H. setoid_rewrite H1 in H. simpl in H. inv H.
      econstructor; eauto.
      eapply simplify_sact_interp_sact_ok; eauto.
      eapply IHEV_INIT.
      eapply wt_simplify_sact; eauto.
    - econstructor.
    - econstructor. eauto.
      eapply IHEV_INIT2. destr; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.

  Lemma simplify_vars_reachable_var_ok:
    forall vvs v (VVSSV: vvs_smaller_variables vvs) a,
    reachable_var (simplify_vars vvs) a v
    -> reachable_var vvs a v.
  Proof.
    induction 2; simpl; intros; eauto.
    - econstructor.
    - setoid_rewrite PTree.gmap in H. unfold option_map in H.
      repeat destr_in H; inv H.
      econstructor; eauto.
      eapply simplify_sact_reachable_vars_ok. auto.
    - eapply reachable_var_if_cond; eauto.
    - eapply reachable_var_if_true; eauto.
    - eapply reachable_var_if_false; eauto.
    - eapply reachable_var_binop1; eauto.
    - eapply reachable_var_binop2; eauto.
    - eapply reachable_var_unop; eauto.
    - constructor; auto.
  Qed.

  Lemma sf_eq_simplify_sf sf:
    wf_sf sf -> sf_eq R Sigma r sigma sf (simplify_sf sf).
  Proof.
    unfold simplify_sf. intros. inv H. constructor; auto.
    intros. simpl.
    split; intros.
    eapply simplify_vars_interp_sact_ok'; eauto.
    inversion H1. subst.
    unfold simplify_vars in H3. rewrite PTree.gmap in H3.
    unfold option_map in H3. repeat destr_in H3; inv H3.
    eapply simplify_vars_interp_sact_ok; eauto.
    econstructor. eauto.
    simpl. intros.
    eapply simplify_vars_wt_sact_ok'; eauto.
    eapply simplify_vars_wt_sact_ok; eauto.
  Qed.

  Lemma wf_sf_simplify_sf: forall sf, wf_sf sf -> wf_sf (simplify_sf sf).
  Proof.
    destruct 1; constructor.
    eapply simplify_vars_wtvvs_ok'; eauto.
    eapply simplify_vars_vvssv_ok'; eauto.
    simpl. intros.
    eapply wf_sf_final in H.
    eapply simplify_vars_wt_sact_ok'. auto.
  Qed.

  Lemma simplify_sf_interp_cycle_ok:
    forall reg sf,
    wf_sf sf
    -> getenv REnv (interp_cycle r sigma sf) reg
    = getenv REnv (interp_cycle r sigma (simplify_sf sf)) reg.
  Proof.
    intros.
    eapply sf_eq_interp_cycle_ok; eauto.
    - apply wf_sf_simplify_sf; auto.
    - apply sf_eq_simplify_sf. auto.
  Qed.
End Simplify.
