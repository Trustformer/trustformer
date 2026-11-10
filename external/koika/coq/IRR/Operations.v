Require Import Koika.IRR.Interpretation.
Require Import Koika.IRR.Properties.
Require Import Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.BitsToLists.
Require Import Koika.IRR.Sact.
Require Import Koika.KoikaForm.Desugaring.DesugaredSyntax.
Require Import Koika.KoikaForm.Syntax.
Require Import Koika.KoikaForm.Types.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.Utils.EqDec.
Require Import Koika.Utils.Environments.
Require Import Koika.Utils.Maps.
Require Import Koika.Utils.Tactics.
Require Import Koika.IRR.IRR.
Require Import Coq.Lists.List.
Scheme Equality for list.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Mergesort.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section Operations.
  Context {pos_t reg_t ext_fn_t rule_name_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {ext_fn_t_eq_dec: EqDec ext_fn_t}.
  Context {REnv: Env reg_t}.

  Context (R: reg_t -> type).
  Context (Sigma: ext_fn_t -> ExternalSignature).

  Definition ext_funs_defs := forall f: ext_fn_t, val -> val.
  Definition UREnv := REnv.(env_t) (fun _ => val).

  Context (r: UREnv).
  Context (sigma: ext_funs_defs).

  Definition sact := sact (ext_fn_t := ext_fn_t) (reg_t := reg_t).
  Definition IRR := IRR (ext_fn_t := ext_fn_t) (reg_t := reg_t) (rule_name_t := rule_name_t).
  Instance etaIRR : Settable _ := @etaIRR reg_t ext_fn_t rule_name_t.
  Definition var_value_map :=
    var_value_map (ext_fn_t := ext_fn_t) (reg_t := reg_t).
  Definition useful_vars := useful_vars (ext_fn_t := ext_fn_t) (reg_t := reg_t) (rule_name_t := rule_name_t).
  Definition eval_sact := eval_sact r sigma.
  Definition wf_sf := wf_sf (rule_name_t := rule_name_t) R Sigma.

  Hypothesis WTRENV: Wt.wt_renv R REnv r.

  Context {
    wt_sigma:
    forall ufn vc, wt_val (arg1Sig (Sigma ufn)) vc
    -> wt_val (retSig (Sigma ufn)) (sigma ufn vc)
  }.

  Definition remove_vars (sf: IRR) : IRR :=
    sf <|
      vars :=
        fold_left
          (fun t n =>
            match (vars sf) ! n with
            | Some v => PTree.set n v t
            | _ => t
            end)
          (useful_vars sf)
          (PTree.empty _)
    |>.

  Definition filter_ptree (vvs t2: var_value_map) (l: list positive) :=
    (fold_left
      (fun t n =>
        match vvs ! n with
        | Some v => PTree.set n v t
        | _ => t
        end)
      l t2).

  Lemma nodup_reachable_vars_aux:
    forall vvs (VSV: vvs_smaller_variables vvs) fuel x acc,
    NoDup acc
    -> NoDup
         (reachable_vars_aux
            (reg_t := reg_t) (ext_fn_t := ext_fn_t) vvs x acc fuel).
  Proof.
    intros.
    eapply reachable_vars_aux_nd; eauto.
  Qed.

  Lemma nodup_useful_vars sf:
    vvs_smaller_variables (vars sf) -> NoDup (useful_vars sf).
  Proof.
    intros. unfold useful_vars. unfold Interpretation.useful_vars.
    apply fold_left_induction. constructor.
    intros.
    eapply nodup_reachable_vars_aux; eauto.
  Qed.

  Lemma filter_ptree_in:
    forall l vvs t2 v (NI: ~ In v l), (filter_ptree vvs t2 l) ! v = t2 ! v.
  Proof.
    induction l; simpl; intros; eauto.
    rewrite IHl. destr. rewrite PTree.gso. auto. intuition congruence.
    intuition.
  Qed.

  Lemma eval_sact_reachable:
    forall
      v1 v2 fuel a (SAME: forall v, reachable_var v1 a v -> v1 ! v = v2 ! v),
    eval_sact v1 a fuel = eval_sact v2 a fuel.
  Proof.
    induction fuel; simpl; intros; eauto.
    destruct a; simpl in *; eauto.
    - rewrite <- SAME. unfold opt_bind; repeat destr; eauto.
      eapply IHfuel. intros; apply SAME. econstructor; eauto. constructor.
    - rewrite <- ! IHfuel. auto.
      intros v RV; apply SAME. eapply reachable_var_if_false; eauto.
      intros v RV; apply SAME. eapply reachable_var_if_true; eauto.
      intros v RV; apply SAME. eapply reachable_var_if_cond; eauto.
    - rewrite <- ! IHfuel. auto.
      intros v RV; apply SAME. eapply reachable_var_unop; eauto.
    - rewrite <- ! IHfuel. auto.
      intros v RV; apply SAME. eapply reachable_var_binop2; eauto.
      intros v RV; apply SAME. eapply reachable_var_binop1; eauto.
    - rewrite <- ! IHfuel. auto.
      intros v RV; apply SAME. eapply reachable_var_externalCall; eauto.
  Qed.

  Lemma remove_vars_correct:
    forall sf (VSV:   vvs_smaller_variables (vars sf)) n,
    In n (List.map snd (final_values sf))
    -> forall fuel,
    eval_sact (vars sf) (SVar n) fuel
    = eval_sact (vars (remove_vars sf)) (SVar n) fuel.
  Proof.
    intros. simpl.
    assert (
      forall v, reachable_var (vars sf) (SVar n) v -> In v (useful_vars sf)
    ). {
      intros v RV. inv RV.
      eapply useful_vars_incl; eauto.
      intros; eapply useful_vars_good; eauto.
    }
    assert (
      forall l v (vvs t2: var_value_map),
      In v l
      -> NoDup l
      -> (forall x, In x l -> t2 ! x = None)
      -> vvs ! v = (filter_ptree vvs t2 l) ! v
    ). {
      clear.
      induction l; simpl; intros. easy.
      inv H0. destruct H. subst.
      destr.
      rewrite filter_ptree_in. rewrite PTree.gss. auto. auto.
      rewrite filter_ptree_in; auto. symmetry; apply H1. auto.
      rewrite <- IHl. auto. auto. auto. intros.
      destr; eauto. rewrite PTree.gso; eauto. congruence.
    }
    specialize (
      fun v REACH vvs t2 => H1 _ _ vvs t2 (H0 v REACH) (nodup_useful_vars _ VSV)
    ).
    fold (filter_ptree (vars sf) (PTree.empty _) (useful_vars sf)).
    apply eval_sact_reachable. intros; apply H1. auto.
    intros; apply PTree.gempty.
  Qed.

  Lemma eval_no_var:
    forall vvs vvs' fuel a,
    (forall n, ~ reachable_var vvs a n)
    -> eval_sact vvs a fuel = eval_sact vvs' a fuel.
  Proof.
    induction fuel; simpl; intros; eauto.
    destruct a; simpl; intros; eauto.
    - elim (H var). constructor.
    - rewrite <- ! IHfuel. eauto.
      intros n REACH; eapply H. apply reachable_var_if_false; eauto.
      intros n REACH; eapply H. apply reachable_var_if_true; eauto.
      intros n REACH; eapply H. apply reachable_var_if_cond; eauto.
    - rewrite <- ! IHfuel. eauto.
      intros n REACH; eapply H. apply reachable_var_unop; eauto.
    - rewrite <- ! IHfuel. eauto.
      intros n REACH; eapply H. apply reachable_var_binop2; eauto.
      intros n REACH; eapply H. apply reachable_var_binop1; eauto.
    - rewrite <- ! IHfuel. eauto.
      intros n REACH; eapply H. apply reachable_var_externalCall; eauto.
  Qed.

  Fixpoint contains_vars (e: sact) : bool :=
    match e with
    | SConst _ => false
    | SBinop ufn a1 a2 => orb (contains_vars a1) (contains_vars a2)
    | SUnop ufn a1 => contains_vars a1
    | SVar v => true
    | SIf cond tb fb =>
      orb (contains_vars cond) (orb (contains_vars tb) (contains_vars fb))
    | SExternalCall _ a => contains_vars a
    | SReg _ => false
    end.

  Fixpoint replace_all_occurrences_in_sact (ua: sact) (from: positive) (to: val)
  : sact :=
    match ua with
    | SBinop ufn a1 a2 =>
      SBinop
        ufn (replace_all_occurrences_in_sact a1 from to)
        (replace_all_occurrences_in_sact a2 from to)
    | SUnop ufn a1 => SUnop ufn (replace_all_occurrences_in_sact a1 from to)
    | SVar v =>
      if Pos.eq_dec v from then SConst to
      else SVar v
    | SIf cond tb fb =>
      SIf
        (replace_all_occurrences_in_sact cond from to)
        (replace_all_occurrences_in_sact tb from to)
        (replace_all_occurrences_in_sact fb from to)
    | SConst c => SConst c
    | SExternalCall ufn a =>
      SExternalCall ufn (replace_all_occurrences_in_sact a from to)
    | SReg r => SReg r
    end.

  Definition replace_all_occurrences_in_vars
    (vars: var_value_map) (from: positive) (to: val)
  : var_value_map :=
    PTree.map
      (fun _ '(t, ua) => (t, replace_all_occurrences_in_sact ua from to))
      vars.

  Definition replace_all_occurrences
    (sf: IRR) (from: positive) (to: val)
  : IRR :=
    sf <| vars := replace_all_occurrences_in_vars (vars sf) from to |>.

  Definition max_var (vars: var_value_map) :=
    PTree.fold (fun acc k _ => Pos.max acc k) vars xH.

  Lemma vvs_range_max_var:
    forall vars, vvs_range vars (Pos.succ (max_var vars)).
  Proof.
    red; intros.
    unfold max_var.
    rewrite PTree.fold_spec.
    apply PTree.elements_correct in H.
    revert H.
    rewrite <- fold_left_rev_right.
    rewrite in_rev.
    generalize (rev (PTree.elements vars)).
    induction l; simpl; intros; eauto. easy.
    destruct H. subst. simpl. red; lia.
    apply IHl in H. red in H. red. lia.
  Qed.

  Open Scope nat.

  Lemma eval_sact_more_fuel:
    forall n1 vvs a v n2,
    eval_sact vvs a n1 = Some v
    -> n1 <= n2
    -> eval_sact vvs a n2 = Some v.
  Proof.
    induction n1; simpl; intros; eauto. easy.
    destruct n2; simpl. lia.
    unfold opt_bind in *.
    assert (n1 <= n2) by lia.
    repeat destr_in H; inv H; eauto.
    - erewrite IHn1; eauto.
    - erewrite IHn1; eauto.
      erewrite IHn1; eauto.
    - erewrite IHn1; eauto.
      simpl. erewrite IHn1; eauto.
    - erewrite IHn1; eauto.
    - erewrite IHn1; eauto.
      erewrite IHn1; eauto.
    - erewrite IHn1; eauto.
  Qed.

  Definition vvs_size (vvs:var_value_map) m : nat :=
    PTree.fold (
      fun acc k '(t,a) =>
        if Pos.ltb k m
        then size_sact (ext_fn_t := ext_fn_t) a + acc
        else acc
    ) vvs O.

  Lemma vvs_size1_aux:
    forall var n (LT: (var < n)%positive),
    forall (l : list (positive * (type * sact))) (n0 n1 : nat),
    n1 <= n0
    -> fold_left
         (fun (a : nat) (p : positive * (type * IRR.sact)) =>
           let '(_, a0) := snd p in
           if (fst p <? var)%positive then size_sact a0 + a else a)
         l n1
    <= fold_left
         (fun (a : nat) (p : positive * (type * IRR.sact)) =>
            let '(_, a0) := snd p in
            if (fst p <? n)%positive
            then size_sact (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) a0 + a
            else a)
         l n0.
  Proof.
    intros var n LT.
    induction l; simpl; intros; eauto.
    destr. apply IHl.
    destruct a; simpl in *. subst.
    generalize (Pos.ltb_spec p var).
    generalize (Pos.ltb_spec p n).
    intros A B. inv A; inv B; lia.
  Qed.

  Lemma vvs_size_le1:
    forall vvs var n, (var < n)%positive -> vvs_size vvs var  <= vvs_size vvs n.
  Proof.
    unfold vvs_size. intros.
    rewrite ! PTree.fold_spec.
    assert (O <= O)%nat. lia.
    revert H0. generalize O at 1 3.
    generalize O.
    generalize (PTree.elements vvs).
    eapply vvs_size1_aux; eauto.
  Qed.

  Lemma vvs_size_rew:
    forall l m n,
    fold_left
      (fun (a0 : nat) (p : positive * (type * IRR.sact)) =>
         let '(_, a1) := snd p in
         if (fst p <? n)%positive then size_sact a1 + a0 else a0)
      l m
    = fold_left
        (fun
          (a0 : nat)
          (p :
            positive
            * (type * IRR.sact (ext_fn_t:=ext_fn_t)(reg_t:=reg_t)))
          =>
            let '(_, a1) := snd p in
            if (fst p <? n)%positive then size_sact a1 + a0 else a0)
      l 0 + m.
  Proof.
    induction l; simpl; intros; eauto.
    rewrite IHl. destruct a. simpl. destruct p0. simpl.
    rewrite (IHl (if (p <? n)%positive then _ else _)).
    rewrite <- Nat.add_assoc. f_equal.
    destr; lia.
  Qed.

  Lemma vvs_size_le2:
    forall vvs a var t n,
    (var < n)%positive
    -> vvs ! var = Some (t, a)
    -> vvs_size vvs var + size_sact a <= vvs_size vvs n.
  Proof.
    unfold vvs_size. intros.
    rewrite ! PTree.fold_spec.
    assert (O <= O)%nat. lia.
    revert H1. generalize O at 1 3.
    generalize O.
    apply PTree.elements_correct in H0. revert H0.
    generalize (PTree.elements vvs).
    induction l; simpl; intros; eauto. easy.
    destr.
    destruct H0.
    subst. simpl in *. inv Heqp.
    rewrite (vvs_size_rew _ (if (_ <? _)%positive then _ else _)).
    rewrite (vvs_size_rew _ (if (_ <? _)%positive then _ else _)).
    generalize (Pos.ltb_spec var var). intro A; inv A. lia.
    generalize (Pos.ltb_spec var n). intro A; inv A. 2: lia.
    generalize (vvs_size1_aux _ _ H4 l _ _ H1).
    rewrite (Nat.add_comm _ n0); rewrite Nat.add_assoc.
    rewrite <- ! vvs_size_rew. lia.
    eapply IHl; eauto.
    generalize (Pos.ltb_spec (fst a0) var).
    generalize (Pos.ltb_spec (fst a0) n).
    intros A B. inv A; inv B; lia.
  Qed.

  Lemma interp_sact_eval_sact_aux:
    forall (vvs: var_value_map) (VSV: vvs_smaller_variables vvs) a v,
    interp_sact (sigma := sigma) REnv r vvs a v
    -> forall n, (forall var, var_in_sact a var -> var < n)%positive
    -> exists m,
     eval_sact vvs a (m + size_sact a) = Some v
     /\ (m <= Pos.to_nat n + vvs_size vvs n)%nat.
  Proof.
    induction 2; simpl; intros; eauto.
    - destruct (IHinterp_sact var) as (m1 & I1 & LE1).
      intros; eapply VSV. eauto. auto.
      eexists. split. rewrite Nat.add_1_r. simpl. rewrite H; simpl; eauto.
      assert (var < n)%positive. eapply H1. constructor.
      generalize (vvs_size_le2 vvs _ _ _ n H2 H). lia.
    - exists 0; split; simpl; eauto.  lia.
    - edestruct IHinterp_sact1 as (m1 & I1 & LE1).
      intros; eapply H1. apply var_in_if_cond; eauto.
      edestruct IHinterp_sact2 as (m2 & I2 & LE2).
      intros; eapply H1. destruct b.
      apply var_in_if_true; eauto. apply var_in_if_false; eauto.
      exists ((max m1 m2)). split.
      rewrite Nat.add_succ_r.
      simpl.
      erewrite eval_sact_more_fuel; eauto. 2: lia. simpl.
      destruct b; eapply eval_sact_more_fuel; eauto. lia. lia. lia.
    - edestruct IHinterp_sact as (m1 & I1 & LE1).
      intros; eapply H1. econstructor; eauto.
      exists m1; rewrite Nat.add_succ_r. simpl. rewrite I1.
      split; simpl; eauto.
    - edestruct IHinterp_sact1 as (m1 & I1 & LE1).
      intros; eapply H2. econstructor; eauto.
      edestruct IHinterp_sact2 as (m2 & I2 & LE2).
      intros; eapply H2. eapply var_in_sact_binop_2; eauto.
      exists (max m1 m2); rewrite Nat.add_succ_r. simpl.
      erewrite eval_sact_more_fuel; eauto. 2: lia. simpl.
      erewrite eval_sact_more_fuel; eauto. 2: lia. simpl.
      split; simpl; eauto. lia.
    - edestruct IHinterp_sact as (m1 & I1 & LE1).
      intros; eapply H0. econstructor; eauto.
      exists m1; rewrite Nat.add_succ_r. simpl. rewrite I1.
      split; simpl; eauto.
    - exists O; split; simpl; eauto.  lia.
  Qed.

  Lemma interp_sact_eval_sact:
    forall (vvs: var_value_map) (VSV: vvs_smaller_variables vvs),
    forall a v t,
    wt_sact (Sigma:=Sigma) R vvs a t
    -> interp_sact (sigma:=sigma) REnv r vvs a v
    -> eval_sact
         vvs a
         (Pos.to_nat
           (Pos.succ (max_var vvs))
           + vvs_size vvs ((Pos.succ (max_var vvs))) + size_sact a)
       = Some v.
  Proof.
    intros.
    generalize (vvs_range_max_var vvs). intro VR.
    generalize (wt_sact_valid_vars _ vvs _ VR _ _ H). intro VALID.
    generalize (interp_sact_eval_sact_aux _ VSV a v H0 _ VALID).
    intros (m & EVAL & LE).
    eapply eval_sact_more_fuel. eauto. lia.
  Qed.

  Definition do_eval_sact vvs a :=
    eval_sact
      vvs a
      (Pos.to_nat
        (Pos.succ (max_var vvs))
        + vvs_size vvs ((Pos.succ (max_var vvs)))
        + size_sact a).

  Lemma interp_sact_do_eval_sact:
    forall (vvs: var_value_map) (VSV: vvs_smaller_variables vvs) a v t,
    wt_sact (Sigma:=Sigma) R vvs a t
    -> interp_sact (sigma:=sigma) REnv r vvs a v
    -> do_eval_sact vvs a = Some v.
  Proof. intros. eapply interp_sact_eval_sact; eauto. Qed.

  Lemma eval_sact_interp_sact:
    forall vvs fuel a v, eval_sact vvs a fuel = Some v
    -> interp_sact (sigma:=sigma) REnv r vvs a v.
  Proof.
    induction fuel; simpl; intros; eauto. easy.
    unfold opt_bind in H; repeat destr_in H; inv H; econstructor; eauto.
  Qed.

  Lemma do_eval_sact_interp_sact:
    forall vvs a v, do_eval_sact vvs a = Some v
    -> interp_sact (sigma:=sigma) REnv r vvs a v.
  Proof. intros; eapply eval_sact_interp_sact; eauto. Qed.

  Definition val_beq_bits (v1 v2: val) : bool :=
    match v1, v2 with
    | Bits b1, Bits b2 => list_beq bool Bool.eqb b1 b2
    | _, _ => false
    end.

  Lemma val_beq_bits_implies_eq :
    forall v1 v2, val_beq_bits v1 v2 = true -> v1 = v2.
  Proof.
    intros.
    induction v1; induction v2; inv H.
    assert (v = v0).
    {
      generalize dependent v0.
      induction v; intros.
      - inv H1. destruct v0; eauto. discriminate.
      - destruct v0.
        + simpl in H1. discriminate.
        + simpl in H1. eapply andb_true_iff in H1. destruct H1.
          eapply Bool.eqb_prop in H. eapply IHv in H0. subst. reflexivity.
    }
    subst. reflexivity.
  Qed.

  Fixpoint eval_sact_no_vars (a: sact) : option val :=
    match a with
    | SConst v => Some v
    | SReg idx => Some (getenv REnv r idx)
    | SVar v => None
    | SIf c t f =>
      let/opt v := eval_sact_no_vars c in
      match v with
      | Bits [b] => if b then eval_sact_no_vars t else eval_sact_no_vars f
      | _ => None
      end
    | SUnop ufn a => let/opt v := eval_sact_no_vars a in sigma1 ufn v
    | SBinop ufn a1 a2 =>
      let/opt v1 := eval_sact_no_vars a1 in
      let/opt v2 := eval_sact_no_vars a2 in
      match ufn with
      | PrimUntyped.UEq false =>
        if (val_beq_bits v1 v2) then Some (Bits [true]) else sigma2 ufn v1 v2
      | PrimUntyped.UEq true =>
        if (val_beq_bits v1 v2) then Some (Bits [false]) else sigma2 ufn v1 v2
      | _ => sigma2 ufn v1 v2
      end
    | SExternalCall ufn a =>
      let/opt v := eval_sact_no_vars a in
      Some (sigma ufn v)
    end.

  Lemma list_assoc_filter:
    forall {K V: Type} {eqdec: EqDec K} (l: list (K*V)) f k,
    (forall v, f (k,v) = true)
    -> list_assoc l k = list_assoc (filter f l) k.
  Proof.
    induction l; simpl; intros; eauto.
    repeat destr.
    - subst. simpl. rewrite eq_dec_refl. reflexivity.
    - subst. simpl. destr. eauto.
    - eauto.
  Qed.

  Lemma list_assoc_map:
    forall
      {K V: Type} {eqdec: EqDec K} (f: K*V -> K*V) (g: V -> V)
      (F: forall k1 v1, f (k1,v1) = (k1, g v1)) l k,
    list_assoc (map f l) k = option_map g (list_assoc l k).
  Proof.
    induction l; simpl; intros; eauto.
    destruct a. rewrite F. destr. subst. simpl. reflexivity.
  Qed.

  Lemma interp_sact_replace:
    forall vvs var v', interp_sact (sigma:=sigma) REnv r vvs (SVar var) v'
    -> forall a res, interp_sact (sigma:=sigma) REnv r vvs a res
    ->
      interp_sact
        (sigma:=sigma) REnv r vvs (replace_all_occurrences_in_sact a var v')
        res.
  Proof.
    induction 2; simpl; intros; eauto.
    - destr.
      + subst. inv H. rewrite H0 in H3. inv H3.
        exploit (interp_sact_determ (ext_fn_t:=ext_fn_t) (reg_t:=reg_t)).
        apply H1. apply H4.
        intros ->; econstructor.
      + econstructor; eauto.
    - econstructor.
    - econstructor; eauto.
      destruct b; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor.
  Qed.

  Lemma interp_sact_replace_inv:
    forall vvs (VSV: vvs_smaller_variables vvs) var v',
    interp_sact (sigma := sigma) REnv r vvs (SVar var) v'
    -> forall a n (BELOW: forall v, var_in_sact a v -> (v < n)%positive) res,
    interp_sact
      (sigma := sigma) REnv r vvs (replace_all_occurrences_in_sact a var v') res
    -> interp_sact (sigma:=sigma) REnv r vvs a res.
  Proof.
    intros vvs VSV var v' INTvar a n.
    change n with (projT1 (existT (fun _ => sact) n a)).
    change a with (projT2 (existT (fun _ => sact) n a)) at 1 3 4.
    generalize (existT (fun _ => sact) n a).
    clear n a. intro s. pattern s.
    eapply well_founded_induction.
    apply wf_order_sact. clear s.
    intros (n1 & a) IH. simpl.
    intros BELOW res INTres.
    destruct a; simpl in *.
    - destr_in INTres.
      + subst. inv INTres. eauto.
      + eauto.
    - inv INTres; econstructor.
    - inv INTres.
      econstructor.
      eapply (IH (existT _ n1 a1)); eauto. constructor 2. simpl; lia.
      simpl; intros. eapply BELOW. eapply var_in_if_cond; eauto.
      eapply (IH (existT _ n1 (if b then a2 else a3))); eauto. constructor 2.
      destruct b; simpl; lia.
      simpl; intros. eapply BELOW. destruct b.
      eapply var_in_if_true; eauto. eapply var_in_if_false; eauto. simpl.
      destruct b; eauto.
    - inv INTres; econstructor; eauto.
      eapply (IH (existT _ n1 a)); eauto. constructor 2. simpl; lia.
      simpl; intros. eapply BELOW. eapply var_in_sact_unop; eauto.
    - inv INTres; econstructor; eauto.
      eapply (IH (existT _ n1 a1)); eauto. constructor 2. simpl; lia.
      simpl; intros. eapply BELOW. eapply var_in_sact_binop_1; eauto.
      eapply (IH (existT _ n1 a2)); eauto. constructor 2. simpl; lia.
      simpl; intros. eapply BELOW. eapply var_in_sact_binop_2; eauto.
    - inv INTres; econstructor; eauto.
      eapply (IH (existT _ n1 a)); eauto. constructor 2. simpl; lia.
      simpl; intros. eapply BELOW. eapply var_in_sact_external; eauto.
    - auto.
  Qed.

  Lemma interp_sact_replace_iff:
    forall vvs (VSV: vvs_smaller_variables vvs) var v' ,
    interp_sact (sigma:=sigma) REnv r vvs (SVar var) v'
    -> forall a t (WT: wt_sact (Sigma:=Sigma) R vvs a t) res,
    interp_sact
      (sigma:=sigma) REnv r vvs (replace_all_occurrences_in_sact a var v') res
    <-> interp_sact (sigma:=sigma) REnv r vvs a res.
  Proof.
    split; intros.
    - eapply interp_sact_replace_inv; eauto.
      eapply wt_sact_valid_vars. 2: eauto.
      apply vvs_range_max_var.
    - eapply interp_sact_replace; eauto.
  Qed.

  Lemma interp_sact_replace_one_variable:
    forall vvs (VSV: vvs_smaller_variables vvs) var v' ,
    interp_sact (sigma:=sigma) REnv r vvs (SVar var) v'
    -> forall a n, (forall v, var_in_sact a v -> (v < n)%positive)
    -> forall res, interp_sact (sigma:=sigma) REnv r vvs a res
    -> interp_sact
         (sigma:=sigma) REnv r
         (replace_all_occurrences_in_vars (PTree.remove var vvs) var v')
         (replace_all_occurrences_in_sact a var v') res.
  Proof.
    intros vvs VSV var v' INTvar.
    intros a n.
    change n with (projT1 (existT (fun _ => sact) n a)).
    change a with (projT2 (existT (fun _ => sact) n a)) at 1 3 4.
    generalize (existT (fun _ => sact) n a).
    clear n a. intro s. pattern s.
    eapply well_founded_induction.
    apply wf_order_sact. clear s.
    intros (n1 & a) IH. simpl.
    intros BELOW res INTres.
    inv INTres; simpl.
    - destr.
      + subst. inv INTvar. rewrite H2 in H. inv H.
        exploit (interp_sact_determ (reg_t:=reg_t) (ext_fn_t:=ext_fn_t)).
        apply H3. apply H0. intros; subst. constructor.
      + econstructor. unfold replace_all_occurrences_in_vars.
        rewrite PTree.gmap. rewrite PTree.gro; auto. rewrite H. simpl; eauto.
        eapply (IH (existT _ var0 a0)).
        constructor. eapply BELOW. constructor.
        simpl. intros; eapply VSV; eauto.
        simpl. auto.
    - constructor.
    - econstructor.
      eapply (IH (existT _ n1 c)). constructor 2. simpl; lia.
      simpl. intros; eapply BELOW. apply var_in_if_cond; eauto. simpl. eauto.
      trim (IH (existT _ n1 (if b then t else f))). constructor 2.
      destruct b; simpl; lia.
      simpl in IH.
      trim IH. intros; eapply BELOW.
      destruct b. eapply var_in_if_true; eauto. eapply var_in_if_false; eauto.
      specialize (IH _ H0).
      destr; eauto.
    - econstructor.
      eapply (IH (existT _ n1 a0)). constructor 2. simpl; lia.
      simpl. intros; eapply BELOW. apply var_in_sact_unop; eauto. simpl. eauto.
      auto.
    - econstructor.
      eapply (IH (existT _ n1 a1)). constructor 2. simpl; lia.
      simpl. intros; eapply BELOW. apply var_in_sact_binop_1; eauto. simpl.
      eauto.
      eapply (IH (existT _ n1 a2)). constructor 2. simpl; lia.
      simpl. intros; eapply BELOW. apply var_in_sact_binop_2; eauto. simpl.
      eauto. auto.
    - econstructor.
      eapply (IH (existT _ n1 a0)). constructor 2. simpl; lia.
      simpl. intros; eapply BELOW. apply var_in_sact_external; eauto. simpl.
      eauto.
    - constructor.
  Qed.

  Lemma interp_sact_replace_one:
    forall vvs (VSV: vvs_smaller_variables vvs) var v',
    interp_sact (sigma:=sigma) REnv r vvs (SVar var) v'
    -> forall a n, (forall v, var_in_sact a v -> (v < n)%positive)
    -> forall res, interp_sact (sigma:=sigma) REnv r vvs a res
    -> interp_sact
         (sigma:=sigma) REnv r (replace_all_occurrences_in_vars vvs var v')
         (replace_all_occurrences_in_sact a var v') res.
  Proof.
    intros vvs VSV var v' INTvar.
    intros a n.
    change n with (projT1 (existT (fun _ => sact) n a)).
    change a with (projT2 (existT (fun _ => sact) n a)) at 1 3 4.
    generalize (existT (fun _ => sact) n a).
    clear n a. intro s. pattern s.
    eapply well_founded_induction.
    apply wf_order_sact. clear s.
    intros (n1 & a) IH. simpl.
    intros BELOW res INTres.
    inv INTres; simpl.
    - destr.
      + subst. inv INTvar. rewrite H2 in H. inv H.
        exploit (interp_sact_determ (reg_t:=reg_t) (ext_fn_t:=ext_fn_t)).
        apply H3. apply H0. intros; subst. constructor.
      + econstructor. unfold replace_all_occurrences_in_vars.
        rewrite PTree.gmap. setoid_rewrite H. simpl; eauto.
        eapply (IH (existT _ var0 a0)).
        constructor. eapply BELOW. constructor.
        simpl. intros; eapply VSV; eauto.
        simpl. auto.
    - constructor.
    - econstructor.
      eapply (IH (existT _ n1 c)). constructor 2. simpl; lia.
      simpl. intros; eapply BELOW. apply var_in_if_cond; eauto. simpl. eauto.
      trim (IH (existT _ n1 (if b then t else f))). constructor 2.
      destruct b; simpl; lia.
      simpl in IH.
      trim IH. intros; eapply BELOW.
      destruct b. eapply var_in_if_true; eauto. eapply var_in_if_false; eauto.
      specialize (IH _ H0).
      destr; eauto.
    - econstructor.
      eapply (IH (existT _ n1 a0)). constructor 2. simpl; lia.
      simpl. intros; eapply BELOW. apply var_in_sact_unop; eauto. simpl. eauto.
      auto.
    - econstructor.
      eapply (IH (existT _ n1 a1)). constructor 2. simpl; lia.
      simpl. intros; eapply BELOW. apply var_in_sact_binop_1; eauto. simpl.
      eauto.
      eapply (IH (existT _ n1 a2)). constructor 2. simpl; lia.
      simpl. intros; eapply BELOW. apply var_in_sact_binop_2; eauto. simpl.
      eauto. auto.
    - econstructor.
      eapply (IH (existT _ n1 a0)). constructor 2. simpl; lia.
      simpl. intros; eapply BELOW. apply var_in_sact_external; eauto. simpl.
      eauto.
    - constructor.
  Qed.

  Lemma interp_eval:
    forall
      vvs vvs' a b (VSV1: vvs_smaller_variables vvs)
      (VSV2: vvs_smaller_variables vvs') ta tb
      (WTa: wt_sact (Sigma:=Sigma) R vvs a ta)
      (WTb: wt_sact (Sigma:=Sigma) R vvs' b tb),
    (exists m, forall n, n >= m
    -> eval_sact vvs a n = eval_sact vvs' b n)
    -> (forall res,
         interp_sact (sigma:=sigma) REnv r vvs a res
         -> interp_sact (sigma:=sigma) REnv r vvs' b res).
  Proof.
    intros.
    destruct H.
    eapply interp_sact_eval_sact in H0; eauto.
    eapply eval_sact_more_fuel with (n2:=max x _) in H0.
    2: apply Nat.le_max_r.
    rewrite H in H0. 2: lia.
    eapply eval_sact_interp_sact; eauto.
  Qed.

  Lemma interp_eval_iff:
    forall
      vvs vvs' a b (VSV1: vvs_smaller_variables vvs)
      (VSV2: vvs_smaller_variables vvs') ta tb
      (WTa: wt_sact (Sigma:=Sigma) R vvs a ta)
      (WTb: wt_sact (Sigma:=Sigma) R vvs' b tb),
    (exists m, forall n, n >= m
    -> eval_sact vvs a n = eval_sact vvs' b n)
    -> (forall res,
       interp_sact (sigma:=sigma) REnv r vvs a res
       <-> interp_sact (sigma:=sigma) REnv r vvs' b res).
  Proof.
    intros vvs vvs' a b VSV1 VSV2 ta tb WTa WTb (m & EQ) res.
    split; intros.
    - eapply interp_eval. 6: eauto. all: eauto.
    - eapply interp_eval. 6: eauto. all: eauto.
      exists m; intros; eauto. rewrite EQ; auto.
  Qed.

  Lemma val_beq_true:
    forall b, val_beq b b = true.
  Proof.
    intros.
    destruct val_beq eqn:?; try congruence. apply val_beq_false in Heqb0. congruence.
  Qed.

  Lemma eval_sact_no_vars_interp:
    forall vvs s v (EVAL: eval_sact_no_vars s = Some v),
    interp_sact (sigma:=sigma) REnv r vvs s v.
  Proof.
    induction s; simpl; intros; eauto; unfold opt_bind in EVAL;
      repeat destr_in EVAL; inv EVAL; try (econstructor; eauto).
    - eapply val_beq_bits_implies_eq in Heqb0. destruct Heqb0.
      simpl. rewrite val_beq_true. auto.
    - eapply val_beq_bits_implies_eq in Heqb0. destruct Heqb0.
      simpl. rewrite val_beq_true. auto.
  Qed.

  Lemma var_in_sact_replace:
    forall a n v x, var_in_sact (replace_all_occurrences_in_sact a n v) x
    -> var_in_sact a x.
  Proof.
    induction a; simpl; intros; eauto.
    - destr_in H; inv H. constructor.
    - inv H. eapply var_in_if_cond; eauto.
      eapply var_in_if_true; eauto.
      eapply var_in_if_false; eauto.
    - inv H. eapply var_in_sact_unop; eauto.
    - inv H. eapply var_in_sact_binop_1; eauto.
      eapply var_in_sact_binop_2; eauto.
    - inv H. eapply var_in_sact_external; eauto.
  Qed.

  Lemma vvs_smaller_variables_replace:
    forall vvs n v,
    vvs_smaller_variables vvs
    -> vvs_smaller_variables (replace_all_occurrences_in_vars vvs n v).
  Proof.
    unfold vvs_smaller_variables; intros.
    setoid_rewrite PTree.gmap in H0.
    unfold option_map in H0; repeat destr_in H0; inv H0.
    eapply var_in_sact_replace in H1; eauto.
  Qed.

  Lemma wt_sact_replace:
    forall vvs a t n v t1,
    wt_sact (Sigma:=Sigma) R vvs a t
    -> wt_sact (Sigma:=Sigma) R vvs (SVar n) t1
    -> wt_val t1 v
    -> wt_sact (Sigma:=Sigma) R vvs (replace_all_occurrences_in_sact a n v) t.
  Proof.
    induction 1; simpl; intros; eauto.
    - destr.
      + subst. inv H0. rewrite H in H3; inv H3. econstructor; eauto.
      + econstructor. eauto.
    - inv H0. econstructor. eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - constructor.
  Qed.

  Lemma wt_sact_replace_vars:
    forall vvs a t n v t1,
    wt_sact (Sigma:=Sigma) R vvs a t
    -> wt_sact (Sigma:=Sigma) R vvs (SVar n) t1
    -> wt_val t1 v
    -> wt_sact
         (Sigma:=Sigma) R (replace_all_occurrences_in_vars vvs n v)
         (replace_all_occurrences_in_sact a n v) t.
  Proof.
    induction 1; simpl; intros; eauto.
    - destr.
      + subst. inv H0. rewrite H in H3; inv H3. econstructor; eauto.
      + econstructor.
        setoid_rewrite PTree.gmap. setoid_rewrite H. simpl; eauto.
    - inv H0. econstructor. eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - constructor.
  Qed.

  Lemma wt_sact_replace_vars':
    forall vvs a t n v t1,
    wt_sact (Sigma:=Sigma) R vvs a t
    -> wt_sact (Sigma:=Sigma) R vvs (SVar n) t1
    -> wt_val t1 v
    -> wt_sact (Sigma:=Sigma) R (replace_all_occurrences_in_vars vvs n v) a t.
  Proof.
    induction 1; simpl; intros; eauto.
    - econstructor.
      setoid_rewrite PTree.gmap.
      setoid_rewrite H. simpl; eauto.
    - inv H0. econstructor. eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - constructor.
  Qed.

  Lemma wt_vvs_replace:
    forall vvs n v t1, wt_vvs (Sigma:=Sigma) R vvs
    -> wt_sact (Sigma:=Sigma) R vvs (SVar n) t1
    -> wt_val t1 v
    -> wt_vvs (Sigma:=Sigma) R (replace_all_occurrences_in_vars vvs n v).
  Proof.
    unfold wt_vvs; intros.
    setoid_rewrite PTree.gmap in H2.
    unfold option_map in H2; repeat destr_in H2; inv H2.
    eapply wt_sact_replace_vars; eauto.
  Qed.

  Lemma eval_sact_no_vars_wt:
    forall vvs s t (WT: wt_sact (Sigma:=Sigma) R vvs s t)
      v (EVAL: eval_sact_no_vars s = Some v),
    wt_val t v.
  Proof.
    induction 1; simpl; intros; unfold opt_bind in EVAL; try (inversion EVAL).
    - inv H1; eauto.
    - repeat destr_in EVAL; try (inversion EVAL).
      + eapply IHWT2 in EVAL; eauto.
      + eapply IHWT3 in EVAL; eauto.
    - repeat destr_in EVAL; try (inversion EVAL).
      eapply Wt.wt_unop_sigma1; eauto.
    - repeat destr_in EVAL; try (inversion EVAL);
        try (inv H; econstructor; eauto); eapply Wt.wt_binop_sigma1; eauto.
    - repeat destr_in EVAL; inv EVAL; eauto.
    - repeat destr_in EVAL; inv EVAL; eauto.
  Qed.

  Lemma eval_sact_no_vars_succeeds:
    forall
      a (NoVars: forall v, ~ var_in_sact a v) vvs t
      (WTa: wt_sact (Sigma:=Sigma) R vvs a t),
    exists r, eval_sact_no_vars a = Some r.
  Proof.
    induction a; simpl; intros; eauto.
    - elim (NoVars var). constructor.
    - inv WTa.
      edestruct IHa1 as (r1 & EQ1); eauto.
      intros v VIS; eapply NoVars; eauto. apply var_in_if_cond; eauto.
      rewrite EQ1. simpl.
      exploit eval_sact_no_vars_wt. 2: eauto. eauto. intro WTc.
      apply wt_val_bool in WTc. destruct WTc; subst.
      destr. eapply IHa2; eauto.
      intros v VIS; eapply NoVars; eauto. apply var_in_if_true; eauto.
      eapply IHa3; eauto.
      intros v VIS; eapply NoVars; eauto. apply var_in_if_false; eauto.
    - inv WTa.
      edestruct IHa as (r1 & EQ1); eauto.
      intros v VIS; eapply NoVars; eauto. apply var_in_sact_unop; eauto.
      rewrite EQ1. simpl.
      eapply wt_unop_interp; eauto.
      eapply eval_sact_no_vars_wt; eauto.
    - inv WTa.
      edestruct IHa1 as (r1 & EQ1); eauto.
      { intros v VIS; eapply NoVars; eauto. apply var_in_sact_binop_1; eauto. }
      edestruct IHa2 as (r2 & EQ2); eauto.
      { intros v VIS; eapply NoVars; eauto. apply var_in_sact_binop_2; eauto. }
      rewrite EQ1, EQ2. simpl.
      edestruct wt_binop_interp. apply H5.
      eapply eval_sact_no_vars_wt. eauto. eauto.
      eapply eval_sact_no_vars_wt. eauto. eauto.
      exists x.
      destr.
      transitivity (
        if val_beq_bits r1 r2
        then Some (Bits [negb negate])
        else sigma2 (PrimUntyped.UEq negate) r1 r2).
      repeat destr; reflexivity.
      destr.
      unfold val_beq_bits in Heqb.
      repeat destr_in Heqb; inv Heqb.
      apply internal_list_dec_bl in H1. subst.
      destruct negate; simpl in H. inv H. simpl. rewrite list_eqb_refl. auto.
      intros; apply eqb_reflx.
      inv H. simpl.
      rewrite list_eqb_refl. auto.
      intros; apply eqb_reflx.
      intros; apply Bool.eqb_eq. rewrite H0. constructor.
    - inv WTa.
      edestruct IHa as (r1 & EQ1); eauto.
      intros v VIS; eapply NoVars; eauto. apply var_in_sact_external; eauto.
      rewrite EQ1. simpl. eauto.
  Qed.

  Lemma wt_sact_var_exists:
    forall a vvs t (WTa: wt_sact (Sigma:=Sigma) R vvs a t),
    forall v, var_in_sact a v -> In v (map fst (PTree.elements vvs)).
  Proof.
    induction 1; simpl; intros; eauto.
    - inv H0. apply PTree.elements_correct in H. apply (in_map fst) in H. auto.
    - inv H0.
    - inv H; eauto.
    - inv H0; eauto.
    - inv H0; eauto.
    - inv H; eauto.
    - inv H.
  Qed.

  Fixpoint simplify_sif (ua: sact) : sact :=
    match ua with
    | SIf cond tb fb =>
      match eval_sact_no_vars cond with
      | Some (Bits [true]) => tb
      | Some (Bits [false]) => fb
      | _ => ua
      end
    | SBinop ufn a1 a2 => SBinop ufn (simplify_sif a1) (simplify_sif a2)
    | SUnop ufn a => SUnop ufn (simplify_sif a)
    | SExternalCall ufn a => SExternalCall ufn (simplify_sif a)
    | SVar _ | SReg _ | SConst _ => ua
    end.

  Definition simplify_var (sf: IRR) var :=
    match (vars sf) ! var with
    | Some (t, a) =>
      match eval_sact_no_vars a with
      | Some v => (replace_all_occurrences sf var v, [(var,v)])
      | None => (sf, [])
      end
    | None => (sf, [])
    end.

  Lemma var_not_in_sact_replace:
    forall s0 v0 v,
      ~ var_in_sact (replace_all_occurrences_in_sact s0 v0 v) v0.
  Proof.
    induction s0; simpl; intros; eauto.
    - destr; inversion 1. congruence.
    - inversion 1.
    - inversion 1; subst; intuition eauto.
    - inversion 1; subst; intuition eauto.
    - inversion 1; subst; intuition eauto.
    - inversion 1; subst; intuition eauto.
    - inversion 1.
  Qed.

  Lemma simplify_var_correct:
    forall
      sf var sf' l (SIMP: simplify_var sf var = (sf', l))
      (VSV: vvs_smaller_variables (vars sf))
      (WT: wt_vvs (Sigma:=Sigma) R (vars sf)),
    Forall
      (fun '(var,v) =>
        interp_sact (sigma:=sigma) REnv r (vars sf') (SVar var) v)
      l
    /\ vvs_smaller_variables (vars sf')
    /\ wt_vvs (Sigma:=Sigma) R (vars sf')
    /\ NoDup (map fst l)
    /\ (forall a res t,
         wt_sact (Sigma:=Sigma) R (vars sf) a t
         -> interp_sact (sigma:=sigma) REnv r (vars sf) a res
         -> interp_sact (sigma:=sigma) REnv r (vars sf') a res)
    /\ (forall x t y res,
         (vars sf) ! x = Some (t,y)
         -> interp_sact (sigma:=sigma) REnv r (vars sf) y res
         -> (exists y' ,
              (vars sf') ! x = Some (t,y')
              /\ interp_sact (sigma:=sigma) REnv r (vars sf') y' res))
    /\ (forall x t y v,
         (vars sf') ! x = Some (t,y)
         -> var_in_sact y v
         -> ~ In v (map fst l))
    /\ (forall x t y,
         (vars sf') ! x = Some (t, y)
         -> exists y',
         (vars sf) ! x = Some (t, y')
         /\ forall v, var_in_sact y v -> var_in_sact y' v).
  Proof.
    unfold simplify_var. intros. repeat destr_in SIMP; inv SIMP; eauto.
    assert
      (VSV': vvs_smaller_variables (vars (replace_all_occurrences sf var v))).
    eapply vvs_smaller_variables_replace; now eauto.
    assert (
      WTVVS': wt_vvs (Sigma:=Sigma) R (vars (replace_all_occurrences sf var v))
    ). {
      eapply wt_vvs_replace; eauto.
      econstructor. eauto.
      eapply eval_sact_no_vars_wt; eauto.
    }
    repeat refine (conj _ _); eauto.
    - repeat constructor.
      simpl.
      erewrite <- interp_sact_replace_iff; eauto.
      eapply interp_sact_replace_one; eauto.
      + econstructor. eauto. eapply eval_sact_no_vars_interp; eauto.
      + intros. eapply wt_sact_valid_vars. 3: eauto. 2: econstructor; eauto.
        apply vvs_range_max_var.
      + econstructor. eauto.
        eapply eval_sact_no_vars_interp; eauto.
      + econstructor.
        setoid_rewrite PTree.gmap.
        setoid_rewrite Heqo. simpl; eauto.
        intros; repeat destr.
        eapply interp_sact_replace_one. eauto.
        econstructor. eauto.
        eapply eval_sact_no_vars_interp; eauto.
        eapply wt_sact_valid_vars. 2: eapply (WT var). apply vvs_range_max_var.
        eauto.
        eapply eval_sact_no_vars_interp; eauto.
      + econstructor.
        setoid_rewrite PTree.gmap.
        setoid_rewrite Heqo. simpl; eauto.
        Unshelve. exact R. exact Sigma.
    - simpl. constructor. easy. constructor.
    - simpl. intros.
      erewrite <- interp_sact_replace_iff; eauto.
      eapply interp_sact_replace_one; eauto.
      + econstructor. eauto. eapply eval_sact_no_vars_interp; eauto.
      + intros. eapply wt_sact_valid_vars. 3: eauto. 2: eauto.
        apply vvs_range_max_var.
      + econstructor.
        setoid_rewrite PTree.gmap.
        setoid_rewrite Heqo. simpl; eauto.
        intros; repeat destr.
        eapply interp_sact_replace_one. eauto.
        econstructor. eauto.
        eapply eval_sact_no_vars_interp; eauto.
        eapply wt_sact_valid_vars. 2: eapply (WT var). apply vvs_range_max_var.
        eauto.
        eapply eval_sact_no_vars_interp; eauto.
      + eapply wt_sact_replace_vars'. eauto. econstructor; eauto.
        eapply eval_sact_no_vars_wt; eauto.
    - simpl. intros.
      setoid_rewrite PTree.gmap.
      setoid_rewrite H. simpl; eauto.
      eexists; split; eauto.
      eapply interp_sact_replace_one; eauto.
      + econstructor. eauto. eapply eval_sact_no_vars_interp; eauto.
      + intros. eapply wt_sact_valid_vars. 3: eauto. 2: eauto.
        apply vvs_range_max_var.
    - simpl.
      setoid_rewrite PTree.gmap.
      unfold option_map; intros x t0 y v0 OM; repeat destr_in OM; inv OM.
      intros VIS [EQ|[]]. subst.
      eapply var_not_in_sact_replace; eauto.
    - simpl. intros x t0 y.
      setoid_rewrite PTree.gmap.
      unfold option_map; intros OM; repeat destr_in OM; inv OM.
      setoid_rewrite Heqo1. eexists; split; eauto.
      eapply var_in_sact_replace; eauto.
    - repeat refine (conj _ _); eauto. constructor.
    - repeat refine (conj _ _); eauto. constructor.
  Qed.

  Lemma simplify_vars_preserves:
    forall
      (lvars: list positive) sf l sf' l'
      (FL: fold_left (fun '(sf, l) var =>
             let '(sf, l1) := simplify_var sf var in
             (sf,l1++l)) lvars (sf, l) = (sf', l'))
      (WTV: wt_vvs (Sigma:=Sigma) R (vars sf))
      (VSV: vvs_smaller_variables (vars sf)) (NDlvars: NoDup lvars)
      (ND: NoDup (map fst l)) (DISJ: forall x, In x lvars -> ~ In x (map fst l))
      (NIV: forall x t y v,
        (vars sf) ! x = Some (t,y)
        -> var_in_sact y v
        -> ~ In v (map fst l)),
    vvs_smaller_variables (vars sf')
    /\ wt_vvs (Sigma:=Sigma) R (vars sf')
    /\ (incl l l')
    /\ NoDup (map fst l')
    /\ (forall x t y v, (vars sf') ! x = Some (t,y)
    -> var_in_sact y v -> ~ In v (map fst l')).
  Proof.
    induction lvars; simpl; intros; eauto.
    - inv FL. repeat refine (conj _ _); eauto. easy.
    - repeat destr_in FL.
      edestruct simplify_var_correct as
        (INT & VSV2 & WT2 & ND2 & INTERP2 & INTERP3 & NAV1 & VIS1); eauto.
      edestruct (IHlvars _ _ _ _ FL) as
        (VSV3 & WTV3 & INCL & ND3 & NIV2); auto.
      inv NDlvars; eauto. {
        rewrite map_app.
        unfold simplify_var in Heqp.
        repeat destr_in Heqp; inv Heqp; simpl; eauto.
        constructor; eauto.
      } {
        intros x IN IN2.
        rewrite map_app, in_app_iff in IN2.
        unfold simplify_var in Heqp.
        repeat destr_in Heqp; inv Heqp; simpl in IN2; intuition eauto.
        subst. inv NDlvars; eauto.
      }
      intros.
      specialize (NAV1 _ _ _ _ H H0).
      rewrite map_app. rewrite in_app_iff. intros [IN|IN]; eauto.
      edestruct VIS1 as (y' & GET2 & IMPL). apply H.
      eapply NIV in IN; eauto.
      split; auto. split; auto. split; auto.
      apply incl_app_inv in INCL. apply INCL.
  Qed.

  Lemma simplify_vars_correct:
    forall (lvars: list positive) sf l sf' l'
           (FL: fold_left
                  (fun '(sf, l) var =>
                     let '(sf, l1) := simplify_var sf var in
                     (sf,l1++l)) lvars (sf, l) = (sf', l'))
           (SORTED: Sorted Pos.lt lvars)
           (VARS_EXIST: Forall (fun v => exists a t, (vars sf) ! v = Some (t,a)) lvars)
           (WTV: wt_vvs (Sigma:=Sigma) R (vars sf))
           (ACC: Forall (fun '(var, v) => interp_sact (sigma:=sigma) REnv r (vars sf) (SVar var) v) l)
           (VSV: vvs_smaller_variables (vars sf))
           (NOvarsl: forall x t y v,
               (vars sf) ! x = Some (t,y)
               -> var_in_sact y v -> ~ In v (map fst l) /\ In v lvars)
    ,
      (forall x t y res,
          (vars sf) ! x = Some (t,y)
          -> interp_sact (sigma:=sigma) REnv r (vars sf) y res
          -> (exists y' ,
              (vars sf') ! x = Some (t,y') /\
                interp_sact (sigma:=sigma) REnv r (vars sf') y' res)
      ) /\
        vvs_smaller_variables (vars sf') /\
        wt_vvs (Sigma:=Sigma) R (vars sf') /\
        Forall (fun '(var, v) => interp_sact (sigma:=sigma) REnv r (vars sf') (SVar var) v) l' /\
        (forall x t y v, (vars sf') ! x = Some (t,y)
        -> var_in_sact y v -> ~ In v (map fst l'))
      /\ (incl l l')
  /\ (forall x, In x lvars -> exists v, In (x, v) l').
  Proof.
    induction lvars; simpl; intros; eauto.
    - inv FL. repeat refine (conj _ _); eauto.
      intros x t y v GET VIS; eapply NOvarsl in GET; eauto. destruct GET; easy.
      easy. easy.
    - repeat destr_in FL.
      edestruct simplify_var_correct as (INT & VSV2 & WT2 & ND2 & INTERP2 & INTERP3 & NAV1 & VIS1); eauto.
      edestruct (IHlvars _ _ _ _ FL) as (LGROWS & VSV3 & WT3 & INTERPl & NAV2 & INCL & INl'); auto.
      * inv SORTED; auto.
      * inv VARS_EXIST. rewrite Forall_forall in H2 |- *. intros x IN.
        specialize (H2 _ IN).
        destruct H2 as (aa & t & GET).
        move Heqp at bottom. unfold simplify_var in Heqp.
        repeat destr_in Heqp; inv Heqp; eauto.
        simpl. unfold replace_all_occurrences_in_vars.
        setoid_rewrite PTree.gmap.
        setoid_rewrite GET. simpl. do 2 eexists; eauto.
      * eapply Forall_app. split. eauto.
        rewrite Forall_forall in ACC |- *. intros (var & v) IN.
        specialize (ACC _ IN). simpl in ACC.
        inv ACC.
        eapply INTERP2. econstructor; eauto. econstructor; eauto.
      * intros x t y v GET VIS.
        split.
        -- intro IN. rewrite map_app in IN. rewrite in_app_iff in IN.
           destruct IN; eauto. eapply NAV1; eauto.
           edestruct VIS1 as (y' & GET2 & IMPL). eauto.
           apply IMPL in VIS.
           eapply NOvarsl; eauto.
        -- edestruct (VIS1 _ _ _ GET) as (y'& GET' & VISS).
           destruct (NOvarsl _ _ _ _ GET' (VISS _ VIS)) as (? & [EQ|IN]); eauto.
           exfalso. subst.
           move Heqp at bottom. unfold simplify_var in Heqp. inv VARS_EXIST.
           destruct H2 as (? & ? & GETv). rewrite GETv in Heqp.
           assert (forall x, ~ var_in_sact x0 x).
           {
             intros xx VVIS.
             generalize (VSV v _ _ GETv _ VVIS). intro LT. red in LT.
             destruct (NOvarsl _ _ _ xx GETv VVIS) as (_ & [EQ|IN]).
             lia.
             move SORTED at bottom.
             apply Sorted_StronglySorted in SORTED.
             2:{
               red. intros; lia.
             }
             inv SORTED.
             rewrite Forall_forall in H4; apply H4 in IN; lia.
           }
           edestruct (eval_sact_no_vars_succeeds _ H0) as (rr & ESNV). eapply WTV. eauto.
           rewrite ESNV in Heqp. inv Heqp.
           revert GET. simpl. unfold replace_all_occurrences_in_vars.
           setoid_rewrite PTree.gmap.
           setoid_rewrite GET'. simpl. intro A; inv A.
           apply var_not_in_sact_replace in VIS. auto.

      * repeat refine (conj _ _); eauto.
        intros x t y res GET INTy.
        edestruct (INTERP3) as (y' & GET2 & INT2); eauto.
        apply incl_app_inv in INCL. apply INCL.
        intros x [EQ|IN]; eauto.
        subst.
        move Heqp at bottom. unfold simplify_var in Heqp.
        inv VARS_EXIST.
        destruct H1 as (? & ? & GETv). rewrite GETv in Heqp.
        assert (forall x, ~ var_in_sact x0 x).
        {
          intros xx VVIS.
          generalize (VSV _ _ _ GETv _ VVIS). intro LT. red in LT.
          destruct (NOvarsl _ _ _ xx GETv VVIS) as (_ & [EQ|IN]).
          lia.
          move SORTED at bottom.
          apply Sorted_StronglySorted in SORTED.
          2:{ red. intros; lia. }
          inv SORTED.
          rewrite Forall_forall in H3; apply H3 in IN; lia.
        }
        edestruct (eval_sact_no_vars_succeeds _ H) as (rr & ESNV). eapply WTV. eauto.
        rewrite ESNV in Heqp. inv Heqp.
        exists rr. eapply INCL. simpl. left. auto.
  Qed.

  Lemma list_assoc_filter2:
    forall {K V: Type} {eqdec: EqDec K}
           f g (FG: forall k v, f (k, v) = g k)
           (l: list (K*V)) k,
      list_assoc (filter f l) k =
        if negb (g k) then None else list_assoc l k.
  Proof.
    induction l; simpl; intros; eauto.
    repeat destr.
    destruct a.
    destr. simpl. destr. subst. erewrite <- FG. rewrite Heqb. reflexivity. auto.
    rewrite IHl. destr.
    destr. subst.
    erewrite FG in Heqb. rewrite Heqb in Heqb0. simpl in Heqb0. congruence.
  Qed.

  Lemma wt_sact_remove_one:
    forall vvs v
           (NV: forall x t y, vvs ! x = Some (t,y) -> ~ var_in_sact y v)
           a t
           (WTa: wt_sact (Sigma:=Sigma) R vvs a t)
           (NVa: ~ var_in_sact a v),
      wt_sact (Sigma:=Sigma) R (PTree.remove v vvs) a t.
  Proof.
    induction 2; simpl; intros; eauto.
    - econstructor; eauto.
      rewrite PTree.gro; eauto. intro; subst; apply NVa; constructor.
    - econstructor; eauto.
    - econstructor; eauto.
      apply IHWTa1. intro VIS; apply NVa; apply var_in_if_cond; auto.
      apply IHWTa2. intro VIS; apply NVa; apply var_in_if_true; auto.
      apply IHWTa3. intro VIS; apply NVa; apply var_in_if_false; auto.
    - econstructor; eauto.
      apply IHWTa. intro VIS; apply NVa; apply var_in_sact_unop; auto.
    - econstructor; eauto.
      apply IHWTa1. intro VIS; apply NVa; apply var_in_sact_binop_1; auto.
      apply IHWTa2. intro VIS; apply NVa; apply var_in_sact_binop_2; auto.
    - econstructor; eauto.
      apply IHWTa. intro VIS; apply NVa; apply var_in_sact_external; auto.
    - constructor.
  Qed.

  Definition inlining_pass (sf: IRR) : list (positive * val) :=
    (* Try to determine the value of variables *)
    let ks := PosSort.sort (map fst (PTree.elements (vars sf))) in
    let '(sf,l) :=
      fold_left
        (fun '(sf,l) var =>
          let '(sf,l1) := simplify_var sf var in
          (sf, l1++l))
        ks (sf,[])
    in l.

  Lemma Sorted_strict:
    forall le1 le2 (STRICT: forall x y, le2 x y <-> (le1 x y /\ x <> y))
           (l: list positive),
      Sorted le1 l
      -> NoDup l
      -> Sorted le2 l.
  Proof.
    induction 2; simpl; intros; eauto.
    inv H1. econstructor. eauto.
    inv H0. econstructor. econstructor. rewrite STRICT. split; auto. intro; subst. apply H4; simpl; auto.
  Qed.

  Lemma sorted_lt: forall l, NoDup l -> Sorted Pos.lt (PosSort.sort l).
  Proof.
    intros.
    generalize (PosSort.Sorted_sort l). intros.
    eapply Sorted_strict. 2: apply H0.
    intros. simpl. fold (Pos.leb x y).  unfold is_true. rewrite Pos.leb_le. lia.
    eapply Permutation.Permutation_NoDup. 2: apply H.
    apply PosSort.Permuted_sort.
  Qed.

  Lemma in_list_assoc:
    forall {K V: Type} {eqdec: EqDec K} (l: list (K*V))
           (ND: NoDup (map fst l)) k v,
      In (k,v) l -> list_assoc l k = Some v.
  Proof.
    induction l; simpl; intros; eauto. easy.
    repeat destr; eauto.
    - subst. destruct H. inv H. auto. simpl in ND. inv ND. elim H2.
      change k0 with (fst (k0, v)).
      eapply in_map. eauto.
    - inv ND; destruct H; eauto. inv H. congruence.
  Qed.

  Lemma inlining_pass_correct:
    forall
      sf l (IP: inlining_pass sf = l) (VSV: vvs_smaller_variables (vars sf))
      (WT: wt_vvs (Sigma:=Sigma) R (vars sf)),
    NoDup (map fst l)
    /\ forall v reg (REG: list_assoc (final_values sf) reg = Some v) res
         (INT: interp_sact (sigma:=sigma) REnv r (vars sf) (SVar v) res),
    In (v,res) l.
  Proof.
    unfold inlining_pass. intros.
    repeat destr_in IP. inv IP.
    split.
    eapply simplify_vars_preserves; eauto.
    eapply Permutation.Permutation_NoDup. apply PosSort.Permuted_sort.
    apply PTree.elements_keys_norepet. constructor.
    intros.
    exploit simplify_vars_correct; eauto.
    - apply sorted_lt. apply PTree.elements_keys_norepet.
    - eapply Permutation.Permutation_Forall. apply PosSort.Permuted_sort.
      rewrite Forall_forall.  intros x.  rewrite in_map_iff.
      intros ((x0 & (?&?)) & EQ & IN). subst. simpl.
      erewrite PTree.elements_complete; eauto.
    - simpl. intros x t y v0 GET VIS. split. auto.
      eapply Permutation.Permutation_in. apply PosSort.Permuted_sort.
      exploit WT. apply GET. intro WTy.
      eapply wt_sact_var_exists; eauto.
    - intros (IMPL & VVS' & WT' & INTERPl & NIV & _ & IN).
      edestruct (IN v).
      eapply Permutation.Permutation_in. apply PosSort.Permuted_sort.
      inv INT.
      eapply PTree.elements_correct in H1. apply (in_map fst) in H1; auto.
      rewrite Forall_forall in INTERPl.
      exploit INTERPl. eauto. simpl. intro.
      inv INT. edestruct IMPL as (y' & GET & INT2). eauto. eauto.
      inv H1. rewrite GET in H5; inv H5.
      exploit @interp_sact_determ. apply H6. apply INT2. intro; subst. auto.
  Qed.

  (* Cycles between variables are possible (a variable v can depend on another
     variable which itself depends on v). However, these can only occur in
     situations in which the cycle can be removed by applying some
     simplifications to the expression. We know this because of the way simple
     forms passed to this function are expected to have been built.

     Note that we don't need our simplifications to be exhaustive: for instance
     we choose to ignore that an and can be short-circuited based on its right
     operand. *)

  Lemma eval_sact_eval_sact_no_vars:
    forall vvs n a res res2,
    eval_sact vvs a n = Some res
    -> eval_sact_no_vars a = Some res2
    -> res = res2.
  Proof.
    induction n; simpl; intros; eauto. inv H.
    unfold opt_bind in H.
    repeat destr_in H; inv H; simpl in H0; inv H0; eauto.
    - unfold opt_bind in H1. destr_in H1.
      exploit IHn. apply Heqo. eauto. intros <-.
      exploit IHn. apply H2. eauto. auto. inv H1.
    - unfold opt_bind in H1. destr_in H1.
      exploit IHn. apply Heqo. eauto. intros <-.
      exploit IHn. apply H2. eauto. auto. inv H1.
    - unfold opt_bind in H1. destr_in H1.
      exploit IHn. apply Heqo. eauto. intros <-.
      congruence. congruence.
    - unfold opt_bind in H1.
      destruct (eval_sact_no_vars s1) eqn:eq1;
      destruct (eval_sact_no_vars s2) eqn:eq2; try congruence.
      apply (IHn _ _ _ Heqo) in eq1.
      apply (IHn _ _ _ Heqo0) in eq2.
      destruct eq1. destruct eq2.
      destruct ufn2; simpl in H2.
      + repeat (destr_in H1); simpl in *; try congruence; destr_in H2;
        try congruence.
        * apply val_beq_bits_implies_eq in Heqb0. apply val_beq_false in Heqb1; congruence.
        * apply val_beq_bits_implies_eq in Heqb0. apply val_beq_false in Heqb1; congruence.
      + repeat destr_in H2; simpl in *; congruence.
      + repeat destr_in H2; simpl in *; congruence.
      + destr_in H2; destr_in H2; simpl in *; congruence.
    - unfold opt_bind in H1. destr_in H1.
      exploit IHn. apply Heqo. eauto. intro; subst. congruence. congruence.
  Qed.

  Lemma eval_sact_wt:
    forall
      vvs (WT: wt_vvs (Sigma:=Sigma) R vvs) n a r t
      (WTa: wt_sact (Sigma:=Sigma) R vvs a t)
      (EVAL: eval_sact vvs a n = Some r),
    wt_val t r.
  Proof.
    induction n; simpl; intros; eauto. inv EVAL.
    unfold opt_bind in EVAL; repeat destr_in EVAL; inv EVAL; inv WTa; eauto.
    - rewrite Heqo in H1; inv H1.
      eapply IHn; eauto.
    - eapply Wt.wt_unop_sigma1; eauto.
    - eapply Wt.wt_binop_sigma1; eauto.
  Qed.

  Fixpoint regs_in_sact_aux (s: sact) (regs: list reg_t) :=
    match s with
    | SReg idx => if in_dec eq_dec idx regs then regs else idx::regs
    | SVar _
    | SConst _ => regs
    | SUnop _ a
    | SExternalCall _ a => regs_in_sact_aux a regs
    | SBinop _ a1 a2 => regs_in_sact_aux a1 (regs_in_sact_aux a2 regs)
    | SIf a0 a1 a2 =>
      regs_in_sact_aux a0 (regs_in_sact_aux a1 (regs_in_sact_aux a2 regs))
    end.

  Definition useful_vars_for_var (sf: IRR) (v: positive)
  : list positive :=
    reachable_vars_aux (vars sf) v [] (S (Pos.to_nat v)).

  Definition useful_regs_for_var sf v :=
    fold_left
      (fun regs v =>
        match (vars sf) ! v with
        | Some (_, s) => regs_in_sact_aux s regs
        | None => regs
        end
      )
      (useful_vars_for_var sf v) [].

  Definition interp_cycle (sf: IRR) : UREnv :=
    let sf := remove_vars sf in
    let fenv := inlining_pass sf in
    create
      REnv
      (fun k =>
        match list_assoc (final_values sf) k with
        | Some n =>
          match list_assoc fenv n with
          | Some v => v
          | None => getenv REnv r k (* Should be unreachable *)
          end
        | None => getenv REnv r k
        end).

  Definition get_val (sf: IRR) reg : option val :=
    let sf := remove_vars sf in
    let fenv := inlining_pass sf in
    match list_assoc (final_values sf) reg with
    | Some n => list_assoc fenv n
    | None => None
    end.

  Lemma filter_ptree_eq:
    forall l v (vvs t2: var_value_map),
    In v l
    -> NoDup l
    -> (forall x, In x l -> t2 ! x = None)
    -> vvs ! v = (filter_ptree vvs t2 l) ! v.
  Proof.
    induction l; simpl; intros. easy.
    inv H0. destruct H. subst.
    destr.
    rewrite filter_ptree_in. rewrite PTree.gss. auto. auto.
    rewrite filter_ptree_in; auto. symmetry; apply H1. auto.
    rewrite <- IHl. auto. auto. auto. intros.
    destr; eauto. rewrite PTree.gso; eauto. congruence.
  Qed.

  Lemma wt_sact_reachable:
    forall v1 v2 a t (SAME: forall v, reachable_var v1 a v -> v1 ! v = v2 ! v),
    wt_sact (Sigma:=Sigma) R v1 a t
    -> wt_sact (Sigma:=Sigma) R v2 a t.
  Proof.
    induction 2; simpl; intros; eauto.
    - econstructor. rewrite <- SAME. eauto. constructor.
    - constructor; auto.
    - econstructor.
      apply IHwt_sact1. intros v RV; apply SAME.
      eapply reachable_var_if_cond; eauto.
      apply IHwt_sact2. intros v RV; apply SAME.
      eapply reachable_var_if_true; eauto.
      apply IHwt_sact3. intros v RV; apply SAME.
      eapply reachable_var_if_false; eauto.
    - econstructor; eauto.
      apply IHwt_sact. intros v RV; apply SAME.
      eapply reachable_var_unop; eauto.
    - econstructor; eauto.
      apply IHwt_sact1. intros v RV; apply SAME.
      eapply reachable_var_binop1; eauto.
      apply IHwt_sact2. intros v RV; apply SAME.
      eapply reachable_var_binop2; eauto.
    - econstructor; eauto.
      apply IHwt_sact. intros v RV; apply SAME.
      eapply reachable_var_externalCall; eauto.
    - constructor.
  Qed.

  Lemma wt_sact_remove_vars:
    forall
      sf (VSV: vvs_smaller_variables (vars sf)) v (IN: In v (useful_vars sf))
      s t (GET: (vars sf) ! v = Some (t, s))
      (WT: wt_sact (Sigma:=Sigma) R (vars sf) s t),
    wt_sact (Sigma:=Sigma) R (vars (remove_vars sf)) s t.
  Proof.
    intros.
    assert (
      forall v0, reachable_var (vars sf) (SVar v) v0 -> In v0 (useful_vars sf)
    ). {
      intros v0 RV. inv RV. auto.
      rewrite GET in H0; inv H0.
      intros; eapply useful_vars_ok; eauto.
    }
    specialize (
      fun v REACH vvs t2 =>
        filter_ptree_eq _ _ vvs t2 (H v REACH) (nodup_useful_vars _ VSV)).
    simpl.
    fold (filter_ptree (vars sf) (PTree.empty _) (useful_vars sf)).
    intros. eapply wt_sact_reachable. 2: eauto.
    intros; apply H0. econstructor; eauto.
    intros; apply PTree.gempty.
  Qed.

  Lemma filter_ptree_inv:
    forall vvs l t2 v x,
    (filter_ptree vvs t2 l ) ! v = Some x
    -> NoDup l
    -> (forall x, In x l -> t2 ! x = None)
    -> t2 ! v = Some x \/ In v l /\ vvs ! v = Some x.
  Proof.
    induction l; simpl; intros; eauto.
    inv H0.
    apply IHl in H; auto.
    - destruct H as [EQ | (IN & GET)].
      + destr_in EQ; auto.
        rewrite PTree.gsspec in EQ.
        destr_in EQ; auto. inv EQ.
        right; split; eauto.
      + right; split; eauto.
    - intros. destr. rewrite PTree.gso; eauto. congruence. apply H1; auto.
  Qed.

  Lemma wt_vvs_remove_vars:
    forall sf (VSV: vvs_smaller_variables (vars sf)),
    wt_vvs (Sigma:=Sigma) R (vars sf)
    -> wt_vvs (Sigma:=Sigma) R (vars (remove_vars sf)).
      Proof.
        red; intros.
        simpl in *.
        fold (filter_ptree (vars sf) (PTree.empty _) (useful_vars sf)) in H0.
        apply filter_ptree_inv in H0. rewrite PTree.gempty in H0.
        destruct H0 as [|(IN & GET)]. inv H0.
        eapply wt_sact_remove_vars; eauto.
        eapply nodup_useful_vars; eauto.
        intros; apply PTree.gempty.
      Qed.

  Lemma vsv_remove_vars:
    forall sf,
    vvs_smaller_variables (vars sf)
    -> vvs_smaller_variables (vars (remove_vars sf)).
  Proof.
    red; intros.
    simpl in *.
    fold (filter_ptree (vars sf) (PTree.empty _) (useful_vars sf)) in H0.
    apply filter_ptree_inv in H0.
    destruct H0.
    rewrite PTree.gempty in H0. congruence.
    destruct H0 as (IN & GET).
    eapply H; eauto.
    eapply nodup_useful_vars; eauto.
    intros; apply PTree.gempty.
  Qed.

  Lemma IRR_ok:
    forall
      {Show_rule: Show rule_name_t} {finreg: FiniteType reg_t}
      (rules: rule_name_t -> daction) (s: schedule) (GS: good_scheduler s)
      (WTr: Wt.wt_renv R REnv r)
      (TA:
        forall rule, exists t,
        wt_daction (R:=R) (Sigma:=Sigma) pos_t string string [] (rules rule) t),
    UntypedSemantics.interp_dcycle rules r sigma s
    = interp_cycle
      (IRR.schedule_to_IRR (Sigma:=Sigma) R rules s).
  Proof.
    intros.
    unfold interp_dcycle.
    generalize (
      schedule_to_IRR_ok
        (wt_sigma:=wt_sigma) REnv r R WTRENV rules _ GS _ eq_refl TA WTr).
    simpl. intros (WTV & VSV & INFINAL & WTFinal & SPECFINAL).
    unfold interp_cycle. unfold commit_update.
    apply create_funext. intro k.
    simpl.
    destruct (SPECFINAL k) as (n & GET & INTERP). rewrite GET.
    assert (VSV2:=vsv_remove_vars _ VSV).
    assert (WTV2:=wt_vvs_remove_vars _ VSV WTV).
    generalize (inlining_pass_correct _ _ eq_refl VSV2 WTV2).
    intros (ND2 & INLINING).
    inversion INTERP. subst.
    exploit INLINING. apply GET.
    rewrite interp_eval_iff.
    6: (exists O; intros; symmetry; eapply remove_vars_correct; eauto).
    apply INTERP. auto. auto.
    econstructor. simpl.
    fold (
      filter_ptree
        (vars (schedule_to_IRR (Sigma:=Sigma) R rules s))
        (PTree.empty _)
        (useful_vars (schedule_to_IRR (Sigma:=Sigma) R rules s))).
    rewrite <- filter_ptree_eq. eauto.
    eapply useful_vars_incl. 2: unfold useful_vars; eauto. eauto.
    eapply list_assoc_in in GET. apply (in_map snd) in GET; eauto.
    apply nodup_useful_vars; auto.
    intros; apply PTree.gempty. econstructor; eauto.
    eapply list_assoc_in in GET. apply (in_map snd) in GET; eauto.
    intro IN. apply in_list_assoc in IN.
    setoid_rewrite IN.
    auto. auto.
  Qed.

  Lemma getenv_interp_cycle:
    forall
      {Show_rule: Show rule_name_t} {finreg: FiniteType reg_t}
      (rules: rule_name_t -> daction) (s: schedule) (GS: good_scheduler s)
      (WTr: Wt.wt_renv R REnv r)
      (TA:
        forall rule, exists t,
        wt_daction (R:=R) (Sigma:=Sigma) pos_t string string [] (rules rule) t)
      k,
    let sf := (IRR.schedule_to_IRR (Sigma:=Sigma) R rules s) in
    exists n s t,
    list_assoc (final_values sf) k = Some n
    /\ (vars sf) ! n = Some (t, s)
    /\ do_eval_sact (vars sf) s = Some (getenv REnv (interp_cycle sf) k).
  Proof.
    intros.
    unfold interp_cycle. rewrite getenv_create.
    Opaque vvs_size. Opaque max_var. Opaque size_sact. Opaque eval_sact.
    generalize (schedule_to_IRR_ok
                  (wt_sigma:=wt_sigma)
                  REnv r R WTRENV rules _ GS _ eq_refl TA WTr). simpl.
    intros (WTV & VSV  & INFINAL & WTFinal & SPECFINAL).
    destruct (SPECFINAL k) as (n & GET & INTERP).
    unfold sf. rewrite GET.
    inv INTERP. exists n. rewrite H0. exists a, t. split; auto. split; auto.
    eapply interp_sact_eval_sact; eauto.
    edestruct inlining_pass_correct as (ND2 & INLINING). reflexivity.
    apply vsv_remove_vars; eauto.
    apply wt_vvs_remove_vars; eauto.
    exploit INLINING. simpl. apply GET.
    eapply interp_eval. apply VSV. eapply vsv_remove_vars; eauto.
    eapply wt_sact_var. eauto.
    econstructor. simpl.
    fold (
      filter_ptree
        (vars (schedule_to_IRR (Sigma:=Sigma) R rules s))
        (PTree.empty _)
        (useful_vars (schedule_to_IRR (Sigma:=Sigma) R rules s))).
    rewrite <- filter_ptree_eq. eauto.
    eapply useful_vars_incl. 2: unfold useful_vars; eauto. eauto.
    eapply list_assoc_in in GET. apply (in_map snd) in GET; eauto.
    apply nodup_useful_vars; auto.
    intros; apply PTree.gempty.
    exists O; intros.
    apply remove_vars_correct. auto.
    eapply list_assoc_in in GET. apply (in_map snd) in GET; eauto.
    econstructor; eauto.
    intro IN. apply in_list_assoc in IN.
    setoid_rewrite IN.
    auto. auto.
  Qed.

  Definition simplify_sifs_sf sf :=
    sf
      <| vars :=
        Maps.PTree.map (fun _ '(t, a) => (t, simplify_sif a)) (vars sf)
       |>.

  Lemma bits_Bits:
    forall vvs a sz (WTA : wt_sact (Sigma := Sigma) R vvs a (bits_t sz))
      x (VA : eval_sact_no_vars a = Some x),
    exists b, x = Bits b /\ List.length b = sz.
  Proof.
    intros.
    apply (eval_sact_no_vars_wt _ _ _ WTA _) in VA.
    inv VA. exists bs. split; eauto.
  Qed.

  Lemma interp_sact_eval_sact_iff:
    forall vvs a v (VVSSV: vvs_smaller_variables vvs) t
      (WTS: wt_sact (Sigma := Sigma) R vvs a t),
    interp_sact (sigma := sigma) REnv r vvs a v
    <-> exists fuel, eval_sact vvs a fuel = Some v.
  Proof.
    intros. split; intros.
    - exists (
        Pos.to_nat (Pos.succ (max_var vvs))
        + vvs_size vvs (Pos.succ (max_var vvs))
        + size_sact a
      ). eapply interp_sact_eval_sact; eauto.
    - destruct H. eapply eval_sact_interp_sact; eauto.
  Qed.

  Lemma schedule_to_IRR_wf:
    forall
      {Show_rule: Show rule_name_t} `{finite: FiniteType reg_t}
      (rules: rule_name_t -> IRR.uact)
      sched (GS: good_scheduler sched)
      (WTrules: forall r0 : rule_name_t, exists tret : type, wt_daction (R:=R) (Sigma:=Sigma) pos_t string string [] (rules r0) tret)
    ,
      wf_sf (schedule_to_IRR (pos_t := pos_t) R (Sigma:=Sigma) rules sched).
  Proof.
    intros.
    edestruct (@schedule_to_IRR_ok) as (WT & VSV & FINAL & FINALWt & FINAL2).
    apply wt_sigma. apply WTRENV. apply GS. reflexivity. apply WTrules.
    apply WTRENV.
    constructor; auto.
    - apply WT.
    - apply VSV.
    - intros. edestruct FINALWt as (n & GET & WTreg).
      rewrite GET in H; inv H. eauto.
  Qed.

  Record sf_eq (sf1 sf2: IRR) := {
    sf_eq_final: final_values sf1 = final_values sf2;
    sf_eq_vars: forall reg v t,
      In (reg,v) (final_values sf1) ->
      wt_sact (Sigma:=Sigma) R (vars sf1) (SVar v) t ->
      forall x,
        interp_sact REnv (sigma:=sigma) r (vars sf1) (SVar v) x <->
          interp_sact REnv (sigma:=sigma) r (vars sf2) (SVar v) x;
    sf_eq_wt:
      forall reg v t,
      In (reg,v) (final_values sf1) ->
      wt_sact (Sigma:=Sigma) R (vars sf1) (SVar v) t <->
      wt_sact (Sigma:=Sigma) R (vars sf2) (SVar v) t
  }.

  Lemma sf_eq_refl: forall sf, sf_eq sf sf.
  Proof. constructor; tauto. Qed.

  Lemma sf_eq_trans:
    forall sf1 sf2,
    sf_eq sf1 sf2
    -> forall sf3, sf_eq sf2 sf3
    -> sf_eq sf1 sf3.
  Proof.
    intros sf1 sf2 EQ1 sf3 EQ2.
    inv EQ1; inv EQ2.
    constructor. congruence.
    intros.
    rewrite sf_eq_vars0. 2: eauto. eapply sf_eq_vars1. rewrite <- sf_eq_final0. eauto.
    eapply sf_eq_wt0. eauto. eauto. eauto.
    intros.
    erewrite sf_eq_wt0. 2: eauto.
    rewrite sf_eq_final0 in H. eauto.
  Qed.

  Lemma sf_eq_sym: forall sf1 sf2, sf_eq sf1 sf2 -> sf_eq sf2 sf1.
  Proof.
    destruct 1; constructor; eauto.
    intros; symmetry; eapply sf_eq_vars0. rewrite sf_eq_final0; eauto.
    rewrite <- sf_eq_final0 in H. rewrite <-sf_eq_wt0 in H0. eauto. eauto.
    intros.
    rewrite <- sf_eq_final0 in H. rewrite <-sf_eq_wt0 . tauto. eauto.
  Qed.

  Lemma sf_eq_remove_vars sf: wf_sf sf -> sf_eq sf (remove_vars sf).
  Proof.
    constructor; auto.
    - intros.
      inversion H1. subst.
      eapply interp_eval_iff. apply H.
      apply vsv_remove_vars; auto. apply H. eauto.
      econstructor.
      simpl. fold (filter_ptree (vars sf) (PTree.empty _) (useful_vars sf)).
      rewrite <- filter_ptree_eq. eapply H3.
      eapply useful_vars_incl. apply H. eauto.
      change v with (snd (reg, v)). apply in_map. eauto.
      apply nodup_useful_vars. apply H.
      intros; rewrite PTree.gempty. auto.
      exists O; intros; eapply remove_vars_correct. apply H.
      change v with (snd (reg, v)). apply in_map. eauto.
    - intros. destruct H. split; intros.
      + inversion H. subst.
        econstructor.
        simpl. fold (filter_ptree (vars sf) (PTree.empty _) (useful_vars sf)).
        rewrite <- filter_ptree_eq. eapply H2.
        eapply useful_vars_incl. eauto. auto.
        change v with (snd (reg, v)). apply in_map. eauto.
        apply nodup_useful_vars. auto.
        intros; rewrite PTree.gempty. auto.
      + inv H.
        unfold remove_vars in H2. simpl in H2.
        fold (filter_ptree (vars sf) (PTree.empty _) (useful_vars sf)) in H2.
        apply filter_ptree_inv in H2. rewrite PTree.gempty in H2.
        destruct H2. congruence.
        destruct H. econstructor; eauto.
        apply nodup_useful_vars. auto.
        intros; rewrite PTree.gempty. auto.
  Qed.

  Instance sf_eq_equi: RelationClasses.Equivalence sf_eq.
  Proof.
    constructor.
    red. apply sf_eq_refl.
    red. apply sf_eq_sym.
    red. intros; eapply sf_eq_trans; eauto.
  Qed.

  Lemma sf_eq_apply_l:
    forall F1 (F1OK: forall sf, wf_sf sf -> sf_eq sf (F1 sf)),
    forall sf1 sf2, wf_sf sf1 -> sf_eq sf1 sf2 -> sf_eq (F1 sf1) sf2.
  Proof. intros. rewrite <- F1OK. auto. auto. Qed.

  Lemma sf_eq_apply:
    forall F1 (F1OK: forall sf, wf_sf sf -> sf_eq sf (F1 sf)),
    forall sf1 sf2,
    wf_sf sf1 -> wf_sf sf2 -> sf_eq sf1 sf2 -> sf_eq (F1 sf1) (F1 sf2).
  Proof. intros. rewrite <- ! F1OK; auto. Qed.

  Record sf_eq_restricted l (sf1 sf2: IRR) := {
    sf_eqr_final:
    forall reg,
      In reg l ->
      list_assoc (final_values sf1) reg =
        list_assoc (final_values sf2) reg;
    sf_eqr_vars: forall reg v t,
      In reg l ->
      list_assoc (final_values sf2) reg = Some v ->
      wt_sact (Sigma:=Sigma) R (vars sf1) (SVar v) t ->
      forall x,
        interp_sact REnv (sigma:=sigma) r (vars sf1) (SVar v) x <->
          interp_sact REnv (sigma:=sigma) r (vars sf2) (SVar v) x;
    sf_eqr_wt:
    forall reg v t,
      In reg l ->
      list_assoc (final_values sf2) reg = Some v ->
      wt_sact (Sigma:=Sigma) R (vars sf1) (SVar v) t <->
        wt_sact (Sigma:=Sigma) R (vars sf2) (SVar v) t
  }.

  Lemma inlining_pass_sf_eqr':
    forall sf1 sf2 l
           (SFEQ: sf_eq_restricted l sf1 sf2)
           (VSV1: vvs_smaller_variables (vars sf1))
           (VSV2: vvs_smaller_variables (vars sf2))
           (WT1: wt_vvs (Sigma:=Sigma) R (vars sf1))
           (WT2: wt_vvs (Sigma:=Sigma) R (vars sf2))
           (WTfinal: forall reg k,
               list_assoc (final_values sf1) reg = Some k ->
               wt_sact (Sigma:=Sigma) R (vars sf1) (SVar k) (R reg)
           )
           reg k
           (IN: In reg l)
           (FINAL: list_assoc (final_values sf1) reg = Some k),
      list_assoc (inlining_pass sf1) k = list_assoc (inlining_pass sf2) k.
  Proof.
    intros.
    exploit inlining_pass_correct. reflexivity. apply VSV1. apply WT1.
    exploit inlining_pass_correct. reflexivity. apply VSV2. apply WT2.
    intros (ND2 & SPEC2) (ND1 & SPEC1).
    specialize (SPEC2 k reg).
    erewrite <- sf_eqr_final in SPEC2. 2: eauto. 2: auto.
    specialize (SPEC2 FINAL).
    exploit @wt_sact_interp. eauto. eauto. apply WT1. apply VSV1. apply vvs_range_max_var.
    apply WTfinal. eauto.
    intros (v & IS & WT).
    erewrite in_list_assoc. 2: auto. 2: eapply SPEC1; eauto.
    erewrite in_list_assoc. 2: auto. 2: eapply SPEC2; eauto.
    reflexivity.
    rewrite <- sf_eqr_vars; eauto.
    erewrite <- sf_eqr_final; eauto.
  Qed.

  Lemma inlining_pass_sf_eqr:
    forall sf1 sf2 l
           (SFEQ: sf_eq_restricted l sf1 sf2)
           (WF1: wf_sf sf1)
           (WF2: wf_sf sf2)
           reg k (IN: In reg l)
           (FINAL: list_assoc (final_values sf1) reg = Some k),
      list_assoc (inlining_pass sf1) k = list_assoc (inlining_pass sf2) k.
  Proof.
    intros.
    destruct WF1, WF2;
    eapply inlining_pass_sf_eqr'; eauto.
  Qed.

  Lemma sf_eq_is_restricted:
    forall sf1 sf2,
      sf_eq sf1 sf2 ->
      sf_eq_restricted (@finite_elements _ (finite_keys REnv)) sf1 sf2.
  Proof.
    intros.
    inv H. constructor.
    - rewrite sf_eq_final0. tauto.
    (* - intros. elim H. eapply nth_error_In. eapply finite_surjective. *)
    - rewrite <- sf_eq_final0. intros; eapply sf_eq_vars0; eauto.
      eapply list_assoc_in; eauto.
    - rewrite <- sf_eq_final0. intros; eapply sf_eq_wt0; eauto.
      eapply list_assoc_in; eauto.
  Qed.

  Lemma inlining_pass_sf_eq:
    forall sf1 sf2
           (SFEQ: sf_eq sf1 sf2)
           (WF1: wf_sf sf1)
           (WF2: wf_sf sf2)
           reg k
           (FINAL: list_assoc (final_values sf1) reg = Some k),
      list_assoc (inlining_pass sf1) k = list_assoc (inlining_pass sf2) k.
  Proof.
    intros.
    eapply inlining_pass_sf_eqr; eauto. apply sf_eq_is_restricted; auto.
    eapply nth_error_In.
    apply finite_surjective.
  Qed.

  Lemma wf_sf_remove_vars sf: wf_sf sf -> wf_sf (remove_vars sf).
  Proof.
    destruct 1.
    constructor.
    eapply wt_vvs_remove_vars; eauto.
    eapply vsv_remove_vars; eauto.
    intros.
    simpl in H.
    generalize (wf_sf_final _ _ H). intro WT. inversion WT; subst.
    simpl. econstructor.
    fold (filter_ptree (vars sf) (PTree.empty _) (useful_vars sf)).
    rewrite <- filter_ptree_eq. eauto. 2: apply nodup_useful_vars. 2: auto.
    2: intros; rewrite PTree.gempty; auto.
    eapply useful_vars_incl. eauto. reflexivity.
    apply list_assoc_in in H.
    apply in_map with (f:=snd) in H. simpl in *; auto.
  Qed.

  Lemma sf_eq_interp_cycle_ok:
    forall reg sf1 sf2,
      wf_sf sf1 -> wf_sf sf2 ->
      sf_eq sf1 sf2 ->
    getenv REnv (interp_cycle sf1) reg
    = getenv REnv (interp_cycle sf2) reg.
  Proof.
    intros.
    unfold interp_cycle. simpl.
    rewrite ! getenv_create.
    erewrite sf_eq_final; eauto.
    destr.
    erewrite inlining_pass_sf_eq. reflexivity.
    apply sf_eq_apply; auto.
    apply sf_eq_remove_vars.
    apply wf_sf_remove_vars; auto.
    apply wf_sf_remove_vars; auto. simpl.
    erewrite sf_eq_final; eauto.
  Qed.

  Lemma wt_vvs_f:
    forall f vvs,
      (forall a t,
        wt_sact (Sigma:=Sigma) R vvs a t ->
        wt_sact (Sigma:=Sigma) R (PTree.map (fun _ '(t,a) => (t, f a)) vvs) (f a) t) ->
      wt_vvs (Sigma:=Sigma) R vvs ->
      wt_vvs (Sigma:=Sigma) R (PTree.map (fun _ '(t,a) => (t, f a)) vvs).
  Proof.
    red; intros.
    rewrite PTree.gmap in H1.
    unfold option_map in H1; repeat destr_in H1; inv H1. eauto.
  Qed.

  Lemma f_wt_sact_ok':
    forall f vvs s t (WTS: wt_sact (Sigma := Sigma) R vvs s t),
    wt_sact (Sigma := Sigma) R (PTree.map (fun _ '(t,a) => (t, f a)) vvs) s t.
  Proof.
    intros.
    induction WTS; econstructor; eauto.
    setoid_rewrite Maps.PTree.gmap.
    unfold option_map. setoid_rewrite H. easy.
  Qed.

  Lemma f_wt_sact_ok'i:
    forall f vvs s t (WTS: wt_sact (Sigma := Sigma) R vvs s t),
    wt_sact (Sigma := Sigma) R (PTree.map (fun k '(t,a) => (t, f k a)) vvs) s t.
  Proof.
    intros.
    induction WTS; econstructor; eauto.
    setoid_rewrite Maps.PTree.gmap.
    unfold option_map. setoid_rewrite H. easy.
  Qed.

  Lemma f_wtvvs_ok':
    forall f (FSPEC: forall vvs a t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
               wt_sact (Sigma := Sigma) R vvs (f a) t)
           vvs (WTVVS: wt_vvs (Sigma := Sigma) R vvs),
    wt_vvs (Sigma := Sigma) R (PTree.map (fun _ '(t,a) => (t, f a)) vvs).
  Proof.
    intros. unfold wt_vvs. intros.
    apply f_wt_sact_ok'.
    rewrite Maps.PTree.gmap in H. unfold option_map in H.
    repeat destr_in H; inv H. apply FSPEC; eauto.
  Qed.

  Lemma f_wtvvs_ok'i:
    forall f (FSPEC: forall k vvs a t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
               wt_sact (Sigma := Sigma) R vvs (f k a) t)
           vvs (WTVVS: wt_vvs (Sigma := Sigma) R vvs),
    wt_vvs (Sigma := Sigma) R (PTree.map (fun k '(t,a) => (t, f k a)) vvs).
  Proof.
    intros. unfold wt_vvs. intros.
    apply f_wt_sact_ok'i.
    rewrite Maps.PTree.gmap in H. unfold option_map in H.
    repeat destr_in H; inv H. apply FSPEC; eauto.
  Qed.

  Lemma f_wtvvs_ok'iP:
    forall {MD:Type} (f: MD -> sact -> sact)(metadata: positive -> MD) Pk
           P (FSPEC: forall k vvs (PV: P vvs) a (PK: Pk k a) t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
               wt_sact (Sigma := Sigma) R vvs (f k a) t)
           vvs (WTVVS: wt_vvs (Sigma := Sigma) R vvs) (PV: P vvs)
           (PK: forall k t a, vvs!k=Some (t,a) -> Pk (metadata k)a),
      wt_vvs (Sigma := Sigma) R (PTree.map (fun k '(t,a) => (t, f (metadata k) a)) vvs).
  Proof.
    intros. unfold wt_vvs. intros.
    apply f_wt_sact_ok'i.
    rewrite Maps.PTree.gmap in H. unfold option_map in H.
    repeat destr_in H; inv H. apply FSPEC; eauto.
  Qed.

  Lemma simplify_sif_wt:
    forall vvs a t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
      wt_sact (Sigma := Sigma) R vvs (simplify_sif a) t.
  Proof.
    induction 1; simpl; intros; try now (econstructor; eauto).
    destr; try (econstructor; eauto).
    exploit eval_sact_no_vars_wt. apply WTS1. eauto. intro A. apply wt_val_bool in A. destruct A. subst.
    destr.
  Qed.

  Lemma vsv_f:
    forall f (FSPEC: forall s v', var_in_sact (f s) v' -> var_in_sact s v')
           vvs,
      vvs_smaller_variables (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) vvs ->
      vvs_smaller_variables (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (PTree.map (fun _ '(t,a) => (t, f a)) vvs).
  Proof.
    red; intros.
    rewrite Maps.PTree.gmap in H0. unfold option_map in H0.
    repeat destr_in H0; inv H0.
    eapply H in Heqo. apply Heqo. eauto.
  Qed.


  Lemma vsv_fi:
    forall f (FSPEC: forall k s v', var_in_sact (f k s) v' -> var_in_sact s v')
           vvs,
      vvs_smaller_variables (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) vvs ->
      vvs_smaller_variables (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (PTree.map (fun k '(t,a) => (t, f k a)) vvs).
  Proof.
    red; intros.
    rewrite Maps.PTree.gmap in H0. unfold option_map in H0.
    repeat destr_in H0; inv H0.
    eapply H in Heqo. apply Heqo. eauto.
  Qed.

  Lemma simplify_sif_vis:
    forall a v' (VIS: var_in_sact (simplify_sif a) v'), var_in_sact a v'.
  Proof.
    induction a; simpl; intros; eauto.
    - repeat destr_in VIS; eauto.
      eapply var_in_if_true; eauto.
      eapply var_in_if_false; eauto.
    - inv VIS; econstructor; eauto.
    - inv VIS. econstructor; eauto.
      eapply var_in_sact_binop_2; eauto.
    - inv VIS; econstructor; eauto.
  Qed.

  Lemma wf_f:
    forall
      sf f
      (FWT:
        forall vvs a t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
        wt_sact (Sigma := Sigma) R vvs (f a) t
      )
      (FVIS: forall s v', var_in_sact (f s) v' -> var_in_sact s v'),
      wf_sf sf
      -> wf_sf
        {| final_values := final_values sf;
           read1_values := read1_values sf;
           debug_log := debug_log sf;
           vars := PTree.map (fun _ '(t,a) => (t, f a)) (vars sf)
         |}.
  Proof.
    destruct 3; constructor.
    - eapply f_wtvvs_ok'; eauto.
    - eapply vsv_f; eauto.
    - simpl.
      intros. eapply f_wt_sact_ok'. eauto.
  Qed.

  Lemma wf_fi:
    forall sf f
           (FWT: forall k vvs a t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
               wt_sact (Sigma := Sigma) R vvs (f k a) t)
           (FVIS: forall k s v', var_in_sact (f k s) v' -> var_in_sact s v'),
      wf_sf sf ->
      wf_sf {| final_values := final_values sf;
              read1_values := read1_values sf;
              debug_log := debug_log sf;
              vars := PTree.map (fun k '(t,a) => (t, f k a)) (vars sf) |}.
  Proof.
    destruct 3; constructor.
    - eapply f_wtvvs_ok'i; eauto.
    - eapply vsv_fi; eauto.
    - simpl.
      intros. eapply f_wt_sact_ok'i. eauto.
  Qed.

  Lemma wf_simplify_sifs:
    forall sf,
      wf_sf sf ->
      wf_sf (simplify_sifs_sf sf).
  Proof.
    intros; eapply wf_f; eauto.
    eapply simplify_sif_wt.
    eapply simplify_sif_vis.
  Qed.

  Lemma f_interp_sact_ok':
    forall f
           (SPEC: forall (a : IRR.sact) (v : val) (vvs : PTree.t (type * IRR.sact)),
               wt_vvs (Sigma:=Sigma) R vvs ->
               forall t : type,
                 wt_sact (Sigma:=Sigma) R vvs a t ->
                 vvs_smaller_variables vvs ->
                 interp_sact (sigma:=sigma) REnv r vvs a v ->
                 interp_sact (sigma:=sigma) REnv r vvs (f a) v
           )
           (FWT: forall vvs (a0 : IRR.sact) (t0 : type),
               wt_sact (Sigma:=Sigma) R vvs a0 t0 ->
               wt_sact (Sigma:=Sigma) R vvs (f a0) t0)
           (VIS: forall (s : IRR.sact) (v' : positive), var_in_sact (f s) v' -> var_in_sact s v')
           vvs
           (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
           (VVSSV: vvs_smaller_variables vvs)
           a v (EV_INIT: interp_sact (sigma := sigma) REnv r vvs a v)
           t (WTa: wt_sact (Sigma:=Sigma) R vvs a t),
    interp_sact (sigma := sigma) REnv r (PTree.map (fun _ '(t,a) => (t, f a)) vvs) a v.
  Proof.
    intros f SPEC FWT VIS vvs WTVVS VVSSV.
    induction 1; try (econstructor; eauto; fail).
    econstructor.
    - setoid_rewrite Maps.PTree.gmap.
      unfold option_map. setoid_rewrite H.
      f_equal.
    - eapply SPEC; eauto.
      eapply f_wtvvs_ok'; eauto.
      eapply f_wt_sact_ok'; eauto.
      eapply vsv_f; eauto.
    - intros t0 WT; inv WT. econstructor; eauto.
      eapply IHEV_INIT2. destr; eauto.
    - intros t0 WT; inv WT. econstructor; eauto.
    - intros t0 WT; inv WT. econstructor; eauto.
    - intros t0 WT; inv WT. econstructor; eauto.
  Qed.

  Lemma f_interp_sact_ok'i:
    forall f
           (SPEC: forall k (a : IRR.sact) (v : val) (vvs : PTree.t (type * IRR.sact)),
               wt_vvs (Sigma:=Sigma) R vvs ->
               forall t : type,
                 wt_sact (Sigma:=Sigma) R vvs a t ->
                 vvs_smaller_variables vvs ->
                 interp_sact (sigma:=sigma) REnv r vvs a v ->
                 interp_sact (sigma:=sigma) REnv r vvs (f k a) v
           )
           (FWT: forall k vvs (a0 : IRR.sact) (t0 : type),
               wt_sact (Sigma:=Sigma) R vvs a0 t0 ->
               wt_sact (Sigma:=Sigma) R vvs (f k a0) t0)
           (VIS: forall k (s : IRR.sact) (v' : positive), var_in_sact (f k s) v' -> var_in_sact s v')
           vvs
           (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
           (VVSSV: vvs_smaller_variables vvs)
           a v (EV_INIT: interp_sact (sigma := sigma) REnv r vvs a v)
           t (WTa: wt_sact (Sigma:=Sigma) R vvs a t),
    interp_sact (sigma := sigma) REnv r (PTree.map (fun k '(t,a) => (t, f k a)) vvs) a v.
  Proof.
    intros f SPEC FWT VIS vvs WTVVS VVSSV.
    induction 1; try (econstructor; eauto; fail).
    econstructor.
    - setoid_rewrite Maps.PTree.gmap.
      unfold option_map. setoid_rewrite H.
      f_equal.
    - eapply SPEC; eauto.
      eapply f_wtvvs_ok'i; eauto.
      eapply f_wt_sact_ok'i; eauto.
      eapply vsv_fi; eauto.
    - intros t0 WT; inv WT. econstructor; eauto.
      eapply IHEV_INIT2. destr; eauto.
    - intros t0 WT; inv WT. econstructor; eauto.
    - intros t0 WT; inv WT. econstructor; eauto.
    - intros t0 WT; inv WT. econstructor; eauto.
  Qed.

  Lemma f_interp_sact_ok'iP:
    forall P {MD: Type} Pk (metadata: positive -> MD) (f: MD -> sact -> sact)
           (SPEC: forall k (a : IRR.sact) (v : val) (vvs : PTree.t (type * IRR.sact)),
               wt_vvs (Sigma:=Sigma) R vvs ->
               vvs_smaller_variables vvs ->
               P vvs ->
               Pk k a ->
               forall t : type,
                 wt_sact (Sigma:=Sigma) R vvs a t ->
                 interp_sact (sigma:=sigma) REnv r vvs a v ->
                 interp_sact (sigma:=sigma) REnv r vvs (f k a) v
           )
           (FWT: forall k vvs (PV: P vvs) (a0 : IRR.sact) (t0 : type),
               Pk k a0 ->
               wt_sact (Sigma:=Sigma) R vvs a0 t0 ->
               wt_sact (Sigma:=Sigma) R vvs (f k a0) t0)
           (Ppres: forall vvs, P vvs ->
                               P (PTree.map (fun (k : positive) '(t1, a0) => (t1, f (metadata k) a0)) vvs)
           )
           (VIS: forall k (s : IRR.sact) (v' : positive), var_in_sact (f k s) v' -> var_in_sact s v')
           vvs
           (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
           (VVSSV: vvs_smaller_variables vvs)
           (PV: P vvs)
           (PK: forall k t a, vvs!k = Some (t,a) -> Pk (metadata k) a)
           a v (EV_INIT: interp_sact (sigma := sigma) REnv r vvs a v)
           t (WTa: wt_sact (Sigma:=Sigma) R vvs a t),
    interp_sact (sigma := sigma) REnv r (PTree.map (fun k '(t,a) => (t, f (metadata k) a)) vvs) a v.
  Proof.
    intros P MD Pk metadata f SPEC FWT Ppres VIS vvs WTVVS VVSSV PV PK.
    induction 1; try (econstructor; eauto; fail).
    - econstructor.
      setoid_rewrite Maps.PTree.gmap.
      unfold option_map. setoid_rewrite H. eauto.
      eapply SPEC.
      + eapply f_wtvvs_ok'iP; eauto.
      + eapply vsv_fi; eauto.
      + eapply Ppres; eauto.
      + eapply PK; eauto.
      + eapply f_wt_sact_ok'i. eauto.
      + eauto.
    - intros t0 WT; inv WT. econstructor; eauto.
      eapply IHEV_INIT2. destr; eauto.
    - intros t0 WT; inv WT. econstructor; eauto.
    - intros t0 WT; inv WT. econstructor; eauto.
    - intros t0 WT; inv WT. econstructor; eauto.
  Qed.

  Lemma f_interp_sact_ok:
    forall vvs f
           (FSPEC: forall vvs : PTree.t (type * IRR.sact),
               wt_vvs (Sigma:=Sigma) R vvs ->
               vvs_smaller_variables vvs ->
               forall (a : sact) (v : val),
                 interp_sact (sigma:=sigma) REnv r vvs (f a) v ->
                 forall t : type, wt_sact (Sigma:=Sigma) R vvs a t -> interp_sact (sigma:=sigma) REnv r vvs a v
           )
           (FWT: forall vvs (a0 : IRR.sact) (t0 : type),
               wt_sact (Sigma:=Sigma) R vvs a0 t0 ->
               wt_sact (Sigma:=Sigma) R vvs (f a0) t0)
           (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
           (VVSSV: vvs_smaller_variables vvs)
           a v
           (EV_INIT: interp_sact (sigma := sigma) REnv r (PTree.map (fun _ '(t,a) => (t, f a)) vvs) a v)
           t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
      interp_sact (sigma := sigma) REnv r vvs a v.
  Proof.
    induction 5; simpl; intros; inv WTS.
    - setoid_rewrite PTree.gmap in H. setoid_rewrite H1 in H. simpl in H. inv H.
      econstructor; eauto.
      eapply FSPEC; eauto.
    - econstructor.
    - econstructor. eauto.
      eapply IHEV_INIT2. destr; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.


  Lemma f_interp_sact_oki:
    forall vvs f
           (FSPEC: forall k (vvs : PTree.t (type * IRR.sact)),
               wt_vvs (Sigma:=Sigma) R vvs ->
               vvs_smaller_variables vvs ->
               forall (a : sact) (v : val),
                 interp_sact (sigma:=sigma) REnv r vvs (f k a) v ->
                 forall t : type, wt_sact (Sigma:=Sigma) R vvs a t -> interp_sact (sigma:=sigma) REnv r vvs a v
           )
           (FWT: forall k vvs (a0 : IRR.sact) (t0 : type),
               wt_sact (Sigma:=Sigma) R vvs a0 t0 ->
               wt_sact (Sigma:=Sigma) R vvs (f k a0) t0)
           (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
           (VVSSV: vvs_smaller_variables vvs)
           a v
           (EV_INIT: interp_sact (sigma := sigma) REnv r (PTree.map (fun k '(t,a) => (t, f k a)) vvs) a v)
           t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
      interp_sact (sigma := sigma) REnv r vvs a v.
  Proof.
    induction 5; simpl; intros; inv WTS.
    - setoid_rewrite PTree.gmap in H. setoid_rewrite H1 in H. simpl in H. inv H.
      econstructor; eauto.
      eapply FSPEC; eauto.
    - econstructor.
    - econstructor. eauto.
      eapply IHEV_INIT2. destr; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.


  Lemma f_interp_sact_okiP:
    forall vvs f P
           (FSPEC: forall k (vvs : PTree.t (type * IRR.sact)) (PV: P vvs),
               wt_vvs (Sigma:=Sigma) R vvs ->
               vvs_smaller_variables vvs ->
               forall (a : sact) (v : val),
                 interp_sact (sigma:=sigma) REnv r vvs (f k a) v ->
                 forall t : type, wt_sact (Sigma:=Sigma) R vvs a t -> interp_sact (sigma:=sigma) REnv r vvs a v
           )
           (FWT: forall k vvs (a0 : IRR.sact) (t0 : type) (PV: P vvs),
               wt_sact (Sigma:=Sigma) R vvs a0 t0 ->
               wt_sact (Sigma:=Sigma) R vvs (f k a0) t0)
           (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
           (VVSSV: vvs_smaller_variables vvs)
           (PV: P vvs)
           a v
           (EV_INIT: interp_sact (sigma := sigma) REnv r (PTree.map (fun k '(t,a) => (t, f k a)) vvs) a v)
           t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
      interp_sact (sigma := sigma) REnv r vvs a v.
  Proof.
    induction 6; simpl; intros; inv WTS.
    - setoid_rewrite PTree.gmap in H. setoid_rewrite H1 in H. simpl in H. inv H.
      econstructor; eauto.
      eapply FSPEC; eauto.
    - econstructor.
    - econstructor. eauto.
      eapply IHEV_INIT2. destr; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.

  Lemma sf_eq_f:
    forall sf f
           (FSPEC: forall vvs : PTree.t (type * IRR.sact),
               wt_vvs (Sigma:=Sigma) R vvs ->
               vvs_smaller_variables vvs ->
               forall (a : sact) (v : val),
                 interp_sact (sigma:=sigma) REnv r vvs (f a) v ->
                 forall t : type, wt_sact (Sigma:=Sigma) R vvs a t -> interp_sact (sigma:=sigma) REnv r vvs a v
           )
           (SPEC: forall (a : IRR.sact) (v : val) (vvs : PTree.t (type * IRR.sact)),
               wt_vvs (Sigma:=Sigma) R vvs ->
               forall t : type,
                 wt_sact (Sigma:=Sigma) R vvs a t ->
                 vvs_smaller_variables vvs ->
                 interp_sact (sigma:=sigma) REnv r vvs a v ->
                 interp_sact (sigma:=sigma) REnv r vvs (f a) v
           )
           (FWT: forall vvs (a0 : IRR.sact) (t0 : type),
               wt_sact (Sigma:=Sigma) R vvs a0 t0 ->
               wt_sact (Sigma:=Sigma) R vvs (f a0) t0)
           (VIS: forall (s : IRR.sact) (v' : positive), var_in_sact (f s) v' -> var_in_sact s v')
    ,
      wf_sf sf ->
      sf_eq sf {| final_values := final_values sf;
                 read1_values := read1_values sf;
                 debug_log := debug_log sf;
                 vars := PTree.map (fun (_ : positive) '(t, a) => (t, f a)) (vars sf) |}.
  Proof.
    intros.
    constructor. simpl. auto.
    - intros. simpl.
      split.
      + intro A; inv A. inv H1. rewrite H3 in H5.
        inv H5.
        econstructor.
        rewrite PTree.gmap. setoid_rewrite H3. simpl. reflexivity.
        eapply f_interp_sact_ok'. eauto. eauto. eauto. apply H. apply H. eapply SPEC; eauto.
        apply H. eapply H. eauto. apply H.
        eapply FWT. eapply H. eauto.
      + intro A; inv A. rewrite PTree.gmap in H3. unfold option_map in H3; repeat destr_in H3; inv H3.
        econstructor. eauto. inv H1. setoid_rewrite H3 in Heqo. inv Heqo.
        eapply FSPEC in H4. eapply f_interp_sact_ok; eauto.
        apply H. apply H. eapply H. eauto.
        eapply f_wtvvs_ok'; eauto. apply H.
        eapply vsv_f; eauto. apply H.
        eapply f_wt_sact_ok'; eauto. eapply H. eauto.
    - intros. simpl.
      split. eapply f_wt_sact_ok'; eauto.
      intro A; inv A.
      rewrite PTree.gmap in H2. unfold option_map in H2; repeat destr_in H2; inv H2.
      econstructor. eauto.
  Qed.

  Lemma sf_eq_mapi:
    forall sf f
           (FSPEC: forall (vvs : PTree.t (type * IRR.sact)) k,
               wt_vvs (Sigma:=Sigma) R vvs ->
               vvs_smaller_variables vvs ->
               forall (a : sact) (v : val),
                 interp_sact (sigma:=sigma) REnv r vvs (f k a) v ->
                 forall t : type, wt_sact (Sigma:=Sigma) R vvs a t -> interp_sact (sigma:=sigma) REnv r vvs a v
           )
           (SPEC: forall k (a : IRR.sact) (v : val) (vvs : PTree.t (type * IRR.sact)),
               wt_vvs (Sigma:=Sigma) R vvs ->
               forall t : type,
                 wt_sact (Sigma:=Sigma) R vvs a t ->
                 vvs_smaller_variables vvs ->
                 interp_sact (sigma:=sigma) REnv r vvs a v ->
                 interp_sact (sigma:=sigma) REnv r vvs (f k a) v
           )
           (FWT: forall k vvs (a0 : IRR.sact) (t0 : type),
               wt_sact (Sigma:=Sigma) R vvs a0 t0 ->
               wt_sact (Sigma:=Sigma) R vvs (f k a0) t0)
           (VIS: forall k (s : IRR.sact) (v' : positive), var_in_sact (f k s) v' -> var_in_sact s v')
    ,
      wf_sf sf ->
      sf_eq sf {| final_values := final_values sf;
                 read1_values := read1_values sf;
                 debug_log := debug_log sf;
                 vars := PTree.map (fun k '(t, a) => (t, f k a)) (vars sf) |}.
  Proof.
    intros.
    constructor. simpl. auto.
    - intros. simpl.
      split.
      + intro A; inv A. inv H1. rewrite H3 in H5.
        inv H5.
        econstructor.
        rewrite PTree.gmap. setoid_rewrite H3. simpl. reflexivity.
        eapply f_interp_sact_ok'i. eauto. eauto. eauto. apply H. apply H. eapply SPEC; eauto.
        apply H. eapply H. eauto. apply H.
        eapply FWT. eapply H. eauto.
      + intro A; inv A. rewrite PTree.gmap in H3. unfold option_map in H3; repeat destr_in H3; inv H3.
        econstructor. eauto. inv H1. setoid_rewrite H3 in Heqo. inv Heqo.
        eapply FSPEC in H4. eapply f_interp_sact_oki; eauto.
        apply H. apply H. eapply H. eauto.
        eapply f_wtvvs_ok'i; eauto. apply H.
        eapply vsv_fi; eauto. apply H.
        eapply f_wt_sact_ok'i; eauto. eapply H. eauto.
    - intros. simpl.
      split. eapply f_wt_sact_ok'i; eauto.
      intro A; inv A.
      rewrite PTree.gmap in H2. unfold option_map in H2; repeat destr_in H2; inv H2.
      econstructor. eauto.
  Qed.

  Lemma sf_eq_mapi':
    forall sf f
           (SPEC: forall (a : IRR.sact) (v : val),
               forall t : type,
                 wt_sact (Sigma:=Sigma) R (vars sf) a t ->
                 interp_sact (sigma:=sigma) REnv r (vars sf) a v <->
                 interp_sact (sigma:=sigma) REnv r (PTree.map (fun k '(t,a) => (t, f k a)) (vars sf)) a v
           )
           (SPEC2:
             forall s x t v,
               (vars sf) ! v = Some (t, s) ->
               interp_sact (sigma:=sigma) REnv r (vars sf) s x <->
               interp_sact (sigma:=sigma) REnv r (vars sf) (f v s) x
           )
           (FWT: forall k (a0 : IRR.sact) (t0 : type),
               wt_sact (Sigma:=Sigma) R (vars sf) a0 t0 ->
               wt_sact (Sigma:=Sigma) R (vars sf) (f k a0) t0)
           (VIS: forall k (s : IRR.sact) (v' : positive), var_in_sact (f k s) v' -> var_in_sact s v')
    ,
      wf_sf sf ->
      sf_eq sf {| final_values := final_values sf;
                 read1_values := read1_values sf;
                 debug_log := debug_log sf;
                 vars := PTree.map (fun k '(t, a) => (t, f k a)) (vars sf) |}.
  Proof.
    intros.
    constructor. simpl. auto.
    - intros. simpl.
      split.
      + intro A; inv A. inv H1. rewrite H3 in H5.
        inv H5.
        econstructor.
        rewrite PTree.gmap. setoid_rewrite H3. simpl. reflexivity.
        eapply SPEC. eapply FWT. eapply wf_sf_wt.  apply H. eauto.
        rewrite <- SPEC2; eauto.
      + intro A; inv A. rewrite PTree.gmap in H3. unfold option_map in H3; repeat destr_in H3; inv H3.
        econstructor. eauto. inv H1. setoid_rewrite H3 in Heqo. inv Heqo.
        eapply SPEC in H4. eapply SPEC2; eauto.
        eapply FWT. eapply wf_sf_wt.  apply H. eauto.
    - intros. simpl.
      split; intro A; inv A.
      econstructor. rewrite PTree.gmap; unfold option_map. rewrite H2. eauto.
      rewrite PTree.gmap in H2. unfold option_map in H2; repeat destr_in H2; inv H2.
      econstructor. eauto.
  Qed.

  Lemma simplify_sif_interp_inv:
    forall vvs : PTree.t (type * IRR.sact),
      wt_vvs (Sigma:=Sigma) R vvs ->
      vvs_smaller_variables vvs ->
      forall (a : sact) (v : val),
        interp_sact (sigma:=sigma) REnv r vvs (simplify_sif a) v ->
        forall t : type, wt_sact (Sigma:=Sigma) R vvs a t -> interp_sact (sigma:=sigma) REnv r vvs a v.
  Proof.
    induction a; simpl; intros; eauto.
    - inv H2.
      destr_in H1; auto.
      exploit eval_sact_no_vars_wt.
      2: eauto. eauto. intro A; apply wt_val_bool in A. destruct A. subst.
      econstructor; eauto.
      eapply eval_sact_no_vars_interp; eauto.
    - inv H2; inv H1. econstructor; eauto.
    - inv H2; inv H1. econstructor; eauto.
    - inv H2; inv H1. econstructor; eauto.
  Qed.

  Lemma simplify_sif_interp:
    forall vvs : PTree.t (type * IRR.sact),
    wt_vvs (Sigma:=Sigma) R vvs
    -> vvs_smaller_variables vvs
    -> forall (a : sact) (v : val), interp_sact (sigma:=sigma) REnv r vvs a v
    -> forall t : type, wt_sact (Sigma:=Sigma) R vvs a t
    -> interp_sact (sigma:=sigma) REnv r vvs (simplify_sif a) v.
  Proof.
    induction 3; simpl; intros; try now (econstructor; eauto).
    - inv H1. destr.
      exploit eval_sact_no_vars_wt. 2: eauto. eauto.
      intro A; apply wt_val_bool in A. destruct A. subst.
      eapply simplify_sif_interp_inv; eauto.
      exploit @interp_sact_determ. apply H1_.
      eapply eval_sact_no_vars_interp; eauto.
      intro A; inv A.
      eapply IHinterp_sact2. destr; eauto. destr; eauto.
      econstructor; eauto.
    - inv H3. econstructor; eauto.
    - inv H2. econstructor; eauto.
    - inv H2. econstructor; eauto.
  Qed.

  Lemma sf_eq_simplify_sifs:
    forall sf, wf_sf sf -> sf_eq sf (simplify_sifs_sf sf).
  Proof.
    intros.
    eapply sf_eq_f; eauto.
    - eapply simplify_sif_interp_inv; eauto.
    - intros; eapply simplify_sif_interp; eauto.
    - apply simplify_sif_wt; eauto.
    - eapply simplify_sif_vis.
  Qed.

  Lemma simplify_sifs_sf_interp_cycle_ok:
    forall reg sf,
    wf_sf sf
    -> getenv REnv (interp_cycle (simplify_sifs_sf sf)) reg
    = getenv REnv (interp_cycle sf) reg.
  Proof.
    intros.
    eapply sf_eq_interp_cycle_ok.
    apply wf_simplify_sifs; auto. auto.
    apply sf_eq_sym. apply sf_eq_simplify_sifs. auto.
  Qed.

  Lemma get_field_wt:
    forall vvs struct_sig field field_v struct_sact struct_v
      (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
      (VSV: vvs_smaller_variables vvs),
    wt_sact (Sigma := Sigma) R vvs struct_sact (struct_t struct_sig)
    -> interp_sact (sigma := sigma) REnv r vvs struct_sact struct_v
    -> get_field struct_v field = Some field_v
    -> forall idx, PrimTypeInference.find_field struct_sig field = Success idx
    -> wt_val (field_type struct_sig idx) field_v .
  Proof.
    destruct struct_sig.
    simpl.
    intros field field_v struct_sact struct_v WTVVS VSV WTs ISs GF.
    exploit @interp_sact_wt. 7: eapply ISs. all: eauto. apply vvs_range_max_var. intro WTval.
    clear ISs WTs. inv WTval. simpl in *.
    unfold PrimTypeInference.find_field. simpl. unfold opt_result. intros idx X; repeat destr_in X; inv X.
    revert lv GF H0 idx Heqo.
    induction struct_fields; intros; eauto. easy.
    Opaque eq_dec.
    simpl in *. repeat destr_in GF; inv GF.
    simpl in Heqo. rewrite eq_dec_refl in Heqo. inv Heqo. simpl.
    unfold field_type. simpl. inv H0. auto.
    simpl in Heqo.
    destr_in Heqo; subst; try intuition congruence.
    repeat destr_in Heqo; inv Heqo. simpl.
    inv H0.
    eapply IHstruct_fields; eauto.
  Qed.

  Lemma wt_sact_filter:
    forall
      l (ND: NoDup l) vvs (VSV: vvs_smaller_variables vvs) v (IN: In v l) s t
      (GET: vvs ! v = Some (t, s)) (WT: wt_sact (Sigma := Sigma) R vvs s t)
      (REACH: forall v0, reachable_var vvs s v0 -> In v0 l),
    wt_sact (Sigma := Sigma) R (filter_ptree vvs (PTree.empty _) l) s t.
  Proof.
    intros.
    assert (forall v0, reachable_var vvs (SVar v) v0 -> In v0 l).
    {
      intros v0 RV. inv RV. auto.
      rewrite GET in H0; inv H0. eauto.
    }
    specialize (fun v REACH vvs t2 => filter_ptree_eq _ _ vvs t2 (H v REACH) ND).
    simpl.
    fold (filter_ptree vvs (PTree.empty _) l).
    intros. eapply wt_sact_reachable. 2: eauto.
    intros; apply H0. econstructor; eauto.
    intros; apply PTree.gempty.
  Qed.

  Lemma wt_vvs_filter:
    forall vvs l (ND: NoDup l) (VSV: vvs_smaller_variables vvs),
    wt_vvs (Sigma := Sigma) R vvs
    -> (
      forall
        v t s (IN : In v l) (GET : vvs ! v = Some (t, s)) v0
        (REACH: reachable_var vvs s v0), In v0 l
    )
    -> wt_vvs (Sigma:=Sigma) R (filter_ptree vvs (PTree.empty _) l).
  Proof.
    red; intros vvs l ND VSV WTVVS CLOSED v s t GET.
    apply filter_ptree_inv in GET; auto. rewrite PTree.gempty in GET.
    destruct GET as [GET|(IN & GET)]. inv GET.
    eapply wt_sact_filter; eauto.
    intros; apply PTree.gempty.
  Qed.

  Lemma vsv_filter:
    forall vvs l (ND: NoDup l),
    vvs_smaller_variables vvs
    -> vvs_smaller_variables (filter_ptree vvs (PTree.empty _) l).
  Proof.
    red; intros.
    simpl in *.
    apply filter_ptree_inv in H0.
    destruct H0.
    rewrite PTree.gempty in H0. congruence.
    destruct H0 as (IN & GET).
    eapply H; eauto. auto.
    intros; apply PTree.gempty.
  Qed.

  Lemma wf_sf_filter_ptree sf1 sf2 l
    (ND: NoDup l)
    (CLOSED:
      forall
        v t s (IN : In v l) (GET : (vars sf1) ! v = Some (t, s)) v0
        (REACH: reachable_var (vars sf1) s v0),
        In v0 l)
  : wf_sf sf1 ->
    (forall r k,
      list_assoc (final_values sf2) r = Some k
      -> list_assoc (final_values sf1) r = Some k /\ In k l)
    -> vars sf2 = filter_ptree (vars sf1) (PTree.empty _) l
    -> wf_sf sf2.
  Proof.
    destruct 1; intros.
    constructor.
    - rewrite H0. eapply wt_vvs_filter; eauto.
    - rewrite H0. apply vsv_filter; auto.
    - intros.
      apply H in H1. destruct H1.
      apply wf_sf_final in H1. inv H1.
      econstructor.
      rewrite H0.
      erewrite <- filter_ptree_eq. eauto. auto. auto.
      intros; rewrite PTree.gempty; auto.
  Qed.

  Lemma filter_ptree_correct:
    forall (sf1 sf2: IRR) l lr (ND: NoDup l)
    (CLOSED:
      forall
        v t s (IN : In v l) (GET : (vars sf1) ! v = Some (t, s)) v0
        (REACH: reachable_var (vars sf1) s v0), In v0 l
    ),
    wf_sf sf1 ->
    (forall reg v,
        In reg lr ->
        list_assoc (final_values sf1) reg = Some v ->
        list_assoc (final_values sf2) reg = Some v) ->
    (forall r k,
        list_assoc (final_values sf2) r = Some k ->
        list_assoc (final_values sf1) r = Some k /\ In k l) ->
    vars sf2 = filter_ptree (vars sf1) (PTree.empty _) l ->
    forall reg n,
      list_assoc (final_values sf2) reg = Some n
      -> forall fuel,
        eval_sact (vars sf1) (SVar n) fuel = eval_sact (vars sf2) (SVar n) fuel.
  Proof.
    intros. simpl.
    assert (forall v, reachable_var (vars sf1) (SVar n) v -> In v l).
    {
      intros v RV. inv RV. eapply H1; eauto.
      eapply CLOSED; eauto. eapply H1; eauto.
    }
    assert (
      forall l v (vvs t2: var_value_map),
      In v l
      -> NoDup l
      -> (forall x, In x l -> t2 ! x = None)
      -> vvs ! v = (filter_ptree vvs t2 l) ! v
    ).
    {
      clear.
      induction l; simpl; intros. easy.
      inv H0. destruct H. subst.
      destr.
      rewrite filter_ptree_in. rewrite PTree.gss. auto. auto.
      rewrite filter_ptree_in; auto. symmetry; apply H1. auto.
      rewrite <- IHl. auto. auto. auto. intros.
      destr; eauto. rewrite PTree.gso; eauto. congruence.
    }

    specialize (fun v REACH vvs t2 => H5 _ _ vvs t2 (H4 v REACH) ND).
    rewrite H2.
    apply eval_sact_reachable. intros; apply H5. auto.
    intros; apply PTree.gempty.
  Qed.

  Lemma reachable_filter_inv:
    forall vvs l (ND: NoDup l) v a,
    reachable_var
      (filter_ptree vvs (PTree.empty (type * IRR.sact)) l) a v
    -> reachable_var vvs a v.
  Proof.
    induction 2; simpl; intros; eauto.
    - econstructor.
    - apply filter_ptree_inv in H; auto. rewrite PTree.gempty in H.
      destruct H as [H|[A B]]; [congruence|]. econstructor; eauto.
      intros; apply PTree.gempty.
    - eapply reachable_var_if_cond; eauto.
    - eapply reachable_var_if_true; eauto.
    - eapply reachable_var_if_false; eauto.
    - eapply reachable_var_binop1; eauto.
    - eapply reachable_var_binop2; eauto.
    - eapply reachable_var_unop; eauto.
    - eapply reachable_var_externalCall; eauto.
  Qed.

  Lemma filter_ptree_wt:
    forall
      (sf1 sf2: IRR) l lr (ND: NoDup l)
      (CLOSED:
        forall
          v t s (IN : In v l) (GET : (vars sf1) ! v = Some (t, s)) v0
          (REACH: reachable_var (vars sf1) s v0), In v0 l),
    wf_sf sf1 ->
    (forall reg v,
        In reg lr ->
        list_assoc (final_values sf1) reg = Some v ->
        list_assoc (final_values sf2) reg = Some v) ->
    (forall r k,
        list_assoc (final_values sf2) r = Some k ->
        list_assoc (final_values sf1) r = Some k /\ In k l) ->
    vars sf2 = filter_ptree (vars sf1) (PTree.empty _) l ->
    forall reg n t,
      list_assoc (final_values sf2) reg = Some n
      ->
        wt_sact (Sigma:=Sigma) R (vars sf1) (SVar n) t
        <-> wt_sact (Sigma:=Sigma) R (vars sf2) (SVar n) t.
  Proof.
    intros. simpl.
    assert (forall v, reachable_var (vars sf1) (SVar n) v -> In v l).
    {
      intros v RV. inv RV. eapply H1; eauto.
      eapply CLOSED; eauto. eapply H1; eauto.
    }
    assert (
      forall l v (vvs t2: var_value_map),
      In v l
      -> NoDup l
      -> (forall x, In x l -> t2 ! x = None)
      -> vvs ! v = (filter_ptree vvs t2 l) ! v
    ).
    {
      clear.
      induction l; simpl; intros. easy.
      inv H0. destruct H. subst.
      destr.
      rewrite filter_ptree_in. rewrite PTree.gss. auto. auto.
      rewrite filter_ptree_in; auto. symmetry; apply H1. auto.
      rewrite <- IHl. auto. auto. auto. intros.
      destr; eauto. rewrite PTree.gso; eauto. congruence.
    }

    split; eapply wt_sact_reachable.
    rewrite H2. intros. eapply filter_ptree_eq; eauto.
    intros; apply PTree.gempty.
    rewrite H2. intros. symmetry; eapply filter_ptree_eq; eauto.
    2: intros; apply PTree.gempty.
    inv H6. eapply H1; eauto.
    eapply CLOSED; eauto. 3: eapply reachable_filter_inv; eauto.
    eapply H1; eauto.
    eapply filter_ptree_inv in H8.
    rewrite PTree.gempty in H8. destruct H8 as [|[A B]]. inv H6. eauto. auto.
    intros; apply PTree.gempty.
  Qed.

  Lemma sf_eqr_filter sf1 sf2 lr l
    (ND: NoDup l)
    (CLOSED: forall v t s
                    (IN : In v l)
                    (GET : (vars sf1) ! v = Some (t, s))
                    v0
                    (REACH: reachable_var (vars sf1) s v0), In v0 l):
    wf_sf sf1 ->
    (forall reg,
        In reg lr ->
        list_assoc (final_values sf1) reg =
        list_assoc (final_values sf2) reg) ->
    (forall r k,
        list_assoc (final_values sf2) r = Some k ->
        list_assoc (final_values sf1) r = Some k /\ In k l) ->
    vars sf2 = filter_ptree (vars sf1) (PTree.empty _) l ->
    sf_eq_restricted lr sf1 sf2.
  Proof.
    intros WF SELECT1 SELECT2 VARS. constructor; auto.
    - intros. inversion H1. subst.
      eapply interp_eval_iff. apply WF.
      rewrite VARS. apply vsv_filter; auto. apply WF. eauto.
      econstructor.
      rewrite VARS.
      rewrite <- filter_ptree_eq. eauto.  eapply SELECT2.  eauto. auto.
      intros; rewrite PTree.gempty. auto.
      exists O; intros; eapply filter_ptree_correct; eauto.
      intros. rewrite <- SELECT1. eauto. eauto.
    - intros; eapply filter_ptree_wt; eauto.
      intros. rewrite <- SELECT1. eauto. eauto.
  Qed.

  Lemma sf_eqr_apply:
    forall
      F1 l1 l2 (F1OK: forall sf, wf_sf sf -> sf_eq_restricted l1 sf (F1 sf))
      sf1 sf2,
    wf_sf sf1 -> wf_sf sf2 ->
    sf_eq_restricted l2 sf1 sf2 ->
    forall l3, incl l3 l1 -> incl l3 l2 ->
    sf_eq_restricted l3 (F1 sf1) (F1 sf2).
  Proof.
    intros.
    destruct (F1OK _ H), (F1OK _ H0), H1.
    constructor.
    - intros; eauto.
      rewrite <- sf_eqr_final0; auto.
      rewrite <- sf_eqr_final1; auto.
    - intros.
      rewrite <- sf_eqr_vars0; eauto.
      rewrite <- sf_eqr_vars1; eauto. eapply sf_eqr_vars2; eauto.
      erewrite sf_eqr_final1; eauto.
      eapply sf_eqr_wt0; eauto.
      rewrite <- sf_eqr_final0; eauto.
      rewrite sf_eqr_final2; eauto.
      rewrite sf_eqr_final1; eauto. eauto.
      eapply sf_eqr_wt2; eauto.
      rewrite sf_eqr_final1; eauto.
      eapply sf_eqr_wt0; eauto.
      rewrite <- sf_eqr_final0; eauto.
      rewrite sf_eqr_final2; eauto.
      rewrite sf_eqr_final1; eauto.
      eauto.
      rewrite <- sf_eqr_final0; eauto.
      rewrite sf_eqr_final2; eauto.
      rewrite sf_eqr_final1; eauto.
      eapply sf_eqr_wt0; eauto.
      rewrite <- sf_eqr_final0; eauto.
      rewrite sf_eqr_final2; eauto.
      rewrite sf_eqr_final1; eauto.
    - intros.
      rewrite <- sf_eqr_wt0; eauto.
      rewrite <- sf_eqr_wt1; eauto.
      eapply sf_eqr_wt2; eauto.
      rewrite sf_eqr_final1; eauto.
      rewrite <- sf_eqr_final0; eauto.
      rewrite sf_eqr_final2; eauto.
      rewrite sf_eqr_final1; eauto.
  Qed.

  Lemma sf_eqr_apply':
    forall F1 l (F1OK: forall sf, wf_sf sf -> sf_eq_restricted l sf (F1 sf)),
      forall sf1 sf2,
        wf_sf sf1 -> wf_sf sf2 ->
        sf_eq_restricted l sf1 sf2 ->
        sf_eq_restricted l (F1 sf1) (F1 sf2).
  Proof.
    intros.
    eapply sf_eqr_apply; eauto.
    red; auto. red; auto.
  Qed.

  Lemma sf_eqr_incl:
    forall l1 l2 sf1 sf2,
    sf_eq_restricted l1 sf1 sf2
    -> incl l2 l1
    -> sf_eq_restricted l2 sf1 sf2.
  Proof. intros. inv H. constructor; eauto. Qed.

  Lemma sf_eqr_interp_cycle_ok:
    forall l sf1 sf2,
      wf_sf sf1 -> wf_sf sf2 ->
      sf_eq_restricted l sf1 sf2 ->
      forall reg, In reg l ->
    getenv REnv (interp_cycle sf1) reg
    = getenv REnv (interp_cycle sf2) reg.
  Proof.
    intros.
    unfold interp_cycle. simpl.
    rewrite ! getenv_create.
    erewrite sf_eqr_final; eauto.
    destr.
    erewrite inlining_pass_sf_eqr. reflexivity. 4: apply H2.
    2: apply wf_sf_remove_vars; eauto.
    2: apply wf_sf_remove_vars; eauto.
    eapply sf_eqr_apply; eauto.
    intros; eapply sf_eq_is_restricted.
    apply sf_eq_remove_vars. auto. red; intros.
    eapply nth_error_In, finite_surjective.
    red; auto. simpl.
    erewrite sf_eqr_final; eauto.
  Qed.

  Lemma vsv_f_reachable:
    forall
      f vvs
      (FSPEC: forall s v', var_in_sact (f s) v' -> reachable_var vvs s v'),
    vvs_smaller_variables (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) vvs
    -> vvs_smaller_variables
         (reg_t:=reg_t) (ext_fn_t:=ext_fn_t)
         (PTree.map (fun _ '(t,a) => (t, f a)) vvs).
  Proof.
    red; intros.
    rewrite Maps.PTree.gmap in H0. unfold option_map in H0.
    repeat destr_in H0; inv H0.
    eapply FSPEC in H1.
    eapply reachable_var_aux_below. 3: eauto. auto.
    intros; eapply H; eauto.
  Qed.

  Lemma vsv_f_reachablei:
    forall
      f vvs
      (FSPEC: forall k s v', var_in_sact (f k s) v' -> reachable_var vvs s v'),
    vvs_smaller_variables (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) vvs
    -> vvs_smaller_variables
         (reg_t:=reg_t) (ext_fn_t:=ext_fn_t)
         (PTree.map (fun k '(t,a) => (t, f k a)) vvs).
  Proof.
    red; intros.
    rewrite Maps.PTree.gmap in H0. unfold option_map in H0.
    repeat destr_in H0; inv H0.
    eapply FSPEC in H1.
    eapply reachable_var_aux_below. 3: eauto. auto.
    intros; eapply H; eauto.
  Qed.

  Lemma f_wtvvs_ok'':
    forall f vvs (FSPEC: forall a t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
               wt_sact (Sigma := Sigma) R vvs (f a) t)
           (WTVVS: wt_vvs (Sigma := Sigma) R vvs),
    wt_vvs (Sigma := Sigma) R (PTree.map (fun _ '(t,a) => (t, f a)) vvs).
  Proof.
    intros. unfold wt_vvs. intros.
    apply f_wt_sact_ok'.
    rewrite Maps.PTree.gmap in H. unfold option_map in H.
    repeat destr_in H; inv H. apply FSPEC; eauto.
  Qed.

  Lemma f_wtvvs_ok''i:
    forall f vvs (FSPEC: forall k a t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
               wt_sact (Sigma := Sigma) R vvs (f k a) t)
           (WTVVS: wt_vvs (Sigma := Sigma) R vvs),
    wt_vvs (Sigma := Sigma) R (PTree.map (fun k '(t,a) => (t, f k a)) vvs).
  Proof.
    intros. unfold wt_vvs. intros.
    apply f_wt_sact_ok'i.
    rewrite Maps.PTree.gmap in H. unfold option_map in H.
    repeat destr_in H; inv H. apply FSPEC; eauto.
  Qed.

  Lemma wf_f_reachable:
    forall
      sf f
      (FWT:
        forall a t (WTS: wt_sact (Sigma := Sigma) R (vars sf) a t),
        wt_sact (Sigma := Sigma) R (vars sf) (f a) t)
      (FVIS: forall s v', var_in_sact (f s) v' -> reachable_var (vars sf) s v'),
    wf_sf sf
    -> wf_sf {|
         final_values := final_values sf;
         read1_values := read1_values sf;
         debug_log := debug_log sf;
         vars := PTree.map (fun _ '(t,a) => (t, f a)) (vars sf)
       |}.
  Proof.
    destruct 3; constructor.
    - eapply f_wtvvs_ok''; eauto.
    - eapply vsv_f_reachable; eauto.
    - simpl. intros. eapply f_wt_sact_ok'. eauto.
  Qed.

  Lemma wf_f_reachablei:
    forall
      sf f
      (FWT:
        forall k a t (WTS: wt_sact (Sigma := Sigma) R (vars sf) a t),
        wt_sact (Sigma := Sigma) R (vars sf) (f k a) t)
      (FVIS: forall k s v', var_in_sact (f k s) v' -> reachable_var (vars sf) s v'),
    wf_sf sf
    -> wf_sf {|
         final_values := final_values sf;
         read1_values := read1_values sf;
         debug_log := debug_log sf;
         vars := PTree.map (fun k '(t,a) => (t, f k a)) (vars sf)
    |}.
  Proof.
    destruct 3; constructor.
    - eapply f_wtvvs_ok''i; eauto.
    - eapply vsv_f_reachablei; eauto.
    - simpl. intros. eapply f_wt_sact_ok'i. eauto.
  Qed.

  Lemma var_in_sact_reachable:
    forall vvs a v,
    var_in_sact a v
    -> reachable_var (reg_t := reg_t) (ext_fn_t := ext_fn_t) vvs a v.
  Proof. induction 1; simpl; intros; try now (econstructor; eauto). Qed.

  Lemma pos_strong_ind:
    forall (P: positive -> Prop),
    (forall p, (forall n, Pos.lt n p -> P n) -> P p)
    -> forall n m, Pos.le m n -> P m.
  Proof.
    intros.
    generalize (strong_ind_type (fun n => P (Pos.of_nat (S n)))). intro.
    replace m with (Pos.of_nat (S (pred (Pos.to_nat m)))).
    eapply H1.
    intros. apply H.
    intros.
    assert (n1 = Pos.of_nat (S (pred (Pos.to_nat n1)))).
    erewrite Nat.lt_succ_pred. rewrite Pnat.Pos2Nat.id. auto.
    instantiate (1:=0); lia. rewrite H4.
    apply H2. lia.
    instantiate (1:=pred (Pos.to_nat n)). lia.
    erewrite Nat.lt_succ_pred. rewrite Pnat.Pos2Nat.id. auto.
    instantiate (1:=0); lia.
  Qed.

  Lemma sf_eq_restricted_trans:
    forall l1 l2 l3 sf1 sf2 sf3,
    sf_eq_restricted l1 sf1 sf2
    -> sf_eq_restricted l2 sf2 sf3
    -> incl l3 l1
    -> incl l3 l2
    -> sf_eq_restricted l3 sf1 sf3.
  Proof.
    intros.
    destruct H, H0.
    constructor.
    - intros.
      rewrite sf_eqr_final0; auto.
    - intros. rewrite sf_eqr_vars0; eauto.
      rewrite sf_eqr_vars1; eauto. tauto.
      eapply sf_eqr_wt0; eauto.
      rewrite sf_eqr_final1; eauto.
      rewrite sf_eqr_final1; eauto.
    - intros.
      rewrite sf_eqr_wt0; eauto.
      rewrite sf_eqr_final1; eauto.
  Qed.

  Lemma sf_eq_sf_eq_restricted_trans:
    forall l sf1 sf2 sf3,
    sf_eq sf1 sf2
    -> sf_eq_restricted l sf2 sf3
    -> sf_eq_restricted l sf1 sf3.
  Proof.
    intros. eapply sf_eq_restricted_trans.
    eapply sf_eq_is_restricted. eauto. eauto.
    red; intros. eapply nth_error_In. apply finite_surjective.
    red; tauto.
  Qed.

  Lemma take_drop'_firstn_skipn:
    forall {A:Type} n (l: list A),
    take_drop' n l = (List.firstn n l, List.skipn n l).
  Proof. reflexivity. Qed.

  Lemma skipn_add:
    forall {A: Type} n2 n1 (l: list A),
    skipn n1 (skipn n2 l) = skipn (n1 + n2) l.
  Proof.
    induction n2; simpl; intros; eauto.
    rewrite Nat.add_0_r. auto.
    replace (n1 + S n2) with (S (n1 + n2)). simpl.
    destr. rewrite skipn_nil. auto. lia.
  Qed.

  Lemma reachable_vars_aux_stays_in:
    forall fuel e vs n visited,
    In e visited
    -> In
         e (reachable_vars_aux (reg_t := reg_t) (ext_fn_t := ext_fn_t) vs n
         visited fuel).
  Proof.
    induction fuel; eauto; intros.
    simpl. destruct (in_dec Pos.eq_dec n visited); eauto.
    destruct (vs ! n); eapply in_cons; eauto.
    destruct p. eapply fold_left_induction; eauto.
  Qed.

  Lemma inlining_no_vars:
    forall reg_id sf (WF: wf_sf sf) t a y k,
    list_assoc (final_values sf) k = Some reg_id
    -> (vars sf) ! reg_id = Some (t,a)
    -> eval_sact_no_vars a = Some y
    -> list_assoc (inlining_pass sf) reg_id = Some y.
  Proof.
    intros.
    exploit inlining_pass_correct. reflexivity. apply WF. apply WF.
    intros (ND & SPEC).
    eapply in_list_assoc. auto. eapply SPEC. eauto.
    econstructor. rewrite H0. eauto.
    eapply eval_sact_no_vars_interp; eauto.
  Qed.

  Lemma getenv_interp:
    forall reg reg_id reg_act x sf (WF: wf_sf sf)
      (REG_ID: list_assoc (final_values sf) reg = Some reg_id)
      (REG_ACT: Maps.PTree.get reg_id (vars sf) = Some reg_act)
      (EVAL_DETERMINED: eval_sact_no_vars (snd reg_act) = Some x),
    getenv REnv (interp_cycle sf) reg = x.
  Proof.
    intros.
    unfold interp_cycle.
    rewrite getenv_create.
    simpl.
    rewrite REG_ID. destruct reg_act.
    (* remove_vars removes the variables that are not in useful_vars *)
    assert (In reg_id (useful_vars sf)). {
      eapply useful_vars_incl. apply WF. auto.
      apply list_assoc_in in REG_ID.
      apply in_map with (f:=snd) in REG_ID. eauto.
    }
    (* remove_vars keeps an association to reg_id *)
    erewrite <- inlining_pass_sf_eq.
    2: apply sf_eq_remove_vars; auto. 2: auto.
    2: apply wf_sf_remove_vars; auto. 2: eauto.
    (* inlining_pass does not impact the result of list_assoc in our case *)
    erewrite inlining_no_vars; eauto.
  Qed.
End Operations.
