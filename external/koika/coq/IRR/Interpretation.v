Require Import Koika.Utils.Environments.
Require Import Koika.IRR.IRR.
Require Import Koika.KoikaForm.TypeInference.
Require Import Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.Desugaring.DesugaredSyntax.
Require Import Koika.BitsToLists.
Require Import Sact.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Mergesort.
Require Import Maps.
Require Import SimpleVal.

Module PosOrder <: Orders.TotalLeBool.
  Definition t := positive.
  Definition leb x y := Pos.leb x y.
  Infix "<=?" := leb (at level 70, no associativity).
  Theorem leb_total : forall a1 a2, is_true (a1 <=? a2) \/ is_true (a2 <=? a1).
  Proof.
    intros.
    generalize (Pos.leb_spec a1 a2).
    generalize (Pos.leb_spec a2 a1).
    unfold leb.
    intros A B. inv A; inv B; try lia; auto.
  Qed.
End PosOrder.

Module Import PosSort := Sort PosOrder.

Section Interpretation.
  Context {pos_t reg_t ext_fn_t rule_name_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {ext_fn_t_eq_dec: EqDec ext_fn_t}.
  Context {REnv: Env reg_t}.

  Context (R: reg_t -> type).
  Context (Sigma: ext_fn_t -> ExternalSignature).

  Definition uact := @daction pos_t string string reg_t ext_fn_t.
  Definition schedule := scheduler pos_t rule_name_t.
  Definition ext_funs_defs :=
    forall f: ext_fn_t, val -> val.
  Definition UREnv := REnv.(env_t) (fun _ => val).

  Context (r: UREnv).
  Context (sigma: ext_funs_defs).

  Definition sact := sact (ext_fn_t:=ext_fn_t) (reg_t:=reg_t).

  Fixpoint vars_in_sact (s: sact) : list positive :=
    match s with
    | SConst _ => []
    | SReg _ => []
    | SVar v => [v]
    | SExternalCall _ a
    | SUnop _ a => vars_in_sact a
    | SBinop _ a1 a2 => vars_in_sact a1 ++ vars_in_sact a2
    | SIf c t f => vars_in_sact c ++ vars_in_sact t ++ vars_in_sact f
    end.

  Fixpoint reachable_vars_aux
    (vvs: var_value_map) (n: positive) (visited: list positive) fuel
  :=
    match fuel with
    | O => visited
    | S fuel =>
        if in_dec Pos.eq_dec n visited then visited
        else
          n::
            match vvs ! n with
            | None => visited
            | Some (_, s) =>
              fold_left
                (fun visited n => reachable_vars_aux vvs n visited fuel)
                (vars_in_sact s) visited
            end
    end.

  Inductive reachable_var (vvs: var_value_map) : sact -> positive -> Prop :=
  | reachable_var_var: forall n, reachable_var vvs (SVar n) n
  | reachable_var_in_var:
    forall n x t a, vvs ! x = Some (t, a)
    -> reachable_var vvs a n
    -> reachable_var vvs (SVar x) n
  | reachable_var_if_cond:
    forall n c t f, reachable_var vvs c n -> reachable_var vvs (SIf c t f) n
  | reachable_var_if_true:
    forall n c t f, reachable_var vvs t n -> reachable_var vvs (SIf c t f) n
  | reachable_var_if_false:
    forall n c t f, reachable_var vvs f n -> reachable_var vvs (SIf c t f) n
  | reachable_var_binop1:
    forall n c a1 a2,
    reachable_var vvs a1 n -> reachable_var vvs (SBinop c a1 a2) n
  | reachable_var_binop2:
    forall n c a1 a2,
    reachable_var vvs a2 n -> reachable_var vvs (SBinop c a1 a2) n
  | reachable_var_unop:
    forall n c a1, reachable_var vvs a1 n -> reachable_var vvs (SUnop c a1) n
  | reachable_var_externalCall:
    forall n c a1,
    reachable_var vvs a1 n -> reachable_var vvs (SExternalCall c a1) n.

  Lemma reachable_vars_aux_incr:
    forall vvs fuel n visited,
    incl visited (reachable_vars_aux vvs n visited fuel).
  Proof.
    induction fuel; simpl; intros; eauto.
    apply incl_refl.
    destr. destr.
    - destr. apply incl_tl.
      apply fold_left_induction. apply incl_refl.
      intros. eapply incl_tran. apply H0. apply IHfuel.
    - apply incl_tl, incl_refl.
  Qed.

  Lemma reachable_var_aux_below:
    forall vvs (VSV: vvs_smaller_variables vvs) a n
      (GET: forall v, var_in_sact a v -> (v < n)%positive) v
      (RV: reachable_var vvs a v),
    (v < n)%positive.
  Proof.
    intros vvs VSV a n.
    change n with (projT1 (existT (fun _ => sact) n a)).
    change a with (projT2 (existT (fun _ => sact) n a)) at 1 3.
    generalize (existT (fun _ => sact) n a).
    clear n a. intro s. pattern s.
    eapply well_founded_induction.
    apply wf_order_sact. clear s.
    intros x IH BELOW v RV.
    destruct x; simpl in *.
    inv RV.
    - eapply BELOW. constructor.
    - eapply VSV in H.
      exploit (IH (existT _ x0 a)). constructor. apply BELOW. constructor.
      simpl. apply H. simpl. eauto. simpl.
      trim (BELOW x0). constructor.  lia.
    - eapply (IH (existT _ x c)). constructor 2. simpl; lia.
      simpl. intros v0 VIS. eapply BELOW.
      eapply var_in_if_cond; eauto. simpl; auto.
    - eapply (IH (existT _ x t)). constructor 2. simpl; lia.
      simpl. intros v0 VIS. eapply BELOW.
      eapply var_in_if_true; eauto. simpl; auto.
    - eapply (IH (existT _ x f)). constructor 2. simpl; lia.
      simpl. intros v0 VIS. eapply BELOW.
      eapply var_in_if_false; eauto. simpl; auto.
    - eapply (IH (existT _ x a1)). constructor 2. simpl; lia.
      simpl. intros v0 VIS. eapply BELOW.
      eapply var_in_sact_binop_1; eauto. simpl; auto.
    - eapply (IH (existT _ x a2)). constructor 2. simpl; lia.
      simpl. intros v0 VIS. eapply BELOW.
      eapply var_in_sact_binop_2; eauto. simpl; auto.
    - eapply (IH (existT _ x a1)). constructor 2. simpl; lia.
      simpl. intros v0 VIS. eapply BELOW.
      eapply var_in_sact_unop; eauto. simpl; auto.
    - eapply (IH (existT _ x a1)). constructor 2. simpl; lia.
      simpl. intros v0 VIS. eapply BELOW.
      eapply var_in_sact_external; eauto. simpl; auto.
  Qed.

  Lemma reachable_var_aux_below_get:
    forall vvs (VSV: vvs_smaller_variables vvs) a n t
      (GET: vvs ! n = Some (t,a)) v (RV: reachable_var vvs a v),
    (v < n)%positive.
  Proof.
    intros; eapply reachable_var_aux_below; eauto.
    eapply VSV. eauto.
  Qed.

  Lemma reachable_inv:
    forall vvs a v, reachable_var vvs a v
    -> exists v',
     var_in_sact a v'
     /\ (
       v = v'
       \/ exists t' a', vvs ! v' = Some (t', a') /\ reachable_var vvs a' v
     ).
  Proof.
    induction 1; simpl; intros; eauto.
    - exists n. split. constructor. left; auto.
    - destruct IHreachable_var as (v'& VIS & OTHER).
      exists x; split. constructor.
      destruct OTHER as [EQ | (t' & a' & GET & RV)]. subst.
      right; eauto.
      right; exists t, a; split. eauto. eauto.
    - destruct IHreachable_var as (v'& VIS & OTHER).
      exists v'; split. eapply var_in_if_cond. auto.
      destruct OTHER as [EQ | (t' & a' & GET & RV)]; auto. right. eauto.
    - destruct IHreachable_var as (v'& VIS & OTHER).
      exists v'; split. eapply var_in_if_true. auto.
      destruct OTHER as [EQ | (t' & a' & GET & RV)]; auto. right. eauto.
    - destruct IHreachable_var as (v'& VIS & OTHER).
      exists v'; split. eapply var_in_if_false. auto.
      destruct OTHER as [EQ | (t' & a' & GET & RV)]; auto. right. eauto.
    - destruct IHreachable_var as (v'& VIS & OTHER).
      exists v'; split. eapply var_in_sact_binop_1. auto.
      destruct OTHER as [EQ | (t' & a' & GET & RV)]; auto. right. eauto.
    - destruct IHreachable_var as (v'& VIS & OTHER).
      exists v'; split. eapply var_in_sact_binop_2. auto.
      destruct OTHER as [EQ | (t' & a' & GET & RV)]; auto. right. eauto.
    - destruct IHreachable_var as (v'& VIS & OTHER).
      exists v'; split. eapply var_in_sact_unop. auto.
      destruct OTHER as [EQ | (t' & a' & GET & RV)]; auto. right. eauto.
    - destruct IHreachable_var as (v'& VIS & OTHER).
      exists v'; split. eapply var_in_sact_external. auto.
      destruct OTHER as [EQ | (t' & a' & GET & RV)]; auto. right. eauto.
  Qed.

  Lemma var_in_sact_ok: forall a v, var_in_sact a v -> In v (vars_in_sact a).
  Proof.
    induction 1; simpl; intros; eauto.
    rewrite ! in_app_iff; now eauto.
    rewrite ! in_app_iff; now eauto.
    rewrite ! in_app_iff; now eauto.
    rewrite ! in_app_iff; now eauto.
    rewrite ! in_app_iff; now eauto.
  Qed.

  Lemma var_in_sact_ok_inv:
    forall a v, In v (vars_in_sact a) -> var_in_sact a v.
  Proof.
    induction a; simpl; intros; eauto; intuition.
    - subst. constructor.
    - rewrite ! in_app_iff in H. intuition.
      econstructor; eauto.
      eapply var_in_if_true; eauto.
      eapply var_in_if_false; eauto.
    - econstructor; eauto.
    - rewrite ! in_app_iff in H. intuition.
      eapply var_in_sact_binop_1; eauto.
      eapply var_in_sact_binop_2; eauto.
    - econstructor; eauto.
  Qed.

  Lemma rev_sym: forall {A: Type} (l1 l2: list A), l1 = rev l2 <-> rev l1 = l2.
  Proof.
    split; intro.
    - rewrite H. rewrite rev_involutive. easy.
    - rewrite <- H. rewrite rev_involutive. easy.
  Qed.

  Lemma app_inv_last:
    forall {A: Type} (l1 l2: list A) (x y: A),
    l1 ++ [x] = l2 ++ [y] -> x = y.
  Proof.
    intros.
    apply (f_equal (@rev A)) in H.
    rewrite rev_app_distr in H. rewrite rev_app_distr in H at 1.
    simpl in H. inv H.
    easy.
  Qed.

  Lemma fold_left_prop_eventually_no_tail:
    forall {A B: Type} (P: B -> Prop) (f: B -> A -> B) (lb: list A) (s: B) x,
    (forall e, P (f e x)) -> P (fold_left f (lb ++ [x]) s).
  Proof.
    intros.
    assert (exists l', l' = rev (lb ++ [x])).
    { exists (rev (lb ++ [x])). easy. }
    destruct H0.
    apply rev_sym in H0.
    rewrite <- H0.
    induction x0.
    - destruct lb; easy.
    - rewrite <- fold_left_rev_right. rewrite rev_involutive.
      assert (x = a). { simpl in H0. apply app_inv_last in H0. easy. }
      simpl. inv H1. eapply H.
  Qed.

  Lemma fold_left_prop_eventually:
    forall {A B: Type} (P: B -> Prop) (f: B -> A -> B) (lb la: list A) (s: B) x,
    (forall e, P (f e x))
    -> (forall y e, In y la -> P e -> P (f e y))
    -> P (fold_left f (lb ++ [x] ++ la) s).
  Proof.
    intros A B P f0 lb la s x H0.
    remember (rev la) as la'. apply rev_sym in Heqla'. rewrite <- Heqla'.
    generalize dependent la.
    induction la'; intros; simpl.
    - apply fold_left_prop_eventually_no_tail. easy.
    - rewrite <- fold_left_rev_right.
      repeat (rewrite rev_app_distr; simpl). rewrite rev_involutive.
      apply H.
      + apply in_rev. rewrite rev_involutive. left. easy.
      + assert ((la' ++ [x]) ++ rev lb = rev (lb ++ [x] ++ rev la')).
        { repeat (rewrite rev_app_distr). rewrite rev_involutive. easy. }
        rewrite H1.
        rewrite fold_left_rev_right.
        eapply IHla'.
        * eauto.
        * intros. apply H.
          ** apply in_rev. rewrite rev_involutive.
             apply in_rev in H2. right. easy.
          ** easy.
  Qed.

  Lemma reachable_vars_aux_in:
    forall vvs fuel visited n,
    (fuel > 0)%nat -> In n (reachable_vars_aux vvs n visited fuel).
  Proof.
    destruct fuel. lia. intros. simpl. destr. destr. destr.
    left; auto. left; auto.
  Qed.

  Lemma fold_left_ev:
    forall {A B: Type} (P: A -> Prop) (I: A -> Prop) (f: A -> B -> A)
      l (INV: forall acc y, In y l -> I acc -> I (f acc y))
      (PRESERVES: forall acc y, In y l -> I acc -> P acc -> P (f acc y)) acc,
    I acc
    -> (P acc \/ exists x, In x l /\ forall acc, I acc -> P (f acc x))
    -> P (fold_left f l acc).
  Proof.
    induction l; simpl; intros; eauto. destruct H0 as [|(? & [] & ?)]. auto.
    destruct H0 as [Pacc|(x & EQIN & Pf)].
    apply IHl. eauto. eauto. eauto. left; apply PRESERVES; auto.
    apply IHl. eauto. eauto. eauto. destruct EQIN. subst; left; auto.
    right; eauto.
  Qed.

  Lemma reachable_vars_aux_inv:
    forall vvs (VSV: vvs_smaller_variables vvs) fuel n visited l,
    reachable_vars_aux vvs n visited fuel = l
    -> forall v, In v l
    -> In v visited
    \/ v = n
    \/ exists t a, vvs !n = Some (t, a) /\ reachable_var vvs a v.
  Proof.
    induction fuel; simpl; intros; eauto.
    subst. auto.
    subst. destr_in H0. auto.
    destruct H0 as [EQ|IN]. auto.
    destr_in IN; auto. destr_in IN.
    destruct (in_dec Pos.eq_dec v visited); auto.
    right.
    cut (
      exists vv, In vv (vars_in_sact s)
      /\ exists vis, ~In v vis /\ In v (reachable_vars_aux vvs vv vis fuel)).
    intros (vv & IN' & vis & INCL & INv).
    edestruct (IHfuel _ _ _ eq_refl _ INv) as [Invis | [EQ | PROP]].
    congruence. subst.
    Lemma reachable_vars_in_sact:
      forall vvs vv s, In vv (vars_in_sact s) -> reachable_var vvs s vv.
    Proof.
      intros. apply var_in_sact_ok_inv in H.
      revert vv s H.
      induction 1; simpl; intros; eauto.
      constructor.
      eapply reachable_var_if_cond; eauto.
      eapply reachable_var_if_true; eauto.
      eapply reachable_var_if_false; eauto.
      eapply reachable_var_unop; eauto.
      eapply reachable_var_binop1; eauto.
      eapply reachable_var_binop2; eauto.
      eapply reachable_var_externalCall; eauto.
    Qed.
    right; do 2 eexists; split; eauto using reachable_vars_in_sact.
    destruct PROP as (?t & ?a & GET & RV).
    right. do 2 eexists; split; eauto.

    Lemma reachable_vars_in_sact2:
      forall vvs vv s, var_in_sact s vv
      -> forall t a, vvs ! vv = Some (t, a)
      -> forall v2, reachable_var vvs a v2
      -> reachable_var vvs s v2.
    Proof.
      induction 1; simpl; intros; eauto.
      econstructor; eauto.
      eapply reachable_var_if_cond; eauto.
      eapply reachable_var_if_true; eauto.
      eapply reachable_var_if_false; eauto.
      eapply reachable_var_unop; eauto.
      eapply reachable_var_binop1; eauto.
      eapply reachable_var_binop2; eauto.
      eapply reachable_var_externalCall; eauto.
    Qed.
    eapply reachable_vars_in_sact2; eauto.
    apply var_in_sact_ok_inv; auto.
    Lemma fold_left_prop_inv:
      forall {A B: Type} (f: A -> B -> A) (P: A -> Prop)
        (PRES: forall acc x, P acc -> P (f acc x))
        (Pdec: forall acc, {P acc} + {~ P acc}) (l: list B) acc,
      P (fold_left f l acc)
      -> ~ P acc
      -> exists x acc, In x l /\ ~ P acc /\ P (f acc x).
    Proof.
      induction l; simpl; intros; eauto. congruence.
      destruct (Pdec (f acc a)).
      exists a, acc; split; eauto.
      apply IHl in H; auto.
      destruct H as (x & ?acc & IN & NP & PF).
      exists x, acc0; split; eauto.
    Qed.
    edestruct @fold_left_prop_inv as (x & acc & INN & NP & PACC). 3: apply IN.
    simpl; intros. eapply reachable_vars_aux_incr; eauto.
    apply in_dec. apply Pos.eq_dec.
    auto.
    exists x; split; auto. simpl in PACC. eauto.
  Qed.

  Lemma reachable_vars_aux_nd:
    forall vvs (VSV: vvs_smaller_variables vvs) fuel n visited l,
    reachable_vars_aux vvs n visited fuel = l
    -> forall (ND: NoDup visited), NoDup l.
  Proof.
    induction fuel; simpl; intros; eauto. subst; auto.
    destr_in H.
    subst. auto. subst.
    constructor.
    - destr. destr.
      intro IN.
      edestruct @fold_left_prop_inv as (x & acc & INN & NP & PACC). 3: apply IN.
      simpl; intros. eapply reachable_vars_aux_incr; eauto.
      apply in_dec. apply Pos.eq_dec.
      auto. simpl in PACC.
      edestruct reachable_vars_aux_inv as [INv | [EQv | PROP]]. eauto. eauto.
      apply PACC. congruence. subst.
      exploit VSV. apply Heqo. apply var_in_sact_ok_inv. apply INN.
      unfold var_lt. lia.
      destruct PROP as (? & ? & GET & REACH).
      eapply reachable_var_aux_below in REACH. 3: eapply VSV; eauto.
      exploit VSV. apply Heqo. apply var_in_sact_ok_inv. apply INN.
      unfold var_lt. lia.
      auto.
    - repeat destr.
      eapply fold_left_induction. auto. intros. eapply IHfuel; eauto.
  Qed.

  Lemma reachable_vars_aux_ok:
    forall vvs (VSV: vvs_smaller_variables vvs) fuel n visited l,
    reachable_vars_aux vvs n visited fuel = l
    -> (forall n, In n visited
        -> forall v t a, vvs ! n = Some (t, a)
        -> reachable_var vvs a v
        -> In v visited)
    -> ((Pos.to_nat n<fuel)%nat)
    -> forall n1 (IN: In n1 l) v t a, vvs ! n1 = Some (t, a)
    -> reachable_var vvs a v
    -> In v l.
  Proof.
    induction fuel; simpl; intros; eauto. lia.
    destr_in H. subst. eauto.
    subst.
    destruct IN as [EQ|IN].
      + subst. rewrite H2.
        right.
        cut (
          exists vv, In vv (vars_in_sact a)
          /\ forall vis,
             (forall n : positive, In n vis
              -> forall (v0 : positive) (t0 : type) (a0 : IRR.sact),
              vvs ! n = Some (t0, a0)
              -> reachable_var vvs a0 v0
              -> In v0 vis)
              -> In v (reachable_vars_aux vvs vv vis fuel)).
        intros (vv & IN & REACH).
        eapply fold_left_ev with (
          I := fun vis =>
            forall n : positive, In n vis
            -> forall (v0 : positive) (t0 : type) (a0 : IRR.sact),
            vvs ! n = Some (t0, a0)
            -> reachable_var vvs a0 v0
            -> In v0 vis).
        {
          intros.
          eapply IHfuel. eauto. eauto.
          exploit VSV. apply H2. apply var_in_sact_ok_inv. apply H.
          unfold var_lt. lia. apply H5.
          eauto. eauto.
        }
        { intros. eapply reachable_vars_aux_incr; eauto. }
        eauto.
        right; exists vv; split; eauto.
        destruct (reachable_inv _ _ _ H3) as (v' & VIS & IN).
        apply var_in_sact_ok in VIS.
        eexists; split. apply VIS.
        destruct IN as [EQ|(t' & a' & GET & REACH)].
        subst. intros. eapply reachable_vars_aux_in; eauto. lia.
        intros.
        eapply IHfuel. eauto.
        eauto.
        exploit VSV. apply H2. apply var_in_sact_ok_inv. apply VIS.
        unfold var_lt. lia.
        2: apply GET. eapply reachable_vars_aux_in. lia. auto.
      + destruct (vvs ! n) eqn:?.
        2: { right; eapply H0; eauto. }
        destruct p.
        right.
        revert n1 IN v t a H2 H3.
        pattern (
          fold_left
            (fun (visited0 : list positive) (n2 : positive) =>
              reachable_vars_aux vvs n2 visited0 fuel)
            (vars_in_sact s) visited).
        eapply fold_left_induction. eauto.
        intros. eapply IHfuel; eauto.
        exploit VSV. apply Heqo.
        apply var_in_sact_ok_inv. apply H. unfold var_lt. lia.
  Qed.

  Definition useful_vars (sf: IRR (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (rule_name_t := rule_name_t))
  : list positive :=
    let todo := map snd (final_values sf) in
    fold_left
      (fun visited n =>
        reachable_vars_aux (vars sf) n visited (S (Pos.to_nat n)))
      todo [].

  Lemma useful_vars_ok:
    forall sf (VSV: vvs_smaller_variables (vars sf)) l, useful_vars sf = l
    -> forall n1 (IN: In n1 l) v t a, (vars sf) ! n1 = Some (t, a)
    -> reachable_var (vars sf) a v
    -> In v l.
  Proof.
    intros sf VSV l <-.
    unfold useful_vars.
    pattern ((fold_left
       (fun (visited : list positive) (n : positive) =>
        reachable_vars_aux (vars sf) n visited (S (Pos.to_nat n)))
       (map snd (final_values sf)) []) ).
    apply fold_left_induction. easy.
    intros.
    eapply reachable_vars_aux_ok. 2: eauto. eauto. auto. lia.
    eauto. eauto. eauto.
  Qed.

  Lemma fold_left_prop:
    forall {A B: Type} (P: A -> Prop) (f: A -> B -> A) (l: list B) x acc,
    In x l
    -> (forall a, P (f a x))
    -> (forall a x, P a -> P (f a x))
    -> P (fold_left f l acc).
  Proof.
    intros; eapply fold_left_ev with (I:= fun _ => True). auto. auto. auto.
    right; eexists; split; eauto.
  Qed.

  Lemma useful_vars_incl:
    forall sf (VSV: vvs_smaller_variables (vars sf)) l, useful_vars sf = l
    -> incl (map snd (final_values sf)) l.
  Proof.
    intros sf VSV l <-.
    unfold useful_vars. generalize (map snd (final_values sf)).
    red; intros. eapply fold_left_prop. eauto.
    intros; eapply reachable_vars_aux_in; eauto. lia.
    intros; eapply reachable_vars_aux_incr; eauto.
  Qed.

  Theorem useful_vars_good:
    forall sf (VSV: vvs_smaller_variables (vars sf)) n1,
    In n1 (map snd (final_values sf))
    -> forall v t a, (vars sf) ! n1 = Some (t, a)
    -> reachable_var (vars sf) a v
    -> In v (useful_vars sf).
  Proof.
    intros.
    eapply useful_vars_ok; eauto.
    eapply useful_vars_incl; eauto.
  Qed.

  Definition IRR := IRR (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) (rule_name_t := rule_name_t).

  Fixpoint eval_sact (vars: var_value_map) (a: sact) (fuel: nat) : option val :=
    match fuel with
    | O => None
    | S fuel =>
      match a with
      | SConst v => Some v
      | SVar v =>
        let/opt2 t, vv := vars ! v in
        eval_sact vars vv fuel
      | SIf c t f =>
        let/opt v := eval_sact vars c fuel in
        match v with
        | Bits [b] => if b then eval_sact vars t fuel else eval_sact vars f fuel
        | _ => None
        end
      | SUnop ufn a =>
        let/opt v := eval_sact vars a fuel in
        sigma1 ufn v
      | SBinop ufn a1 a2 =>
        let/opt v1 := eval_sact vars a1 fuel in
        let/opt v2 := eval_sact vars a2 fuel in
        sigma2 ufn v1 v2
      | SExternalCall ufn a =>
        let/opt v := eval_sact vars a fuel in
        Some (sigma ufn v)
      | SReg idx => Some (getenv REnv r idx)
      end
    end.
End Interpretation.
