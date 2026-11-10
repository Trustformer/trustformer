Require Import Coq.Numbers.DecimalString.
Require Import Coq.Program.Equality Coq.Strings.Ascii.
Require Import Koika.Primitives.
Require Import Koika.KoikaForm.Syntax.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.BitsToLists.
Require Import Wt.
Require Import Wellfounded.
Require Import SimpleVal.
Require Export Koika.Utils.Tactics.

(* List utils *)
Fixpoint filter_map {A B: Type} (f: A -> option B) (l: list A) : list B :=
  match l with
    [] => []
  | x::r =>
      match f x with
      | None => filter_map f r
      | Some b => b::filter_map f r
      end
  end.

Lemma filter_map_In:
  forall {A B: Type} (f: A -> option B) l x,
    In x (filter_map f l) <-> (exists y, Some x = f y /\ In y l).
Proof.
  induction l; simpl; intros; eauto. split. tauto. intros (y & _ & []).
  destr; simpl; rewrite IHl.
  - split. intros [C | (y & EQ & IN)]. subst. eexists; split; eauto.
    eexists; split; eauto.
    intros (y & EQ & [IN|IN]); subst. left; congruence. right; eexists; split; eauto.
  - split; intros (y & EQ & IN); eauto.
    destruct IN as [IN|IN]; eauto. congruence.
Qed.

Lemma Forall_list_options:
  forall {A:Type} (P: A -> Prop) l,
    (forall x y,
        In x l ->
        x = Some y ->
        P y
    ) ->
    Forall P (filter_map id l).
Proof.
  intros.
  rewrite Forall_forall. intros.
  rewrite filter_map_In in H0. destruct H0 as (y & EQ & IN). unfold id in EQ. subst.
  eauto.
Qed.

Lemma list_assoc_set_key_in:
  forall {K V: Type} {eq_dec_k: EqDec K} (l: list (K*V)) k v,
    In k (map fst (list_assoc_set l k v)).
Proof.
  induction l; simpl; intros; eauto.
  repeat destr. subst; simpl; auto. simpl; eauto.
Qed.


Lemma list_assoc_set_key_stays_in:
  forall {K V: Type} {eq_dec_k: EqDec K} (l: list (K*V)) k k' v,
    In k (map fst l) ->
    In k (map fst (list_assoc_set l k' v)).
Proof.
  induction l; simpl; intros; eauto.
  repeat destr. subst; simpl; auto. simpl in *; eauto.
  destruct H; auto.
Qed.

Lemma list_assoc_cons:
  forall {K V: Type} {eq_dec_k: EqDec K} (l: list (K*V)) k k' v,
    list_assoc ((k,v)::l) k' =
      if eq_dec k' k then Some v else list_assoc l k'.
Proof.
  reflexivity.
Qed.

Lemma list_assoc_set_not_before:
  forall {K V: Type} {eqdec: EqDec K} (l: list (K * V)) k v k' v' ,
    ~ In k (map fst l) ->
    In (k', v') (list_assoc_set l k v) <-> In (k', v') l \/ (k, v) = (k', v').
Proof.
  induction l; simpl; intros; eauto. tauto.
  repeat destr; simpl in *; subst.
  contradict H. auto.
  rewrite IHl. tauto. tauto.
Qed.

Lemma list_assoc_app : forall {K V: Type} {eqdec: EqDec K} (l1 l2: list (K * V)) k v,
    list_assoc l1 k = Some v ->
    list_assoc (l1 ++ l2) k = Some v.
Proof.
  induction l1; simpl; intros; eauto. easy. repeat destr_in H; eauto.
Qed.

Lemma list_assoc_app_none : forall {K V: Type} {eqdec: EqDec K} (l1 l2: list (K * V)) k,
    list_assoc l1 k = None ->
    list_assoc (l1 ++ l2) k = list_assoc l2 k.
Proof.
  induction l1; simpl; intros; eauto. repeat destr_in H; eauto. easy.
Qed.


Lemma list_assoc_spec: forall {K V} {eqdec: EqDec K} (l: list (K * V)) k k' v,
    list_assoc (list_assoc_set l k v) k' = if eq_dec k k' then Some v else list_assoc l k'.
Proof.
  intros; destr; subst.
  rewrite list_assoc_gss; auto.
  rewrite list_assoc_gso; auto.
Qed.

Lemma list_assoc_app_spec: forall {K V} {eqdec: EqDec K} (l1 l2: list (K * V)) k,
    list_assoc (l1 ++ l2) k =
      match list_assoc l1 k with
      | Some v => Some v
      | None => list_assoc l2 k
      end.
Proof.
  intros; destr; subst.
  eapply list_assoc_app; eauto.
  eapply list_assoc_app_none; eauto.
Qed.

Lemma list_assoc_unknown_key:
  forall {A B: Type} {eqdec: EqDec A} (l: list (A * B)) k,
    ~ In k (map fst l) ->
    list_assoc l k = None.
Proof.
  induction l; simpl; intros; eauto. repeat destr; intuition auto with *.
Qed.

Lemma list_assoc_none_unknown_key:
  forall {A B: Type} {eqdec: EqDec A} (l: list (A * B)) k,
    list_assoc l k = None ->
    ~ In k (map fst l).
Proof.
  induction l; simpl; intros; eauto. repeat destr_in H. easy.
  apply IHl in H. simpl. intuition.
Qed.

Lemma list_assoc_in_keys:
  forall {A B: Type} {eqdec: EqDec A} (l: list (A * B)) k x,
    list_assoc l k = Some x ->
    In k (map fst l).
Proof.
  induction l; simpl; intros; eauto. easy.
  repeat destr_in H; inv H; eauto.
Qed.

Lemma list_assoc_in:
  forall {K V: Type} {eq_dec_k: EqDec K} (l: list (K*V)) k v,
    list_assoc l k = Some v -> In (k,v) l.
Proof.
  induction l; simpl; intros; eauto. easy. repeat destr_in H. inv H. auto. eauto.
Qed.

Lemma in_list_assoc_set_inv:
  forall {K V: Type} {eq_dec: EqDec K} (l: list (K * V)) k' v' k v,
    In (k', v') (list_assoc_set l k v) ->
    (k, v) = (k', v') \/ In (k', v') l.
Proof.
  induction l; simpl; intros; eauto.
  repeat destr_in H; simpl in *; subst.
  destruct H; auto.
  destruct H; auto. apply IHl in H. destruct H; auto.
Qed.

Lemma in_map_list_assoc_set_inv:
  forall {K V: Type} {eqdec: EqDec K} (l : list (K * V)) (k : K)
    (v : V) k' ,
    In k' (map fst (list_assoc_set l k v)) ->
    k = k' \/ In k' (map fst l).
Proof.
  induction l; simpl; intros; eauto. repeat destr_in H. subst. simpl. auto.
  simpl in *. destruct H; auto. apply IHl in H. tauto.
Qed.

Lemma in_keys_list_assoc_ex:
  forall {K V: Type} {eqdec: EqDec K} (l: list (K*V)) k,
    In k (map fst l) ->
    exists v, list_assoc l k = Some v.
Proof.
  induction l; simpl; intros; eauto. easy.
  destruct H. destr. simpl in *. subst. rewrite eq_dec_refl. eauto.
  repeat destr; subst; eauto.
Qed.

Lemma assoc_list_assoc:
  forall {K1 K2: Type} {eqdec: EqDec K1} (l: list (K1 * K2)) k tm,
    assoc k l = Some tm ->
    list_assoc l k = Some (projT1 tm).
Proof.
  induction l; simpl; intros; eauto. inv H.
  repeat destr_in H.
  subst.
  unfold eq_rect_r in H; simpl in H. inv H. simpl. auto.
  inv H. simpl. erewrite IHl; eauto. simpl; auto. inv H.
Qed.

Lemma incl_incl_map:
  forall {A B: Type} (l1 l2: list (A * B))
         (P: forall x y, In (x, y) l1 -> In (x, y) l2),
  forall x, In x (map fst l1) -> In x (map fst l2).
Proof.
  intros.
  rewrite in_map_iff in H.
  destruct H as ((a,b) & EQ & IN). subst.
  apply in_map; auto.
Qed.

Lemma nth_error_lt:
  forall {A: Type} (l: list A) n (LT: n < List.length l),
  exists a, nth_error l n = Some a.
Proof.
  induction l; simpl; intros; eauto. lia.
  destruct n. simpl. eauto.
  simpl. apply IHl. lia.
Qed.

Lemma NoDup_map_In_eq:
  forall {A B: Type} (f: A -> B)
         l
         (ND: NoDup (map f l)) x1 x2
         (IN1: In x1 l)
         (IN2: In x2 l)
         (EQ: f x1 = f x2),
    x1 = x2.
Proof.
  induction l; simpl; intros; eauto. easy. inv ND.
  destruct IN1 as [EQ1|IN1]. subst. destruct IN2 as [EQ2|IN2]; eauto.
  apply (in_map f) in IN2. congruence.
  destruct IN2 as [EQ2|IN2]; eauto.
  subst.
  apply (in_map f) in IN1. congruence.
Qed.

Lemma Forall2_trans:
  forall {P: Type} (R: P -> P -> Prop) (Rtrans: forall x y z, R x y -> R y z -> R x z)
    l1 l2,
    Forall2 R l1 l2 -> forall l3, Forall2 R l2 l3 -> Forall2 R l1 l3.
Proof.
  induction 2; simpl; intros; eauto. inv H1; constructor; eauto.
Qed.


Fixpoint val_of_type (t: type) : val :=
  match t with
  | bits_t n => Bits (repeat false n)
  | enum_t sg => Enum sg (repeat false (enum_bitsize sg))
  | struct_t sg => Struct sg (map (fun x => val_of_type (snd x)) (struct_fields sg))
  | array_t sg => Array sg (repeat (val_of_type (array_type sg)) (array_len sg))
  end.

Lemma wt_val_of_type:
  forall t,
    wt_val t (val_of_type t).
Proof.
  induction t using type_ind'; simpl; intros; eauto.
  - constructor. rewrite repeat_length. auto.
  - constructor. rewrite repeat_length. auto.
  - constructor. revert IH. generalize (struct_fields sg).
    induction l; simpl; intros; eauto.
    constructor; eauto. eapply IH. left. apply surjective_pairing.
  - constructor. rewrite Forall_forall.
    intros x IN. apply repeat_spec in IN. subst. eauto.
    rewrite repeat_length. auto.
Qed.

Lemma wt_unop_interp:
  forall ufn t1 t2 v,
    wt_unop ufn t1 t2 ->
    wt_val t1 v ->
    exists v2, sigma1 ufn v = Some v2.
Proof.
  inversion 1; subst; simpl; intros; eauto.
  - inv H0. edestruct uvalue_of_bits_succeeds. eauto. rewrite H0. simpl; eauto.
  - inv H0. simpl.  eauto.
  - inv H0. simpl. eauto.
  - inv H0. simpl. eauto.
  - inv H0. simpl. eauto.
  - inv H0. simpl. eauto.
  - inv H0. simpl. eauto.
  - inv H1. simpl.
    unfold PrimTypeInference.find_field in H0. unfold opt_result in H0.
    destr_in H0; inv H0. clear - Heqo H3.
    revert lv idx Heqo H3. generalize (struct_fields sg).
    induction l; simpl; intros; eauto. easy. destr. simpl in *. subst.
    inv H3.
    repeat destr_in Heqo; inv Heqo.
    rewrite Heqs0. eauto.
    destr. subst; congruence.
    eauto.
  - inv H1. simpl.
    unfold PrimTypeInference.find_field in H0. unfold opt_result in H0.
    destr_in H0; inv H0. clear - Heqo H3.
    revert bs idx Heqo H3. generalize (struct_fields sg).
    induction l; simpl; intros; eauto. easy. destr. simpl in *. subst.
    repeat destr_in Heqo; inv Heqo.
    simpl. eauto. eauto.
  - inv H1.
    apply nth_error_lt.
    unfold PrimTypeInference.check_index, opt_result in H0.
    destr_in H0; inv H0.
    destruct (lt_dec idx (Datatypes.length lv)). auto.
    erewrite index_of_nat_ge_none in Heqo. congruence. lia.
  - inv H1. simpl.  eauto.
Qed.

Lemma wt_binop_interp:
  forall ufn t1 t2 t3 v1 v2,
    wt_binop ufn t1 t2 t3 ->
    wt_val t1 v1 ->
    wt_val t2 v2 ->
    exists v3, sigma2 ufn v1 v2 = Some v3.
Proof.
  inversion 1; subst; simpl; intros WT1 WT2; try now (inv WT1; inv WT2; simpl; eauto).
  - destr; eauto.
  - inv WT1.
    unfold PrimTypeInference.find_field in H0. unfold opt_result in H0.
    destr_in H0; inv H0. clear - Heqo H2.
    revert lv idx Heqo H2. generalize (struct_fields sg).
    induction l; simpl; intros; eauto. easy. destr. simpl in *. subst.
    inv H2.
    repeat destr_in Heqo; inv Heqo.
    simpl; eauto.
    edestruct IHl; eauto. unfold opt_bind in H; repeat destr_in H; inv H. simpl; eauto.
  - inv WT1. inv WT2.

    assert (exists w, find_field_offset_right (struct_fields sg) name = Some w).
    {
      unfold PrimTypeInference.find_field in H0. unfold opt_result in H0.
      destr_in H0; inv H0. clear - Heqo.
      revert idx Heqo. generalize (struct_fields sg).
      induction l; simpl; intros; eauto. easy. destr. simpl in *. subst.
      repeat destr_in Heqo; inv Heqo. eauto. eauto.
    }
    destruct H1. rewrite H1. simpl. destr. eauto.
  - inv WT1.
    assert (idx < List.length lv).
    unfold PrimTypeInference.check_index, opt_result in H0.
    destr_in H0; inv H0.
    destruct (lt_dec idx (Datatypes.length lv)). lia.
    erewrite index_of_nat_ge_none in Heqo. congruence. lia.
    edestruct (@take_drop_succeeds) as (la & lb & EQ).
    2: rewrite EQ. lia.
    edestruct (@take_drop_spec) as (EQapp & LA & LB). eauto. simpl.
    destr. simpl in LB. lia. eauto.
Qed.

Lemma wt_val_bool:
  forall x, wt_val (bits_t 1) x -> exists b, x = Bits [b].
Proof.
  inversion 1. subst.
  destruct bs; simpl in *; try lia.
  destruct bs; simpl in *; try lia. eauto.
Qed.
