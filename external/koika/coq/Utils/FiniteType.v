(*! Utilities | Finiteness typeclass !*)
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Arith.
Import ListNotations.

Class FiniteType {T} :=
  { finite_index: T -> nat;
    finite_elements: list T;
    finite_surjective: forall a: T, List.nth_error finite_elements (finite_index a) = Some a;
    finite_injective: NoDup (List.map finite_index finite_elements) }.
Arguments FiniteType: clear implicits.

Definition finite_index_injective {T: Type} {FT: FiniteType T}:
  forall t1 t2,
    finite_index t1 = finite_index t2 ->
    t1 = t2.
Proof.
  intros t1 t2 H.
  apply (f_equal (nth_error finite_elements)) in H.
  rewrite !finite_surjective in H.
  inversion H; auto.
Defined.

Lemma finite_elements_index  {T: Type} {FT: FiniteType T}:
  forall m x0,
    nth_error finite_elements m = Some x0 ->
    finite_index x0 = m.
Proof.
  intros.
  generalize (finite_surjective x0).
  intros.
  generalize (finite_injective).
  rewrite NoDup_nth_error. intros SPEC.
  apply SPEC.
  apply nth_error_Some. rewrite nth_error_map. rewrite H0. simpl. congruence.
  rewrite ! nth_error_map. rewrite H, H0. simpl. auto.
Qed.

Definition finite_nodup {T} {FT: FiniteType T} :
  NoDup finite_elements.
Proof.
  eapply NoDup_map_inv.
  apply finite_injective.
Qed.

Fixpoint increasing (l: list nat) :=
  match l with
  | [] => true
  | n1 :: [] => true
  | n1 :: (n2 :: _) as l => andb (Nat.ltb n1 n2) (increasing l)
  end.

Lemma increasing_not_In :
  forall l n, increasing (n :: l) = true -> forall n', n' <= n -> ~ In n' l.
Proof.
  induction l; intros n H n' Hle Habs.
  - auto.
  - apply Bool.andb_true_iff in H; destruct H; apply PeanoNat.Nat.ltb_lt in H.
    destruct Habs as [ ? | ? ]; subst; try lia.
    eapply IHl; [ eassumption | .. | eassumption ]; lia.
Qed.

Lemma increasing_not_In' :
  forall l n, increasing (n :: l) = true -> forall n', n' <? n = true -> ~ In n' (n :: l).
Proof.
  unfold not; intros l n Hincr n' Hlt [ -> | Hin ]; apply PeanoNat.Nat.ltb_lt in Hlt.
  - lia.
  - eapply increasing_not_In;
      [ eassumption | apply Nat.lt_le_incl | eassumption ]; eauto.
Qed.

Lemma increasing_NoDup :
  forall l, increasing l = true -> NoDup l.
Proof.
  induction l as [ | n1 l IHl]; cbn; intros H.
  - constructor.
  - destruct l.
    + repeat constructor; inversion 1.
    + apply Bool.andb_true_iff in H; destruct H.
      constructor.
      apply increasing_not_In'; eauto.
      eauto.
Qed.

Section ORDER.
Variable T: Type.
Variable lt: T -> T -> Prop.
Variable ltb: T -> T -> bool.
Hypothesis ltb_asym: forall a b, ltb a b = negb (ltb b a).

Fixpoint increasing_ (l: list T) :=
  match l with
  | [] => true
  | n1 :: [] => true
  | n1 :: (n2 :: _) as l => andb (ltb n1 n2) (increasing_ l)
  end.

Definition leb (a b: T) := negb (ltb b a).

Hypothesis trans_le_lt:
  forall a b c,
    leb a b = true -> ltb b c = true -> leb a c = true.

Lemma increasing__not_In :
  forall l n, increasing_ (n :: l) = true -> forall n', leb n' n = true -> ~ In n' l.
Proof.
  unfold leb. induction l; intros n H n' Hle Habs.
  - auto.
  - apply Bool.andb_true_iff in H; destruct H.
    destruct Habs as [ ? | ? ]; subst. rewrite H in Hle. simpl in Hle. congruence.
    eapply IHl. eassumption. 2: eassumption.
    change (leb n' a = true).
    change (leb n' n = true) in Hle.
    eapply trans_le_lt; eauto.
Qed.

Hypothesis ltb_irrefl : forall n, ltb n n = false.

Lemma increasing__not_In' :
  forall l n, increasing_ (n :: l) = true -> forall n', ltb n' n = true -> ~ In n' (n :: l).
Proof.
  unfold not; intros l n Hincr n' Hlt [ -> | Hin ].
  - rewrite ltb_irrefl in Hlt; congruence.
  - eapply increasing__not_In;
      [ eassumption | idtac | eassumption ]. eauto.
Qed.

Lemma increasing__NoDup :
  forall l, increasing_ l = true -> NoDup l.
Proof.
  induction l as [ | n1 l IHl]; cbn; intros H.
  - constructor.
  - destruct l.
    + repeat constructor; inversion 1.
    + apply Bool.andb_true_iff in H; destruct H.
      constructor.
      apply increasing__not_In'; eauto.
      eauto.
Qed.

End ORDER.

Fixpoint fin_list (n : nat) : list (Fin.t n) :=
  match n with
  | 0 => []
  | S n' => Fin.F1 :: (map Fin.FS (fin_list n'))
  end.

Lemma fin_list_some:
  forall n x, x < n ->
    exists a, nth_error (fin_list n) x = Some a /\ proj1_sig (Fin.to_nat a) = x.
Proof.
  induction n; simpl; intros; eauto. lia.
  destruct x. simpl. eexists; split. eauto. simpl. auto.
  edestruct IHn as (a & NTH & EQ). apply PeanoNat.lt_S_n. apply H.
  simpl.
  rewrite nth_error_map. rewrite NTH. simpl.
  eexists; split. eauto. simpl. destruct (Fin.to_nat a). simpl in *. congruence.
Qed.

Lemma NoDup_map:
  forall {A B: Type} (f: A -> B) (l: list A),
    NoDup l ->
    (forall x y, f x = f y -> x = y) ->
    NoDup (map f l).
Proof.
  induction 1; simpl; intros; eauto. constructor.
  specialize (IHNoDup H1). constructor. intro IN. apply in_map_iff in IN. destruct IN as (x0 & EQ & IN). apply H1 in EQ. subst. congruence. auto.
Qed.

Lemma NoDup_finlist n: NoDup (fin_list n).
Proof.
  induction n; simpl; intros; eauto. constructor.
  constructor. intro A. apply in_map_iff in A. destruct A as (x & EQ & IN). congruence.
  apply NoDup_map. auto. intros. apply Fin.FS_inj; auto.
Qed.

#[global] Instance fin_finitetype:
  forall i, FiniteType (Fin.t i).
Proof.
  intros.
  refine ({|
             finite_index := fun i =>  proj1_sig (Fin.to_nat i);
             finite_elements := fin_list i;
           |}).
  - intros.
    edestruct (fin_list_some) as (x & NTH & EQ).
    2: rewrite NTH.
    destruct (Fin.to_nat a) eqn:?. simpl.
    auto.
    apply Fin.to_nat_inj in EQ. congruence.
  - apply NoDup_map.
    apply NoDup_finlist. simpl.
    apply Fin.to_nat_inj.
Qed.

Fixpoint nth_error_app_l {A} (l l' : list A):
  forall n x,
    nth_error l n = Some x ->
    nth_error (l ++ l') n = Some x.
Proof.
  destruct l, n; cbn; (solve [inversion 1] || eauto).
Defined.

Fixpoint map_nth_error {A B} (l: list A) (f: A -> B) {struct l}:
  forall n x,
    nth_error l n = Some x ->
    nth_error (map f l) n = Some (f x).
Proof.
  destruct l, n; cbn;inversion 1; eauto.
Defined.

Class FiniteType2 {T} :=
  { finite2_index: T -> (nat * nat);
    finite2_elements: list (list T);
    finite2_surjective: forall a: T, forall n m,
      finite2_index a = (n, m) ->
      exists l,
        List.nth_error finite2_elements n = Some l /\
          List.nth_error l m = Some a;

    finite2_:
    forall n l,
      nth_error finite2_elements n = Some l ->
      forall m x,
        nth_error l m = Some x ->
        finite2_index x = (n, m);

    (* finite2_injective: *)
    (* forall t1 t2, finite2_index t1 = finite2_index t2 -> t1 = t2; *)
    (* finite2_nodup: *)
    (* NoDup (fold_left (fun acc i : list T => acc ++ i) finite2_elements []) *)

    (* finite2_injective1: *)
    (* NoDup (map fst finite2_elements); *)

    finite2_injective2:
    Forall (fun l => NoDup (map finite2_index l)) finite2_elements

  }.
Arguments FiniteType2: clear implicits.

Section F2.
  Context {T: Type}.
  Context `{fin: FiniteType2 T}.
  Definition finite_index_of_finite_index2 (t: T) : nat :=
    let (n, m) := finite2_index t in
    List.fold_left (fun acc i =>
                      acc + List.length i
      ) (firstn n finite2_elements) 0  + m.
  Definition finite_elements_of_finite_elements2 : list T :=
    List.fold_left (fun acc i =>
                      acc ++ i
      ) finite2_elements [].

  Lemma nth_error_split:
    forall {T} (l: list T) n x,
      nth_error l n = Some x ->
      exists l2, skipn n l = x :: l2.
  Proof.
    induction l; simpl; intros; eauto. destruct n; simpl in H; easy.
    destruct n; simpl in H. inversion H; clear H; subst. simpl. eauto.
    simpl. apply IHl. auto.
  Qed.

  Lemma fold_left_concat_app:
    forall {T: Type} (l1: list (list T)) l0,
      (fold_left (fun acc l => acc ++ l) l1 l0)
      =
        l0 ++ (fold_left (fun acc l => acc ++ l) l1 [])
  .
  Proof.
    induction l1; simpl; intros; eauto. rewrite app_nil_r. auto.
    rewrite (IHl1 (l0 ++ a)), (IHl1 a).
    rewrite app_assoc. auto.
  Qed.


  Lemma fold_left_sum_plus:
    forall {T: Type} (l1: list (list T)) l0,
      (fold_left (fun acc l => acc + length l) l1 l0)
      =
        l0 + (fold_left (fun acc l => acc + length l) l1 0)
  .
  Proof.
    induction l1; simpl; intros; eauto.
    rewrite (IHl1 (l0 + length a)), (IHl1 (length a)).
    lia.
  Qed.

  Lemma nth_error_concat_sum_cancel:
    forall {T: Type} n (l1 l2: list (list T)) n0 l0 (EQ: length l0 = n0),
               nth_error
                 (fold_left (fun acc l => acc ++ l) (l1 ++ l2) l0)
                 (fold_left (fun acc l => acc + length l) l1 n0 + n)
               =
                 nth_error
                   (fold_left (fun acc l => acc ++ l) l2 [])
                   n.
  Proof.
      intros. rewrite fold_left_concat_app. rewrite fold_left_sum_plus.
      rewrite nth_error_app2 by lia.
      replace (n0 + fold_left (fun (acc : nat) (l : list T0) => acc + length l) l1 0 + n - length l0)
                with
                (fold_left (fun (acc : nat) (l : list T0) => acc + length l) l1 0 + n) by lia.
      clear n0 l0 EQ. revert l2 n.
      induction l1; simpl; intros; eauto.
      rewrite (fold_left_concat_app _ a).
      rewrite (fold_left_sum_plus).
      rewrite nth_error_app2 by lia.
      replace (length a + fold_left (fun (acc : nat) (l : list T0) => acc + length l) l1 0 + n - length a)
                with
                (fold_left (fun (acc : nat) (l : list T0) => acc + length l) l1 0 + n) by lia. auto.
  Qed.

  Lemma finite_surjective_of_finite2:
    forall a : T,
      nth_error finite_elements_of_finite_elements2 (finite_index_of_finite_index2 a) = Some a.
  Proof.
    intros. unfold finite_elements_of_finite_elements2.
    unfold finite_index_of_finite_index2. destruct (finite2_index a) eqn:?.

    rewrite <- (firstn_skipn n finite2_elements) at 1.
    rewrite nth_error_concat_sum_cancel by reflexivity.
    apply finite2_surjective in Heqp.
    destruct Heqp as (l & NTH & NTH2).
    edestruct (nth_error_split _ _ _ NTH) as (l2 & SKIP).
    rewrite SKIP. simpl.
    rewrite fold_left_concat_app. rewrite nth_error_app1. auto.
    apply nth_error_Some. congruence.
  Qed.

  Lemma firstn_plus: forall T a b (l: list T),
    firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
  Proof.
    induction a; simpl; intros; eauto.
    destruct l. rewrite firstn_nil. reflexivity.
    simpl. f_equal. apply IHa.
  Qed.

  Lemma NoDup_app:
    forall {T: Type} (l1 l2: list T),
      NoDup l1 ->
      NoDup l2 ->
      (forall x, In x l1 -> In x l2 -> False) ->
      NoDup (l1 ++ l2).
  Proof.
    induction l1; simpl; intros; eauto.
    inversion H; clear H; subst.
    specialize (IHl1 _ H5 H0).
    constructor. rewrite in_app_iff. intros [A|B]. congruence. eapply H1. left; reflexivity. auto.
    apply IHl1. eauto.
  Qed.

  Lemma fold_left_concat:
    forall T l l0,
      fold_left (fun acc i : list T => acc ++ i) l l0 = l0 ++ concat l.
  Proof.
    induction l; simpl; intros; eauto.
    rewrite app_nil_r; auto.
    rewrite IHl. rewrite app_assoc. auto.
  Qed.

  Ltac inv H:= inversion H; clear H; try subst.


  Lemma finite2_inj:
    forall x y : T, finite_index_of_finite_index2 x = finite_index_of_finite_index2 y -> x = y.
  Proof.
    intros. unfold finite_index_of_finite_index2 in H.
    intros. destruct (finite2_index x) eqn:?, (finite2_index y) eqn:?.
    destruct (finite2_surjective _ _ _ Heqp)  as (? & NTH1 & NTH2).
    destruct (finite2_surjective _ _ _ Heqp0) as (? & NTH3 & NTH4).
    destruct (eq_nat_dec n n1).
    - subst. rewrite NTH1 in NTH3; inversion NTH3; clear NTH3; subst.
      assert (n0 = n2) by lia. subst. congruence.
    - exfalso. clear Heqp Heqp0.
      assert (forall {T} (l: list T) n x, nth_error l n = Some x -> n < length l).
      intros; apply nth_error_Some; congruence.
      apply H0 in NTH2, NTH4.
      destruct (lt_dec n n1).
      + replace n1 with (n + (n1 - n)) in H by lia.
        rewrite firstn_plus in H.
        rewrite fold_left_app in H.
        rewrite (fold_left_sum_plus _ (fold_left _ _ _)) in H.
        rewrite <- Nat.add_assoc in H. apply Nat.add_cancel_l in H.
        destruct (nth_error_split _ _ _ NTH1) as (? & SKIP). rewrite SKIP in H.
        simpl in H.
        destruct (n1 - n) eqn:?. lia. simpl in H.
        rewrite fold_left_sum_plus in H. lia.
      + replace n with (n1 + (n - n1)) in H by lia.
        rewrite firstn_plus in H.
        rewrite fold_left_app in H.
        rewrite (fold_left_sum_plus _ (fold_left _ _ _)) in H.
        rewrite <- Nat.add_assoc in H. apply Nat.add_cancel_l in H.
        destruct (nth_error_split _ _ _ NTH3) as (? & SKIP). rewrite SKIP in H.
        simpl in H.
        destruct (n - n1) eqn:?. lia. simpl in H.
        rewrite fold_left_sum_plus in H. lia.
  Qed.

  Lemma finite_injective_of_finite2:
    NoDup finite_elements_of_finite_elements2.
  Proof.
    unfold finite_elements_of_finite_elements2.
    rewrite fold_left_concat. simpl.
    unfold finite2_elements. destruct fin. clear fin.
    rename finite2_index0 into idx.
    rename finite2_elements0 into l.
    rename finite2_surjective0 into SURJ.
    rename finite2_0 into P.
    rename finite2_injective3 into INJ.
    clear SURJ.
    assert (PROP: 
        forall n1 m1 n2 m2 a l1 l2,
          nth_error l n1 = Some l1 ->
          nth_error l1 m1 = Some a ->
          nth_error l n2 = Some l2 ->
          nth_error l2 m2 = Some a ->
          n1 = n2 /\ m1 = m2
      ).
    {
      intros n1 m1 n2 m2 a l1 l2 NTH11 NTH12 NTH21 NTH22.
      generalize (P _ _ NTH11 _ _ NTH12).
      generalize (P _ _ NTH21 _ _ NTH22). intuition congruence.
    }
    assert (ND: Forall (fun l => NoDup l) l).
    {
      eapply Forall_impl. 2: apply INJ. simpl. intros.
      eapply NoDup_map_inv. eauto.
    }
    clear - PROP ND. revert ND PROP.
    induction 1; simpl; intros; eauto.
    constructor.
    apply NoDup_app; auto.
    apply IHND.
    intros.
    specialize (PROP (S n1) m1 (S n2) m2). simpl in PROP.
    specialize (PROP _ _ _ H0 H1 H2 H3). intuition congruence.
    intros ? IN1 INconcat.
    edestruct In_nth_error as (? & NTH). apply IN1. clear IN1.
    specialize (PROP 0 x1). simpl in PROP.
    rewrite in_concat in INconcat. destruct INconcat as (? & INl & INx).
    edestruct In_nth_error as (? & NTH2). apply INl.
    edestruct In_nth_error as (? & NTH4). apply INx.
    specialize (PROP (S x3) x4 x0).
    edestruct PROP; eauto. congruence.
  Qed.

  Instance FiniteType2_FiniteType: FiniteType T.
  Proof.
    refine {|
        finite_index := finite_index_of_finite_index2;
        finite_elements := finite_elements_of_finite_elements2;
      |}.
    apply finite_surjective_of_finite2.
    apply NoDup_map. apply finite_injective_of_finite2. apply finite2_inj.
  Defined.
End F2.

Ltac list_length l :=
  lazymatch l with
  | _ :: ?tl => let len := list_length tl in constr:(S len)
  | _ => constr:(0)
  end.

Inductive FiniteType_norec (T: Type) :=
  | finite_type_norec : FiniteType_norec T.

Ltac FiniteType_t_compute_index :=
  vm_compute;
  lazymatch goal with
  | [  |- _ ?l ?idx = Some ?x ] =>
    let len := list_length l in
    match x with
    | ?f ?y =>
      let tx := type of x in
      let idx' := fresh "index" in
      evar (idx': nat); unify idx (len + idx'); subst idx';
      vm_compute; apply nth_error_app_l, map_nth_error;
      (* Must call typeclasses eauto manually, because plain typeclass resolution
         doesn't operate in the current context (and so FiniteType_norec isn't
         taken into account). *)
      pose proof (finite_type_norec tx);
      lazymatch goal with
      | [ |- _ = Some ?z ] =>
        let tx' := type of z in
        eapply (finite_surjective (T := tx') (FiniteType := ltac:(typeclasses eauto)))
      end
    | ?x => instantiate (1 := len);
           instantiate (1 := _ :: _);
           vm_compute; reflexivity
    | _ => idtac
    end
  end.


Ltac FiniteType_t_nodup_increasing :=
  apply increasing_NoDup;
  vm_compute; reflexivity.

Ltac FiniteType_t_init :=
  unshelve econstructor;
    [ destruct 1; shelve | shelve | .. ].


Ltac FiniteType_t :=
  lazymatch goal with
  | [ H: FiniteType_norec ?T |- FiniteType ?T ] => fail "Type" T "is recursive"
  | [  |- FiniteType ?T ] =>
    let nm := fresh in
    FiniteType_t_init;
    [ intros nm; destruct nm; [> FiniteType_t_compute_index ..] |
      instantiate (1 := []); FiniteType_t_nodup_increasing ];
    fold (@nth_error nat)
  end.

#[export] Hint Extern 1 (FiniteType _) => FiniteType_t : typeclass_instances.


Lemma nth0_cons:
  forall {T: Type} (l: list T) x,
    nth_error (x::l) O = Some x.
Proof.
  reflexivity.
Qed.

Lemma nth0_consnil:
  forall {T: Type} (x: T),
    nth_error (x::nil) O = Some x.
Proof.
  intros; apply nth0_cons.
Qed.


Lemma nthS_cons:
  forall {T: Type} (l: list T) x n,
    nth_error (x::l) (S n) = nth_error l n.
Proof.
  reflexivity.
Qed.


Lemma nth_one:
  forall {T: Type} (a b: T) n,
    nth_error [a] n = Some b -> a = b /\ n = 0.
Proof.
  intros. destruct n; simpl in *. intuition try congruence.
  destruct n; simpl in *; intuition try congruence.
Qed.

Lemma nth_error_map_inv:
  forall {T1 T2: Type} (f: T1 -> T2) l n b,
    nth_error (map f l) n = Some b ->
    exists a, nth_error l n = Some a /\ b = f a.
Proof.
  intros. rewrite nth_error_map in H.  unfold option_map in H. destruct (nth_error l n) eqn:?; inversion H; clear H. subst. eauto.
Qed.

Lemma NoDup_map_pair:
  forall {T R N: Type} (f: T -> R) (n: N) l,
    NoDup (map f l) -> NoDup (map (fun x : T => (n, f x)) l).
Proof.
  intros.
  apply NoDup_map with (f:= fun x => (n, x)) in H. simpl in H.
  rewrite map_map in H. auto.
  intuition congruence.
Qed.

Lemma NoDup_one:
  forall {T: Type} (t: T), NoDup [t].
Proof.
  repeat constructor. easy.
Qed.

Lemma Some_inj: forall {T: Type} (t1 t2: T), Some t1 = Some t2 -> t1 = t2.
Proof.
  intuition congruence.
Qed.

Ltac consume_nth H H0 :=
  match type of H with
    nth_error (?a::_) ?n = Some ?l =>
      destruct n as [|n]; [
        cbn [nth_error] in H; apply Some_inj in H; subst;
        match type of H0 with
          nth_error [?a] ?m = Some ?x =>
            apply nth_one in H0; destruct H0; subst; auto
        | nth_error (map ?f _) ?m = Some ?x =>
            apply nth_error_map_inv in H0;
            destruct H0 as (? & H0 & ?); try subst; apply finite_elements_index in H0; congruence
        end
      | cbn [nth_error] in H; consume_nth H H0
      ]
  | nth_error [] ?n = Some ?l =>
      rewrite nth_error_nil in H; congruence

  end.

Ltac forall_nodup_tac :=
  match goal with
    |- Forall _ (_::_) => apply Forall_cons; [
        cbn [map];
        match goal with
        | |- NoDup [?x] => apply NoDup_one
        | |- NoDup (map _ (map _ _)) => rewrite map_map; apply NoDup_map_pair; apply finite_injective
        end
      |forall_nodup_tac]
  | |- Forall _ [] => apply Forall_nil
  end.

Ltac FiniteType_t2 :=
  let nm := fresh "nm" in
  let n := fresh "n" in
  let m := fresh "m" in
  let EQ := fresh "EQ" in
  FiniteType_t_init; [
      intros nm n m EQ;
      destruct nm;
      (instantiate (1:= (_,_)) in EQ; inversion EQ; clear EQ; subst;
      eexists; split; [
          repeat match goal with
            |- nth_error (_::_) _ = Some ?x_ => rewrite nthS_cons
          | |- nth_error _ _ = Some ?x => apply nth0_cons
          end
        |
          match goal with
            |- nth_error _ _ = Some (?f ?x) =>
              apply map_nth_error;
              lazymatch goal with
              | [ |- _ = Some ?z ] =>
                  let tx' := type of x in
                  eapply (finite_surjective (T := tx') (FiniteType := ltac:(typeclasses eauto)))
              end
          | |- nth_error _ _ = Some ?x =>
              apply nth0_consnil
          end
      ])
    |
      instantiate (1:=[]); cbn [nth_error]; intros;
      match goal with
        H: nth_error _ _ = Some ?l,
          H2: nth_error ?l _ = Some _ |- _ => try consume_nth H H2
      end
    | try forall_nodup_tac].

Module Examples.
  Inductive t    := A | B.
  Inductive t'   := A' | B'.
  Inductive t''  := A'' | B'' (x': t) | C''.
  Inductive t''' := A''' | B''' (x': t) | C''' | D''' (x' : t').

  Inductive t4 := A4 | B4 (x': t''') | C4 | D4 (x' : t''').

  #[local] Instance tf: FiniteType t.
  Proof. FiniteType_t. Defined.


  #[local] Instance t'f : FiniteType t''.
  Proof.
    eapply FiniteType2_FiniteType. Unshelve.
    FiniteType_t2.
  Defined.

  #[local] Instance t''f: FiniteType t''.
  Proof. FiniteType_t. Defined.

  #[local] Instance t'''f: FiniteType t'''.
  Proof. FiniteType_t. Defined.

  #[local] Instance t4f: FiniteType t4.
  Proof.
    FiniteType_t.
    Restart.
    eapply FiniteType2_FiniteType. Unshelve.
    FiniteType_t2.
  Defined.

End Examples.
