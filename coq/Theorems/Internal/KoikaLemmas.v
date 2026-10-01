(*! Properties that are useful to reason about untyped semantics !*)
(* TODO: move this to the kôika repo *)
Require Export Koika.Utils.Common.
Require Import Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.KoikaForm.Untyped.UntypedLogs.

Require Import Coq.Lists.List.
Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Program.Equality.

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Section Schedule.

  Context {pos_t rule_name_t: Type}.
  Context {rule_name_t_eq_dec: EqDec rule_name_t}.
  Definition sched := @scheduler pos_t rule_name_t.

  Fixpoint scheduler_has_rule (scheduler : sched) (r_target : rule_name_t) : Prop :=
    match scheduler with
    | Done => False
    | Cons r s => if eq_dec r r_target then True else scheduler_has_rule s r_target
    | Try r s1 s2 => if eq_dec r r_target then True else (scheduler_has_rule s1 r_target \/ scheduler_has_rule s2 r_target)
    | SPos p s => scheduler_has_rule s r_target
    end.
  
End Schedule.

Section Environments.

  Lemma getenv_ccreate:
     forall {K : Type} {FT: FiniteType K}
      {V : esig K}
      (fn : forall k : K, V k)
      (k : K),
      ContextEnv.(getenv) (ccreate finite_elements (fun k _ => fn k)) k = fn k.
  Proof.
    intros. unfold getenv. cbn.
    rewrite cassoc_ccreate. reflexivity.
  Qed.

  Lemma get_put_eq:
    forall {K : Type} {FT: FiniteType K} {V : esig K} (ev : env_t ContextEnv V) (k : K) (v : V k),
      ContextEnv.(getenv) (ContextEnv.(putenv) ev k v) k = v.
  Proof.
    intros. rewrite get_put_eq. reflexivity.
  Qed.

  Lemma cassoc_put_eq:
    forall {K : Type} {FT: FiniteType K} {V : esig K} (ev : env_t ContextEnv V) (k : K) (v : V k),
      cassoc (finite_member k) (ContextEnv.(putenv) ev k v) = v.
  Proof.
    intros. generalize (get_put_eq ev k v). intros H.
    unfold getenv in H. cbn in *. rewrite H. reflexivity.
  Qed.

  Lemma get_put_neq:
    forall {K : Type} {FT: FiniteType K} {V : esig K} (ev : env_t ContextEnv V) (k k' : K) (v : V k),
      k <> k' ->
      ContextEnv.(getenv) (ContextEnv.(putenv) ev k v) k' = ContextEnv.(getenv) ev k'.
  Proof.
    intros. rewrite get_put_neq. reflexivity. sfirstorder.
  Qed.

  Lemma cassoc_put_neq:
    forall {K : Type} {FT: FiniteType K} {V : esig K} (ev : env_t ContextEnv V) (k k' : K) (v : V k),
      k <> k' ->
      cassoc (finite_member k') (ContextEnv.(putenv) ev k v) = cassoc (finite_member k') ev.
  Proof.
    intros. generalize (get_put_neq ev k k' v H). intros Hget.
    unfold getenv in Hget. cbn in *. rewrite Hget. reflexivity.
  Qed.

End Environments.

Section BitsToLists.
  
  Lemma bits_to_list_assoc_app:
    forall {K V: Type} {eq: EqDec K} (l: list (K * V)) (k: K) x a,
    BitsToLists.list_assoc l k = Some x -> 
      BitsToLists.list_assoc (l ++ a) k = Some x.
  Proof.
    intros. generalize dependent H.
    induction l; intros; cbn in *; try congruence.
    destruct a0 as [k1 v1]. destruct (eq_dec k k1).
    - subst. exact H.
    - apply IHl. exact H.
  Qed.

  Lemma bits_to_list_assoc_app_not_in3:
    forall {K V: Type} {eq: EqDec K} (l: list (K * V)) (k: K) a,
    ~ In k (map fst a) ->
    BitsToLists.list_assoc (a ++ l) k = BitsToLists.list_assoc l k.
  Proof.
    intros.
    induction a; intros; cbn in *.
    - reflexivity.
    - destruct a as [k1 v1]. destruct (eq_dec k k1).
      + subst. contradict H. left. reflexivity.
      + apply IHa; auto.
  Qed.

  Lemma bits_to_list_assoc_app_in:
    forall {K V: Type} {eq: EqDec K} (l: list (K * V)) (k: K) a,
    In k (map fst a) ->
    BitsToLists.list_assoc (a ++ l) k = BitsToLists.list_assoc a k.
  Proof.
    intros.
    induction a; intros; cbn in *.
    - contradict H.
    - destruct a as [k1 v1]. destruct (eq_dec k k1).
      + reflexivity.
      + destruct H.
        * subst. cbn in n. congruence.
        * apply IHa; auto.
  Qed.

  Lemma bits_to_list_assoc_app_both_none1:
    forall {K V: Type} {eq: EqDec K} (l: list (K * V)) (k: K) a,
    BitsToLists.list_assoc a k = None -> 
      BitsToLists.list_assoc (a ++ l) k = BitsToLists.list_assoc l k.
  Proof.
    intros. generalize dependent H.
    induction a; intros; cbn in *.
    - reflexivity.
    - destruct a as [k1 v1]. destruct (eq_dec k k1).
      + inversion H.
      + apply IHa; auto.
  Qed.

End BitsToLists.

Section Bits.

  Lemma bits_single_is_neg_beq_dec:
    forall x, beq_dec x Ob~0 = negb (Bits.single x).
  Proof.
    intros. unfold Bits.single, beq_dec.
    destruct x. destruct vtl. destruct vhd; cbn; auto.
  Qed. 

End Bits.

Section Helper.

  Lemma tl_skipn:
    forall {T} (l: list T) n,
    tl (List.skipn n l) = List.skipn (S n) l.
  Proof.
    intros.
    generalize dependent l.
    induction n; intros; simpl.
    - reflexivity.
    - destruct l; simpl in *; try reflexivity. apply IHn.
    Show Proof.
  Qed.

End Helper.

Require Import Koika.KoikaForm.Logs.
Require Koika.Properties.SemanticProperties.

Section LogHelpers.

  Context {reg_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {R: reg_t -> type}.
  Context {REnv: Env reg_t}.

  (** Lemma for searching a newly added entry (log_cons) **)
  Lemma log_existsb_empty : forall (r : reg_t) (f : LogEntryKind -> Port -> bool),
    log_existsb (REnv:=REnv) (R:=R) log_empty r f = false.
  Proof.
    (* log_empty is defined as an environment of empty lists. *)
    intros. unfold log_existsb, log_empty.
    rewrite getenv_create. reflexivity.
  Qed.

  Lemma latest_write_log_cons_read :
    forall log idx idx' le,
      kind le = LogRead ->
      latest_write (reg_t:=reg_t) (R:=R) (REnv:=REnv) (log_cons idx' le log) idx = latest_write (reg_t:=reg_t) (R:=R) (REnv:=REnv) log idx.
  Proof.
    intros. unfold latest_write.
    destruct (eq_dec idx' idx).
    - subst idx'. rewrite SemanticProperties.log_find_cons_eq. destruct le; simpl; auto. destruct kind; simpl; auto.
      contradict H. sauto.
    - rewrite SemanticProperties.log_find_cons_neq; auto.
  Qed.

End LogHelpers.

Section ListHelpers.

  Context {A: Type}.
  Context {A_eq_dec: EqDec A}.
  Context {B: Type}.
  Context {B_eq_dec: EqDec B}.

  Lemma in_dec (x: A) (l: list A): {In x l} + {~ In x l}.
  Proof.
    intros. induction l.
    - right. intros H. inversion H.
    - destruct (eq_dec x a).
      + left. subst. left. reflexivity.
      + specialize (IHl). destruct IHl.
        * left. right. exact i.
        * right. intros H. destruct H.
          { subst. contradiction. }
          { apply n0. exact H. }
  Qed.

  Lemma not_in_map :
    forall (f: A -> B) x l,
    ~ In x l ->
    (forall y1 y2, f y1 = f y2 -> y1 = y2) ->
    ~ In (f x) (map f l).
  Proof.
    intros. intros HL. apply in_map_iff in HL. destruct HL as [y [Hfy Hin]]. 
    specialize (H0 y x Hfy). subst. congruence.
  Qed.

End ListHelpers.

Lemma fst_let_repackage : forall {A B C} (p : A * B) (f : A -> C),
  fst (let (v, l) := p in (f v, l)) = f (fst p).
Proof. destruct p; reflexivity. Qed.

Lemma not_in_app : forall {A: Type} (x: A) (l1 l2: list A),
  ~ In x l1 ->
  ~ In x l2 ->
  ~ In x (l1 ++ l2).
Proof.
  intros. intros HIn. apply in_app_iff in HIn. destruct HIn; auto.
Qed.

Lemma not_in_app_l : forall {A: Type} (x: A) (l1 l2: list A),
  ~ In x (l1 ++ l2) ->
  ~ In x l1.
Proof.
  intros. intros HIn. apply H; clear H. apply in_or_app. left. exact HIn.
Qed.

Lemma not_in_app_r : forall {A: Type} (x: A) (l1 l2: list A),
  ~ In x (l1 ++ l2) ->
  ~ In x l2.
Proof.
  intros. intros HIn. apply H; clear H. apply in_or_app. right. exact HIn.
Qed.

Lemma not_in_app_iff : forall {A: Type} (x: A) (l1 l2: list A),
  ~ In x (l1 ++ l2) <-> ~ In x l1 /\ ~ In x l2.
Proof.
  intros. split; intros H.
  - split.
    + apply not_in_app_l in H. assumption.
    + apply not_in_app_r in H. assumption.
  - destruct H as [H1 H2]. apply not_in_app; assumption.
Qed.
