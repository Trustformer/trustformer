Require Import Koika.Frontend.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.

Require Import Coq.Lists.List.
Import ListNotations.

(* Opt-in: calls on the two arms of an [if] become one call whose argument picks
   the arm.  A suffix both arms share is pulled out first, but only when it holds
   a call; on some designs that costs cycles, so nothing applies this by default. *)

Section MergeCalls.
  Context {S I O P: Type}.
  Context {S_eq: EqDec S} {I_eq: EqDec I} {O_eq: EqDec O} {P_eq: EqDec P}.

  Local Notation E := (@tf_expr S I O).
  Local Notation OP := (@tf_op S I O P).
  Local Notation OPS := (@tf_ops S I O P).

  Definition unary_eq_dec (a b: tf_unary_ops) : {a = b} + {a <> b}.
  Proof. decide equality; apply Nat.eq_dec. Defined.

  Definition cmp_eq_dec (a b: tf_comparison_ops) : {a = b} + {a <> b}.
  Proof. decide equality. Defined.

  Definition binary_eq_dec (a b: tf_binary_ops) : {a = b} + {a <> b}.
  Proof. decide equality; first [apply Nat.eq_dec | apply cmp_eq_dec]. Defined.

  Definition expr_eq_dec (a b: E) : {a = b} + {a <> b}.
  Proof.
    decide equality;
      first [apply Nat.eq_dec | apply eq_dec | apply unary_eq_dec | apply binary_eq_dec].
  Defined.

  Definition op_eq_dec (a b: OP) : {a = b} + {a <> b}.
  Proof. decide equality; first [apply eq_dec | apply expr_eq_dec]. Defined.

  Definition ops_eq_dec (a b: OPS) : {a = b} + {a <> b}.
  Proof. decide equality; first [apply op_eq_dec | apply expr_eq_dec]. Defined.

  Fixpoint to_list (o: OPS) : list OPS :=
    match o with
    | tf_ops_cons a b => to_list a ++ to_list b
    | _ => [o]
    end.

  Fixpoint of_list (l: list OPS) : OPS :=
    match l with
    | [] => tf_ops_base tf_nop
    | [x] => x
    | x :: r => tf_ops_cons x (of_list r)
    end.

  Fixpoint common_prefix (a b: list OPS) : list OPS * list OPS * list OPS :=
    match a, b with
    | x :: a1, y :: b1 =>
        if ops_eq_dec x y then
          let '(p, a', b') := common_prefix a1 b1 in (x :: p, a', b')
        else ([], a, b)
    | _, _ => ([], a, b)
    end.

  Definition split_suffix (a b: list OPS) : list OPS * list OPS * list OPS :=
    let '(k, a', b') := common_prefix (rev a) (rev b) in (rev a', rev b', rev k).

  Fixpoint has_call (o: OPS) : bool :=
    match o with
    | tf_ops_base (tf_call _ _ _) => true
    | tf_ops_base _ => false
    | tf_ops_cons a b | tf_ops_if _ a b => has_call a || has_call b
    end.

  Definition merge_arms (c: E) (t e: OPS) : OPS :=
    let '(t', e', k) := split_suffix (to_list t) (to_list e) in
    let factored :=
      if existsb has_call k then of_list (tf_ops_if c (of_list t') (of_list e') :: k)
      else tf_ops_if c t e in
    match t', e' with
    | [tf_ops_base (tf_call p d a1)], [tf_ops_base (tf_call p' d' a2)] =>
        if eq_dec p p' then
          if eq_dec d d' then of_list (tf_ops_base (tf_call p d (tf_expr_if c a1 a2)) :: k)
          else factored
        else factored
    | _, _ => factored
    end.

  Fixpoint merge_calls (o: OPS) : OPS :=
    match o with
    | tf_ops_base _ => o
    | tf_ops_cons a b => tf_ops_cons (merge_calls a) (merge_calls b)
    | tf_ops_if c t e => merge_arms c (merge_calls t) (merge_calls e)
    end.

  Lemma common_prefix_spec : forall a b p a' b',
    common_prefix a b = (p, a', b') -> a = p ++ a' /\ b = p ++ b'.
  Proof.
    induction a as [| x a1 IH]; intros b p a' b' H.
    - cbn in H. inversion H; subst. auto.
    - destruct b as [| y b1]; cbn in H.
      + inversion H; subst. auto.
      + destruct (ops_eq_dec x y) as [-> | _].
        * destruct (common_prefix a1 b1) as [[p0 a0] b0] eqn:Hc.
          inversion H; subst. destruct (IH _ _ _ _ Hc) as [-> ->]. auto.
        * inversion H; subst. auto.
  Qed.

  Lemma split_suffix_spec : forall a b a' b' k,
    split_suffix a b = (a', b', k) -> a = a' ++ k /\ b = b' ++ k.
  Proof.
    unfold split_suffix. intros a b a' b' k H.
    destruct (common_prefix (rev a) (rev b)) as [[k0 a0] b0] eqn:Hc.
    inversion H; subst.
    destruct (common_prefix_spec _ _ _ _ _ Hc) as [Ha Hb].
    split.
    - rewrite <- (rev_involutive a), Ha, rev_app_distr. reflexivity.
    - rewrite <- (rev_involutive b), Hb, rev_app_distr. reflexivity.
  Qed.

  Context {S_fin: FiniteType S} {I_fin: FiniteType I} {O_fin: FiniteType O}.
  Context (s_sz: S -> nat) (i_sz: I -> nat) (o_sz: O -> nat) (ips: P -> ip_decl).

  Local Notation run o st inp := (tf_ops_run s_sz i_sz o_sz ips o st inp).

  Lemma run_cons : forall a b st inp, run (tf_ops_cons a b) st inp = run b (run a st inp) inp.
  Proof.
    intros. unfold tf_ops_run. cbn [tf_ops_updates].
    destruct (tf_ops_updates _ _ _ _ a st inp) as [u1 s1]. cbn [snd].
    destruct (tf_ops_updates _ _ _ _ b s1 inp) as [u2 s2]. reflexivity.
  Qed.

  Lemma run_nop : forall st inp, run (tf_ops_base tf_nop) st inp = st.
  Proof. intros [st out] inp. reflexivity. Qed.

  Fixpoint run_list (l: list OPS) st inp :=
    match l with
    | [] => st
    | o :: r => run_list r (run o st inp) inp
    end.

  Lemma run_list_app : forall l1 l2 st inp, run_list (l1 ++ l2) st inp = run_list l2 (run_list l1 st inp) inp.
  Proof. induction l1; intros; cbn; auto. Qed.

  Lemma run_of_list : forall l st inp, run (of_list l) st inp = run_list l st inp.
  Proof.
    induction l as [| x r IH]; intros st inp.
    - apply run_nop.
    - destruct r as [| y r'].
      + reflexivity.
      + change (of_list (x :: y :: r')) with (tf_ops_cons x (of_list (y :: r'))).
        rewrite run_cons, IH. reflexivity.
  Qed.

  Lemma run_to_list : forall o st inp, run o st inp = run_list (to_list o) st inp.
  Proof.
    induction o as [op | a IHa b IHb | c t IHt e IHe]; intros st inp.
    - reflexivity.
    - cbn [to_list]. rewrite run_cons, run_list_app, <- IHa, <- IHb. reflexivity.
    - reflexivity.
  Qed.

  Lemma run_if : forall c t e st inp,
    run (tf_ops_if c t e) st inp =
    if beq_dec (tf_eval_expr s_sz i_sz o_sz (szB:=1) c st inp) Bits.zero then run e st inp else run t st inp.
  Proof.
    intros. unfold tf_ops_run. cbn [tf_ops_updates].
    destruct (beq_dec _ _); reflexivity.
  Qed.

  Lemma run_call_if : forall p d c a1 a2 st inp,
    run (tf_ops_base (tf_call p d (tf_expr_if c a1 a2))) st inp =
    run (tf_ops_if c (tf_ops_base (tf_call p d a1)) (tf_ops_base (tf_call p d a2))) st inp.
  Proof.
    intros. rewrite run_if. unfold tf_ops_run. cbn.
    destruct (beq_dec _ _); reflexivity.
  Qed.

  Lemma run_factor : forall c t e t' e' k st inp,
    to_list t = t' ++ k -> to_list e = e' ++ k ->
    run (of_list (tf_ops_if c (of_list t') (of_list e') :: k)) st inp = run (tf_ops_if c t e) st inp.
  Proof.
    intros c t e t' e' k st inp Ht He.
    rewrite run_of_list. cbn [run_list]. rewrite !run_if.
    rewrite (run_to_list t), (run_to_list e), Ht, He, !run_list_app, !run_of_list.
    destruct (beq_dec _ _); reflexivity.
  Qed.

  Lemma merge_arms_correct : forall c t e st inp,
    run (merge_arms c t e) st inp = run (tf_ops_if c t e) st inp.
  Proof.
    intros c t e st inp. unfold merge_arms.
    destruct (split_suffix (to_list t) (to_list e)) as [[t' e'] k] eqn:Hs.
    destruct (split_suffix_spec _ _ _ _ _ Hs) as [Ht He].
    assert (Hf : run (if existsb has_call k then of_list (tf_ops_if c (of_list t') (of_list e') :: k)
                      else tf_ops_if c t e) st inp = run (tf_ops_if c t e) st inp)
      by (destruct (existsb has_call k); [ apply run_factor; assumption | reflexivity ]).
    destruct t' as [| [[| | | p d a1] | | ] [|]]; try exact Hf.
    destruct e' as [| [[| | | p' d' a2] | | ] [|]]; try exact Hf.
    destruct (eq_dec p p') as [<- |]; [| exact Hf].
    destruct (eq_dec d d') as [<- |]; [| exact Hf].
    rewrite <- (run_factor c t e [tf_ops_base (tf_call p d a1)] [tf_ops_base (tf_call p d a2)] k st inp Ht He).
    rewrite !run_of_list. cbn [run_list of_list]. rewrite run_call_if. reflexivity.
  Qed.

  Theorem merge_calls_correct : forall o st inp, run (merge_calls o) st inp = run o st inp.
  Proof.
    induction o as [op | a IHa b IHb | c t IHt e IHe]; intros st inp.
    - reflexivity.
    - cbn [merge_calls]. rewrite !run_cons, IHa, IHb. reflexivity.
    - cbn [merge_calls]. rewrite merge_arms_correct, !run_if, IHt, IHe. reflexivity.
  Qed.
End MergeCalls.

Definition merge_calls_ctx (ctx: TFSchedContext) : TFSchedContext := {|
  tfs_spec_states := tfs_spec_states ctx;
  tfs_spec_states_eq_dec := tfs_spec_states_eq_dec ctx;
  tfs_spec_states_fin := tfs_spec_states_fin ctx;
  tfs_spec_states_names := tfs_spec_states_names ctx;
  tfs_spec_states_size := tfs_spec_states_size ctx;
  tfs_spec_states_init := tfs_spec_states_init ctx;
  tfs_spec_inputs := tfs_spec_inputs ctx;
  tfs_spec_inputs_eq_dec := tfs_spec_inputs_eq_dec ctx;
  tfs_spec_inputs_fin := tfs_spec_inputs_fin ctx;
  tfs_spec_inputs_names := tfs_spec_inputs_names ctx;
  tfs_spec_inputs_size := tfs_spec_inputs_size ctx;
  tfs_spec_inputs_class := tfs_spec_inputs_class ctx;
  tfs_spec_outputs := tfs_spec_outputs ctx;
  tfs_spec_outputs_eq_dec := tfs_spec_outputs_eq_dec ctx;
  tfs_spec_outputs_fin := tfs_spec_outputs_fin ctx;
  tfs_spec_outputs_names := tfs_spec_outputs_names ctx;
  tfs_spec_outputs_size := tfs_spec_outputs_size ctx;
  tfs_spec_outputs_class := tfs_spec_outputs_class ctx;
  tfs_spec_ips := tfs_spec_ips ctx;
  tfs_spec_ips_eq_dec := tfs_spec_ips_eq_dec ctx;
  tfs_spec_ips_fin := tfs_spec_ips_fin ctx;
  tfs_spec_ips_names := tfs_spec_ips_names ctx;
  tfs_spec_ip := tfs_spec_ip ctx;
  tfs_spec_action := tfs_spec_action ctx;
  tfs_spec_action_eq_dec := tfs_spec_action_eq_dec ctx;
  tfs_spec_action_fin := tfs_spec_action_fin ctx;
  tfs_spec_action_ops := fun a => merge_calls (tfs_spec_action_ops ctx a);
  tfs_spec_decls := tfs_spec_decls ctx
|}.

Lemma merge_calls_ctx_correct (ctx: TFSchedContext) a st inp :
  tf_ops_run (tfs_spec_states_size ctx) (tfs_spec_inputs_size ctx) (tfs_spec_outputs_size ctx)
    (tfs_spec_ip ctx) (tfs_spec_action_ops (merge_calls_ctx ctx) a) st inp
  = tf_ops_run (tfs_spec_states_size ctx) (tfs_spec_inputs_size ctx) (tfs_spec_outputs_size ctx)
    (tfs_spec_ip ctx) (tfs_spec_action_ops ctx a) st inp.
Proof. apply merge_calls_correct. Qed.
