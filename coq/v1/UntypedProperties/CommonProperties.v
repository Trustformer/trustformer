(*! Properties that are useful to reason about untyped semantics !*)
(* TODO: move this to the kôika repo *)
Require Export Koika.Utils.Common.
Require Import Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.KoikaForm.Untyped.UntypedLogs.

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Section Logs.
    Context {V: Type}.

    Context {reg_t: Type}.
    Context {REnv: Env reg_t}.
    Definition R : reg_t -> Type := fun _ => V.

    Notation Log := (@_ULog V reg_t REnv).

    Lemma log_find_empty {T} idx (f: @LogEntry (R idx) -> option T):
        log_find (log_empty: Log) idx f = None.
    Proof.
        unfold log_find, log_empty; intros; rewrite getenv_create; reflexivity.
    Qed.

    Lemma log_app_assoc : forall (l1 l2 l3: Log),
        log_app (log_app l1 l2) l3 = log_app l1 (log_app l2 l3).
    Proof.
        unfold log_app, map2; intros.
        apply create_funext. intros.
        rewrite !getenv_create.
        rewrite app_assoc.
        reflexivity.
    Qed.

    Lemma log_app_empty_l : forall (l: Log),
        log_app log_empty l = l.
    Proof.
        intros.
        apply equiv_eq.
        unfold equiv, log_app, map2, log_empty; intros.
        rewrite !getenv_create, app_nil_l.
        reflexivity.
    Qed.

    Lemma log_app_empty_r : forall (l: Log),
        log_app l log_empty = l.
    Proof.
        intros.
        apply equiv_eq.
        unfold equiv, log_app, map2, log_empty; intros.
        rewrite !getenv_create, app_nil_r.
        reflexivity.
    Qed.


End Logs.

Section FiniteType.

    Context {T: Type}.
    Context {fin_t: FiniteType T}.

    Definition finite_cardinality := List.length (finite_elements).

    Lemma finite_index_in_range (x: T):
        (finite_index x < finite_cardinality)%nat.
    Proof.
        unfold finite_cardinality.
        generalize (finite_surjective x). intros H.
        apply nth_error_Some. timeout 10 sauto.
    Qed.

    Definition finite_bits_needed :=
        log2 finite_cardinality.

    Lemma finite_bits_needed_correct (x: T):
        (finite_index x < 2 ^ finite_bits_needed)%nat.
    Proof.
        unfold finite_bits_needed, finite_cardinality.
        generalize (finite_surjective x). intros H.
        assert (H_lt : finite_index x < Datatypes.length finite_elements).
        { apply nth_error_Some. timeout 10 sauto. }
        assert (H_log : Datatypes.length finite_elements <= 2 ^ log2 (Datatypes.length finite_elements)).
        { 
            destruct (Datatypes.length finite_elements) as [| [| n]]; simpl.
            - lia.
            - lia.
            - apply Nat.log2_up_spec. lia.
        }
        timeout 10 lia.
    Qed.

End FiniteType.

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
    
    Lemma scheduler_has_rule_dec:
        forall (s: sched) (r: rule_name_t),
        {scheduler_has_rule s r} + {~ scheduler_has_rule s r}.
    Proof.
        induction s; intros; simpl.
        - right; intros H; inversion H.
        - destruct (eq_dec r r0).
            + left; auto.
            + specialize (IHs r0). auto.
        - destruct (eq_dec r r0).
            + left; auto.
            + specialize (IHs1 r0). specialize (IHs2 r0).
                destruct IHs1; destruct IHs2.
                * left; auto.
                * left; auto.
                * left; auto.
                * right. intros [H1 | H2]; auto.
        - specialize (IHs r). auto.
    Qed.

    Lemma scheduler_has_not_rule_inductive:
        forall (s: sched) (r: rule_name_t),
        ~ scheduler_has_rule s r ->
            match s with
            | Done => True
            | Cons r0 s' => if eq_dec r0 r then False else ~ scheduler_has_rule s' r
            | Try r0 s1 s2 => if eq_dec r0 r then False else (~ scheduler_has_rule s1 r /\ ~ scheduler_has_rule s2 r)
            | SPos p s' => ~ scheduler_has_rule s' r
            end.
    Proof.
        induction s; intros; simpl in *.
        - auto.
        - destruct (eq_dec r r0).
            + exfalso; apply H. timeout 10 sauto.
            + timeout 10 sauto.
        - destruct (eq_dec r r0).
            + exfalso; apply H. timeout 10 sauto.
            + timeout 10 sauto.
        - timeout 10 sauto.
    Qed.

End Schedule.
