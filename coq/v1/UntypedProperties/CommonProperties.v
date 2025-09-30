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
