(*! The injectivity of the nat -> string encoding in Utils.v.  Only
    [string_id_of_nat_inj] is used downstream, by the synthesis proof, where it
    rules out two registers sharing a Verilog name; the other three prove it. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Utils.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Import ListNotations.

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Section Properties.
  
  Lemma increment_inj (b1 b2 : list bool) :
    increment b1 = increment b2 -> (b1 = b2 \/ b1 = [] \/ b2 = []).
  Proof.
    intros H. inversion H. clear H.
    generalize dependent b2.
    induction b1 as [| b1 b1']; intros.
    {
      sauto.
    }
    {
      simpl in H1. destruct b1.
      - sauto.
      - unfold increment in H1. destruct b2.
        + sauto.
        + destruct b.
          * sauto.
          * sauto.
    }
  Qed.

  Lemma nat_to_bin_inj (n m : nat) :
    nat_to_bin n = nat_to_bin m -> n = m.
  Proof.
    intros H.
    generalize dependent m.
    induction n.
    {
      intros.
      simpl in H. destruct m.
      - sauto. 
      - exfalso. simpl in H. destruct m. sauto. destruct m. sauto. simpl in H.
        destruct (nat_to_bin m). sauto. simpl in H. destruct b. simpl in H. destruct (increment l). sauto. simpl in H. destruct b. sauto. sauto.
        simpl in H. sauto.
    }
    {
      intros.
      destruct m.
      - simpl in H. destruct n. sauto. simpl in H. destruct n. sauto. simpl in H. destruct (nat_to_bin n). sauto. simpl in H. destruct b. simpl in H. 
        destruct (increment l). sauto. simpl in H. destruct b. sauto. sauto. simpl in H. sauto.
      - simpl in H. apply increment_inj in H. destruct H as [H_eq | H_empty].
        + apply IHn in H_eq. sauto.
        + contradict H_empty. unfold not. intros. destruct H.
          * destruct n. sauto. simpl in H. destruct (nat_to_bin n). sauto. simpl in H. destruct b. sauto. sauto.
          * destruct m. sauto. simpl in H. destruct (nat_to_bin m). sauto. simpl in H. destruct b. sauto. sauto.
    }
  Qed.

  Lemma bin_to_string_inj (b1 b2 : list bool) :
    bin_to_string b1 = bin_to_string b2 -> b1 = b2.
  Proof.
    intros H.
    generalize dependent b2.
    induction b1 as [| b1 b1']; intros.
    {
      simpl in H. destruct b2.
      - sauto.
      - simpl in H. destruct b. sauto. sauto.
    }
    {
      simpl in H. destruct b2.
      - sauto.
      - simpl in H. 
        assert (b1 = b) by (destruct b1; destruct b2; inversion H; sauto). subst b1.
        f_equal.
        + destruct b. apply IHb1'; sauto. apply IHb1'; sauto.
    }
  Qed.

  Lemma string_id_of_nat_inj (n m : nat) :
    string_id_of_nat n = string_id_of_nat m -> n = m.
  Proof.
    unfold string_id_of_nat.
    intros H.
    apply nat_to_bin_inj.
    apply bin_to_string_inj in H.
    sauto.
  Qed.

End Properties.
