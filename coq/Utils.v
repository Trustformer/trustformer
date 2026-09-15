Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Init.Tactics.
Require Import Coq.Init.Nat.
Require Import Program.  
Require Import Coq.micromega.Lia.
Require Import Arith Bool List.
Import ListNotations.


Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

(* Helper functions & code for an injective nat -> string representation *)
Fixpoint increment (b : list bool) : list bool :=
  match b with
  | [] => [false]
  | false :: bs => true :: bs
  | true :: bs => false :: increment bs
  end.


Fixpoint nat_to_bin (n : nat) : list bool :=
  match n with
  | 0 => [false]
  | S n' => increment (nat_to_bin n')
  end.

Fixpoint bin_to_string (b : list bool) : string :=
  match b with
  | [] => ""
  | false :: bs => "0" ++ bin_to_string bs
  | true :: bs => "1" ++ bin_to_string bs
  end.

Definition string_id_of_nat (n : nat) : string :=
  bin_to_string (nat_to_bin n).


Section Properties.
  
  Lemma increment_changes_list (b : list bool) :
    b <> increment b.
  Proof.
    intros H.
    induction b as [| b b']; intros.
    {
      simpl in H. sauto.
    }
    {
      simpl in H. destruct b.
      - inversion H.
      - inversion H.
    }
  Qed.

  Lemma increment_ge_length (b : list bool) :
    length (increment b) >= length b.
  Proof.
    induction b as [| b b']; intros.
    - simpl. lia.
    - simpl. destruct b.
      + simpl. lia.
      + simpl. lia.
  Qed.

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

(*
Fixpoint string_id_of_nat (n : nat) : string :=
  match n with
    | 0 => "0"
    | S n' => "S" ++ string_id_of_nat n'
  end.

Eval compute in (string_id_of_nat 5).

Section Properties.
    
  Lemma string_id_of_nat_inj (n m : nat) :
    string_id_of_nat n = string_id_of_nat m -> n = m.
  Proof.
    intros H. 
    generalize dependent m.
    induction n. 
    {
      intros.
      simpl in H. destruct m.
      - reflexivity.
      - inversion H.
    }
    {
      intros.
      destruct m.
      - inversion H.
      - injection H as H_inj. assert (n = m) by (apply IHn; assumption). subst n.
        reflexivity.
    }

  Qed.

End Properties. *)

(* ===================================================================== *)
(*  FiniteType / Show / EqDec plumbing                                   *)
(* ===================================================================== *)
(*
    A design with no attached IP names its IPs by [Empty_set]; a lowered
    schedule's inputs are the design's inputs PLUS one response per IP.  Koika
    provides instances for neither shape.

    Note: inside [Koika.Frontend], bare [length] is [String.length] and bare
    [map] is [Env.map], so the list operations below are qualified.
*)

Require Import Koika.Frontend.

#[global] Instance Empty_set_eqdec : EqDec Empty_set :=
  {| eq_dec := fun (x: Empty_set) _ => match x with end |}.

#[global] Instance Empty_set_show : Show Empty_set :=
  {| show := fun (x: Empty_set) => match x with end |}.

#[global] Instance Empty_set_finite : FiniteType Empty_set :=
  {| finite_index := fun (x: Empty_set) => match x with end;
     finite_elements := [];
     finite_surjective := fun (a: Empty_set) => match a with end;
     finite_injective := NoDup_nil _ |}.

Lemma NoDup_map_shift {B} (k: nat) (f: B -> nat) (l: list B) :
  NoDup (List.map f l) -> NoDup (List.map (fun b => k + f b) l).
Proof.
  intros H.
  rewrite <- List.map_map with (f := f) (g := fun n => k + n).
  apply NoDup_map; [ exact H | intros; lia ].
Qed.

Lemma finite_index_lt {A} {FA: FiniteType A} (a: A) :
  finite_index a < List.length (finite_elements (T:=A)).
Proof.
  apply nth_error_Some. rewrite finite_surjective. discriminate.
Qed.

#[global] Program Instance sum_finite {A B} {FA: FiniteType A} {FB: FiniteType B}
  : FiniteType (A + B) :=
  {| finite_index x := match x with
                       | inl a => finite_index a
                       | inr b => List.length (finite_elements (T:=A)) + finite_index b
                       end;
     finite_elements := List.map inl (finite_elements (T:=A))
                        ++ List.map inr (finite_elements (T:=B)) |}.
Next Obligation.
  destruct a as [a|b].
  - rewrite nth_error_app1 by (rewrite List.map_length; apply finite_index_lt).
    apply List.map_nth_error. apply finite_surjective.
  - rewrite nth_error_app2 by (rewrite List.map_length; lia).
    rewrite List.map_length.
    replace (List.length (finite_elements (T:=A)) + finite_index b
             - List.length (finite_elements (T:=A))) with (finite_index b) by lia.
    apply List.map_nth_error. apply finite_surjective.
Qed.
Next Obligation.
  rewrite List.map_app, !List.map_map. cbn.
  apply NoDup_app.
  - apply (finite_injective (FiniteType:=FA)).
  - apply NoDup_map_shift. apply (finite_injective (FiniteType:=FB)).
  - intros x Hx Hy.
    apply List.in_map_iff in Hx as [a [<- _]].
    apply List.in_map_iff in Hy as [b [Hb _]].
    pose proof (finite_index_lt a). lia.
Qed.

#[global] Instance sum_show {A B} {SA: Show A} {SB: Show B} : Show (A + B) :=
  {| show x := match x with inl a => show a | inr b => show b end |}.
