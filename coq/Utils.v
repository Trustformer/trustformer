Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Init.Tactics.
Require Import Coq.Init.Nat.
Require Import Program.  
Require Import Coq.micromega.Lia.
Require Import Arith Bool List.
Import ListNotations.

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

(* ===================================================================== *)
(*  FiniteType / Show / EqDec plumbing                                   *)
(* ===================================================================== *)
(* Instances for [Empty_set] (a design with no IP) and for sums (a lowered
   schedule's inputs: the design's, plus one response per IP).  Inside
   [Koika.Frontend] bare [length]/[map] are String/Env, hence the qualifiers. *)

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
