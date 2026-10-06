(*! Bit facts the packet proofs share: how [convert] behaves between widths,
    and what a branch condition is once it reads true or false. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.
Require Import Koika.BitsToLists.

Require Import Trustformer.Semantics.
Require Import Trustformer.DFG.

Require Import Coq.Lists.List.
Require Import Lia.

Lemma convert_id {w} (x: bits_t w) : convert (szA := w) (szB := w) x = x.
Proof.
  unfold convert. destruct (eq_dec w w) as [e | ne].
  - rewrite (Eqdep_dec.UIP_dec eq_dec e eq_refl). reflexivity.
  - exfalso. apply ne. reflexivity.
Qed.

Lemma convert_roundtrip {a b} (x: bits_t a) :
  a = b -> convert (szA := b) (szB := a) (convert (szB := b) x) = x.
Proof. intros <-. rewrite !convert_id. reflexivity. Qed.

Lemma convert_cast {a b} (x: bits_t a) (y: bits_t b) (e: a = b) :
  convert (szB := b) x = y -> x = convert y.
Proof. destruct e. rewrite !convert_id. auto. Qed.

(* Widening pads at the top and narrowing drops it, so one list-level resize
   covers [convert] in both directions. *)
Definition resize_bits (w: nat) (l: list bool) : list bool :=
  firstn w (l ++ List.repeat false w).

Lemma firstn_repeat_false (k m: nat) :
  firstn k (List.repeat false m) = List.repeat false (Nat.min k m).
Proof.
  revert m. induction k as [| k IH]; intro m; [ reflexivity | ].
  destruct m as [| m]; [ reflexivity | ].
  cbn [List.repeat firstn Nat.min]. rewrite IH. reflexivity.
Qed.

Lemma convert_to_list (szA szB: nat) (x: bits_t szA) :
  vect_to_list (convert (szB := szB) x) = resize_bits szB (vect_to_list x).
Proof.
  unfold convert, resize_bits.
  destruct (eq_dec szA szB) as [e | ne].
  - destruct e. cbn [eq_rect].
    rewrite firstn_app, vect_to_list_length.
    rewrite firstn_all2 by (rewrite vect_to_list_length; lia).
    replace (szA - szA) with 0 by lia. cbn [firstn].
    symmetry. apply app_nil_r.
  - rewrite BitsToLists.slice. cbn [take_drop' fst snd].
    rewrite firstn_app, vect_to_list_length, firstn_repeat_false.
    f_equal. f_equal. pose proof (vect_to_list_length x). lia.
Qed.

Lemma convert_widen_narrow {a b} (x: bits_t a) :
  a <= b -> convert (szA := b) (szB := a) (convert (szB := b) x) = x.
Proof.
  intro Hle. apply (vect_to_list_inj bool a).
  rewrite !convert_to_list. unfold resize_bits.
  pose proof (vect_to_list_length x) as Hl.
  rewrite firstn_app, firstn_length, app_length, repeat_length.
  replace (a - Nat.min b (length (vect_to_list x) + b)) with 0 by lia.
  cbn [firstn]. rewrite app_nil_r, firstn_firstn.
  replace (Nat.min a b) with a by lia.
  rewrite firstn_app, Hl. replace (a - a) with 0 by lia.
  cbn [firstn]. rewrite app_nil_r.
  apply firstn_all2. lia.
Qed.

Lemma nonzero_false {w} (v: bits_t w) : nonzero v = false -> v = Bits.zero.
Proof.
  unfold nonzero. destruct (beq_dec v Bits.zero) eqn:E; [ | discriminate ].
  intros _. apply beq_dec_iff in E. exact E.
Qed.

(* A one-bit condition that reads true is the bit one. *)
Lemma nonzero_true_1 {w} (v: bits_t w) :
  w = 1 -> nonzero v = true -> v = Bits.of_nat w 1.
Proof.
  intros -> Hnz. destruct v as [hd tl]. destruct tl. destruct hd; [ reflexivity | ].
  discriminate Hnz.
Qed.

Lemma convert_twice {a b c} (x: bits_t c) :
  a = b -> convert (szA := a) (szB := b) (convert (szB := a) x) = convert (szB := b) x.
Proof. intros <-. rewrite convert_id. reflexivity. Qed.

Lemma convert_zero {a b} : a = b -> convert (szA := a) (szB := b) Bits.zero = Bits.zero.
Proof. intros <-. apply convert_id. Qed.
