(*! Declassification rule: exclusive or.  `xor` is invertible once one operand
    is known, so each operand is recoverable from the node and the other.  Two
    unconditional instances per `DFG_Binary tf_xor` node. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.DFG.
Require Import Trustformer.Declassification.PacketLemmas.

Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

(* Koika has no xor lemmas; these mirror the shape of [Bits.neg_involutive]. *)
Fixpoint xor_comm {sz} (x y: bits sz) {struct sz} :
  Bits.xor x y = Bits.xor y x.
Proof.
  destruct sz.
  - destruct x, y. reflexivity.
  - destruct x as [a x'], y as [b y']. unfold Bits.xor in *. cbn.
    unfold vect_cons. f_equal;
      [ destruct a, b; reflexivity | apply xor_comm ].
Defined.

Fixpoint xor_cancel_r {sz} (bs k: bits sz) {struct sz} :
  Bits.xor (Bits.xor bs k) k = bs.
Proof.
  destruct sz.
  - destruct bs, k. reflexivity.
  - destruct bs as [b bs'], k as [c k']. unfold Bits.xor in *. cbn.
    unfold vect_cons. f_equal;
      [ destruct b, c; reflexivity | apply xor_cancel_r ].
Defined.


Lemma xor_cancel_l {sz} (x y: bits sz) :
  Bits.xor (Bits.xor x y) x = y.
Proof. rewrite (xor_comm x y). apply xor_cancel_r. Qed.


Definition xor_rule {s i o p} (dfg: @dfg_state_t s i o p) : list decl_instance :=
  flat_map
    (fun n =>
       match op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}) with
       | DFG_Binary tf_xor a1 a2 =>
           [ {| di_target := a1; di_sources := [n; a2]; di_guard := [] |};
             {| di_target := a2; di_sources := [n; a1]; di_guard := [] |} ]
       | _ => []
       end)
    (List.seq 1 (length (graph dfg) - 1)).

(* xor is its own inverse: either operand is the node xor the other. *)
Definition xor_extract {s i o p} (g: @dfg_state_t s i o p) (inst: decl_instance)
    (w: valuation g) : bits_t (node_sz g (di_target inst)) :=
  convert (Bits.xor (w (nth 0 (di_sources inst) 0))
                    (convert (w (nth 1 (di_sources inst) 0)))).

Lemma xor_packet_sound {s i o p} (g: @dfg_state_t s i o p) inst (val w: valuation g) :
  well_sized g -> In inst (xor_rule g) -> consistent g val ->
  guard_holds g val (di_guard inst) ->
  (forall x, In x (di_sources inst) -> w x = val x) ->
  val (di_target inst) = xor_extract g inst w.
Proof.
  intros Hws Hin Hcons _ Hagree.
  unfold xor_rule in Hin. apply in_flat_map in Hin. destruct Hin as [n [_ Hi]].
  specialize (Hws n). specialize (Hcons n).
  unfold xor_extract, consistent, well_sized, node_sz, node_at in *.
  revert Hws Hcons Hi.
  destruct (op (nth n (graph g) {| nid := 0; op := DFG_Empty; sz := 0 |}))
    as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa | dp darg den
       | sp stok sen | ja jb | ];
    intros Hws Hcons Hi; cbn [List.In] in Hi; try contradiction.
  destruct bop; cbn [List.In] in Hi; try contradiction.
  destruct Hws as [H1 H2].
  destruct Hi as [<- | [<- | []]]; cbn [di_target di_sources nth] in *;
    rewrite (Hagree n (or_introl eq_refl)),
            (Hagree _ (or_intror (or_introl eq_refl))), Hcons; cbn [op2_bits].
  - rewrite xor_cancel_r. symmetry. apply convert_roundtrip. exact H1.
  - rewrite xor_cancel_l. symmetry. apply convert_roundtrip. exact H2.
Qed.

Definition xor_packet {s i o p} : decl_packet s i o p :=
  {| dp_rule := xor_rule; dp_extract := xor_extract; dp_sound := xor_packet_sound |}.
