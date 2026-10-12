(*! Declassification rule: `not` is invertible, so a node's operand is
    recoverable from it.  Each rule here is self-contained and users pick the
    ones they want in `tfs_spec_decls`, the empty list giving blackbox. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.DFG.
Require Import Trustformer.Declassification.PacketLemmas.

Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

(* Nodes are visited by position, so [1 <= n] and [n < length] come for free
   from [in_seq]; position and [nid] coincide in the exported graph. *)
Definition neg_rule {s i o p} (dfg: @dfg_state_t s i o p) : list decl_instance :=
  flat_map
    (fun n =>
       match op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}) with
       | DFG_Unary tf_not arg => [ {| di_target := arg; di_sources := [n]; di_guard := [] |} ]
       | _ => []
       end)
    (List.seq 1 (length (graph dfg) - 1)).

(* The operand is the negation of the node. *)
Definition neg_extract {s i o p} (g: @dfg_state_t s i o p) (inst: decl_instance)
    (w: valuation g) : bits_t (node_sz g (di_target inst)) :=
  convert (Bits.neg (w (nth 0 (di_sources inst) 0))).

Lemma neg_packet_sound {s i o p} (g: @dfg_state_t s i o p) inst (val w: valuation g) :
  well_sized g -> In inst (neg_rule g) -> consistent g val ->
  guard_holds g val (di_guard inst) ->
  (forall x, In x (di_sources inst) -> w x = val x) ->
  val (di_target inst) = neg_extract g inst w.
Proof.
  intros Hws Hin Hcons _ Hagree.
  unfold neg_rule in Hin. apply in_flat_map in Hin. destruct Hin as [n [_ Hi]].
  specialize (Hws n). specialize (Hcons n).
  unfold neg_extract, consistent, well_sized, node_sz, node_at in *.
  revert Hws Hcons Hi.
  destruct (op (nth n (graph g) {| nid := 0; op := DFG_Empty; sz := 0 |}))
    as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa | dp darg den
       | sp stok sen | ja jb | ];
    intros Hws Hcons Hi; cbn [List.In] in Hi; try contradiction.
  destruct uop as [| source_size | ss off]; cbn [List.In] in Hi; [ | contradiction | contradiction ].
  destruct Hi as [<- | []]. cbn [di_target di_sources nth] in *.
  rewrite (Hagree n (or_introl eq_refl)), Hcons. cbn [op1_bits].
  rewrite Bits.neg_involutive.
  symmetry. apply convert_roundtrip. exact Hws.
Qed.

Definition neg_packet {s i o p} : decl_packet s i o p :=
  {| dp_rule := neg_rule; dp_extract := neg_extract; dp_sound := neg_packet_sound |}.
