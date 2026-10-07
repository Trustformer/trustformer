(*! Declassification rule: a widening resize keeps every source bit, so the
    operand is recoverable by narrowing back; the width check restricts it to
    [szA <= szB]. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.DFG.
Require Import Trustformer.Declassification.PacketLemmas.

Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

(* [DFG_Resize] takes its source width from the argument node, while
   [DFG_Unary (tf_resize source_size)] carries it explicitly; both encodings
   occur, and both are widening exactly when the source width is not larger. *)
Definition widen_rule {s i o p} (dfg: @dfg_state_t s i o p) : list decl_instance :=
  flat_map
    (fun n =>
       let dflt := {| nid := 0; op := DFG_Empty; sz := 0 |} in
       let nd := nth n (graph dfg) dflt in
       let keep arg source_size :=
         if Nat.leb source_size (sz nd)
         then [ {| di_target := arg; di_sources := [n]; di_guard := [] |} ]
         else [] in
       match op nd with
       | DFG_Resize arg => keep arg (sz (nth arg (graph dfg) dflt))
       | DFG_Unary (tf_resize source_size) arg => keep arg source_size
       | _ => []
       end)
    (List.seq 1 (length (graph dfg) - 1)).

(* Widening pads at the top, so the operand is the node's low bits. *)
Definition widen_extract {s i o p} (g: @dfg_state_t s i o p) (inst: decl_instance)
    (w: valuation g) : bits_t (node_sz g (di_target inst)) :=
  convert (w (nth 0 (di_sources inst) 0)).

Lemma widen_packet_sound {s i o p} (g: @dfg_state_t s i o p) inst (val w: valuation g) :
  well_sized g -> In inst (widen_rule g) -> consistent g val ->
  guard_holds g val (di_guard inst) ->
  (forall x, In x (di_sources inst) -> w x = val x) ->
  val (di_target inst) = widen_extract g inst w.
Proof.
  intros Hws Hin Hcons _ Hagree.
  unfold widen_rule in Hin. apply in_flat_map in Hin. destruct Hin as [n [_ Hi]].
  specialize (Hws n). specialize (Hcons n). cbv zeta in Hi.
  unfold widen_extract, consistent, well_sized, node_sz, node_at in *.
  revert Hws Hcons Hi.
  destruct (op (nth n (graph g) {| nid := 0; op := DFG_Empty; sz := 0 |}))
    as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa | dp darg den
       | sp stok sen | ja jb | ];
    intros Hws Hcons Hi; try (cbn [List.In] in Hi; contradiction).
  - destruct uop as [| src]; [ cbn [List.In] in Hi; contradiction | ].
    destruct (Nat.leb src _) eqn:Hle; cbn [List.In] in Hi; [ | contradiction ].
    destruct Hi as [<- | []]. cbn [di_target di_sources nth] in *.
    rewrite (Hagree n (or_introl eq_refl)), Hcons. cbn [op1_bits].
    subst src. rewrite convert_id.
    symmetry. apply convert_widen_narrow. apply Nat.leb_le. exact Hle.
  - destruct (Nat.leb _ _) eqn:Hle; cbn [List.In] in Hi; [ | contradiction ].
    destruct Hi as [<- | []]. cbn [di_target di_sources nth] in *.
    rewrite (Hagree n (or_introl eq_refl)), Hcons.
    symmetry. apply convert_widen_narrow. apply Nat.leb_le. exact Hle.
Qed.

Definition widen_packet {s i o p} : decl_packet s i o p :=
  {| dp_rule := widen_rule; dp_extract := widen_extract; dp_sound := widen_packet_sound |}.
