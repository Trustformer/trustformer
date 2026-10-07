(*! Declassification rule: a phi between two constants differing AS BITVECTORS
    at the node's width makes the selector recoverable -- the paper's PhiCUT.
    Unconditional; the taint analysis composes it with the lockbox's guard. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.DFG.
Require Import Trustformer.Declassification.PacketLemmas.

Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

(* Distinctness is checked on the evaluated bitvectors: as naturals 0 and 2
   differ, but at width 1 they denote the same value. *)
Definition phiconst_rule {s i o p} (dfg: @dfg_state_t s i o p) : list decl_instance :=
  flat_map
    (fun n =>
       let dflt := {| nid := 0; op := DFG_Empty; sz := 0 |} in
       let nd := nth n (graph dfg) dflt in
       match op nd with
       | DFG_Phi cnd tid eid =>
           match op (nth tid (graph dfg) dflt), op (nth eid (graph dfg) dflt) with
           | DFG_Const kt, DFG_Const ke =>
               if beq_dec (Bits.of_nat (sz nd) kt) (Bits.of_nat (sz nd) ke)
               then []
               else [ {| di_target := cnd; di_sources := [n]; di_guard := [] |} ]
           | _, _ => []
           end
       | _ => []
       end)
    (List.seq 1 (length (graph dfg) - 1)).

(* The arms differ, so the phi's value names the arm: the condition is one
   exactly when the value is the then-constant. *)
Definition phiconst_extract {s i o p} (g: @dfg_state_t s i o p) (inst: decl_instance)
    (w: valuation g) : bits_t (node_sz g (di_target inst)) :=
  let n := nth 0 (di_sources inst) 0 in
  match op (node_at g n) with
  | DFG_Phi _ tid _ =>
      match op (node_at g tid) with
      | DFG_Const kt =>
          if beq_dec (w n) (Bits.of_nat (node_sz g n) kt) then Bits.of_nat _ 1 else Bits.zero
      | _ => Bits.zero
      end
  | _ => Bits.zero
  end.

Lemma phiconst_packet_sound {s i o p} (g: @dfg_state_t s i o p) inst (val w: valuation g) :
  well_sized g -> In inst (phiconst_rule g) -> consistent g val ->
  guard_holds g val (di_guard inst) ->
  (forall x, In x (di_sources inst) -> w x = val x) ->
  val (di_target inst) = phiconst_extract g inst w.
Proof.
  intros Hws Hin Hcons _ Hagree.
  unfold phiconst_rule in Hin. apply in_flat_map in Hin. destruct Hin as [n [_ Hi]].
  cbv zeta in Hi. pose proof (Hws n) as Hwn. pose proof (Hcons n) as Hcn.
  unfold phiconst_extract, consistent, well_sized, node_sz, node_at in *.
  revert Hwn Hcn Hi.
  destruct (op (nth n (graph g) {| nid := 0; op := DFG_Empty; sz := 0 |}))
    as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa | dp darg den
       | sp stok sen | ja jb | ] eqn:Hop;
    intros Hwn Hcn Hi; try (cbn [List.In] in Hi; contradiction).
  pose proof (Hcons tid) as Hct. pose proof (Hcons eid) as Hce.
  revert Hct Hce Hi.
  destruct (op (nth tid (graph g) {| nid := 0; op := DFG_Empty; sz := 0 |}))
    as [kt | | | | | | | | | | | ] eqn:Hopt; intros Hct Hce Hi; try contradiction.
  revert Hce Hi.
  destruct (op (nth eid (graph g) {| nid := 0; op := DFG_Empty; sz := 0 |}))
    as [ke | | | | | | | | | | | ] eqn:Hope; intros Hce Hi; try contradiction.
  destruct (beq_dec _ _) eqn:Hdistinct in Hi; [ contradiction | ].
  destruct Hi as [<- | []]. cbn [di_target di_sources nth] in *.
  rewrite Hop, Hopt, (Hagree n (or_introl eq_refl)), Hcn, Hct, Hce.
  destruct Hwn as [Hcsz [Htsz Hesz]].
  assert (Ht : convert (szB := sz (nth n (graph g) {| nid := 0; op := DFG_Empty; sz := 0 |}))
                 (Bits.of_nat (sz (nth tid (graph g) {| nid := 0; op := DFG_Empty; sz := 0 |})) kt)
               = Bits.of_nat _ kt) by (rewrite Htsz; apply convert_id).
  assert (He : convert (szB := sz (nth n (graph g) {| nid := 0; op := DFG_Empty; sz := 0 |}))
                 (Bits.of_nat (sz (nth eid (graph g) {| nid := 0; op := DFG_Empty; sz := 0 |})) ke)
               = Bits.of_nat _ ke) by (rewrite Hesz; apply convert_id).
  rewrite Ht, He.
  match goal with |- context [if @nonzero ?w ?v then _ else _] => destruct (@nonzero w v) eqn:Hnz end;
    cbv beta iota.
  - match goal with |- context [@beq_dec ?T ?E ?x ?y] => destruct (@beq_dec T E x y) eqn:Eb end;
      [ exact (nonzero_true_1 _ Hcsz Hnz) | ].
    exfalso. apply beq_dec_false_iff in Eb. apply Eb. reflexivity.
  - match goal with |- context [@beq_dec ?T ?E ?x ?y] => destruct (@beq_dec T E x y) eqn:Ee end.
    + apply beq_dec_iff in Ee. rewrite Ee, beq_dec_refl in Hdistinct. discriminate.
    + exact (nonzero_false _ Hnz).
Qed.

Definition phiconst_packet {s i o p} : decl_packet s i o p :=
  {| dp_rule := phiconst_rule; dp_extract := phiconst_extract;
     dp_sound := phiconst_packet_sound |}.
