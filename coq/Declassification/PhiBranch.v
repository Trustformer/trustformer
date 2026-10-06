(*! Declassification rule: for `n = Phi c t e`, wherever `c` holds the node's
    value IS the then-branch's -- the paper's PhiAUT, the one rule with a
    NON-EMPTY guard.  Both directions, downward giving the lockbox pattern. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.DFG.
Require Import Trustformer.Declassification.PacketLemmas.

Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

Definition phibranch_rule {s i o p} (dfg: @dfg_state_t s i o p) : list decl_instance :=
  flat_map
    (fun n =>
       let dflt := {| nid := 0; op := DFG_Empty; sz := 0 |} in
       match op (nth n (graph dfg) dflt) with
       | DFG_Phi cnd tid eid =>
           [ {| di_target := n;   di_sources := [tid]; di_guard := [(cnd, true)] |}
           ; {| di_target := tid; di_sources := [n];   di_guard := [(cnd, true)] |}
           ; {| di_target := n;   di_sources := [eid]; di_guard := [(cnd, false)] |}
           ; {| di_target := eid; di_sources := [n];   di_guard := [(cnd, false)] |} ]
       | _ => []
       end)
    (List.seq 1 (length (graph dfg) - 1)).

(* The selected arm and the phi carry the same bits. *)
Definition phibranch_extract {s i o p} (g: @dfg_state_t s i o p) (inst: decl_instance)
    (w: valuation g) : bits_t (node_sz g (di_target inst)) :=
  convert (w (nth 0 (di_sources inst) 0)).

Lemma phibranch_packet_sound {s i o p} (g: @dfg_state_t s i o p) inst (val w: valuation g) :
  well_sized g -> In inst (phibranch_rule g) -> consistent g val ->
  guard_holds g val (di_guard inst) ->
  (forall x, In x (di_sources inst) -> w x = val x) ->
  val (di_target inst) = phibranch_extract g inst w.
Proof.
  intros Hws Hin Hcons Hg Hagree.
  unfold phibranch_rule in Hin. apply in_flat_map in Hin. destruct Hin as [n [_ Hi]].
  cbv zeta in Hi. pose proof (Hws n) as Hwn. pose proof (Hcons n) as Hcn.
  unfold phibranch_extract, guard_holds, consistent, well_sized, node_sz, node_at in *.
  revert Hwn Hcn Hi.
  destruct (op (nth n (graph g) {| nid := 0; op := DFG_Empty; sz := 0 |}))
    as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa | dp darg den
       | sp stok sen | ja jb | ];
    intros Hwn Hcn Hi; try (cbn [List.In] in Hi; contradiction).
  destruct Hwn as [_ [Htsz Hesz]].
  destruct Hi as [<- | [<- | [<- | [<- | []]]]];
    cbn [di_target di_sources di_guard nth] in *;
    specialize (Hg cnd _ (or_introl eq_refl));
    rewrite (Hagree _ (or_introl eq_refl)), Hcn;
    match goal with
    | H: @nonzero _ ?v = ?b |- context [if @nonzero ?w ?v then _ else _] =>
        replace (@nonzero w v) with b by (symmetry; exact H)
    end; cbv beta iota;
    first [ reflexivity
          | symmetry; apply convert_roundtrip; first [ exact Htsz | exact Hesz ] ].
Qed.

Definition phibranch_packet {s i o p} : decl_packet s i o p :=
  {| dp_rule := phibranch_rule; dp_extract := phibranch_extract;
     dp_sound := phibranch_packet_sound |}.
