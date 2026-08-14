(*! Declassification rule: widening resize.  DATA ONLY -- SOUNDNESS UNPROVED.

    A widening resize keeps every source bit, so the operand is recoverable
    from the node.  Narrowing is not invertible, hence the width check.

    TODO (Phase C, agents/whitebox-untainting/PLAN.md): prove
      [widen_rule_sound : In i (widen_rule (build_dfg ctx act)) ->
                          instance_sound ctx cost_limit act a_idx input i].
    Why it is not done yet: the obligation reduces to injectivity of
    [Semantics.convert] when [szA <= szB], i.e.
      [Bits.slice 0 szB x = Bits.slice 0 szB y -> x = y].
    Koika ships no slice lemmas beyond the definition, and [Bits.slice] unfolds
    to [vect_extend_end_firstn (vect_firstn ...)] carrying two [rew] casts.
    The one available simplification, [vect_extend_end_firstn_simpl]
    (vendor/koika/coq/Utils/Vect.v L533), covers [Nat.min n sz = n] -- the
    NARROWING direction -- so the widening case must be proved from scratch in
    that proof's style ([eq_trans_rew_distr], [eq_rect_eqdec_irrel]).  That is
    fragile-cast territory; follow the coq-fragile-proofs skill.

    Until that theorem exists this rule cannot be used in a verified context:
    supplying it leaves [analysis_sound] undischarged, so the IPR theorems
    simply do not apply.  The definition is kept here so the remaining work is
    explicit and the two DFG encodings are recorded.
!*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.DFG.

Require Import Coq.Lists.List.
Import ListNotations.

(* [DFG_Resize] takes its source width from the argument node, while
   [DFG_Unary (tf_resize source_size)] carries it explicitly; both encodings
   occur, and both are widening exactly when the source width is not larger. *)
Definition widen_rule {s i o} : decl_rule s i o :=
  fun dfg =>
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
