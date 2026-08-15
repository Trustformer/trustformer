(*! Declassification rule: phi with two distinct constant branches.

    If a phi selects between two constants that differ *as bitvectors at the
    node's width*, the selector is recoverable from the node's value.  This is
    the paper's PhiCUT.

    The instance is unconditional (`di_guard = []`): the conditionality of the
    lockbox comes from the phi node itself being only guarded-derivable, and is
    added by `decl_compose`, not by this rule.
!*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.DFG.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.
Require Import Trustformer.Properties.SchedulerSimulation.
Require Import Trustformer.Properties.IPR.

Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

(* Distinctness is checked on the evaluated bitvectors: as naturals 0 and 2
   differ, but at width 1 they denote the same value. *)
Definition phiconst_rule {s i o} : decl_rule s i o :=
  fun dfg =>
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

Section Soundness.
  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation sched := (tfs_schedule ctx cost_limit).
  Local Notation s_var := (tfs_spec_states ctx).
  Local Notation i_var := (tfs_spec_inputs ctx).
  Local Notation o_var := (tfs_spec_outputs ctx).

  Local Notation i_sz := (tfs_spec_inputs_size ctx).
  Local Notation o_sz := (tfs_spec_outputs_size ctx).

  Hint Extern 0 (FiniteType s_var) => exact (tfs_spec_states_fin ctx)  : typeclass_instances.
  Hint Extern 0 (FiniteType i_var) => exact (tfs_spec_inputs_fin ctx)  : typeclass_instances.
  Hint Extern 0 (FiniteType o_var) => exact (tfs_spec_outputs_fin ctx) : typeclass_instances.
  Hint Extern 0 (FiniteType (tfs_states sched))  => exact (tfs_states_fin sched)  : typeclass_instances.
  Hint Extern 0 (FiniteType (tfs_outputs sched)) => exact (tfs_outputs_fin sched) : typeclass_instances.

  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).
  Local Notation a_index := (Vect.index (length (buffer_needs ctx cost_limit))).

  Theorem phiconst_rule_sound (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (i: decl_instance) :
    List.In i (phiconst_rule (build_dfg ctx act)) ->
    instance_sound ctx cost_limit act a_idx input i.
  Proof.
    unfold phiconst_rule. intro Hin.
    apply in_flat_map in Hin. destruct Hin as [n [Hseq Hi]].
    apply in_seq in Hseq. destruct Hseq as [Hn1 Hn2].
    assert (Hlen : n < length (graph (build_dfg ctx act))) by lia.
    cbv zeta in Hi.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | ] eqn:Hop;
      cbn [List.In] in Hi; try contradiction.
    destruct (op (nth tid (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [kt | | | | | | | ] eqn:Hopt; try contradiction.
    destruct (op (nth eid (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [ke | | | | | | | ] eqn:Hope; try contradiction.
    destruct (beq_dec
                (Bits.of_nat (sz (nth n (graph (build_dfg ctx act))
                                    {| nid := 0; op := DFG_Empty; sz := 0 |})) kt)
                (Bits.of_nat (sz (nth n (graph (build_dfg ctx act))
                                    {| nid := 0; op := DFG_Empty; sz := 0 |})) ke))
      eqn:Hdistinct; [ contradiction | ].
    destruct Hi as [Hi | []]. subst i.
    intros ss ss' Hpub _ _ Hsrc.
    cbn [di_sources di_target] in Hsrc |- *.
    specialize (Hsrc n (or_introl eq_refl)).

    (* widths: the condition is one bit, the branches carry the node's width *)
    assert (Hnode_in : List.In (nth n (graph (build_dfg ctx act))
                                  {| nid := 0; op := DFG_Empty; sz := 0 |})
                         (graph (build_dfg ctx act)))
      by (apply nth_In; exact Hlen).
    pose proof (wfg_build_dfg ctx cost_limit act _ Hnode_in) as Hfg.
    unfold node_args_sz in Hfg. rewrite Hop in Hfg.
    destruct Hfg as [Hfc [Hft Hfe]].
    destruct (wsz_node_sz ctx cost_limit act cnd 1 Hfc) as [Hclen Hcsz].
    rewrite Hcsz.

    destruct (node_args_range ctx cost_limit act n Hn1 Hlen tid
                ltac:(unfold get_args; rewrite Hop; right; left; reflexivity))
      as [Ht1 Ht2].
    destruct (node_args_range ctx cost_limit act n Hn1 Hlen eid
                ltac:(unfold get_args; rewrite Hop; right; right; left; reflexivity))
      as [He1 He2].
    pose proof (nre_phi ctx cost_limit act a_idx n cnd tid eid Hn1 Hlen Hop)
      as Hnre.
    pose proof (nre_const ctx cost_limit act a_idx tid kt Ht1 ltac:(lia) Hopt)
      as Hnret.
    pose proof (nre_const ctx cost_limit act a_idx eid ke He1 ltac:(lia) Hope)
      as Hnree.

    (* evaluate the phi in both states *)
    unfold nval in Hsrc |- *.
    rewrite Hnre, Hnret, Hnree in Hsrc. cbn [tf_eval_expr] in Hsrc.

    (* The selector is one bit, so if the two runs disagreed the node would
       take both constants -- which the distinctness check ruled out. *)
    assert (Hnz : forall b: bits_t 1, beq_dec b Bits.zero = false -> b = Bits.ones 1).
    { intros b Hb. destruct (bits1_cases b) as [Ho | Hz]; [ exact Ho | ].
      rewrite Hz, beq_dec_refl in Hb. discriminate. }
    match type of Hsrc with
    | (if ?B1 then _ else _) = (if ?B2 then _ else _) =>
        destruct B1 eqn:E1; destruct B2 eqn:E2
    end.
    - apply beq_dec_iff in E1. apply beq_dec_iff in E2. rewrite E1, E2. reflexivity.
    - exfalso. rewrite Hsrc in Hdistinct.
      rewrite beq_dec_refl in Hdistinct. discriminate.
    - exfalso. rewrite Hsrc in Hdistinct.
      rewrite beq_dec_refl in Hdistinct. discriminate.
    - rewrite (Hnz _ E1), (Hnz _ E2). reflexivity.
  Qed.

End Soundness.

Print Assumptions phiconst_rule_sound.
