(*! Declassification rule: exclusive or.

    `xor` is invertible once one operand is known, so each operand is
    recoverable from the node together with the other operand.  Emits two
    unconditional instances per `DFG_Binary tf_xor` node.
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
Require Import Trustformer.Properties.IPR_Guarded.

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

Lemma xor_inj_r {sz} (x y k: bits sz) :
  Bits.xor x k = Bits.xor y k -> x = y.
Proof.
  intro H.
  rewrite <- (xor_cancel_r x k), <- (xor_cancel_r y k), H. reflexivity.
Qed.

Lemma xor_inj_l {sz} (x y k: bits sz) :
  Bits.xor k x = Bits.xor k y -> x = y.
Proof.
  intro H. apply (xor_inj_r x y k).
  rewrite (xor_comm x k), (xor_comm y k). exact H.
Qed.

Definition xor_rule {s i o} : decl_rule s i o :=
  fun dfg =>
    flat_map
      (fun n =>
         match op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}) with
         | DFG_Binary tf_xor a1 a2 =>
             [ {| di_target := a1; di_sources := [n; a2]; di_guard := [] |};
               {| di_target := a2; di_sources := [n; a1]; di_guard := [] |} ]
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

  Theorem xor_rule_sound (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (i: decl_instance) :
    List.In i (xor_rule (build_dfg ctx act)) ->
    instance_sound ctx cost_limit act a_idx input i.
  Proof.
    unfold xor_rule. intro Hin.
    apply in_flat_map in Hin. destruct Hin as [n [Hseq Hi]].
    apply in_seq in Hseq. destruct Hseq as [Hn1 Hn2].
    assert (Hlen : n < length (graph (build_dfg ctx act))) by lia.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | ] eqn:Hop;
      cbn [List.In] in Hi; try contradiction.
    destruct bop; cbn [List.In] in Hi; try contradiction.
    assert (Hnode_in : List.In (nth n (graph (build_dfg ctx act))
                                  {| nid := 0; op := DFG_Empty; sz := 0 |})
                         (graph (build_dfg ctx act)))
      by (apply nth_In; exact Hlen).
    pose proof (wfg_build_dfg ctx cost_limit act _ Hnode_in) as Hfg.
    unfold node_args_sz in Hfg. rewrite Hop in Hfg.
    destruct Hfg as [Hf1 Hf2].
    destruct (wsz_node_sz ctx cost_limit act a1 _ Hf1) as [H1len H1sz].
    destruct (wsz_node_sz ctx cost_limit act a2 _ Hf2) as [H2len H2sz].
    pose proof (nre_binary ctx cost_limit act a_idx n tf_xor a1 a2 Hn1 Hlen Hop)
      as Hnre.
    (* both instances: recover one operand from the node and the other *)
    destruct Hi as [Hi | [Hi | []]]; subst i;
      intros ss ss' Hpub _ _ Hsrc;
      cbn [di_sources di_target] in Hsrc |- *;
      pose proof (Hsrc n (or_introl eq_refl)) as Hn;
      unfold nval in Hn; rewrite Hnre in Hn; cbn [tf_eval_expr] in Hn.
    - pose proof (Hsrc a2 (or_intror (or_introl eq_refl))) as Ha2.
      rewrite H1sz. rewrite H2sz in Ha2. unfold nval in Ha2 |- *.
      rewrite Ha2 in Hn. exact (xor_inj_r _ _ _ Hn).
    - pose proof (Hsrc a1 (or_intror (or_introl eq_refl))) as Ha1.
      rewrite H2sz. rewrite H1sz in Ha1. unfold nval in Ha1 |- *.
      rewrite Ha1 in Hn. exact (xor_inj_l _ _ _ Hn).
  Qed.

End Soundness.

Print Assumptions xor_rule_sound.
