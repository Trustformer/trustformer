(*! Declassification rule: bitwise negation.

    `not` loses no information, so a node's operand is recoverable from the
    node itself.  Emits one unconditional instance (`di_guard = []`) per
    `DFG_Unary tf_not` node.

    Each rule in this directory is self-contained: the computable
    instantiation plus its `instance_sound` proof.  Users pick the rules they
    want in `tfs_spec_decls`; picking none reproduces blackbox behaviour.
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

(* Nodes are visited by position, so [1 <= n] and [n < length] come for free
   from [in_seq]; position and [nid] coincide in the exported graph. *)
Definition neg_rule {s i o} : decl_rule s i o :=
  fun dfg =>
    flat_map
      (fun n =>
         match op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}) with
         | DFG_Unary tf_not arg =>
             [ {| di_target := arg; di_sources := [n]; di_guard := [] |} ]
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

  (* Required: without these, elaborating any [ContextEnv.(env_t)] statement
     diverges instead of failing. *)
  Hint Extern 0 (FiniteType s_var) => exact (tfs_spec_states_fin ctx)  : typeclass_instances.
  Hint Extern 0 (FiniteType i_var) => exact (tfs_spec_inputs_fin ctx)  : typeclass_instances.
  Hint Extern 0 (FiniteType o_var) => exact (tfs_spec_outputs_fin ctx) : typeclass_instances.
  Hint Extern 0 (FiniteType (tfs_states sched))  => exact (tfs_states_fin sched)  : typeclass_instances.
  Hint Extern 0 (FiniteType (tfs_outputs sched)) => exact (tfs_outputs_fin sched) : typeclass_instances.

  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).
  Local Notation a_index := (Vect.index (length (buffer_needs ctx cost_limit))).

  Theorem neg_rule_sound (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (i: decl_instance) :
    List.In i (neg_rule (build_dfg ctx act)) ->
    instance_sound ctx cost_limit act a_idx input i.
  Proof.
    unfold neg_rule. intro Hin.
    apply in_flat_map in Hin. destruct Hin as [n [Hseq Hi]].
    apply in_seq in Hseq. destruct Hseq as [Hn1 Hn2].
    assert (Hlen : n < length (graph (build_dfg ctx act))) by lia.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | ] eqn:Hop;
      cbn [List.In] in Hi; try (destruct Hi).
    destruct uop as [| source_size]; cbn [List.In] in Hi; [ | destruct Hi ].
    destruct Hi as [Hi | []]. subst i.
    intros ss ss' Hpub _ _ Hsrc.
    cbn [di_sources di_target] in Hsrc |- *.
    specialize (Hsrc n (or_introl eq_refl)).
    assert (Hnode_in : List.In (nth n (graph (build_dfg ctx act))
                                  {| nid := 0; op := DFG_Empty; sz := 0 |})
                         (graph (build_dfg ctx act)))
      by (apply nth_In; exact Hlen).
    pose proof (wfg_build_dfg ctx cost_limit act _ Hnode_in) as Hfg.
    unfold node_args_sz in Hfg. rewrite Hop in Hfg.
    destruct (wsz_node_sz ctx cost_limit act arg _ Hfg) as [Halen Hasz].
    rewrite Hasz.
    pose proof (nre_unary ctx cost_limit act a_idx n tf_not arg Hn1 Hlen Hop)
      as Hnre.
    unfold nval in Hsrc |- *. rewrite Hnre in Hsrc.
    cbn [tf_eval_expr] in Hsrc.
    apply (f_equal Bits.neg) in Hsrc.
    rewrite !Bits.neg_involutive in Hsrc. exact Hsrc.
  Qed.

End Soundness.

Print Assumptions neg_rule_sound.
