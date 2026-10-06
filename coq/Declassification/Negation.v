(*! Declassification rule: `not` is invertible, so a node's operand is
    recoverable from it.  Each rule here is self-contained and users pick the
    ones they want in `tfs_spec_decls`, the empty list giving blackbox. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Theorems.Definitions.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.DFG.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Theorems.SchedulerSimulation.
Require Import Trustformer.Theorems.Internal.SchedulerRoundTrip.
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
  destruct uop as [| source_size]; cbn [List.In] in Hi; [ | contradiction ].
  destruct Hi as [<- | []]. cbn [di_target di_sources nth] in *.
  rewrite (Hagree n (or_introl eq_refl)), Hcons. cbn [op1_bits].
  rewrite Bits.neg_involutive.
  symmetry. apply convert_roundtrip. exact Hws.
Qed.

Definition neg_packet {s i o p} : decl_packet s i o p :=
  {| dp_rule := neg_rule; dp_extract := neg_extract; dp_sound := neg_packet_sound |}.

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

  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).
  Local Notation sched_input_t :=
    (forall x : tfs_inputs sched, type_denote (tf_inputs_type (tfs_inputs_size sched) x)).
  Local Notation a_index := (Vect.index (length (buffer_needs ctx cost_limit))).

  Theorem neg_rule_sound (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (i: decl_instance) :
    List.In i (neg_rule (build_dfg ctx act)) ->
    instance_sound ctx cost_limit act a_idx input i.
  Proof.
    unfold neg_rule. intro Hin.
    apply in_flat_map in Hin. destruct Hin as [n [Hseq Hi]].
    apply in_seq in Hseq. destruct Hseq as [Hn1 Hn2].
    assert (Hlen : n < length (graph (build_dfg ctx act))) by lia.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa | dp darg den | sp stok sen | ja jb | ] eqn:Hop;
      cbn [List.In] in Hi; try (destruct Hi).
    destruct uop as [| source_size]; cbn [List.In] in Hi; [ | destruct Hi ].
    destruct Hi as [Hi | []]. subst i.
    intros ss ss' input' pi Hpub _ _ Hsrc Hpi Hpi' Hv Hv'.
    cbn [di_sources di_target] in Hsrc, Hv, Hv' |- *.
    assert (Hnlen : n < length (graph (build_dfg ctx act))) by exact Hlen.
    assert (Hop' : node_op ctx cost_limit act n = DFG_Unary tf_not arg)
      by (unfold Definitions.node_op; rewrite Hop; reflexivity).
    destruct (node_args_range ctx cost_limit act n Hn1 Hlen arg
                ltac:(unfold get_args; rewrite Hop; left; reflexivity)) as [Harg1 _].
    specialize (Hsrc n pi (or_introl eq_refl) Hpi Hpi'
                  (nrv_lift_unary ctx cost_limit act a_idx n tf_not arg pi ss  input
                     Hop' Harg1 Hnlen Hv)
                  (nrv_lift_unary ctx cost_limit act a_idx n tf_not arg pi ss' input'
                     Hop' Harg1 Hnlen Hv')).
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

