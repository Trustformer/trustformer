(*! Declassification rule: widening resize.

    A widening resize keeps every source bit, so the operand is recoverable
    from the node.  Narrowing is not invertible, hence the width check.

    The obligation reduces to injectivity of [Semantics.convert] when
    [szA <= szB], i.e. [Bits.slice 0 szB x = Bits.slice 0 szB y -> x = y].
    Koika ships no slice lemmas at the vector level, but it does ship a
    LIST-level characterisation ([BitsToLists.slice]) together with
    [vect_to_list_inj], and at offset 0 the list form is just
    [vect_to_list x ++ repeat false (szB - szA)].  That avoids the [rew] casts
    in [vect_extend_end_firstn] entirely.
!*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.
Require Import Koika.BitsToLists.

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

(* [DFG_Resize] takes its source width from the argument node, while
   [DFG_Unary (tf_resize source_size)] carries it explicitly; both encodings
   occur, and both are widening exactly when the source width is not larger. *)
Definition widen_rule {s i o e} : decl_rule s i o e :=
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

Section ConvertInj.

  Lemma slice_to_list_widen (szA szB: nat) (x: bits_t szA) :
    szA <= szB ->
    vect_to_list (Bits.slice 0 szB x)
    = vect_to_list x ++ List.repeat false (szB - szA).
  Proof.
    intro Hle.
    rewrite (BitsToLists.slice szA x 0 szB).
    unfold take_drop'. cbn [List.firstn List.skipn].
    rewrite List.firstn_all2
      by (rewrite vect_to_list_length; exact Hle).
    rewrite Nat.sub_0_r, Nat.min_r by exact Hle.
    reflexivity.
  Qed.

  Lemma convert_inj (szA szB: nat) (x y: bits_t szA) :
    szA <= szB ->
    convert (szB := szB) x = convert (szB := szB) y ->
    x = y.
  Proof.
    intros Hle Hc. unfold convert in Hc.
    destruct (eq_dec szA szB) as [e | ne].
    - destruct e. exact Hc.
    - apply (vect_to_list_inj bool szA).
      apply (f_equal vect_to_list) in Hc.
      rewrite !slice_to_list_widen in Hc by exact Hle.
      exact (List.app_inv_tail _ _ _ Hc).
  Qed.

End ConvertInj.

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
  Hint Extern 1 (tf_externs _) => exact (tfs_spec_externs_sig ctx) : typeclass_instances.
  Hint Extern 0 (FiniteType (tfs_states sched))  => exact (tfs_states_fin sched)  : typeclass_instances.
  Hint Extern 0 (FiniteType (tfs_outputs sched)) => exact (tfs_outputs_fin sched) : typeclass_instances.

  Local Notation sched_st_env  := (ContextEnv.(env_t) (tf_states_type (tfs_states_size sched))).
  Local Notation sched_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation sched_sys_state := (sched_st_env * sched_out_env)%type.
  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).
  Local Notation a_index := (Vect.index (length (buffer_needs ctx cost_limit))).

  Local Notation nsz act n :=
    (sz (nth n (graph (build_dfg ctx act)) {| nid := 0; op := DFG_Empty; sz := 0 |})).

  (* Both DFG encodings reduce to this: the node evaluates to [convert] of the
     argument at width [src], so a widening [convert] being injective is the
     whole content of the rule. *)
  Lemma widen_step (act: tfs_action sched) (a_idx: a_index) (input: input_t)
      (n arg src: nid_t) (ss ss': sched_sys_state) :
    node_ref_expr ctx cost_limit act a_idx n
      = tf_op1 (tf_resize src) (node_ref_expr ctx cost_limit act a_idx arg) ->
    nsz act arg = src ->
    src <= nsz act n ->
    nval ctx cost_limit act a_idx ss  input (nsz act n) n
    = nval ctx cost_limit act a_idx ss' input (nsz act n) n ->
    nval ctx cost_limit act a_idx ss  input (nsz act arg) arg
    = nval ctx cost_limit act a_idx ss' input (nsz act arg) arg.
  Proof.
    intros Hnre Hsz Hle Hn.
    unfold nval in Hn |- *. rewrite Hnre in Hn. cbn [tf_eval_expr] in Hn.
    rewrite Hsz.
    exact (convert_inj src (nsz act n) _ _ Hle Hn).
  Qed.

  Theorem widen_rule_sound (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (i: decl_instance) :
    List.In i (widen_rule (build_dfg ctx act)) ->
    instance_sound ctx cost_limit act a_idx input i.
  Proof.
    unfold widen_rule. intro Hin.
    apply in_flat_map in Hin. destruct Hin as [n [Hseq Hi]].
    apply in_seq in Hseq. destruct Hseq as [Hn1 Hn2].
    assert (Hlen : n < length (graph (build_dfg ctx act))) by lia.
    cbv zeta in Hi.
    assert (Hnode_in : List.In (nth n (graph (build_dfg ctx act))
                                  {| nid := 0; op := DFG_Empty; sz := 0 |})
                         (graph (build_dfg ctx act)))
      by (apply nth_In; exact Hlen).
    pose proof (wfg_build_dfg ctx cost_limit act _ Hnode_in) as Hfg.
    unfold node_args_sz in Hfg.

    (* the two encodings, then the shared argument *)
    assert (Hcase : exists arg src,
              node_ref_expr ctx cost_limit act a_idx n
                = tf_op1 (tf_resize src) (node_ref_expr ctx cost_limit act a_idx arg)
              /\ nsz act arg = src
              /\ src <= nsz act n
              /\ i = {| di_target := arg; di_sources := [n]; di_guard := [] |}).
    { destruct (op (nth n (graph (build_dfg ctx act))
                      {| nid := 0; op := DFG_Empty; sz := 0 |}))
        as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | xf xarg xdly | dly | ] eqn:Hop;
        cbn [List.In] in Hi; try contradiction.
      - (* DFG_Unary: only tf_resize emits an instance *)
        destruct uop as [| src]; cbn [List.In] in Hi; try contradiction.
        destruct (Nat.leb src (sz (nth n (graph (build_dfg ctx act))
                                     {| nid := 0; op := DFG_Empty; sz := 0 |})))
          eqn:Hleb; cbn [List.In] in Hi; [ | contradiction ].
        destruct Hi as [Hi | []].
        destruct (wsz_node_sz ctx cost_limit act arg src Hfg) as [_ Hsz].
        exists arg, src. split; [ | split; [ | split ] ].
        + exact (nre_unary ctx cost_limit act a_idx n (tf_resize src) arg
                   Hn1 Hlen Hop).
        + exact Hsz.
        + apply Nat.leb_le; exact Hleb.
        + symmetry; exact Hi.
      - (* DFG_Resize: the source width is the argument node's own width *)
        destruct (Nat.leb (sz (nth arg (graph (build_dfg ctx act))
                                 {| nid := 0; op := DFG_Empty; sz := 0 |}))
                          (sz (nth n (graph (build_dfg ctx act))
                                 {| nid := 0; op := DFG_Empty; sz := 0 |})))
          eqn:Hleb; cbn [List.In] in Hi; [ | contradiction ].
        destruct Hi as [Hi | []].
        exists arg, (sz (nth arg (graph (build_dfg ctx act))
                           {| nid := 0; op := DFG_Empty; sz := 0 |})).
        split; [ | split; [ | split ] ].
        + exact (nre_resize ctx cost_limit act a_idx n arg Hn1 Hlen Hop).
        + reflexivity.
        + apply Nat.leb_le; exact Hleb.
        + symmetry; exact Hi. }

    destruct Hcase as [arg [src [Hnre [Hsz [Hle Hieq]]]]]. subst i.
    intros ss ss' Hpub _ _ Hsrc.
    cbn [di_sources di_target] in Hsrc |- *.
    exact (widen_step act a_idx input n arg src ss ss' Hnre Hsz Hle
             (Hsrc n (or_introl eq_refl))).
  Qed.

End Soundness.

Print Assumptions widen_rule_sound.
