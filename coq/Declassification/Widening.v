(*! Declassification rule: a widening resize keeps every source bit, so the
    operand is recoverable; the width check restricts it to [szA <= szB].  The
    obligation is [Semantics.convert]'s injectivity, via [BitsToLists.slice]. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.
Require Import Koika.BitsToLists.

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


  Local Notation sched_st_env  := (ContextEnv.(env_t) (tf_states_type (tfs_states_size sched))).
  Local Notation sched_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation sched_sys_state := (sched_st_env * sched_out_env)%type.
  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).
  Local Notation sched_input_t :=
    (forall x : tfs_inputs sched, type_denote (tf_inputs_type (tfs_inputs_size sched) x)).
  Local Notation a_index := (Vect.index (length (buffer_needs ctx cost_limit))).
  Local Notation rvalid act a_idx pi n ss input :=
    (tf_eval_expr (tfs_states_size sched) (tfs_inputs_size sched)
       (tfs_outputs_size sched) (szB := 1)
       (snd (compile_dfg_expr_at ctx (buffer_needs ctx cost_limit) pi
               (length (graph (build_dfg ctx act))) a_idx
               (build_dfg ctx act) n (sample_bufs ctx cost_limit act a_idx)))
       ss input) (only parsing).

  Local Notation nsz act n :=
    (sz (nth n (graph (build_dfg ctx act)) {| nid := 0; op := DFG_Empty; sz := 0 |})).

  (* Both DFG encodings reduce to this: the node evaluates to [convert] of the
     argument at width [src], so a widening [convert] being injective is the
     whole content of the rule. *)
  Lemma widen_step (act: tfs_action sched) (a_idx: a_index)
      (input input': sched_input_t)
      (n arg src: nid_t) (ss ss': sched_sys_state) :
    node_ref_expr ctx cost_limit act a_idx n
      = tf_op1 (tf_resize src) (node_ref_expr ctx cost_limit act a_idx arg) ->
    nsz act arg = src ->
    src <= nsz act n ->
    nval ctx cost_limit act a_idx ss  input  (nsz act n) n
    = nval ctx cost_limit act a_idx ss' input' (nsz act n) n ->
    nval ctx cost_limit act a_idx ss  input  (nsz act arg) arg
    = nval ctx cost_limit act a_idx ss' input' (nsz act arg) arg.
  Proof.
    intros Hnre Hsz Hle Hn.
    unfold nval in Hn |- *. rewrite Hnre in Hn. cbn [tf_eval_expr] in Hn.
    rewrite Hsz.
    exact (convert_inj src (nsz act n) _ _ Hle Hn).
  Qed.


  (* The two encodings of a widening, and what the instance looks like for
     either.  Both theorems below read their content off this. *)
  Lemma widen_shape (act: tfs_action sched) (a_idx: a_index) (i: decl_instance) :
    List.In i (widen_rule (build_dfg ctx act)) ->
    exists n arg src,
              node_ref_expr ctx cost_limit act a_idx n
                = tf_op1 (tf_resize src) (node_ref_expr ctx cost_limit act a_idx arg)
              /\ nsz act arg = src
              /\ src <= nsz act n
              /\ i = {| di_target := arg; di_sources := [n]; di_guard := [] |}
              /\ (forall pi (s: sched_sys_state) (inp: sched_input_t),
                    rvalid act a_idx pi arg s inp = Bits.ones 1 ->
                    rvalid act a_idx pi n   s inp = Bits.ones 1)
      .
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
    exists n.
      destruct (op (nth n (graph (build_dfg ctx act))
                      {| nid := 0; op := DFG_Empty; sz := 0 |}))
        as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa | dp darg den | sp stok sen | ja jb | ] eqn:Hop;
        cbn [List.In] in Hi; try contradiction.
      - (* DFG_Unary: only tf_resize emits an instance *)
        destruct uop as [| src]; cbn [List.In] in Hi; try contradiction.
        destruct (Nat.leb src (sz (nth n (graph (build_dfg ctx act))
                                     {| nid := 0; op := DFG_Empty; sz := 0 |})))
          eqn:Hleb; cbn [List.In] in Hi; [ | contradiction ].
        destruct Hi as [Hi | []].
        destruct (wsz_node_sz ctx cost_limit act arg src Hfg) as [_ Hsz].
        exists arg, src. split; [ | split; [ | split; [ | split ] ] ].
        + exact (nre_unary ctx cost_limit act a_idx n (tf_resize src) arg
                   Hn1 Hlen Hop).
        + exact Hsz.
        + apply Nat.leb_le; exact Hleb.
        + symmetry; exact Hi.
        + intros pi s inp Hva.
          destruct (node_args_range ctx cost_limit act n Hn1 Hlen arg
                      ltac:(unfold get_args; rewrite Hop; left; reflexivity))
            as [Harg1 _].
          exact (nrv_lift_unary ctx cost_limit act a_idx n (tf_resize src) arg pi
                   s inp ltac:(unfold Definitions.node_op;
                               rewrite Hop; reflexivity) Harg1 Hlen Hva).
      - (* DFG_Resize: the source width is the argument node's own width *)
        destruct (Nat.leb (sz (nth arg (graph (build_dfg ctx act))
                                 {| nid := 0; op := DFG_Empty; sz := 0 |}))
                          (sz (nth n (graph (build_dfg ctx act))
                                 {| nid := 0; op := DFG_Empty; sz := 0 |})))
          eqn:Hleb; cbn [List.In] in Hi; [ | contradiction ].
        destruct Hi as [Hi | []].
        exists arg, (sz (nth arg (graph (build_dfg ctx act))
                           {| nid := 0; op := DFG_Empty; sz := 0 |})).
        split; [ | split; [ | split; [ | split ] ] ].
        + exact (nre_resize ctx cost_limit act a_idx n arg Hn1 Hlen Hop).
        + reflexivity.
        + apply Nat.leb_le; exact Hleb.
        + symmetry; exact Hi.
        + intros pi s inp Hva.
          destruct (node_args_range ctx cost_limit act n Hn1 Hlen arg
                      ltac:(unfold get_args; rewrite Hop; left; reflexivity))
            as [Harg1 _].
          exact (nrv_lift_resize ctx cost_limit act a_idx n arg pi s inp
                   ltac:(unfold Definitions.node_op;
                         rewrite Hop; reflexivity) Harg1 Hlen Hva).
  Qed.

  Theorem widen_rule_sound (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (i: decl_instance) :
    List.In i (widen_rule (build_dfg ctx act)) ->
    instance_sound ctx cost_limit act a_idx input i.
  Proof.
    intro Hin.
    destruct (widen_shape act a_idx i Hin)
      as [n [arg [src [Hnre [Hsz [Hle [Hieq Hlift]]]]]]]. subst i.
    intros ss ss' input' pi Hpub _ _ Hsrc Hpi Hpi' Hv Hv'.
    cbn [di_sources di_target] in Hsrc, Hv, Hv' |- *.
    exact (widen_step act a_idx input input' n arg src ss ss' Hnre Hsz Hle
             (Hsrc n pi (or_introl eq_refl) Hpi Hpi'
                (Hlift pi ss input Hv) (Hlift pi ss' input' Hv'))).
  Qed.


End Soundness.

