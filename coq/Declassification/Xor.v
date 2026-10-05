(*! Declassification rule: exclusive or.  `xor` is invertible once one operand
    is known, so each operand is recoverable from the node and the other.  Two
    unconditional instances per `DFG_Binary tf_xor` node. !*)

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
Require Import Trustformer.Theorems.IPR.

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


Lemma xor_cancel_l {sz} (x y: bits sz) :
  Bits.xor (Bits.xor x y) x = y.
Proof. rewrite (xor_comm x y). apply xor_cancel_r. Qed.

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


(* The bit-level reading of [Bits.xor], which is what [di_extract] computes. *)
Fixpoint vect_to_list_xor {sz} (x y: bits sz) {struct sz} :
  vect_to_list (Bits.xor x y)
  = List.map (fun p => xorb (fst p) (snd p))
             (List.combine (vect_to_list x) (vect_to_list y)).
Proof.
  destruct sz.
  - destruct x, y. reflexivity.
  - destruct x as [a x'], y as [b y']. unfold Bits.xor in *. cbn.
    f_equal. apply vect_to_list_xor.
Defined.

Definition xor_rule {s i o p} : decl_rule s i o p :=
  fun dfg =>
    flat_map
      (fun n =>
         match op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}) with
         | DFG_Binary tf_xor a1 a2 =>
             (* xor is its own inverse: either operand is the node xor the other *)
             let unxor := fun vs : list (list bool) =>
               List.map (fun p => xorb (fst p) (snd p))
                        (List.combine (nth 0 vs []) (nth 1 vs [])) in
             [ {| di_target := a1; di_sources := [n; a2]; di_guard := [];
                  di_extract := unxor |};
               {| di_target := a2; di_sources := [n; a1]; di_guard := [];
                  di_extract := unxor |} ]
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


  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).
  Local Notation sched_input_t :=
    (forall x : tfs_inputs sched, type_denote (tf_inputs_type (tfs_inputs_size sched) x)).
  Local Notation sched_st_env  := (ContextEnv.(env_t) (tf_states_type (tfs_states_size sched))).
  Local Notation sched_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation sched_sys_state := (sched_st_env * sched_out_env)%type.
  Local Notation a_index := (Vect.index (length (buffer_needs ctx cost_limit))).
  Local Notation rvalid act a_idx pi n ss input :=
    (tf_eval_expr (tfs_states_size sched) (tfs_inputs_size sched)
       (tfs_outputs_size sched) (szB := 1)
       (snd (compile_dfg_expr_at ctx (buffer_needs ctx cost_limit) pi
               (length (graph (build_dfg ctx act))) a_idx
               (build_dfg ctx act) n (sample_bufs ctx cost_limit act a_idx)))
       ss input) (only parsing).


  (* A rule reads a source where that source is valid.  These instances read the
     xor node, so they want its validity given an operand's; [nrv_peel_binary]
     then returns the other operand. *)
  Definition xor_settled (act: tfs_action sched) (a_idx: a_index) : Prop :=
    forall n a1 a2,
      node_op ctx cost_limit act n = DFG_Binary tf_xor a1 a2 ->
      forall (p: list lit) (ss: sched_sys_state) (inp: sched_input_t),
        rvalid act a_idx p a1 ss inp = Bits.ones 1
        \/ rvalid act a_idx p a2 ss inp = Bits.ones 1 ->
        rvalid act a_idx p n ss inp = Bits.ones 1.

  Theorem xor_rule_sound (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (i: decl_instance) :
    List.In i (xor_rule (build_dfg ctx act)) ->
    xor_settled act a_idx ->
    instance_sound ctx cost_limit act a_idx input i.
  Proof.
    unfold xor_rule. intros Hin Hset.
    apply in_flat_map in Hin. destruct Hin as [n [Hseq Hi]].
    apply in_seq in Hseq. destruct Hseq as [Hn1 Hn2].
    assert (Hlen : n < length (graph (build_dfg ctx act))) by lia.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa | dp darg den | sp stok sen | ja jb | ] eqn:Hop;
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
    assert (Hopn : node_op ctx cost_limit act n = DFG_Binary tf_xor a1 a2)
      by (unfold Definitions.node_op; rewrite Hop; reflexivity).
    destruct (node_args_range ctx cost_limit act n Hn1 Hlen a1
                ltac:(unfold get_args; rewrite Hop; left; reflexivity)) as [Ha11 _].
    destruct (node_args_range ctx cost_limit act n Hn1 Hlen a2
                ltac:(unfold get_args; rewrite Hop; right; left; reflexivity))
      as [Ha21 _].

    (* both instances: recover one operand from the node and the other *)
    destruct Hi as [Hi | [Hi | []]]; subst i;
      intros ss ss' input' pi Hpub _ _ Hsrc Hpi Hpi' Hv Hv';
      cbn [di_sources di_target] in Hsrc, Hv, Hv' |- *.
    - pose proof (Hset n a1 a2 Hopn pi ss  input  (or_introl Hv ))  as Hvn.
      pose proof (Hset n a1 a2 Hopn pi ss' input' (or_introl Hv')) as Hvn'.
      pose proof (Hsrc n pi (or_introl eq_refl) Hpi Hpi' Hvn Hvn') as Hn.
      unfold nval in Hn. rewrite Hnre in Hn. cbn [tf_eval_expr] in Hn.
      pose proof (Hsrc a2 pi (or_intror (or_introl eq_refl)) Hpi Hpi'
                    (proj2 (nrv_peel_binary ctx cost_limit act a_idx n tf_xor a1 a2
                              pi ss  input  Hopn Ha11 Ha21 Hlen Hvn ))
                    (proj2 (nrv_peel_binary ctx cost_limit act a_idx n tf_xor a1 a2
                              pi ss' input' Hopn Ha11 Ha21 Hlen Hvn'))) as Ha2.
      rewrite H1sz. rewrite H2sz in Ha2. unfold nval in Ha2 |- *.
      rewrite Ha2 in Hn. exact (xor_inj_r _ _ _ Hn).
    - pose proof (Hset n a1 a2 Hopn pi ss  input  (or_intror Hv ))  as Hvn.
      pose proof (Hset n a1 a2 Hopn pi ss' input' (or_intror Hv')) as Hvn'.
      pose proof (Hsrc n pi (or_introl eq_refl) Hpi Hpi' Hvn Hvn') as Hn.
      unfold nval in Hn. rewrite Hnre in Hn. cbn [tf_eval_expr] in Hn.
      pose proof (Hsrc a1 pi (or_intror (or_introl eq_refl)) Hpi Hpi'
                    (proj1 (nrv_peel_binary ctx cost_limit act a_idx n tf_xor a1 a2
                              pi ss  input  Hopn Ha11 Ha21 Hlen Hvn ))
                    (proj1 (nrv_peel_binary ctx cost_limit act a_idx n tf_xor a1 a2
                              pi ss' input' Hopn Ha11 Ha21 Hlen Hvn'))) as Ha1.
      rewrite H2sz. rewrite H1sz in Ha1. unfold nval in Ha1 |- *.
      rewrite Ha1 in Hn. exact (xor_inj_l _ _ _ Hn).
  Qed.


  (* THE REVERSING FUNCTION IS CORRECT: xoring the node with one operand gives
     the other, which is what [di_extract] computes bitwise. *)
  Theorem xor_rule_extracts (act: tfs_action sched) (a_idx: a_index)
      (i: decl_instance) :
    List.In i (xor_rule (build_dfg ctx act)) ->
    instance_extracts ctx cost_limit act a_idx i.
  Proof.
    unfold xor_rule. intro Hin.
    apply in_flat_map in Hin. destruct Hin as [n [Hseq Hi]].
    apply in_seq in Hseq. destruct Hseq as [Hn1 Hn2].
    assert (Hlen : n < length (graph (build_dfg ctx act))) by lia.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa | dp darg den | sp stok sen | ja jb | ] eqn:Hop;
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
    destruct Hi as [Hi | [Hi | []]]; subst i;
      intros ss input _;
      cbn [di_sources di_target di_extract];
      cbn [map nth];
      rewrite H1sz, H2sz;
      unfold nval; rewrite Hnre; cbn [tf_eval_expr];
      rewrite <- vect_to_list_xor.
    - rewrite xor_cancel_r. reflexivity.
    - rewrite xor_cancel_l. reflexivity.
  Qed.
  (* THE SETTLEDNESS LIFT: each instance reads the xor node and the other
     operand, which is [xor_settled] followed by [nrv_peel_binary]. *)
  Theorem xor_rule_lifts (act: tfs_action sched) (a_idx: a_index)
      (i: decl_instance) :
    List.In i (xor_rule (build_dfg ctx act)) ->
    xor_settled act a_idx ->
    instance_in_range ctx cost_limit act i
    /\ instance_guards_sized ctx cost_limit act i
    /\ instance_lifts ctx cost_limit act a_idx i.
  Proof.
    unfold xor_rule. intros Hin Hset.
    apply in_flat_map in Hin. destruct Hin as [n [Hseq Hi]].
    apply in_seq in Hseq. destruct Hseq as [Hn1 Hn2].
    assert (Hlen : n < length (graph (build_dfg ctx act))) by lia.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa | dp darg den | sp stok sen | ja jb | ] eqn:Hop;
      cbn [List.In] in Hi; try contradiction.
    destruct bop; cbn [List.In] in Hi; try contradiction.
    assert (Hopn : node_op ctx cost_limit act n = DFG_Binary tf_xor a1 a2)
      by (unfold Definitions.node_op; rewrite Hop; reflexivity).
    destruct (node_args_range ctx cost_limit act n Hn1 Hlen a1
                ltac:(unfold get_args; rewrite Hop; left; reflexivity))
      as [Ha11 Ha12].
    destruct (node_args_range ctx cost_limit act n Hn1 Hlen a2
                ltac:(unfold get_args; rewrite Hop; right; left; reflexivity))
      as [Ha21 Ha22].
    destruct Hi as [Hi | [Hi | []]]; subst i;
      (split; [ intros m Hm; cbn [di_target di_sources di_guard map List.app] in Hm
              | split; [ intros l Hl; destruct Hl | ] ]).
    - destruct Hm as [<- | [<- | [<- | []]]]; split; lia.
    - intros ss input Hst.
      cbn [di_target di_sources di_guard map] in Hst |- *.
      split; [ intros c0 [] | ].
      intros _ s Hs. destruct Hst as [pi [Hpi Hv]].
      assert (Hvn : rvalid act a_idx pi n ss input = Bits.ones 1)
        by (exact (Hset n a1 a2 Hopn pi ss input (or_introl Hv))).
      destruct Hs as [<- | [<- | []]]; exists pi; split; [ exact Hpi | exact Hvn
                                                        | exact Hpi | ].
      exact (proj2 (nrv_peel_binary ctx cost_limit act a_idx n tf_xor a1 a2 pi
                      ss input Hopn Ha11 Ha21 Hlen Hvn)).
    - destruct Hm as [<- | [<- | [<- | []]]]; split; lia.
    - intros ss input Hst.
      cbn [di_target di_sources di_guard map] in Hst |- *.
      split; [ intros c0 [] | ].
      intros _ s Hs. destruct Hst as [pi [Hpi Hv]].
      assert (Hvn : rvalid act a_idx pi n ss input = Bits.ones 1)
        by (exact (Hset n a1 a2 Hopn pi ss input (or_intror Hv))).
      destruct Hs as [<- | [<- | []]]; exists pi; split; [ exact Hpi | exact Hvn
                                                        | exact Hpi | ].
      exact (proj1 (nrv_peel_binary ctx cost_limit act a_idx n tf_xor a1 a2 pi
                      ss input Hopn Ha11 Ha21 Hlen Hvn)).
  Qed.

End Soundness.

