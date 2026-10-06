(*! The proofs behind Theorems/IPR.v, and the intermediate results they are
    built from: that taint over-approximates what an attacker can derive, that
    each declassification rule instance composes into a sound whole, and that
    two runs agreeing on public data step their validity and done bits in
    lockstep.  The latency guarantees themselves are stated in
    Theorems/IPR.v. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Export Trustformer.Theorems.Definitions.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Theorems.SchedulerSimulation.
Require Import Trustformer.Theorems.Internal.SchedulerRoundTrip.
Require Import Trustformer.Declassification.Recover.

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Lia.
Import ListNotations.

(* ===================================================================== *)
(* Kôika's [mem] decides [In], but returns a [member] rather than a bool. *)
(* ===================================================================== *)

Section MemIn.
  Context {K: Type} `{EqDec K}.

  Lemma In_member (k: K) (l: list K) : List.In k l -> member k l.
  Proof.
    induction l as [| k' l IH]; intro Hin.
    - destruct Hin.
    - destruct (eq_dec k k') as [Heq | Hne].
      + subst k'. exact (MemberHd _ _).
      + apply MemberTl. apply IH.
        destruct Hin as [Heq | Hin]; [ congruence | exact Hin ].
  Defined.

  Lemma mem_inr_not_In (k: K) (l: list K) (f: member k l -> False) :
    mem k l = inr f -> ~ List.In k l.
  Proof.
    intros _ Hin. exact (f (In_member k l Hin)).
  Qed.
End MemIn.

(* ===================================================================== *)
(* Generic facts about a left fold that only ever conses one designated   *)
(* element per step.  [get_tainted] is such a fold.                       *)
(* ===================================================================== *)

Section FoldAccum.
  Context {A B: Type}.
  Variable f: list A -> B -> list A.

  Lemma fold_left_grows (Hstep: forall acc b, incl acc (f acc b)) :
    forall (l: list B) (acc: list A), incl acc (fold_left f l acc).
  Proof.
    induction l as [| b l IH]; intro acc; simpl.
    - apply incl_refl.
    - eapply incl_tran; [ apply Hstep | apply IH ].
  Qed.

  Variable g: B -> A.

  Lemma fold_left_source
    (Hstep: forall acc b x, List.In x (f acc b) -> List.In x acc \/ x = g b) :
    forall (l: list B) (acc: list A) x,
      List.In x (fold_left f l acc) ->
      List.In x acc \/ exists b, List.In b l /\ x = g b.
  Proof.
    induction l as [| b l IH]; intros acc x Hin; simpl in Hin.
    - left; exact Hin.
    - destruct (IH _ x Hin) as [Hacc | [b' [Hb' Hx]]].
      + destruct (Hstep acc b x Hacc) as [Hacc' | Hx].
        * left; exact Hacc'.
        * right; exists b; split; [ left; reflexivity | exact Hx ].
      + right; exists b'; split; [ right; exact Hb' | exact Hx ].
  Qed.
End FoldAccum.

(* ===================================================================== *)
(* Bounded search.  [least_witness] lives in Prop, so it cannot produce a *)
(* latency *function*; this computes the same index.                      *)
(* ===================================================================== *)
Section FirstTrue.
  Variable f : nat -> bool.

  (* Stated in Theorems/Definitions.v; bound here at this section's context. *)
  Local Notation first_true := (Definitions.first_true f).

  Lemma first_true_spec (fuel: nat) :
    forall k n, k <= n -> n <= k + fuel -> f n = true ->
      f (first_true fuel k) = true
      /\ (forall j, k <= j -> j < first_true fuel k -> f j = false).
  Proof.
    induction fuel as [| fuel IH]; intros k n Hkn Hnk Hf.
    - assert (Heq : n = k) by lia. subst n.
      cbn [first_true]. split; [ exact Hf | intros j Hj1 Hj2; lia ].
    - cbn [first_true]. destruct (f k) eqn:Ek.
      + split; [ exact Ek | intros j Hj1 Hj2; lia ].
      + assert (Hne : n <> k) by (intro Hc; subst n; congruence).
        destruct (IH (S k) n ltac:(lia) ltac:(lia) Hf) as [H1 H2].
        split; [ exact H1 | ].
        intros j Hj1 Hj2. destruct (Nat.eq_dec j k) as [Heq | Hjk].
        * subst j. exact Ek.
        * apply H2; lia.
  Qed.
End FirstTrue.

(* At size one, a conjunction holds exactly when both sides do. *)
Lemma and1_iff (b1 b2: bool) (x y: bits_t 1) :
  (b1 = true <-> x = Bits.ones 1) ->
  (b2 = true <-> y = Bits.ones 1) ->
  (andb b1 b2 = true <-> Bits.and x y = Bits.ones 1).
Proof.
  intros H1 H2. split.
  - intro H. apply andb_prop in H. destruct H as [Hb1 Hb2].
    rewrite (proj1 H1 Hb1), (proj1 H2 Hb2). reflexivity.
  - intro H.
    destruct (SchedulerSimulationLemmas.bits1_and_split x y H) as [Hx Hy].
    rewrite (proj2 H1 Hx), (proj2 H2 Hy). reflexivity.
Qed.

Lemma bit_of_to_list (b: bool) : vect_to_list (Definitions.bit_of b) = [b].
Proof. destruct b; reflexivity. Qed.

(* A one-bit node's value is the bit its condition reading names. *)
Lemma bit_of_nonzero (f: forall w, bits_t w) (w: nat) (v: bits_t w) :
  w = 1 -> f w = v -> f 1 = Definitions.bit_of (nonzero v).
Proof.
  intros -> <-.
  destruct (SchedulerSimulationLemmas.bits1_cases (f 1)) as [Ho | Hz];
    rewrite ?Ho, ?Hz; reflexivity.
Qed.

(* A conjunction over a list, read as booleans or as one-bit values. *)
Lemma forallb_fold_and1 {A} (f: A -> bool) (g: A -> bits_t 1) (l: list A) :
  (forall a, List.In a l -> (f a = true <-> g a = Bits.ones 1)) ->
  (forallb f l = true
   <-> fold_right Bits.and (Bits.ones 1) (map g l) = Bits.ones 1).
Proof.
  induction l as [| a l IH]; intro H; cbn [forallb map fold_right].
  - split; intros _; reflexivity.
  - exact (and1_iff _ _ _ _ (H a (or_introl eq_refl))
             (IH (fun b Hb => H b (or_intror Hb)))).
Qed.

(* Two tests that agree wherever the search can still be running give the same
   first-true cycle. *)
Lemma first_true_ext (f g: nat -> bool) (fuel: nat) :
  forall k,
    (forall j, k <= j -> (forall i, k <= i < j -> f i = false) -> f j = g j) ->
    Definitions.first_true f fuel k = Definitions.first_true g fuel k.
Proof.
  induction fuel as [| fuel IH]; intros k H; [ reflexivity | ].
  cbn [Definitions.first_true].
  rewrite <- (H k (le_n k) ltac:(intros i Hi; lia)).
  destruct (f k) eqn:Hk; [ reflexivity | ].
  apply IH. intros j Hj Hbefore.
  apply H; [ lia | ].
  intros i Hi. destruct (Nat.eq_dec i k) as [-> | Hne];
    [ exact Hk | apply Hbefore; lia ].
Qed.

Section IPRProof.
  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  (* Stated in Theorems/Definitions.v; bound at this section's context. *)
  Local Notation base_sound := (Definitions.base_sound ctx cost_limit).
  Local Notation decl_sound := (Definitions.decl_sound ctx cost_limit).
  Local Notation derivable := (Definitions.derivable ctx cost_limit).
  Local Notation gderivable := (Definitions.gderivable ctx cost_limit).
  Local Notation sample_args_settled := (Definitions.sample_args_settled ctx cost_limit).
  Local Notation sample_guards_settled := (Definitions.sample_guards_settled ctx cost_limit).
  Local Notation samples_answered := (Definitions.samples_answered ctx cost_limit).
  Local Notation samples_zeroed := (Definitions.samples_zeroed ctx cost_limit).
  Local Notation settled := (Definitions.settled ctx cost_limit).
  Local Notation uncond_sound := (Definitions.uncond_sound ctx cost_limit).

  (* Stated in Theorems/Definitions.v; bound here at this section's context. *)
  Local Notation L := (Definitions.L ctx cost_limit).
  Local Notation bit_of := Definitions.bit_of.
  Local Notation done_test := (Definitions.done_test ctx cost_limit).
  Local Notation drives_sized := (Definitions.drives_sized ctx cost_limit).
  Local Notation emulate := (Definitions.emulate ctx).
  Local Notation first_done := (Definitions.first_done ctx cost_limit).
  Local Notation guards_sized := (Definitions.guards_sized ctx cost_limit).
  Local Notation instance_sound := (Definitions.instance_sound ctx cost_limit).
  Local Notation is_plumbing := (Definitions.is_plumbing ctx cost_limit).
  Local Notation pi_holds := (Definitions.pi_holds ctx cost_limit).
  Local Notation plumbing_not_root := (Definitions.plumbing_not_root ctx cost_limit).
  Local Notation pub_eq := (Definitions.pub_eq ctx cost_limit).

  (* The attacker's clock, defined in Definitions.v. *)
  Local Notation vvec := Definitions.vvec.
  Local Notation sstate := Definitions.sstate.
  Local Notation slot_valid := Definitions.slot_valid.
  Local Notation avalid := (Definitions.avalid ctx cost_limit).
  Local Notation vv_matches := (Definitions.vv_matches ctx cost_limit).
  Local Notation settled_at := (Definitions.settled_at ctx cost_limit).
  Local Notation vals_sound := (Definitions.vals_sound ctx cost_limit).
  Local Notation selectors_extractable :=
    (Definitions.selectors_extractable ctx cost_limit).
  Local Notation path_ok := (Definitions.path_ok ctx cost_limit).
  Local Notation gate_bufs := (Definitions.gate_bufs ctx cost_limit).
  Local Notation slot_gate := (Definitions.slot_gate ctx cost_limit).
  Local Notation slot_step := (Definitions.slot_step ctx cost_limit).
  Local Notation sstep := (Definitions.sstep ctx cost_limit).
  Local Notation sstart := (Definitions.sstart ctx cost_limit).
  Local Notation srun := (Definitions.srun ctx cost_limit).
  Local Notation adone := (Definitions.adone ctx cost_limit).
  Local Notation pdone_test := (Definitions.pdone_test ctx cost_limit).
  Local Notation L_pub_at := (Definitions.L_pub_at ctx cost_limit).

  Local Notation sched := (tfs_schedule ctx cost_limit).
  Local Notation s_var := (tfs_spec_states ctx).
  Local Notation i_var := (tfs_spec_inputs ctx).
  Local Notation o_var := (tfs_spec_outputs ctx).
  Local Notation p_var := (tfs_spec_ips ctx).
  Local Notation node_t := (@dfg_node_t s_var i_var o_var p_var).

  Local Notation s_sz := (tfs_spec_states_size ctx).
  Local Notation i_sz := (tfs_spec_inputs_size ctx).
  Local Notation o_sz := (tfs_spec_outputs_size ctx).


  Local Notation sched_st_env  := (ContextEnv.(env_t) (tf_states_type (tfs_states_size sched))).
  Local Notation sched_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation sched_sys_state := (sched_st_env * sched_out_env)%type.
  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).
  Local Notation sched_input_t :=
    (forall x : tfs_inputs sched, type_denote (tf_inputs_type (tfs_inputs_size sched) x)).
  Local Notation si_sz := (tfs_inputs_size sched).
  Local Notation ss_sz  := (tfs_states_size sched).
  Local Notation oo_sz  := (tfs_outputs_size sched).
  Local Notation eval1 e ss input :=
    (tf_eval_expr ss_sz si_sz oo_sz (szB := 1) e ss input).
  Local Notation resp_val :=
    (forall p : tfs_ips sched, bits_t (ip_resp_sz (tfs_ip sched p))).
  Local Notation a_index := (Vect.index (length (buffer_needs ctx cost_limit))).
  Local Notation bneeds := (buffer_needs ctx cost_limit).

  (* ------------------------------------------------------------------- *)
  (* Node ids increase along the forward graph.  [build_dfg_wf] states    *)
  (* this on the reversed (emission-order) list; transport it.            *)
  (* ------------------------------------------------------------------- *)

  Lemma ids_asc_fwd (act: tfs_action sched) :
    forall pre (a: node_t) rest,
      graph (build_dfg ctx act) = pre ++ a :: rest ->
      forall M, List.In M pre -> nid M < nid a.
  Proof.
    intros pre a rest Hsplit M HM.
    pose proof (build_dfg_wf ctx cost_limit act) as [Hdesc _].
    apply (Hdesc (rev rest) a (rev pre)).
    - rewrite Hsplit, rev_app_distr. simpl.
      rewrite <- app_assoc. reflexivity.
    - apply -> in_rev. exact HM.
  Qed.

  Lemma ids_post_gt (act: tfs_action sched) :
    forall pre (a: node_t) rest,
      graph (build_dfg ctx act) = pre ++ a :: rest ->
      forall M, List.In M rest -> nid a < nid M.
  Proof.
    intros pre a rest Hsplit M HM.
    destruct (in_split _ _ HM) as [r1 [r2 Hr]].
    apply (ids_asc_fwd act (pre ++ a :: r1) M r2).
    - rewrite Hsplit, Hr. rewrite <- app_assoc. reflexivity.
    - apply in_or_app. right. left. reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* Issue D (agents/taint-tagging-soundness/PLAN.md): taint propagates   *)
  (* along arguments.  A node with a tainted argument is itself tainted,  *)
  (* unless it is declassified by [untainted_roots].                      *)
  (*                                                                      *)
  (* The fold decides each node against the accumulator as it reaches it, *)
  (* so this needs the emission order: [args_lt_fwd] puts the argument    *)
  (* strictly earlier in the graph, hence already in the accumulator.     *)
  (* ------------------------------------------------------------------- *)

  Lemma sample_drive_head_le (act: tfs_action sched) (p: p_var) (h d: nid_t) :
    h < length (graph (build_dfg ctx act)) ->
    sample_drive_head ctx cost_limit act p h = Some d ->
    d <= h.
  Proof.
    intros Hlen Hsd.
    unfold Definitions.sample_drive_head,
           Definitions.node_op in Hsd.
    destruct (op (nth h (graph (build_dfg ctx act))
                   {| nid := 0; op := DFG_Empty; sz := 0 |})) eqn:Hh;
      try discriminate.
    - destruct (eq_dec p0 p); [ | discriminate ].
      injection Hsd as Heq. lia.
    - destruct (op (nth a (graph (build_dfg ctx act))
                     {| nid := 0; op := DFG_Empty; sz := 0 |})) eqn:Ha;
        try discriminate.
      destruct (eq_dec p0 p); [ | discriminate ].
      injection Hsd as Heq.
      assert (Hin : List.In a (get_args ctx (nth h (graph (build_dfg ctx act))
                                              {| nid := 0; op := DFG_Empty; sz := 0 |})))
        by (unfold get_args; rewrite Hh; left; reflexivity).
      pose proof (arg_lt_of_op ctx cost_limit act h a Hlen Hin). lia.
  Qed.

  (* A sample's drive sits below it: the token is the sample's argument, the
     head is the stall's, and a join's drive is the join's. *)
  Lemma sample_drive_lt (act: tfs_action sched) (n d: nid_t) :
    n < length (graph (build_dfg ctx act)) ->
    sample_drive ctx cost_limit act n = Some d ->
    d < n.
  Proof.
    intros Hlen Hsd.
    unfold Definitions.sample_drive,
           Definitions.node_op in Hsd.
    destruct (op (nth n (graph (build_dfg ctx act))
                   {| nid := 0; op := DFG_Empty; sz := 0 |})) eqn:Hn;
      try discriminate.
    assert (Hint : List.In tok (get_args ctx (nth n (graph (build_dfg ctx act))
                                               {| nid := 0; op := DFG_Empty; sz := 0 |})))
      by (unfold get_args; rewrite Hn; left; reflexivity).
    pose proof (arg_lt_of_op ctx cost_limit act n tok Hlen Hint) as Htok.
    assert (Htlen : tok < length (graph (build_dfg ctx act))) by lia.
    destruct (op (nth tok (graph (build_dfg ctx act))
                   {| nid := 0; op := DFG_Empty; sz := 0 |})) eqn:Ht.
    all: try (pose proof (sample_drive_head_le act p tok d Htlen Hsd); lia).
    (* the stall arm: the head is the stall's own argument *)
    match goal with
    | H : op (nth tok _ _) = DFG_Stall _ ?hh |- _ =>
        assert (Hinh : List.In hh
                  (get_args ctx (nth tok (graph (build_dfg ctx act))
                                   {| nid := 0; op := DFG_Empty; sz := 0 |})))
          by (unfold get_args; rewrite H; left; reflexivity);
        pose proof (arg_lt_of_op ctx cost_limit act tok hh Htlen Hinh) as Hah;
        assert (Halen : hh < length (graph (build_dfg ctx act))) by lia;
        pose proof (sample_drive_head_le act p hh d Halen Hsd); lia
    end.
  Qed.


  Lemma taint_propagates (act: tfs_action sched) :
    forall (node: node_t) (a: nid_t),
      List.In node (graph (build_dfg ctx act)) ->
      List.In a (get_args ctx node) ->
      List.In a (get_tainted ctx (build_dfg ctx act)) ->
      ~ List.In (nid node) (untainted_roots ctx (build_dfg ctx act)) ->
      List.In (nid node) (get_tainted ctx (build_dfg ctx act)).
  Proof.
    intros node a Hnode Harg Hat Hnd.
    pose proof (args_lt_fwd ctx cost_limit act node Hnode a Harg) as Halt.
    destruct (in_split _ _ Hnode) as [pre [post Hsplit]].
    pose proof (ids_post_gt act pre node post Hsplit) as Hgt.
    unfold get_tainted in Hat |- *. cbv zeta in Hat |- *.
    set (U := untainted_roots ctx (build_dfg ctx act)) in *.
    match goal with |- context [fold_left ?F _ _] => set (aux := F) in * end.

    assert (Hgrow : forall acc (b: node_t), incl acc (aux acc b)).
    { intros acc b. unfold aux; cbn beta.
      destruct (mem (nid b) U); [ apply incl_refl | ].
      destruct (_ || _)%bool; [ apply incl_tl, incl_refl | apply incl_refl ]. }

    assert (Hsrc : forall acc (b: node_t) x,
               List.In x (aux acc b) -> List.In x acc \/ x = nid b).
    { intros acc b x Hx. unfold aux in Hx; cbn beta in Hx.
      destruct (mem (nid b) U); [ left; exact Hx | ].
      destruct (_ || _)%bool; [ | left; exact Hx ].
      destruct Hx as [Hx | Hx]; [ right; symmetry; exact Hx | left; exact Hx ]. }

    rewrite Hsplit, fold_left_app in Hat |- *. simpl in Hat |- *.
    set (accP := fold_left aux pre []) in *.

    (* the argument was already tainted when the fold reached [node] *)
    assert (HaP : List.In a accP).
    { destruct (fold_left_source aux nid Hsrc post _ _ Hat)
        as [Hin | [b [Hb Heq]]].
      - destruct (Hsrc _ _ _ Hin) as [Hin' | Heq]; [ exact Hin' | lia ].
      - specialize (Hgt b Hb). lia. }

    (* hence [node] is tainted at its own step, and stays so *)
    apply (fold_left_grows aux Hgrow post (aux accP node)).
    unfold aux; cbn beta.
    destruct (mem (nid node) U) as [m | _].
    { exfalso. apply Hnd. exact (member_In _ _ m). }
    replace (existsb
               (fun arg_id => match mem arg_id accP with
                              | inl _ => true
                              | inr _ => false
                              end) (get_args ctx node)) with true.
    - rewrite Bool.orb_true_r. left. reflexivity.
    - symmetry. apply existsb_exists. exists a. split; [ exact Harg | ].
      destruct (mem a accP) as [| f]; [ reflexivity | ].
      exfalso. exact (f (In_member a accP HaP)).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* Two syntactic facts about a built graph, carried as side conditions   *)
  (* until they are read off the builder's invariants.                     *)
  (* ------------------------------------------------------------------- *)

  (* One step of the taint walk, read backwards. *)
  Lemma arg_untainted (act: tfs_action sched) (m x: nid_t) :
    m < length (graph (build_dfg ctx act)) ->
    ~ List.In m (get_tainted ctx (build_dfg ctx act)) ->
    ~ List.In m (untainted_roots ctx (build_dfg ctx act)) ->
    List.In x (get_args ctx (nth m (graph (build_dfg ctx act))
                              {| nid := 0; op := DFG_Empty; sz := 0 |})) ->
    ~ List.In x (get_tainted ctx (build_dfg ctx act)).
  Proof.
    intros Hlen Hmt Hmr Hx Hxt.
    rewrite <- (node_nid_at ctx cost_limit act m Hlen) in Hmt, Hmr.
    exact (Hmt (taint_propagates act _ x (nth_In _ _ Hlen) Hx Hxt Hmr)).
  Qed.

  Lemma sample_drive_head_untainted (act: tfs_action sched) (p: p_var) (h d: nid_t) :
    plumbing_not_root act ->
    h < length (graph (build_dfg ctx act)) ->
    sample_drive_head ctx cost_limit act p h = Some d ->
    ~ List.In h (get_tainted ctx (build_dfg ctx act)) ->
    ~ List.In d (get_tainted ctx (build_dfg ctx act)).
  Proof.
    intros Hpl Hlen Hsd Hht.
    unfold Definitions.sample_drive_head,
           Definitions.node_op in Hsd.
    destruct (op (nth h (graph (build_dfg ctx act))
                   {| nid := 0; op := DFG_Empty; sz := 0 |})) eqn:Hh;
      try discriminate.
    - destruct (eq_dec p0 p); [ | discriminate ].
      injection Hsd as Heq. rewrite <- Heq. exact Hht.
    - destruct (op (nth a (graph (build_dfg ctx act))
                     {| nid := 0; op := DFG_Empty; sz := 0 |})) eqn:Ha;
        try discriminate.
      destruct (eq_dec p0 p); [ | discriminate ].
      injection Hsd as Heq. rewrite <- Heq.
      apply (arg_untainted act h a Hlen Hht).
      + apply Hpl. unfold is_plumbing, Definitions.node_op.
        rewrite Hh. reflexivity.
      + unfold get_args. rewrite Hh. left. reflexivity.
  Qed.

  (* An untainted sample has an untainted DRIVE: the walk runs through the
     token and the stall, and a rule can declassify neither. *)
  Lemma sample_drive_untainted (act: tfs_action sched) (n d: nid_t) :
    plumbing_not_root act ->
    n < length (graph (build_dfg ctx act)) ->
    sample_drive ctx cost_limit act n = Some d ->
    ~ List.In n (get_tainted ctx (build_dfg ctx act)) ->
    ~ List.In n (untainted_roots ctx (build_dfg ctx act)) ->
    ~ List.In d (get_tainted ctx (build_dfg ctx act)).
  Proof.
    intros Hpl Hlen Hsd Hnt Hnr.
    unfold Definitions.sample_drive,
           Definitions.node_op in Hsd.
    destruct (op (nth n (graph (build_dfg ctx act))
                   {| nid := 0; op := DFG_Empty; sz := 0 |})) eqn:Hn;
      try discriminate.
    assert (Hint : List.In tok (get_args ctx (nth n (graph (build_dfg ctx act))
                                               {| nid := 0; op := DFG_Empty; sz := 0 |})))
      by (unfold get_args; rewrite Hn; left; reflexivity).
    pose proof (arg_lt_of_op ctx cost_limit act n tok Hlen Hint) as Htok.
    assert (Htlen : tok < length (graph (build_dfg ctx act))) by lia.
    pose proof (arg_untainted act n tok Hlen Hnt Hnr Hint) as Htokt.
    destruct (op (nth tok (graph (build_dfg ctx act))
                   {| nid := 0; op := DFG_Empty; sz := 0 |})) eqn:Ht.
    all: try (exact (sample_drive_head_untainted act p tok d Hpl Htlen Hsd Htokt)).
    match goal with
    | H : op (nth tok _ _) = DFG_Stall _ ?hh |- _ =>
        assert (Hinh : List.In hh
                  (get_args ctx (nth tok (graph (build_dfg ctx act))
                                   {| nid := 0; op := DFG_Empty; sz := 0 |})))
          by (unfold get_args; rewrite H; left; reflexivity);
        pose proof (arg_lt_of_op ctx cost_limit act tok hh Htlen Hinh) as Hah;
        assert (Halen : hh < length (graph (build_dfg ctx act))) by lia;
        assert (Hhnr : ~ List.In tok (untainted_roots ctx (build_dfg ctx act)))
          by (apply Hpl; unfold is_plumbing, Definitions.node_op;
              rewrite H; reflexivity);
        pose proof (arg_untainted act tok hh Htlen Htokt Hhnr Hinh) as Hht;
        exact (sample_drive_head_untainted act p hh d Hpl Halen Hsd Hht)
    end.
  Qed.

  (* The self-taint counterpart of [taint_propagates]: a read of pre-action
     secret state is a taint source, so it is tainted unless declassified. *)
  Lemma svar_tainted (act: tfs_action sched) (node: node_t) (sv: s_var) :
    List.In node (graph (build_dfg ctx act)) ->
    op node = DFG_Var (DFG_SVar sv) ->
    ~ List.In (nid node) (untainted_roots ctx (build_dfg ctx act)) ->
    List.In (nid node) (get_tainted ctx (build_dfg ctx act)).
  Proof.
    intros Hnode Hop Hnd.
    destruct (in_split _ _ Hnode) as [pre [post Hsplit]].
    unfold get_tainted. cbv zeta.
    set (U := untainted_roots ctx (build_dfg ctx act)) in *.
    match goal with |- context [fold_left ?F _ _] => set (aux := F) in * end.

    assert (Hgrow : forall acc (b: node_t), incl acc (aux acc b)).
    { intros acc b. unfold aux; cbn beta.
      destruct (mem (nid b) U); [ apply incl_refl | ].
      destruct (_ || _)%bool; [ apply incl_tl, incl_refl | apply incl_refl ]. }

    rewrite Hsplit, fold_left_app. simpl.
    set (accP := fold_left aux pre []).
    apply (fold_left_grows aux Hgrow post (aux accP node)).
    unfold aux; cbn beta.
    destruct (mem (nid node) U) as [m | _].
    { exfalso. apply Hnd. exact (member_In _ _ m). }
    rewrite Hop. cbn [orb]. left. reflexivity.
  Qed.

  (* The read-side twin of [svar_tainted]: a read of an output the attacker
     cannot see is a taint source too.  Same proof, one extra rewrite to compute
     [self_tainted] through the class. *)
  Lemma ovar_secret_tainted (act: tfs_action sched) (node: node_t) (ov: o_var) :
    List.In node (graph (build_dfg ctx act)) ->
    op node = DFG_Var (DFG_OVar ov) ->
    tfs_spec_outputs_class ctx ov = Secret ->
    ~ List.In (nid node) (untainted_roots ctx (build_dfg ctx act)) ->
    List.In (nid node) (get_tainted ctx (build_dfg ctx act)).
  Proof.
    intros Hnode Hop Hcls Hnd.
    destruct (in_split _ _ Hnode) as [pre [post Hsplit]].
    unfold get_tainted. cbv zeta.
    set (U := untainted_roots ctx (build_dfg ctx act)) in *.
    match goal with |- context [fold_left ?F _ _] => set (aux := F) in * end.

    assert (Hgrow : forall acc (b: node_t), incl acc (aux acc b)).
    { intros acc b. unfold aux; cbn beta.
      destruct (mem (nid b) U); [ apply incl_refl | ].
      destruct (_ || _)%bool; [ apply incl_tl, incl_refl | apply incl_refl ]. }

    rewrite Hsplit, fold_left_app. simpl.
    set (accP := fold_left aux pre []).
    apply (fold_left_grows aux Hgrow post (aux accP node)).
    unfold aux; cbn beta.
    destruct (mem (nid node) U) as [m | _].
    { exfalso. apply Hnd. exact (member_In _ _ m). }
    rewrite Hop, Hcls. cbn [orb]. left. reflexivity.
  Qed.

  (* The input-side sibling of [svar_tainted] and [ovar_secret_tainted], same
     proof over [self_tainted]'s own [DFG_Input] arm. *)
  Lemma input_secret_tainted (act: tfs_action sched) (node: node_t) (iv: i_var) :
    List.In node (graph (build_dfg ctx act)) ->
    op node = DFG_Input iv ->
    tfs_spec_inputs_class ctx iv = Secret ->
    ~ List.In (nid node) (untainted_roots ctx (build_dfg ctx act)) ->
    List.In (nid node) (get_tainted ctx (build_dfg ctx act)).
  Proof.
    intros Hnode Hop Hcls Hnd.
    destruct (in_split _ _ Hnode) as [pre [post Hsplit]].
    unfold get_tainted. cbv zeta.
    set (U := untainted_roots ctx (build_dfg ctx act)) in *.
    match goal with |- context [fold_left ?F _ _] => set (aux := F) in * end.

    assert (Hgrow : forall acc (b: node_t), incl acc (aux acc b)).
    { intros acc b. unfold aux; cbn beta.
      destruct (mem (nid b) U); [ apply incl_refl | ].
      destruct (_ || _)%bool; [ apply incl_tl, incl_refl | apply incl_refl ]. }

    rewrite Hsplit, fold_left_app. simpl.
    set (accP := fold_left aux pre []).
    apply (fold_left_grows aux Hgrow post (aux accP node)).
    unfold aux; cbn beta.
    destruct (mem (nid node) U) as [m | _].
    { exfalso. apply Hnd. exact (member_In _ _ m). }
    rewrite Hop, Hcls. cbn [orb]. left. reflexivity.
  Qed.

  (* A node's compiled VALIDITY at an explicit path.  A buffered node -- every
     sample is one -- reads its validity register here, so for a sample this is
     the same expression at every path. *)
  Local Notation rvalid act a_idx pi n ss input :=
    (eval1 (snd (compile_dfg_expr_at ctx bneeds pi
                   (length (graph (build_dfg ctx act))) a_idx
                   (build_dfg ctx act) n (sample_bufs ctx cost_limit act a_idx)))
       ss input) (only parsing).

  Lemma pi_holds_nil (act: tfs_action sched) (a_idx: a_index) (input: sched_input_t)
      (ss: sched_sys_state) : pi_holds act a_idx input [] ss.
  Proof. intros c b Hin; destruct Hin. Qed.

  (* Extending a path with a literal the run agrees with. *)
  Lemma pi_holds_cons (act: tfs_action sched) (a_idx: a_index) (input: sched_input_t)
      (c: nid_t) (b: bool) (pi: list lit) (ss: sched_sys_state) :
    pi_holds act a_idx input pi ss ->
    nval ctx cost_limit act a_idx ss input 1 c = bit_of b ->
    pi_holds act a_idx input ((c, b) :: pi) ss.
  Proof.
    intros Hpi Hc x bb [He | Hin]; [ injection He as -> ->; exact Hc |].
    exact (Hpi x bb Hin).
  Qed.


  (* Deciding it: the literals are a finite list of one-bit comparisons, and
     the sample case splits on whether the guard held. *)
  Definition pi_holdsb (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (pi: list lit) (ss: sched_sys_state) : bool :=
    forallb (fun l => beq_dec (nval ctx cost_limit act a_idx ss input 1 (fst l))
                        (bit_of (snd l))) pi.

  Lemma pi_holdsb_spec (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (pi: list lit) (ss: sched_sys_state) :
    pi_holdsb act a_idx input pi ss = true <-> pi_holds act a_idx input pi ss.
  Proof.
    unfold pi_holdsb, pi_holds. rewrite forallb_forall. split.
    - intros H c b Hin.
      exact (proj1 (beq_dec_iff _ _ _) (H (c, b) Hin)).
    - intros H l Hin. destruct l as [c b].
      apply (proj2 (beq_dec_iff _ _ _)). cbn [fst snd]. exact (H c b Hin).
  Qed.

  (* [pi_holds] is the scheduler's [en_holds], read at one bit. *)
  Lemma pi_holds_guard (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (en: list lit) (ss: sched_sys_state) :
    pi_holds act a_idx input en ss ->
    SchedulerRoundTrip.en_holds ctx cost_limit act a_idx ss input en.
  Proof.
    intros H c b Hin. specialize (H c b Hin).
    unfold Definitions.nval, bit_of in H. split.
    - intro Hb. subst b. rewrite H. exact ones1_neq_zero.
    - intro Hb. subst b. exact H.
  Qed.

  Lemma guard_pi_holds (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (en: list lit) (ss: sched_sys_state) :
    SchedulerRoundTrip.en_holds ctx cost_limit act a_idx ss input en ->
    pi_holds act a_idx input en ss.
  Proof.
    intros H c b Hin. destruct (H c b Hin) as [Ht Hf].
    unfold Definitions.nval, bit_of. destruct b.
    - destruct (bits1_cases (eval1 (node_ref_expr ctx cost_limit act a_idx c) ss input))
        as [Ho | Hz]; [ exact Ho | exfalso; exact (Ht eq_refl Hz) ].
    - exact (Hf eq_refl).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* PHASE 0: the public view, and what it means for a node to be         *)
  (* derivable from it.                                                    *)
  (*                                                                       *)
  (* The three attacker-visible sources of the taint campaign's            *)
  (* authoritative definition, stated at the DFG level:                    *)
  (*   1. the action's inputs      -- a shared parameter, not a conjunct;  *)
  (*   2. the pre-action outputs   -- the [snd] component;                 *)
  (*   3. the post-action outputs  -- the values of the var_map roots of   *)
  (*      output variables, which is what those registers hold at done.    *)
  (* The secret state ([tf_dfg_s] registers) is deliberately unconstrained. *)
  (* ------------------------------------------------------------------- *)

  Local Notation nsz act n :=
    (sz (nth n (graph (build_dfg ctx act))
           {| nid := 0; op := DFG_Empty; sz := 0 |})).

  (* ------------------------------------------------------------------- *)
  (* (D1) for the blackbox instantiation: the seed of the taint fold is    *)
  (* derivable.  Phase 1 consumes this and nothing else about the seed, so *)
  (* the whitebox campaign only has to re-prove *this* lemma for its own   *)
  (* [untainted_roots].                                                     *)
  (* ------------------------------------------------------------------- *)

  (* Only a PUBLIC destination declassifies: the public view covers exactly
     those, so a secret written anywhere else stays tainted.  REVIEW.md 2.3. *)
  Lemma public_dst_derivable (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (o: o_var) (r: nid_t) :
    tfs_spec_outputs_class ctx o = Public ->
    List.In (DFG_OVar o, r) (var_map (build_dfg ctx act)) ->
    derivable act a_idx input r.
  Proof.
    intros Hpub Hin ss ss' input' pi [_ [_ Hroots]] _ _ Hpi Hpi' Hv Hv'.
    exact (Hroots o r pi Hpub Hin Hpi Hpi' Hv Hv').
  Qed.

  Lemma public_dsts_derivable (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (n: nid_t) :
    List.In n (public_dsts ctx (build_dfg ctx act)) ->
    derivable act a_idx input n.
  Proof.
    unfold public_dsts. intro Hin.
    apply in_map_iff in Hin. destruct Hin as [[v r] [Hsnd Hfil]].
    simpl in Hsnd. subst r.
    apply filter_In in Hfil. destruct Hfil as [Hvm Hv].
    destruct v as [sv | ov]; [ discriminate Hv | ].
    (* The filter now carries the class, so the hypothesis is available here
       rather than having to be assumed. *)
    destruct (tfs_spec_outputs_class ctx ov) eqn:Hcls; [ | discriminate Hv ].
    exact (public_dst_derivable act a_idx input ov n Hcls Hvm).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The user's obligation for the unconditional declassification          *)
  (* instances their rules emit: derivable sources give a derivable        *)
  (* target.  [instance_sound] below is its guarded form, which implies    *)
  (* this one because [pi_holds []] is trivial.                            *)
  (* ------------------------------------------------------------------- *)

  (* Discharged by the user, per context; the rule library in coq/Rules/ proves
     it for the rules it ships. *)
  Context (Hdecls : forall act a_idx input, uncond_sound act a_idx input).

  Lemma mem_nid_In (n: nid_t) (l: list nid_t) : mem_nid n l = true -> List.In n l.
  Proof.
    unfold mem_nid. intro H. apply existsb_exists in H.
    destruct H as [x [Hin Heq]]. apply Nat.eqb_eq in Heq. subst x. exact Hin.
  Qed.

  Lemma saturate_step_derivable (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (acc: list nid_t) :
    (forall x, List.In x acc -> derivable act a_idx input x) ->
    forall n, List.In n (saturate_step ctx (build_dfg ctx act) acc) ->
      derivable act a_idx input n.
  Proof.
    unfold saturate_step.
    assert (Hgen : forall l acc,
              (forall i, List.In i l ->
                 List.In i (uncond_instances ctx (build_dfg ctx act))) ->
              (forall x, List.In x acc -> derivable act a_idx input x) ->
              forall n, List.In n
                (fold_left (fun acc i =>
                              if forallb (fun s => mem_nid s acc) (di_sources i)
                                 && negb (mem_nid (di_target i) acc)
                              then di_target i :: acc else acc) l acc) ->
                derivable act a_idx input n).
    { induction l as [| i l IH]; intros acc0 Hsub Hacc n Hin;
        [ exact (Hacc n Hin) | ].
      cbn [fold_left] in Hin.
      destruct (forallb (fun s => mem_nid s acc0) (di_sources i)
                && negb (mem_nid (di_target i) acc0)) eqn:Hf.
      - apply andb_prop in Hf. destruct Hf as [Hf _].
        assert (Hacc' : forall x, List.In x (di_target i :: acc0) ->
                          derivable act a_idx input x).
        { intros x Hx. destruct Hx as [Hx | Hx]; [ | exact (Hacc x Hx) ].
          subst x.
          apply (Hdecls act a_idx input i (Hsub i (or_introl eq_refl))).
          intros s Hs. apply Hacc.
          rewrite forallb_forall in Hf. exact (mem_nid_In s acc0 (Hf s Hs)). }
        exact (IH _ (fun j Hj => Hsub j (or_intror Hj)) Hacc' n Hin).
      - exact (IH _ (fun j Hj => Hsub j (or_intror Hj)) Hacc n Hin). }
    intro Hacc. exact (Hgen _ acc (fun i Hi => Hi) Hacc).
  Qed.

  Lemma saturate_derivable (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (fuel: nat) (acc: list nid_t) :
    (forall x, List.In x acc -> derivable act a_idx input x) ->
    forall n, List.In n (saturate ctx fuel (build_dfg ctx act) acc) ->
      derivable act a_idx input n.
  Proof.
    revert acc. induction fuel as [| fuel IH]; intros acc Hacc n Hin;
      [ exact (Hacc n Hin) | ].
    cbn [saturate] in Hin. cbv zeta in Hin.
    destruct (Nat.eqb (length (saturate_step ctx (build_dfg ctx act) acc))
                      (length acc)) eqn:Hstop.
    - exact (Hacc n Hin).
    - exact (IH _ (saturate_step_derivable act a_idx input acc Hacc) n Hin).
  Qed.

  (* Constants agree across any two runs, and a PUBLIC input does too because the
     attacker drives it and [pub_eq] pins it.  [trivially_public] admits exactly
     those, a secret input being a taint source. *)
  Lemma trivial_derivable (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (n: nid_t) :
    List.In n (trivially_public ctx (build_dfg ctx act)) ->
    derivable act a_idx input n.
  Proof.
    unfold trivially_public. intro Hin.
    apply filter_In in Hin. destruct Hin as [Hseq Hop].
    apply in_seq in Hseq. destruct Hseq as [Hn1 Hn2].
    assert (Hlen : n < length (graph (build_dfg ctx act))) by lia.
    intros ss ss' input' pi Hpe _ _ _ _ _ _. unfold nval.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa | dp darg den | sp stok sen | ja jb | ] eqn:Hopn;
      try discriminate.
    - rewrite (nre_const ctx cost_limit act a_idx n c Hn1 Hlen Hopn). reflexivity.
    - rewrite (nre_input ctx cost_limit act a_idx n v Hn1 Hlen Hopn).
      (* the filter admitted this node, so the input is Public *)
      destruct (tfs_spec_inputs_class ctx v) eqn:Hcls; [ | discriminate Hop ].
      destruct Hpe as [Hipub _]. cbn [tf_eval_expr]. f_equal.
      exact (Hipub v Hcls).
  Qed.

  Lemma untainted_roots_derivable (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (n: nid_t) :
    List.In n (untainted_roots ctx (build_dfg ctx act)) ->
    derivable act a_idx input n.
  Proof.
    unfold untainted_roots.
    apply (saturate_derivable act a_idx input).
    intros m Hm. apply in_app_or in Hm. destruct Hm as [Hm | Hm].
    - exact (public_dsts_derivable act a_idx input m Hm).
    - exact (trivial_derivable act a_idx input m Hm).
  Qed.

  (* [pub_eq]'s second conjunct is at the output's own width, so it reads "the
     two states publish the same values".  Stated at [tfs_outputs_size sched],
     to rewrite against [dfg_action_semantics]. *)
  Lemma pub_eq_root_width (act: tfs_action sched) (o: o_var) (r: nid_t) :
    List.In (DFG_OVar o, r) (var_map (build_dfg ctx act)) ->
    nsz act r = tfs_outputs_size sched o.
  Proof.
    intro Hin.
    exact (proj2 (wsz_node_sz ctx cost_limit act r _
                    (wvsz_build_dfg ctx cost_limit act _ r Hin))).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* PHASE 0, falsification.  A security definition that the bug it exists *)
  (* to catch cannot violate is the wrong definition, so we check that      *)
  (* [derivable] has teeth on a secret read.                                *)
  (*                                                                       *)
  (* The GENERAL_REQUIREMENTS 1.1 bug seeded [untainted_roots] from *every* *)
  (* [var_map] root rather than only the [DFG_OVar] ones, so it declassified *)
  (* [DFG_Var (DFG_SVar _)] nodes.  Under that seed the (D1) obligation      *)
  (* above would have to be discharged for such nodes; the lemmas here show  *)
  (* what that commits us to, and that it is false.                          *)
  (* ------------------------------------------------------------------- *)

  (* An action that writes no output variable. Its public view carries no
     post-action component at all, so [pub_eq] then constrains only [snd]. *)
  Definition publishes_nothing (act: tfs_action sched) : Prop :=
    forall (o: o_var) (r: nid_t),
      ~ List.In (DFG_OVar o, r) (var_map (build_dfg ctx act)).

  Lemma pub_eq_publishes_nothing (act: tfs_action sched) (a_idx: a_index)
      (input input': sched_input_t) (ss ss': sched_sys_state) :
    publishes_nothing act ->
    (forall v : i_var, tfs_spec_inputs_class ctx v = Public -> input (inl v) = input' (inl v)) ->
    (forall o : o_var, (snd ss).[o] = (snd ss').[o]) ->
    pub_eq act a_idx input input' ss ss'.
  Proof.
    intros Hno Hipub Hout. split; [ exact Hipub | split ].
    - intros o _; exact (Hout o).
    - intros o r pi _ Hin. destruct (Hno o r Hin).
  Qed.

  (* A SOURCE node is valid unconditionally: it holds one value for the whole
     action, so the compiler gives it [tf_const 1]. *)
  Lemma nrv_source (act: tfs_action sched) (a_idx: a_index) (n: nid_t)
      (ss: sched_sys_state) (input: sched_input_t) :
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    source_op ctx (op (nth n (graph (build_dfg ctx act))
                        {| nid := 0; op := DFG_Empty; sz := 0 |})) = true ->
    eval1 (node_ref_valid ctx cost_limit act a_idx n) ss input = Bits.ones 1.
  Proof.
    intros H1 Hlen Hsrc. unfold node_ref_valid.
    destruct (length (graph (build_dfg ctx act))) as [| f] eqn:Ef; [ lia | ].
    cbn [compile_dfg_expr_aux].
    rewrite (not_sample_not_in_sample_bufs ctx cost_limit act a_idx n
               ltac:(unfold is_sample_of, node_op;
                     destruct (op (nth n (graph (build_dfg ctx act))
                                    {| nid := 0; op := DFG_Empty; sz := 0 |}));
                     solve [ reflexivity | discriminate Hsrc ])).
    cbv beta iota.
    unfold source_op in Hsrc.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |})) eqn:Hopn;
      try discriminate Hsrc; cbn [snd];
      [ exact (eval1_const1 ctx cost_limit ss input)
      | exact (eval1_const1 ctx cost_limit ss input)
      | destruct v; exact (eval1_const1 ctx cost_limit ss input) ].
  Qed.

  Lemma svar_nval (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t) (szB: nat) (n: nid_t)
      (sv: s_var) :
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    op (nth n (graph (build_dfg ctx act))
          {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Var (DFG_SVar sv) ->
    nval ctx cost_limit act a_idx ss input szB n
    = convert (fst ss).[tf_dfg_s sv].
  Proof.
    intros H1 H2 Hop. unfold nval.
    rewrite (nre_svar ctx cost_limit act a_idx n sv H1 H2 Hop).
    cbn [tf_eval_expr]. reflexivity.
  Qed.

  (* Declassifying a secret read commits us to this: for an action that
     publishes nothing, the secret register is pinned by the outputs alone. *)
  Theorem svar_derivable_forces_secret_public (act: tfs_action sched)
      (a_idx: a_index) (input: sched_input_t) (n: nid_t) (sv: s_var) :
    publishes_nothing act ->
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    op (nth n (graph (build_dfg ctx act))
          {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Var (DFG_SVar sv) ->
    derivable act a_idx input n ->
    forall (ss ss': sched_sys_state),
      settled act a_idx ss  input ->
      settled act a_idx ss' input ->
      (forall o : o_var, (snd ss).[o] = (snd ss').[o]) ->
      convert (szB := nsz act n) (fst ss ).[tf_dfg_s sv]
      = convert (szB := nsz act n) (fst ss').[tf_dfg_s sv].
  Proof.
    intros Hno H1 H2 Hop Hder ss ss' Hsa Hsa' Hout.
    rewrite <- (svar_nval act a_idx ss  input _ n sv H1 H2 Hop).
    rewrite <- (svar_nval act a_idx ss' input _ n sv H1 H2 Hop).
    (* both runs here use the SAME input, so the public-input agreement is
       reflexivity; the content of the lemma is about differing secret STATE *)
    apply (Hder ss ss' input []);
      [ | exact Hsa | exact Hsa'
      | exact (pi_holds_nil act a_idx input ss)
      | exact (pi_holds_nil act a_idx input ss')
      | exact (nrv_source act a_idx n ss  input  H1 H2 ltac:(rewrite Hop; reflexivity))
      | exact (nrv_source act a_idx n ss' input  H1 H2 ltac:(rewrite Hop; reflexivity)) ].
    apply pub_eq_publishes_nothing;
      [ assumption | intros v _; reflexivity | assumption ].
  Qed.

  (* ... and that consequent fails once the register holds two values the node's
     width tells apart, so [0 < width] is the real hypothesis.  [nsz act n] is
     explicit because no lemma records it as the register's own width. *)
  Theorem svar_not_derivable (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (n: nid_t) (sv: s_var) :
    publishes_nothing act ->
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    op (nth n (graph (build_dfg ctx act))
          {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Var (DFG_SVar sv) ->
    (exists b1 b2 : bits_t (tfs_states_size sched (tf_dfg_s sv)),
       convert (szB := nsz act n) b1 <> convert (szB := nsz act n) b2) ->
    ~ derivable act a_idx input n.
  Proof.
    intros Hno H1 H2 Hop [b1 [b2 Hne]] Hder.
    apply Hne.
    pose (base := ContextEnv.(create)
                    (fun k => Bits.zero) : sched_st_env).
    pose (o0 := ContextEnv.(create)
                  (fun k => Bits.zero) : sched_out_env).
    (* every validity register reads zero here, so the round-trip obligation
       has no latched sample to talk about *)
    assert (Hzv : forall b n_idx,
              (fst (ContextEnv.(putenv) base (tf_dfg_s sv) b, o0))
                .[tf_dfg_v a_idx n_idx] <> Bits.ones 1).
    { intros b n_idx Hv. cbn [fst] in Hv.
      rewrite get_put_neq in Hv by discriminate.
      unfold base in Hv. rewrite getenv_create in Hv.
      exact (ones1_neq_zero (eq_sym Hv)). }
    assert (Hsa : forall b, settled act a_idx
                    (ContextEnv.(putenv) base (tf_dfg_s sv) b, o0) input).
    { intro b. split; [| split; [| split ]].
      - intros n_idx p tok en d av en' _ _ _ _ Hv.
        destruct (Hzv b n_idx Hv).
      - intros n_idx p tok en _ Hv.
        destruct (Hzv b n_idx Hv).
      - intros n_idx p tok en d av en' _ _ _ Hv.
        destruct (Hzv b n_idx Hv).
      - intros n_idx p tok en _ Hv.
        destruct (Hzv b n_idx Hv). }
    pose proof (svar_derivable_forces_secret_public act a_idx input n sv
                  Hno H1 H2 Hop Hder
                  (ContextEnv.(putenv) base (tf_dfg_s sv) b1, o0)
                  (ContextEnv.(putenv) base (tf_dfg_s sv) b2, o0)
                  (Hsa b1) (Hsa b2)
                  (fun o => eq_refl)) as Heq.
    cbn [fst] in Heq. rewrite !get_put_eq in Heq. exact Heq.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* PHASE 1: taint soundness.  Whatever the analysis leaves untainted is  *)
  (* a function of the public view alone.                                  *)
  (*                                                                       *)
  (* The only fact used about the seed is [untainted_roots_derivable], so   *)
  (* a whitebox seed re-proves that lemma and inherits this one unchanged.  *)
  (* ------------------------------------------------------------------- *)

  Theorem untainted_derivable (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) :
    act_idx_aligned ctx cost_limit act a_idx ->
    plumbing_not_root act ->
    drives_sized act ->
    guards_sized act ->
    forall n,
      1 <= n -> n < length (graph (build_dfg ctx act)) ->
      ~ List.In n (get_tainted ctx (build_dfg ctx act)) ->
      derivable act a_idx input n.
  Proof.
    intros Halign Hpl Hdsz Hgsz.
    intro n. pattern n. apply (well_founded_ind lt_wf). clear n.
    intros n IH H1 Hlen Hnt.

    destruct (in_dec Nat.eq_dec n (untainted_roots ctx (build_dfg ctx act)))
      as [Hroot | Hnroot].
    { exact (untainted_roots_derivable act a_idx input n Hroot). }

    assert (Hin : List.In (nth n (graph (build_dfg ctx act))
                             {| nid := 0; op := DFG_Empty; sz := 0 |})
                    (graph (build_dfg ctx act)))
      by (apply nth_In; exact Hlen).
    assert (Hnid : nid (nth n (graph (build_dfg ctx act))
                          {| nid := 0; op := DFG_Empty; sz := 0 |}) = n)
      by (apply node_nid_at; exact Hlen).
    assert (Hnr' : ~ List.In (nid (nth n (graph (build_dfg ctx act))
                                     {| nid := 0; op := DFG_Empty; sz := 0 |}))
                     (untainted_roots ctx (build_dfg ctx act)))
      by (rewrite Hnid; exact Hnroot).

    (* Every argument is untainted too -- the contrapositive of
       [taint_propagates] -- hence derivable by the induction hypothesis. *)
    assert (Hargder : forall x,
              List.In x (get_args ctx (nth n (graph (build_dfg ctx act))
                                         {| nid := 0; op := DFG_Empty; sz := 0 |})) ->
              derivable act a_idx input x).
    { intros x Hx.
      destruct (node_args_range ctx cost_limit act n H1 Hlen x Hx) as [Hx1 Hxn].
      apply IH; [ exact Hxn | exact Hx1 | lia | ].
      intro Hxt.
      assert (Ht := taint_propagates act _ x Hin Hx Hxt Hnr').
      rewrite Hnid in Ht. exact (Hnt Ht). }

    intros ss ss' input' pi Hpub Hsa Hsa' Hpin Hpin' Hvn Hvn'. unfold nval.
    pose proof (wfg_build_dfg ctx cost_limit act _ Hin) as Hfg.

    (* [node_args_sz] pins the width each argument is consumed at, so a fact at
       the argument's declared width is exactly what every case needs. *)
    assert (Hder_at : forall x W (p: list lit),
              List.In x (get_args ctx (nth n (graph (build_dfg ctx act))
                                         {| nid := 0; op := DFG_Empty; sz := 0 |})) ->
              wsz ctx (build_dfg ctx act) x W ->
              pi_holds act a_idx input  p ss  ->
              pi_holds act a_idx input' p ss' ->
              rvalid act a_idx p x ss  input  = Bits.ones 1 ->
              rvalid act a_idx p x ss' input' = Bits.ones 1 ->
              tf_eval_expr (tfs_states_size sched) si_sz (tfs_outputs_size sched)
                (szB := W) (node_ref_expr ctx cost_limit act a_idx x) ss input
              = tf_eval_expr (tfs_states_size sched) si_sz (tfs_outputs_size sched)
                (szB := W) (node_ref_expr ctx cost_limit act a_idx x) ss' input').
    { intros x W p Hx Hwsz Hp Hp' Hxv Hxv'.
      destruct (wsz_node_sz ctx cost_limit act x W Hwsz) as [_ Hxsz].
      rewrite <- Hxsz.
      exact (Hargder x Hx ss ss' input' p Hpub Hsa Hsa' Hp Hp' Hxv Hxv'). }

    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | iv | [sv | ov] | uop arg | bop a1 a2 | src | cnd tid eid | slat sa | dp darg den | sp stok sen | ja jb | ]
      eqn:Eop.

    - rewrite (nre_const ctx cost_limit act a_idx n c H1 Hlen Eop).
      cbn [tf_eval_expr]. reflexivity.

    - rewrite (nre_input ctx cost_limit act a_idx n iv H1 Hlen Eop).
      cbn [tf_eval_expr]. destruct Hpub as [Hipub _].
      destruct (tfs_spec_inputs_class ctx iv) eqn:Hcls.
      + f_equal. exact (Hipub iv Hcls).
      + (* a secret input is a taint source, exactly like a secret state read,
           so an untainted node cannot be one *)
        exfalso.
        assert (Ht := input_secret_tainted act _ iv Hin Eop Hcls Hnr').
        rewrite Hnid in Ht. exact (Hnt Ht).

    - (* a secret read is always tainted, so this case cannot arise *)
      exfalso.
      assert (Ht := svar_tainted act _ sv Hin Eop Hnr').
      rewrite Hnid in Ht. exact (Hnt Ht).

    - rewrite (nre_ovar ctx cost_limit act a_idx n ov H1 Hlen Eop).
      (* [nval] reads outputs at [tfs_outputs_size sched], [pub_eq] at the
         convertible [tfs_spec_outputs_size ctx], so [apply] not [rewrite]. *)
      cbn [tf_eval_expr]. destruct Hpub as [_ [Hout _]].
      destruct (tfs_spec_outputs_class ctx ov) eqn:Hcls.
      + f_equal. apply Hout. exact Hcls.
      + (* reading an output the attacker cannot see is itself a taint source,
           so an untainted node cannot be one -- the read-side twin of the
           [DFG_SVar] case above *)
        exfalso.
        assert (Ht := ovar_secret_tainted act _ ov Hin Eop Hcls Hnr').
        rewrite Hnid in Ht. exact (Hnt Ht).

    - assert (Ha : List.In arg (get_args ctx (nth n (graph (build_dfg ctx act))
                                                {| nid := 0; op := DFG_Empty; sz := 0 |})))
        by (unfold get_args; rewrite Eop; left; reflexivity).
      destruct (node_args_range ctx cost_limit act n H1 Hlen arg Ha) as [Har1 _].
      unfold node_args_sz in Hfg. rewrite Eop in Hfg.
      pose proof (nrv_peel_unary ctx cost_limit act a_idx n uop arg pi
                    ss input Eop Har1 Hlen Hvn) as Huv.
      pose proof (nrv_peel_unary ctx cost_limit act a_idx n uop arg pi
                    ss' input' Eop Har1 Hlen Hvn') as Huv'.
      rewrite (nre_unary ctx cost_limit act a_idx n uop arg H1 Hlen Eop).
      (* destruct first: [tf_resize] binds its own width in the match pattern *)
      cbn [tf_eval_expr]. destruct uop;
        rewrite (Hder_at arg _ pi Ha Hfg Hpin Hpin' Huv Huv'); reflexivity.

    - assert (Ha1 : List.In a1 (get_args ctx (nth n (graph (build_dfg ctx act))
                                                {| nid := 0; op := DFG_Empty; sz := 0 |})))
        by (unfold get_args; rewrite Eop; left; reflexivity).
      assert (Ha2 : List.In a2 (get_args ctx (nth n (graph (build_dfg ctx act))
                                                {| nid := 0; op := DFG_Empty; sz := 0 |})))
        by (unfold get_args; rewrite Eop; right; left; reflexivity).
      destruct (node_args_range ctx cost_limit act n H1 Hlen a1 Ha1) as [Hb11 _].
      destruct (node_args_range ctx cost_limit act n H1 Hlen a2 Ha2) as [Hb21 _].
      destruct (nrv_peel_binary ctx cost_limit act a_idx n bop a1 a2 pi
                  ss input Eop Hb11 Hb21 Hlen Hvn) as [Hv1 Hv2].
      destruct (nrv_peel_binary ctx cost_limit act a_idx n bop a1 a2 pi
                  ss' input' Eop Hb11 Hb21 Hlen Hvn') as [Hv1' Hv2'].
      unfold node_args_sz in Hfg. rewrite Eop in Hfg.
      rewrite (nre_binary ctx cost_limit act a_idx n bop a1 a2 H1 Hlen Eop).
      destruct bop; destruct Hfg as [Hg1 Hg2]; cbn [tf_eval_expr];
        rewrite (Hder_at a1 _ pi Ha1 Hg1 Hpin Hpin' Hv1 Hv1'),
                (Hder_at a2 _ pi Ha2 Hg2 Hpin Hpin' Hv2 Hv2'); reflexivity.

    - assert (Ha : List.In src (get_args ctx (nth n (graph (build_dfg ctx act))
                                                {| nid := 0; op := DFG_Empty; sz := 0 |})))
        by (unfold get_args; rewrite Eop; left; reflexivity).
      destruct (node_args_range ctx cost_limit act n H1 Hlen src Ha) as [Hsr1 _].
      (* [DFG_Resize] resizes from the argument's declared width by construction,
         which is why [node_args_sz] records no constraint for it. *)
      pose proof (Hargder src Ha ss ss' input' pi Hpub Hsa Hsa' Hpin Hpin'
                    (nrv_peel_resize ctx cost_limit act a_idx n src pi
                       ss input Eop Hsr1 Hlen Hvn)
                    (nrv_peel_resize ctx cost_limit act a_idx n src pi
                       ss' input' Eop Hsr1 Hlen Hvn')) as E.
      unfold nval in E.
      rewrite (nre_resize ctx cost_limit act a_idx n src H1 Hlen Eop).
      cbn [tf_eval_expr]. rewrite E. reflexivity.
    - assert (Hc : List.In cnd (get_args ctx (nth n (graph (build_dfg ctx act))
                                                {| nid := 0; op := DFG_Empty; sz := 0 |})))
        by (unfold get_args; rewrite Eop; left; reflexivity).
      assert (Ht : List.In tid (get_args ctx (nth n (graph (build_dfg ctx act))
                                                {| nid := 0; op := DFG_Empty; sz := 0 |})))
        by (unfold get_args; rewrite Eop; right; left; reflexivity).
      assert (He : List.In eid (get_args ctx (nth n (graph (build_dfg ctx act))
                                                {| nid := 0; op := DFG_Empty; sz := 0 |})))
        by (unfold get_args; rewrite Eop; right; right; left; reflexivity).
      destruct (node_args_range ctx cost_limit act n H1 Hlen cnd Hc) as [Hc1 _].
      destruct (node_args_range ctx cost_limit act n H1 Hlen tid Ht) as [Ht1 _].
      destruct (node_args_range ctx cost_limit act n H1 Hlen eid He) as [He1 _].
      (* An untainted node has an untainted condition, so the phi is NOT
         critical and its validity gates the branch the value selects. *)
      assert (Hnc : phi_crit (get_tainted ctx (build_dfg ctx act))
                      (decl_facts ctx (build_dfg ctx act)) cnd pi = false).
      { unfold phi_crit.
        destruct (mem_nid cnd (get_tainted ctx (build_dfg ctx act))) eqn:Em;
          [ exfalso | reflexivity ].
        assert (Htt := taint_propagates act _ cnd Hin Hc
                         (mem_nid_In cnd _ Em) Hnr').
        rewrite Hnid in Htt. exact (Hnt Htt). }
      destruct (nrv_peel_phi_sel ctx cost_limit act a_idx n cnd tid eid pi
                  ss input Eop Hnc Hc1 Ht1 He1 Hlen Hvn) as [Hcv [Htv Hev]].
      destruct (nrv_peel_phi_sel ctx cost_limit act a_idx n cnd tid eid pi
                  ss' input' Eop Hnc Hc1 Ht1 He1 Hlen Hvn') as [Hcv' [Htv' Hev']].
      unfold node_args_sz in Hfg. rewrite Eop in Hfg.
      destruct Hfg as [Hgc [Hgt Hge]].
      assert (Hcc : eval1 (node_ref_expr ctx cost_limit act a_idx cnd) ss input
                    = eval1 (node_ref_expr ctx cost_limit act a_idx cnd) ss' input')
        by exact (Hder_at cnd _ pi Hc Hgc Hpin Hpin' Hcv Hcv').
      rewrite (nre_phi ctx cost_limit act a_idx n cnd tid eid H1 Hlen Eop).
      cbn [tf_eval_expr]. rewrite Hcc.
      destruct (beq_dec (eval1 (node_ref_expr ctx cost_limit act a_idx cnd)
                           ss' input') Bits.zero) eqn:Hb.
      + (* the else arm is selected in both runs *)
        assert (Hz : eval1 (node_ref_expr ctx cost_limit act a_idx cnd) ss' input'
                     = Bits.zero) by (apply beq_dec_iff in Hb; exact Hb).
        rewrite (Hder_at eid _ ((cnd, false) :: pi) He Hge
                   (pi_holds_cons act a_idx input cnd false pi ss Hpin
                      ltac:(unfold Definitions.nval, bit_of;
                            rewrite Hcc; exact Hz))
                   (pi_holds_cons act a_idx input' cnd false pi ss' Hpin'
                      ltac:(unfold Definitions.nval, bit_of; exact Hz))
                   (Hev ltac:(rewrite Hcc; exact Hz)) (Hev' Hz)).
        reflexivity.
      + (* the then arm is selected in both runs *)
        assert (Hz : eval1 (node_ref_expr ctx cost_limit act a_idx cnd) ss' input'
                     <> Bits.zero).
        { intro Hc0. rewrite Hc0, beq_dec_refl in Hb. discriminate. }
        rewrite (Hder_at tid _ ((cnd, true) :: pi) Ht Hgt
                   (pi_holds_cons act a_idx input cnd true pi ss Hpin
                      ltac:(unfold Definitions.nval, bit_of;
                            apply (proj1 (bits1_nonzero_ones _));
                            rewrite Hcc; exact Hz))
                   (pi_holds_cons act a_idx input' cnd true pi ss' Hpin'
                      ltac:(unfold Definitions.nval, bit_of;
                            apply (proj1 (bits1_nonzero_ones _)); exact Hz))
                   (Htv ltac:(rewrite Hcc; exact Hz)) (Htv' Hz)).
        reflexivity.

    - (* A stall is the round trip's COUNTER: it carries no value, so its
         reference expression is a constant. *)
      rewrite (nre_stall ctx cost_limit act a_idx n slat sa H1 Hlen Eop).
      cbn [tf_eval_expr]. reflexivity.
    - (* A drive is the message on its way to the port: its reference
         expression is its argument's. *)
      assert (Ha : List.In darg (get_args ctx (nth n (graph (build_dfg ctx act))
                                               {| nid := 0; op := DFG_Empty; sz := 0 |})))
        by (unfold get_args; rewrite Eop; left; reflexivity).
      destruct (node_args_range ctx cost_limit act n H1 Hlen darg Ha) as [Hdr1 _].
      unfold node_args_sz in Hfg. rewrite Eop in Hfg.
      rewrite (nre_drive ctx cost_limit act a_idx n dp darg den H1 Hlen Eop).
      exact (Hder_at darg _ pi Ha Hfg Hpin Hpin'
               (nrv_peel_drive ctx cost_limit act a_idx n dp darg den pi
                  ss input Eop Hdr1 Hlen Hvn)
               (nrv_peel_drive ctx cost_limit act a_idx n dp darg den pi
                  ss' input' Eop Hdr1 Hlen Hvn')).

    - (* A sample is [ip_fn] of its request.  Untainted means the REQUEST is
         untainted, so both runs send the same payload and the pure IP hands
         back the same answer. *)
      assert (Hsam : is_sample_of ctx cost_limit act n = true)
        by (unfold Definitions.is_sample_of,
                   Definitions.node_op; rewrite Eop; reflexivity).
      destruct (sample_index ctx cost_limit act a_idx n Halign Hsam) as [n_idx Hvid].
      assert (Hop' : node_op ctx cost_limit act n = DFG_Sample sp stok sen)
        by (unfold Definitions.node_op; exact Eop).
      destruct (sample_has_drive ctx cost_limit act n sp stok sen Hop')
        as [d [av [Hsd Hdop]]].

      (* the latch is up in both runs: a sample's compiled validity IS its
         register, the same expression at every path *)
      assert (Hrr : forall (s: sched_sys_state) (i: sched_input_t),
                rvalid act a_idx pi n s i = Bits.ones 1 ->
                (fst s).[tf_dfg_v a_idx n_idx] = Bits.ones 1).
      { intros s i Hv. rewrite <- Hvid in Hv.
        rewrite (sample_ref_is_register ctx cost_limit act a_idx n_idx Halign
                   ltac:(rewrite Hvid; exact Hsam) pi
                   (length (graph (build_dfg ctx act)))
                   ltac:(rewrite Hvid; exact Hlen)) in Hv.
        cbn [snd] in Hv. rewrite eval1_svar_v in Hv. exact Hv. }
      pose proof (Hrr ss  input  Hvn)  as Hreg.
      pose proof (Hrr ss' input' Hvn') as Hreg'.

      (* the request is untainted and sits below [n], so [IH] reaches it *)
      pose proof (sample_drive_lt act n d Hlen Hsd) as Hdn.
      pose proof (sample_drive_untainted act n d Hpl Hlen Hsd Hnt Hnroot) as Hdt.
      assert (Hdlen : d < length (graph (build_dfg ctx act))) by lia.
      destruct (node_op_pos ctx cost_limit act d
                  ltac:(rewrite Hdop; discriminate)) as [Hd1 _].
      assert (Hain : List.In av (get_args ctx (nth d (graph (build_dfg ctx act))
                                                {| nid := 0; op := DFG_Empty; sz := 0 |})))
        by (unfold get_args, Definitions.node_op in Hdop |- *;
            rewrite Hdop; left; reflexivity).
      assert (Hdnr : ~ List.In d (untainted_roots ctx (build_dfg ctx act)))
        by (apply Hpl; unfold is_plumbing; rewrite Hdop; reflexivity).
      pose proof (arg_untainted act d av Hdlen Hdt Hdnr Hain) as Havt.
      destruct (node_args_range ctx cost_limit act d Hd1 Hdlen av Hain) as [Hav1 Havd].

      (* the payload's width is the IP's request width *)
      pose proof (wfg_build_dfg ctx cost_limit act
                    (nth d (graph (build_dfg ctx act))
                       {| nid := 0; op := DFG_Empty; sz := 0 |})
                    (nth_In _ _ Hdlen)) as Hfgd.
      unfold node_args_sz in Hfgd.
      unfold Definitions.node_op in Hdop.
      rewrite Hdop in Hfgd.
      destruct (wsz_node_sz ctx cost_limit act av _ Hfgd) as [_ Havsz].

      destruct Hsa  as [Hans  [Hzer  [Hargs  Hgrd ]]].
      destruct Hsa' as [Hans' [Hzer' [Hargs' Hgrd']]].
      pose proof (conj Hans  (conj Hzer  (conj Hargs  Hgrd )))  as Hsa.
      pose proof (conj Hans' (conj Hzer' (conj Hargs' Hgrd'))) as Hsa'.
      rewrite <- Hvid in Hop', Hsd.
      assert (Hdz : sz (nth d (graph (build_dfg ctx act))
                         {| nid := 0; op := DFG_Empty; sz := 0 |})
                    = ip_req_sz (tfs_spec_ip ctx sp))
        by (apply (Hdsz d sp av sen); exact Hdop).

      (* THE GUARD.  Its literals are arguments of the drive, so they are
         untainted and sit below the sample; each is one bit, and each is
         valid where the latch is up.  So the two runs read the same guard,
         and the split below is the same split in both. *)
      assert (Hlit : forall l, List.In l sen ->
                nval ctx cost_limit act a_idx ss  input  1 (fst l)
                = nval ctx cost_limit act a_idx ss' input' 1 (fst l)).
      { intros l Hl.
        assert (Hlin : List.In (fst l)
                  (get_args ctx (nth d (graph (build_dfg ctx act))
                     {| nid := 0; op := DFG_Empty; sz := 0 |})))
          by (unfold get_args; rewrite Hdop; right; exact (in_map fst sen l Hl)).
        pose proof (arg_untainted act d (fst l) Hdlen Hdt Hdnr Hlin) as Hlt.
        destruct (node_args_range ctx cost_limit act d Hd1 Hdlen (fst l) Hlin)
          as [Hl1 Hld].
        pose proof (IH (fst l) ltac:(lia) Hl1 ltac:(lia) Hlt ss ss' input' []
                      Hpub Hsa Hsa' (pi_holds_nil act a_idx input ss)
                      (pi_holds_nil act a_idx input' ss')
                      (Hgrd  n_idx sp stok sen Hop' Hreg  l Hl)
                      (Hgrd' n_idx sp stok sen Hop' Hreg' l Hl)) as Hl_eq.
        unfold Definitions.nval in Hl_eq |- *.
        rewrite (Hgsz d sp av sen Hdop l Hl) in Hl_eq. exact Hl_eq. }
      assert (Hiff : pi_holds act a_idx input  sen ss
                     <-> pi_holds act a_idx input' sen ss').
      { split; intros H c b Hin0;
          pose proof (Hlit (c, b) Hin0) as He; cbn [fst] in He.
        - rewrite <- He. exact (H c b Hin0).
        - rewrite He. exact (H c b Hin0). }

      unfold Definitions.nval. rewrite <- Hvid.
      rewrite (nre_sample ctx cost_limit act a_idx n_idx Halign
                 ltac:(rewrite Hvid; exact Hsam)).
      rewrite <- (buffer_register_node_size ctx cost_limit act a_idx n_idx Halign).
      rewrite !eval_svar_same.
      destruct (pi_holdsb act a_idx input sen ss) eqn:Hdec.
      + (* the guard held in both runs: the round trip, and the payloads agree *)
        assert (Hg  : pi_holds act a_idx input  sen ss)
          by (apply pi_holdsb_spec; exact Hdec).
        assert (Hg' : pi_holds act a_idx input' sen ss') by (apply Hiff; exact Hg).
        pose proof (Hans  n_idx sp stok sen d av sen Hop' Hsd Hdop Hdz Hreg  Hg)  as Hb.
        pose proof (Hans' n_idx sp stok sen d av sen Hop' Hsd Hdop Hdz Hreg' Hg') as Hb'.
        pose proof (Hargs  n_idx sp stok sen d av sen Hop' Hsd Hdop Hreg)  as Hvav.
        pose proof (Hargs' n_idx sp stok sen d av sen Hop' Hsd Hdop Hreg') as Hvav'.
        pose proof (IH av ltac:(lia) Hav1 ltac:(lia) Havt ss ss' input' []
                      Hpub Hsa Hsa' (pi_holds_nil act a_idx input ss)
                      (pi_holds_nil act a_idx input' ss') Hvav Hvav') as Hav.
        unfold Definitions.nval in Hav.
        rewrite Havsz, Hdz in Hav.
        rewrite Hb, Hb'. rewrite Hav. reflexivity.
      + (* it held in neither: both arms were skipped, so both buffers are 0 *)
        assert (Hng  : ~ pi_holds act a_idx input  sen ss).
        { intro Hc. pose proof (proj2 (pi_holdsb_spec _ _ _ _ _) Hc) as Ht.
          rewrite Hdec in Ht. discriminate Ht. }
        assert (Hng' : ~ pi_holds act a_idx input' sen ss')
          by (intro Hc; exact (Hng (proj2 Hiff Hc))).
        rewrite (Hzer  n_idx sp stok sen Hop' Hreg  Hng).
        rewrite (Hzer' n_idx sp stok sen Hop' Hreg' Hng').
        reflexivity.

    - (* A join ORDERS the calls on a port and carries no value. *)
      assert (Hemp : node_ref_expr ctx cost_limit act a_idx n = tf_const 0).
      { rewrite (nre_unfold ctx cost_limit act a_idx n H1 Hlen).
        cbn [compile_dfg_expr_aux].
        rewrite (not_sample_not_in_sample_bufs ctx cost_limit act a_idx n
                   ltac:(unfold is_sample_of, node_op; rewrite Eop; reflexivity)).
        cbv beta iota. rewrite Eop.
        destruct (compile_dfg_expr ctx (buffer_needs ctx cost_limit) n a_idx
                    (build_dfg ctx act) ja (sample_bufs ctx cost_limit act a_idx)).
        destruct (compile_dfg_expr ctx (buffer_needs ctx cost_limit) n a_idx
                    (build_dfg ctx act) jb (sample_bufs ctx cost_limit act a_idx)).
        reflexivity. }
      rewrite Hemp. cbn [tf_eval_expr]. reflexivity.

    - assert (Hemp : node_ref_expr ctx cost_limit act a_idx n = tf_const 0).
      { rewrite (nre_unfold ctx cost_limit act a_idx n H1 Hlen).
        cbn [compile_dfg_expr_aux].
        rewrite (not_sample_not_in_sample_bufs ctx cost_limit act a_idx n
                   ltac:(unfold is_sample_of, node_op; rewrite Eop; reflexivity)).
        cbv beta iota. rewrite Eop. reflexivity. }
      rewrite Hemp. cbn [tf_eval_expr]. reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* GUARDED DERIVABILITY.  A whitebox rule usually only declassifies a    *)
  (* condition on some paths (the lock is open only when the guess was      *)
  (* right), so the compiler decides criticality per phi OCCURRENCE from    *)
  (* the path of selector literals it is under.  [lit] / [guard_incl] are  *)
  (* the scheduler's (coq/Scheduler/Schedule.v); only their       *)
  (* semantics live here.                                                  *)
  (* ------------------------------------------------------------------- *)

  Lemma guard_incl_holds (act: tfs_action sched) (a_idx: a_index) (input: sched_input_t)
      (g pi: list lit) (ss: sched_sys_state) :
    guard_incl g pi = true -> pi_holds act a_idx input pi ss ->
    pi_holds act a_idx input g ss.
  Proof.
    unfold guard_incl, pi_holds. intros Hincl Hpi c b Hin.
    rewrite forallb_forall in Hincl.
    specialize (Hincl _ Hin). rewrite existsb_exists in Hincl.
    destruct Hincl as [[c' b'] [Hin' Heq]].
    unfold lit_eqb in Heq. cbn [fst snd] in Heq.
    apply andb_prop in Heq. destruct Heq as [Hc Hb].
    apply Nat.eqb_eq in Hc. apply Bool.eqb_prop in Hb. subst c' b'.
    exact (Hpi _ _ Hin').
  Qed.

  Lemma pi_holds_app (act: tfs_action sched) (a_idx: a_index) (input: sched_input_t)
      (g1 g2: list lit) (ss: sched_sys_state) :
    pi_holds act a_idx input (g1 ++ g2) ss ->
    pi_holds act a_idx input g1 ss /\ pi_holds act a_idx input g2 ss.
  Proof.
    intro H. split; intros c b Hin; apply H; apply in_or_app;
      [ left | right ]; exact Hin.
  Qed.

  (* A fact learned under fewer conditions still holds under more. *)
  Lemma gderivable_weaken (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (g g': list lit) (n: nid_t) :
    guard_incl g g' = true ->
    gderivable act a_idx input g n ->
    gderivable act a_idx input g' n.
  Proof.
    intros Hincl Hg ss ss' input' pi Hpub Hs Hs' Hp Hp' Hv Hv'.
    exact (Hg ss ss' input' pi Hpub Hs Hs'
             (guard_incl_holds act a_idx input  g g' ss  Hincl Hp)
             (guard_incl_holds act a_idx input' g g' ss' Hincl Hp')
             Hv Hv').
  Qed.

  Lemma derivable_gderivable (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (g: list lit) (n: nid_t) :
    derivable act a_idx input n -> gderivable act a_idx input g n.
  Proof.
    intros Hd ss ss' input' pi Hpub Hs Hs' _ _ Hv Hv'.
    exact (Hd ss ss' input' pi Hpub Hs Hs' Hv Hv').
  Qed.

  (* An unconditionally derivable node is derivable under any guard. *)
  Lemma untainted_gderivable (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (g: list lit) (n: nid_t) :
    act_idx_aligned ctx cost_limit act a_idx ->
    plumbing_not_root act ->
    drives_sized act ->
    guards_sized act ->
    1 <= n ->
    n < length (graph (build_dfg ctx act)) ->
    ~ List.In n (get_tainted ctx (build_dfg ctx act)) ->
    gderivable act a_idx input g n.
  Proof.
    intros Halign Hpl Hdsz Hgsz Hn1 Hnlen Hnt.
    exact (derivable_gderivable act a_idx input g n
             (untainted_derivable act a_idx input Halign Hpl Hdsz Hgsz n Hn1 Hnlen Hnt)).
  Qed.

  (* CHAINING.  A rule whose sources are themselves only known under [g]
     yields its target under both guards. *)
  Theorem decl_compose (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (i: decl_instance) (g: list lit) :
    instance_sound act a_idx input i ->
    (forall s, List.In s (di_sources i) -> gderivable act a_idx input g s) ->
    gderivable act a_idx input (di_guard i ++ g) (di_target i).
  Proof.
    intros Hi Hsrc ss ss' input' pi Hpub Hs Hs' Hp Hp' Hpi Hpi' Hv Hv'.
    destruct (pi_holds_app act a_idx input  _ _ ss  Hp)  as [Hp1  Hp2 ].
    destruct (pi_holds_app act a_idx input' _ _ ss' Hp') as [Hp1' Hp2'].
    exact (Hi ss ss' input' pi Hpub Hp1 Hp1'
             (fun s ps Hs0 Hps Hps' Hvs Hvs' =>
                Hsrc s Hs0 ss ss' input' ps Hpub Hs Hs' Hp2 Hp2' Hps Hps' Hvs Hvs')
             Hpi Hpi' Hv Hv').
  Qed.

  Lemma guard_incl_refl (g: list lit) : guard_incl g g = true.
  Proof.
    unfold guard_incl. apply forallb_forall. intros a Ha.
    apply existsb_exists. exists a. split; [ exact Ha | ].
    unfold lit_eqb. rewrite Nat.eqb_refl, Bool.eqb_reflx. reflexivity.
  Qed.

  Corollary decl_direct (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (i: decl_instance) :
    act_idx_aligned ctx cost_limit act a_idx ->
    plumbing_not_root act ->
    drives_sized act ->
    guards_sized act ->
    instance_sound act a_idx input i ->
    (forall s, List.In s (di_sources i) ->
       1 <= s /\ s < length (graph (build_dfg ctx act))
       /\ ~ List.In s (get_tainted ctx (build_dfg ctx act))) ->
    gderivable act a_idx input (di_guard i) (di_target i).
  Proof.
    intros Halign Hpl Hdsz Hgsz Hi Hsrc.
    apply (gderivable_weaken act a_idx input (di_guard i ++ []) (di_guard i));
      [ rewrite app_nil_r; apply guard_incl_refl | ].
    apply (decl_compose act a_idx input i []); [ exact Hi | ].
    intros s Hs. destruct (Hsrc s Hs) as [Hs1 [Hs2 Hs3]].
    exact (untainted_gderivable act a_idx input [] s Halign Hpl Hdsz Hgsz Hs1 Hs2 Hs3).
  Qed.

  (* Bridge to the unconditional obligation, so the rules in coq/Rules/ can
     discharge [Hdecls] from the same [instance_sound] proof. *)
  Lemma uncond_guard_nil (dfg: @dfg_state_t s_var i_var o_var p_var) (i: decl_instance) :
    List.In i (uncond_instances ctx dfg) -> di_guard i = [].
  Proof.
    unfold uncond_instances. intro Hin.
    apply filter_In in Hin. destruct Hin as [_ Hg].
    destruct (di_guard i); [ reflexivity | discriminate ].
  Qed.

  Theorem uncond_sound_of_instances (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) :
    (forall i, List.In i (uncond_instances ctx (build_dfg ctx act)) ->
       instance_sound act a_idx input i) ->
    uncond_sound act a_idx input.
  Proof.
    intros Hall i Hi Hsrc ss ss' input' pi Hpub Hs Hs' Hv Hv'.
    pose proof (uncond_guard_nil (build_dfg ctx act) i Hi) as Hg.
    apply (Hall i Hi ss ss' input' pi Hpub);
      [ rewrite Hg; intros c b Hin; destruct Hin
      | rewrite Hg; intros c b Hin; destruct Hin
      | intros s ps Hs0 Hvs Hvs';
        exact (Hsrc s Hs0 ss ss' input' ps Hpub Hs Hs' Hvs Hvs')
      | exact Hv | exact Hv' ].
  Qed.

  (* And to the guarded one, which is what the compiler's producer emits.
     [decl_facts] is a saturated base, so soundness is an induction over the
     saturation: every entry is [gderivable] under the guard recorded with it. *)
  Lemma guard_incl_app_l (g pi pi': list lit) :
    guard_incl g pi = true -> guard_incl g (pi ++ pi') = true.
  Proof.
    unfold guard_incl. rewrite !forallb_forall. intros H a Ha.
    rewrite existsb_app, (H a Ha). reflexivity.
  Qed.

  Lemma guard_incl_app_r (g pi pi': list lit) :
    guard_incl g pi' = true -> guard_incl g (pi ++ pi') = true.
  Proof.
    unfold guard_incl. rewrite !forallb_forall. intros H a Ha.
    rewrite existsb_app, (H a Ha), Bool.orb_true_r. reflexivity.
  Qed.

  Lemma gfacts_of_In (base: list gfact) (c: nid_t) (g: list lit) :
    List.In g (gfacts_of base c) -> List.In (c, g) base.
  Proof.
    unfold gfacts_of. intro H. apply in_map_iff in H.
    destruct H as [[n g'] [Hsnd Hfil]]. cbn in Hsnd. subst g'.
    apply filter_In in Hfil. destruct Hfil as [Hin Heq].
    cbn in Heq. apply Nat.eqb_eq in Heq. subst n. exact Hin.
  Qed.

  (* One combined guard per way of picking a fact for each source; each source
     is derivable under its own guard, hence under the (stronger) combination. *)
  Lemma gcombine_sound (base: list gfact) (ss: list nid_t) (gs: list lit) :
    List.In gs (gcombine base ss) ->
    forall s, List.In s ss ->
      exists g, List.In (s, g) base /\ guard_incl g gs = true.
  Proof.
    revert gs. induction ss as [| s0 ss IH]; intros gs Hgs x Hx; [ destruct Hx | ].
    cbn [gcombine] in Hgs. apply in_flat_map in Hgs.
    destruct Hgs as [g0 [Hg0 Hmap]]. apply in_map_iff in Hmap.
    destruct Hmap as [gr [Heq Hgr]]. subst gs.
    destruct Hx as [Hxeq | Hx].
    - subst x. exists g0. split; [ apply gfacts_of_In; exact Hg0 | ].
      apply guard_incl_app_l, guard_incl_refl.
    - destruct (IH gr Hgr x Hx) as [g [Hg Hincl]].
      exists g. split; [ exact Hg | apply guard_incl_app_r, Hincl ].
  Qed.

  Lemma gadd_of_sound (act: tfs_action sched) (a_idx: a_index) (input: sched_input_t)
      (i: decl_instance) (acc: list gfact) (gs: list lit) :
    gderivable act a_idx input (di_guard i ++ gs) (di_target i) ->
    base_sound act a_idx input acc ->
    base_sound act a_idx input (gadd_of i acc gs).
  Proof.
    intros Hg Hacc. unfold gadd_of.
    destruct (gsubsumed acc (di_target i) (di_guard i ++ gs)); [ exact Hacc | ].
    intros c g Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    - exact (Hacc c g Hin).
    - destruct Hin as [Heq | []]. injection Heq as Ht Hgg. subst c g. exact Hg.
  Qed.

  Lemma gfold_sound (act: tfs_action sched) (a_idx: a_index) (input: sched_input_t)
      (i: decl_instance) :
    forall combos acc,
      (forall gs, List.In gs combos ->
         gderivable act a_idx input (di_guard i ++ gs) (di_target i)) ->
      base_sound act a_idx input acc ->
      base_sound act a_idx input (fold_left (gadd_of i) combos acc).
  Proof.
    induction combos as [| gs combos IH]; intros acc Hnew Hacc; cbn [fold_left];
      [ exact Hacc | ].
    apply IH; [ intros x Hx; apply Hnew; right; exact Hx | ].
    exact (gadd_of_sound act a_idx input i acc gs
             (Hnew gs (or_introl eq_refl)) Hacc).
  Qed.

  Lemma gstep1_sound (act: tfs_action sched) (a_idx: a_index) (input: sched_input_t)
      (i: decl_instance) (acc: list gfact) :
    instance_sound act a_idx input i ->
    base_sound act a_idx input acc ->
    base_sound act a_idx input (gstep1 acc i).
  Proof.
    intros Hi Hacc. unfold gstep1.
    apply gfold_sound; [ | exact Hacc ].
    intros gs Hgs. apply (decl_compose act a_idx input i gs); [ exact Hi | ].
    intros s Hsrc.
    destruct (gcombine_sound acc (di_sources i) gs Hgs s Hsrc) as [g [Hg Hincl]].
    exact (gderivable_weaken act a_idx input g gs s Hincl (Hacc s g Hg)).
  Qed.

  Lemma gfold_instances_sound (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) :
    forall l base,
      (forall i, List.In i l -> instance_sound act a_idx input i) ->
      base_sound act a_idx input base ->
      base_sound act a_idx input (fold_left gstep1 l base).
  Proof.
    induction l as [| i l IH]; intros base Hl Hbase; cbn [fold_left];
      [ exact Hbase | ].
    apply IH; [ intros j Hj; apply Hl; right; exact Hj | ].
    exact (gstep1_sound act a_idx input i base (Hl i (or_introl eq_refl)) Hbase).
  Qed.

  Lemma gsaturate_step_sound (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) :
    (forall i, List.In i (decl_instances ctx (build_dfg ctx act)) ->
       instance_sound act a_idx input i) ->
    forall base, base_sound act a_idx input base ->
      base_sound act a_idx input
        (gsaturate_step ctx (build_dfg ctx act) base).
  Proof.
    intros Hall base Hbase.
    exact (gfold_instances_sound act a_idx input _ base Hall Hbase).
  Qed.

  Lemma gsaturate_sound (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) :
    (forall i, List.In i (decl_instances ctx (build_dfg ctx act)) ->
       instance_sound act a_idx input i) ->
    forall fuel base, base_sound act a_idx input base ->
      base_sound act a_idx input (gsaturate ctx fuel (build_dfg ctx act) base).
  Proof.
    intros Hall fuel. induction fuel as [| fuel IH]; intros base Hbase;
      cbn [gsaturate]; [ exact Hbase | ].
    destruct (Nat.eqb (length (gsaturate_step ctx (build_dfg ctx act) base))
                      (length base));
      [ exact Hbase | ].
    exact (IH _ (gsaturate_step_sound act a_idx input Hall base Hbase)).
  Qed.

  Lemma seed_sound (act: tfs_action sched) (a_idx: a_index) (input: sched_input_t) :
    base_sound act a_idx input
      (map (fun n => (n, [])) (untainted_roots ctx (build_dfg ctx act))).
  Proof.
    intros c g Hin. apply in_map_iff in Hin.
    destruct Hin as [n [Heq Hn]]. injection Heq as Hc Hg. subst c g.
    exact (derivable_gderivable act a_idx input [] n
             (untainted_roots_derivable act a_idx input n Hn)).
  Qed.

  Theorem decl_sound_of_instances (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) :
    (forall i, List.In i (decl_instances ctx (build_dfg ctx act)) ->
       instance_sound act a_idx input i) ->
    decl_sound act a_idx input.
  Proof.
    intros Hall c g Hg.
    exact (gsaturate_sound act a_idx input Hall _ _
             (seed_sound act a_idx input) c g Hg).
  Qed.

  Context (Hdguard : forall act a_idx input, decl_sound act a_idx input).

  (* ------------------------------------------------------------------- *)
  (* PHASE 2, step 1: what a pre-done cycle leaves alone.  Output registers
     hold, and a VALID node keeps its reference value. *)
  (* ------------------------------------------------------------------- *)

  Local Notation ss_step := (sched_step ctx cost_limit).
  Local Notation ss_run  := (run_n ctx cost_limit).
  Local Notation ss_done := (done_set ctx cost_limit).

  (* A node's reference value ignores the response coordinates: the sample
     buffers stop the expansion at a latch, so no compiled value reads a port.
     [r1] is therefore free of [r0] here. *)
  Lemma nval_step_stable (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: input_t) (r0 r1: resp_val)
      (szB: nat) (n: nid_t) :
    act_idx_aligned ctx cost_limit act a_idx ->
    ~ ss_done (ss_step act ss (sched_input ctx cost_limit input r0)) ->
    n < length (graph (build_dfg ctx act)) ->
    eval1 (node_ref_valid ctx cost_limit act a_idx n)
      ss (sched_input ctx cost_limit input r0) = Bits.ones 1 ->
    nval ctx cost_limit act a_idx
      (ss_step act ss (sched_input ctx cost_limit input r0))
      (sched_input ctx cost_limit input r1) szB n
    = nval ctx cost_limit act a_idx ss
      (sched_input ctx cost_limit input r0) szB n.
  Proof.
    intros Halign Hnd Hnlen Hval. unfold nval, node_ref_expr.
    exact (compile_nobuf_step_stable ctx cost_limit act a_idx ss input r0 r1
             Halign Hnd (length (graph (build_dfg ctx act))) n szB Hnlen Hval).
  Qed.

  Lemma out_run_stable (act: tfs_action sched) (ss: sched_sys_state)
      (input: input_t) (resp: nat -> resp_val) (o: o_var) (k: nat) :
    (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input resp ss)) ->
    (snd (ss_run k act input resp ss)).[o] = (snd ss).[o].
  Proof.
    induction k as [| k IH]; intro Hnd; [ reflexivity | ].
    cbn [run_n]. rewrite sched_step_preserves_ovar.
    - apply IH. intros i Hi. apply Hnd. lia.
    - change (ss_step act (ss_run k act input resp ss)
                (sched_input ctx cost_limit input (resp k)))
        with (ss_run (S k) act input resp ss).
      apply Hnd. lia.
  Qed.

  (* Every pre-done cycle owes the round trip, and pays.  The four parts come
     from four scheduler lemmas; [pi_holds] and the scheduler's [en_holds]
     are the same condition read at one bit. *)
  Lemma settled_run (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (resp: nat -> resp_val) (ss0: sched_sys_state) k :
    act_idx_aligned ctx cost_limit act a_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    (forall x, Definitions.zeroed_at_start ctx cost_limit x ->
       (fst ss0).[x] = Bits.zero) ->
    (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input resp ss0)) ->
    Definitions.ip_contract ctx cost_limit act input resp ss0 ->
    settled act a_idx (ss_run k act input resp ss0)
      (sched_input ctx cost_limit input (resp k)).
  Proof.
    intros Halign Hlen Hz0 Hpre Hipc.
    pose proof (SchedulerRoundTrip.requests_sent_holds ctx cost_limit act a_idx
                  input resp ss0 k Halign Hlen Hz0 Hpre) as Hrs.
    split; [| split; [| split ]].
    - intros n_idx p tok en d av en' Hsamp Hsd Hdop Hdsz Hvk Hpi.
      exact (SchedulerRoundTrip.round_trip ctx cost_limit act a_idx input resp ss0 k
               n_idx p tok en d av en' Halign Hlen Hz0 Hpre Hvk Hipc Hrs
               Hsamp Hsd Hdop Hdsz (pi_holds_guard act a_idx _ en _ Hpi)).
    - intros n_idx p tok en Hsamp Hvk Hnpi.
      exact (SchedulerRoundTrip.sample_buffer_zero_run ctx cost_limit act a_idx
               input resp ss0 k n_idx p tok en Halign Hlen Hz0 Hpre Hsamp Hvk
               (fun Hg => Hnpi (guard_pi_holds act a_idx _ en _ Hg))).
    - intros n_idx p tok en d av en' Hsamp Hsd Hdop Hvk.
      exact (SchedulerRoundTrip.sample_arg_settled ctx cost_limit act a_idx
               input resp ss0 k n_idx p tok en d av en' Halign Hlen Hz0 Hpre
               Hsamp Hsd Hdop Hvk).
    - intros n_idx p tok en Hsamp Hvk l Hin.
      exact (SchedulerRoundTrip.sample_guards_valid_run ctx cost_limit act a_idx
               input resp ss0 k n_idx p tok en Halign Hlen Hz0 Hpre Hsamp Hvk l Hin).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* PHASE 2, step 2: a compiled validity expression is public.            *)
  (*                                                                      *)
  (* The only data-dependent validity is the untainted Phi, which compiles *)
  (* to [cond_val AND (if cond_expr then then_val else else_val)].  Note   *)
  (* that [cond_expr] is the value expression compiled WITH buffers, so    *)
  (* before the condition settles it holds junk that may well differ       *)
  (* between the two states -- taint soundness alone does not discharge    *)
  (* this case.  The [cond_val] conjunct is what saves it: unsettled means *)
  (* [cond_val] is 0 in both states, and settled means [cond_expr] agrees  *)
  (* with the buffer-free reference, which taint soundness does equate.    *)
  (* ------------------------------------------------------------------- *)


  Lemma and1_zero_l (x: bits_t 1) : Bits.and Bits.zero x = Bits.zero.
  Proof. destruct (bits1_cases x) as [Hx | Hx]; subst; reflexivity. Qed.

  Lemma mem_nid_not_In (n: nid_t) (l: list nid_t) :
    mem_nid n l = false -> ~ List.In n l.
  Proof.
    unfold mem_nid. intros H Hin.
    assert (Hex : existsb (Nat.eqb n) l = true)
      by (apply existsb_exists; exists n; split; [ exact Hin | apply Nat.eqb_refl ]).
    rewrite H in Hex. discriminate.
  Qed.

  Lemma valid_public_gen (act: tfs_action sched) (a_idx: a_index)
      (input input': sched_input_t) (ss ss': sched_sys_state) :
    act_idx_aligned ctx cost_limit act a_idx ->
    plumbing_not_root act ->
    drives_sized act ->
    guards_sized act ->
    valid_refs ctx cost_limit act a_idx ss  input  ->
    valid_refs ctx cost_limit act a_idx ss' input' ->
    settled act a_idx ss  input  ->
    settled act a_idx ss' input' ->
    valid_settled ctx cost_limit act a_idx ss  input  ->
    valid_settled ctx cost_limit act a_idx ss' input' ->
    pub_eq act a_idx input input' ss ss' ->
    (forall n_idx, (fst ss).[tf_dfg_v a_idx n_idx]
                 = (fst ss').[tf_dfg_v a_idx n_idx]) ->
    forall bufs,
      (forall e, List.In e bufs ->
         List.In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
      forall fuel n (pi: list lit),
        (* the substitution to the reference needs the sample slots to match,
           at the ids this expression can reach *)
        (forall x, x < n ->
           BitsToLists.list_assoc bufs x = None ->
           BitsToLists.list_assoc (sample_bufs ctx cost_limit act a_idx) x = None) ->
        (forall x m msz, x < n ->
           BitsToLists.list_assoc bufs x = Some (m, msz) ->
           is_sample_of ctx cost_limit act x = true ->
           BitsToLists.list_assoc (sample_bufs ctx cost_limit act a_idx) x
             = Some (m, msz)) ->
        1 <= n ->
        n < length (graph (build_dfg ctx act)) ->
        n < fuel ->
        pi_holds act a_idx input  pi ss ->
        pi_holds act a_idx input' pi ss' ->
        eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                      (build_dfg ctx act) n bufs)) ss input
        = eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                      (build_dfg ctx act) n bufs)) ss' input'.
  Proof.
    intros Halign Hpl Hdsz Hgsz Hrf Hrf' Hst Hst' Hvs Hvs' Hpub Hveq bufs Hsub fuel.
    induction fuel as [| fuel IH];
      intros n pi Hsam_sub Hsam_same Hn1 Hnlen Hnfuel Hpi Hpi'; [ lia | ].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:Hla.
    { cbn [compile_dfg_expr_aux]. rewrite Hla. cbv beta iota.
      destruct (index_of_nat
                  (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))
                  m) as [n_idx' |]; cbn [snd]; [ | reflexivity ].
      destruct (op (nth n (graph (build_dfg ctx act))
                      {| nid := 0; op := DFG_Empty; sz := 0 |}));
        cbn [snd]; rewrite !eval1_svar_v; apply Hveq. }
    cbn [compile_dfg_expr_aux]. rewrite Hla. cbv beta iota.
    set (node := nth n (graph (build_dfg ctx act))
                   {| nid := 0; op := DFG_Empty; sz := 0 |}) in *.
    assert (Hnode_in : List.In node (graph (build_dfg ctx act)))
      by (unfold node; apply nth_In; exact Hnlen).
    assert (Hrange : forall x, List.In x (get_args ctx node) -> 1 <= x /\ x < n)
      by (intros x Hx; exact (node_args_range ctx cost_limit act n Hn1 Hnlen x Hx)).
    pose proof (wfg_build_dfg ctx cost_limit act node Hnode_in) as Hfg.
    destruct (op node) as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa | dp darg den | sp stok sen | ja jb | ]
      eqn:Hop.
    - reflexivity.
    - reflexivity.
    - destruct v; reflexivity.
    - assert (Hain : List.In arg (get_args ctx node))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      destruct (Hrange arg Hain) as [Ha1 Ha2].
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  arg bufs) as [ae ve] eqn:E1.
      pose proof (IH arg pi ltac:(intros y Hy Hy2; exact (Hsam_sub y ltac:(lia) Hy2)) ltac:(intros y my mszy Hy Hy2 Hy3; exact (Hsam_same y my mszy ltac:(lia) Hy2 Hy3)) Ha1 ltac:(lia) ltac:(lia) Hpi Hpi') as Ha.
      rewrite E1 in Ha. cbn [snd] in Ha |- *. exact Ha.
    - assert (Ha1in : List.In a1 (get_args ctx node))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      assert (Ha2in : List.In a2 (get_args ctx node))
        by (unfold get_args; rewrite Hop; right; left; reflexivity).
      destruct (Hrange a1 Ha1in) as [Hb1 Hb2].
      destruct (Hrange a2 Ha2in) as [Hd1 Hd2].
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  a1 bufs) as [a1e v1e] eqn:E1.
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  a2 bufs) as [a2e v2e] eqn:E2.
      pose proof (IH a1 pi ltac:(intros y Hy Hy2; exact (Hsam_sub y ltac:(lia) Hy2)) ltac:(intros y my mszy Hy Hy2 Hy3; exact (Hsam_same y my mszy ltac:(lia) Hy2 Hy3)) Hb1 ltac:(lia) ltac:(lia) Hpi Hpi') as Hx1.
      pose proof (IH a2 pi ltac:(intros y Hy Hy2; exact (Hsam_sub y ltac:(lia) Hy2)) ltac:(intros y my mszy Hy Hy2 Hy3; exact (Hsam_same y my mszy ltac:(lia) Hy2 Hy3)) Hd1 ltac:(lia) ltac:(lia) Hpi Hpi') as Hx2.
      rewrite E1 in Hx1. rewrite E2 in Hx2. cbn [snd] in Hx1, Hx2 |- *.
      rewrite !valid_and_eval. rewrite Hx1, Hx2. reflexivity.
    - assert (Hain : List.In arg (get_args ctx node))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      destruct (Hrange arg Hain) as [Ha1 Ha2].
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  arg bufs) as [ae ve] eqn:E1.
      pose proof (IH arg pi ltac:(intros y Hy Hy2; exact (Hsam_sub y ltac:(lia) Hy2)) ltac:(intros y my mszy Hy Hy2 Hy3; exact (Hsam_same y my mszy ltac:(lia) Hy2 Hy3)) Ha1 ltac:(lia) ltac:(lia) Hpi Hpi') as Ha.
      rewrite E1 in Ha. cbn [snd] in Ha |- *. exact Ha.
    - assert (Hcin : List.In cnd (get_args ctx node))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      assert (Htin : List.In tid (get_args ctx node))
        by (unfold get_args; rewrite Hop; right; left; reflexivity).
      assert (Hein : List.In eid (get_args ctx node))
        by (unfold get_args; rewrite Hop; right; right; left; reflexivity).
      destruct (Hrange cnd Hcin) as [Hc1 Hc2].
      destruct (Hrange tid Htin) as [Ht1 Ht2].
      destruct (Hrange eid Hein) as [He1 He2].
      unfold node_args_sz in Hfg. rewrite Hop in Hfg.
      destruct Hfg as [Hf1 [Hf2 Hf3]].
      destruct (wsz_node_sz ctx cost_limit act cnd 1 Hf1) as [Hclen Hcsz].
      destruct (phi_crit (get_tainted ctx (build_dfg ctx act))
                  (decl_facts ctx (build_dfg ctx act)) cnd pi) eqn:Hcrit;
        cbn [phi_path]; cbv beta iota.
      + (* critical HERE: both branch validities are read, so the branches are
           compiled under the SAME path and no declassification is admitted *)
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    cnd bufs) as [ce cv] eqn:Ec.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    tid bufs) as [te tv] eqn:Et.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    eid bufs) as [ee ev] eqn:Ee.
        pose proof (IH cnd pi ltac:(intros y Hy Hy2; exact (Hsam_sub y ltac:(lia) Hy2)) ltac:(intros y my mszy Hy Hy2 Hy3; exact (Hsam_same y my mszy ltac:(lia) Hy2 Hy3)) Hc1 ltac:(lia) ltac:(lia) Hpi Hpi') as Hcc.
        pose proof (IH tid pi ltac:(intros y Hy Hy2; exact (Hsam_sub y ltac:(lia) Hy2)) ltac:(intros y my mszy Hy Hy2 Hy3; exact (Hsam_same y my mszy ltac:(lia) Hy2 Hy3)) Ht1 ltac:(lia) ltac:(lia) Hpi Hpi') as Hct.
        pose proof (IH eid pi ltac:(intros y Hy Hy2; exact (Hsam_sub y ltac:(lia) Hy2)) ltac:(intros y my mszy Hy Hy2 Hy3; exact (Hsam_same y my mszy ltac:(lia) Hy2 Hy3)) He1 ltac:(lia) ltac:(lia) Hpi Hpi') as Hce.
        rewrite Ec in Hcc. rewrite Et in Hct. rewrite Ee in Hce.
        cbn [snd] in Hcc, Hct, Hce |- *.
        rewrite !valid_and_eval. rewrite Hcc, Hct, Hce. reflexivity.
      + (* non-critical HERE: either the condition is untainted, or the analysis
           declassified it under a guard this path implies *)
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    cnd bufs) as [ce cv] eqn:Ec.
        destruct (compile_dfg_expr_at ctx bneeds ((cnd, true) :: pi) fuel a_idx
                    (build_dfg ctx act) tid bufs) as [te tv] eqn:Et.
        destruct (compile_dfg_expr_at ctx bneeds ((cnd, false) :: pi) fuel a_idx
                    (build_dfg ctx act) eid bufs) as [ee ev] eqn:Ee.
        pose proof (IH cnd pi ltac:(intros y Hy Hy2; exact (Hsam_sub y ltac:(lia) Hy2)) ltac:(intros y my mszy Hy Hy2 Hy3; exact (Hsam_same y my mszy ltac:(lia) Hy2 Hy3)) Hc1 ltac:(lia) ltac:(lia) Hpi Hpi') as Hcc.
        rewrite Ec in Hcc. cbn [snd] in Hcc |- *.
        assert (Hcder : gderivable act a_idx input pi cnd).
        { unfold phi_crit in Hcrit. apply andb_false_iff in Hcrit.
          destruct Hcrit as [Hmt | Hdg].
          - exact (untainted_gderivable act a_idx input pi cnd Halign Hpl Hdsz Hgsz Hc1 Hclen
                     (mem_nid_not_In cnd _ Hmt)).
          - apply Bool.negb_false_iff in Hdg.
            unfold declassified_at in Hdg. apply existsb_exists in Hdg.
            destruct Hdg as [g [Hg Hincl]].
            exact (gderivable_weaken act a_idx input g pi cnd Hincl
                     (Hdguard act a_idx input cnd g (gfacts_of_In _ _ _ Hg))). }
        rewrite !valid_and_eval. rewrite Hcc.
        destruct (bits1_cases (eval1 cv ss' input')) as [Hones | Hzero];
          [ | rewrite Hzero, !and1_zero_l; reflexivity ].
        f_equal.
        assert (Hvalc : eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                          (build_dfg ctx act) cnd bufs)) ss input = Bits.ones 1)
          by (rewrite Ec; cbn [snd]; rewrite Hcc; exact Hones).
        assert (Hvalc' : eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                          (build_dfg ctx act) cnd bufs)) ss' input' = Bits.ones 1)
          by (rewrite Ec; cbn [snd]; exact Hones).
        pose proof (compile_subst_valid_gen_at ctx cost_limit act a_idx ss input
                      Halign Hvs bufs Hsub fuel cnd 1 pi
                      ltac:(intros y Hy Hy2; exact (Hsam_sub y ltac:(lia) Hy2))
                      ltac:(intros y my mszy Hy Hy2 Hy3;
                            exact (Hsam_same y my mszy ltac:(lia) Hy2 Hy3))
                      Hc1 Hclen ltac:(lia)
                      (eq_sym Hcsz) Hvalc) as S1.
        pose proof (compile_subst_valid_gen_at ctx cost_limit act a_idx ss' input'
                      Halign Hvs' bufs Hsub fuel cnd 1 pi
                      ltac:(intros y Hy Hy2; exact (Hsam_sub y ltac:(lia) Hy2))
                      ltac:(intros y my mszy Hy Hy2 Hy3;
                            exact (Hsam_same y my mszy ltac:(lia) Hy2 Hy3))
                      Hc1 Hclen ltac:(lia)
                      (eq_sym Hcsz) Hvalc') as S2.
        rewrite Ec in S1, S2. cbn [fst] in S1, S2.
        rewrite (compile_fst_pi_irrel ctx cost_limit _ _ a_idx _ (sample_bufs ctx cost_limit act a_idx) fuel cnd pi [])
          in S1, S2.
        rewrite (compile_fuel_irrel ctx cost_limit act a_idx (sample_bufs ctx cost_limit act a_idx) cnd Hc1 Hclen
                   fuel (length (graph (build_dfg ctx act))) ltac:(lia) Hclen)
          in S1, S2.
        assert (Href : eval1 ce ss input
                       = nval ctx cost_limit act a_idx ss input 1 cnd)
          by (rewrite S1; unfold nval, node_ref_expr; reflexivity).
        assert (Href' : eval1 ce ss' input'
                        = nval ctx cost_limit act a_idx ss' input' 1 cnd)
          by (rewrite S2; unfold nval, node_ref_expr; reflexivity).
        (* the gate is read at the REFERENCE table; carry it over from this
           cycle's table, then refuel to the reference fuel *)
        assert (Hrv : forall (s: sched_sys_state) (i: sched_input_t),
                  valid_settled ctx cost_limit act a_idx s i ->
                  valid_refs ctx cost_limit act a_idx s i ->
                  eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                                (build_dfg ctx act) cnd bufs)) s i = Bits.ones 1 ->
                  rvalid act a_idx pi cnd s i = Bits.ones 1).
        { intros s i Hvsi Hrfi Hv.
          rewrite <- (compile_fuel_irrel_gen ctx cost_limit act a_idx
                        (sample_bufs ctx cost_limit act a_idx) _ _ cnd Hc1 Hclen
                        fuel (length (graph (build_dfg ctx act))) pi
                        ltac:(lia) Hclen).
          exact (compile_subst_ref_valid_gen_at ctx cost_limit act a_idx s i
                   Halign Hvsi Hrfi bufs Hsub fuel cnd pi
                   ltac:(intros y Hy; apply Hsam_sub; lia)
                   ltac:(intros y my mszy Hy; apply Hsam_same; lia)
                   Hc1 Hclen ltac:(lia) Hv). }
        assert (Hcev : eval1 ce ss input = eval1 ce ss' input').
        { rewrite Href, Href'.
          pose proof (Hcder ss ss' input' pi Hpub Hst Hst' Hpi Hpi' Hpi Hpi'
                        (Hrv ss  input  Hvs  Hrf  Hvalc)
                        (Hrv ss' input' Hvs' Hrf' Hvalc')) as Hcd.
          rewrite Hcsz in Hcd. exact Hcd. }
        assert (Hcase : (tv = tf_const 1 /\ ev = tf_const 1)
                        \/ valid_expr_if ctx bneeds ce tv ev
                           = tf_expr_if ce tv ev).
        { unfold valid_expr_if.
          destruct tv as [vt| | | | | |]; try (right; reflexivity).
          destruct vt as [|[|vt]]; try (right; reflexivity).
          destruct ev as [vee| | | | | |]; try (right; reflexivity).
          destruct vee as [|[|vee]]; try (right; reflexivity).
          left; split; reflexivity. }
        destruct Hcase as [[Htc Hec] | Hcs].
        * subst tv ev. reflexivity.
        * rewrite Hcs. cbn [tf_eval_expr]. rewrite Hcev.
          destruct (beq_dec (eval1 ce ss' input') Bits.zero) eqn:Hb.
          -- (* else branch selected: extend the path with [cnd = 0] *)
             assert (Hz : eval1 ce ss' input' = Bits.zero)
               by (apply beq_dec_iff in Hb; exact Hb).
             assert (Hp0 : pi_holds act a_idx input ((cnd, false) :: pi) ss).
             { intros c b Hin. destruct Hin as [Heq | Hin].
               - injection Heq as Hc Hbv. subst c b. unfold bit_of.
                 rewrite <- Href, Hcev. exact Hz.
               - exact (Hpi _ _ Hin). }
             assert (Hp0' : pi_holds act a_idx input' ((cnd, false) :: pi) ss').
             { intros c b Hin. destruct Hin as [Heq | Hin].
               - injection Heq as Hc Hbv. subst c b. unfold bit_of.
                 rewrite <- Href'. exact Hz.
               - exact (Hpi' _ _ Hin). }
             pose proof (IH eid ((cnd, false) :: pi) ltac:(intros y Hy Hy2; exact (Hsam_sub y ltac:(lia) Hy2)) ltac:(intros y my mszy Hy Hy2 Hy3; exact (Hsam_same y my mszy ltac:(lia) Hy2 Hy3)) He1 ltac:(lia) ltac:(lia)
                           Hp0 Hp0') as Hce.
             rewrite Ee in Hce. cbn [snd] in Hce. exact Hce.
          -- (* then branch selected: extend the path with [cnd = 1] *)
             assert (Hz : eval1 ce ss' input' = Bits.ones 1).
             { destruct (bits1_cases (eval1 ce ss' input')) as [Ho | Hzz];
                 [ exact Ho | ].
               rewrite Hzz, beq_dec_refl in Hb. discriminate. }
             assert (Hp1 : pi_holds act a_idx input ((cnd, true) :: pi) ss).
             { intros c b Hin. destruct Hin as [Heq | Hin].
               - injection Heq as Hc Hbv. subst c b. unfold bit_of.
                 rewrite <- Href, Hcev. exact Hz.
               - exact (Hpi _ _ Hin). }
             assert (Hp1' : pi_holds act a_idx input' ((cnd, true) :: pi) ss').
             { intros c b Hin. destruct Hin as [Heq | Hin].
               - injection Heq as Hc Hbv. subst c b. unfold bit_of.
                 rewrite <- Href'. exact Hz.
               - exact (Hpi' _ _ Hin). }
             pose proof (IH tid ((cnd, true) :: pi) ltac:(intros y Hy Hy2; exact (Hsam_sub y ltac:(lia) Hy2)) ltac:(intros y my mszy Hy Hy2 Hy3; exact (Hsam_same y my mszy ltac:(lia) Hy2 Hy3)) Ht1 ltac:(lia) ltac:(lia)
                           Hp1 Hp1') as Hct.
             rewrite Et in Hct. cbn [snd] in Hct. exact Hct.
    - (* DFG_Stall: same as DFG_Unary -- validity passes through. *)
      assert (Hain : List.In sa (get_args ctx node))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      destruct (Hrange sa Hain) as [Ha1 Ha2].
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  sa bufs) as [ae ve] eqn:E1.
      pose proof (IH sa pi ltac:(intros y Hy Hy2; exact (Hsam_sub y ltac:(lia) Hy2)) ltac:(intros y my mszy Hy Hy2 Hy3; exact (Hsam_same y my mszy ltac:(lia) Hy2 Hy3)) Ha1 ltac:(lia) ltac:(lia) Hpi Hpi') as Ha.
      rewrite E1 in Ha. cbn [snd] in Ha |- *. exact Ha.
    - (* A drive's validity is its argument's conjoined with every literal on
         its path condition: a request must not leave before its guard reads
         true. *)
      assert (Hain : List.In darg (get_args ctx node))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      destruct (Hrange darg Hain) as [Ha1 Ha2].
      assert (Hfold : forall (gs: list lit)
                        (base: @tf_expr (tfs_states sched) (tfs_inputs sched) o_var),
                (forall l, List.In l gs -> 1 <= fst l /\ fst l < n) ->
                eval1 base ss input = eval1 base ss' input' ->
                eval1 (fold_right (fun l acc =>
                         valid_expr_and ctx bneeds
                           (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                                   (build_dfg ctx act) (fst l) bufs)) acc)
                         base gs) ss input
              = eval1 (fold_right (fun l acc =>
                         valid_expr_and ctx bneeds
                           (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                                   (build_dfg ctx act) (fst l) bufs)) acc)
                         base gs) ss' input').
      { induction gs as [| l rest IHgs]; intros base Hr Hb;
          cbn [fold_right]; [ exact Hb | ].
        rewrite !valid_and_eval.
        destruct (Hr l (or_introl eq_refl)) as [Hl1 Hl2].
        pose proof (IH (fst l) pi ltac:(intros y Hy Hy2; exact (Hsam_sub y ltac:(lia) Hy2)) ltac:(intros y my mszy Hy Hy2 Hy3; exact (Hsam_same y my mszy ltac:(lia) Hy2 Hy3)) Hl1 ltac:(lia) ltac:(lia) Hpi Hpi') as Hl.
        rewrite Hl.
        rewrite (IHgs base ltac:(intros l' Hl'; apply Hr; right; exact Hl') Hb).
        reflexivity. }
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  darg bufs) as [ae ve] eqn:E1.
      pose proof (IH darg pi ltac:(intros y Hy Hy2; exact (Hsam_sub y ltac:(lia) Hy2)) ltac:(intros y my mszy Hy Hy2 Hy3; exact (Hsam_same y my mszy ltac:(lia) Hy2 Hy3)) Ha1 ltac:(lia) ltac:(lia) Hpi Hpi') as Ha.
      rewrite E1 in Ha. cbn [snd] in Ha |- *.
      apply Hfold; [ | exact Ha ].
      intros l Hl. apply Hrange.
      unfold get_args; rewrite Hop; right; apply in_map; exact Hl.
    - (* DFG_Sample: its VALIDITY is the token's by construction in
         [compile_dfg_expr_aux], so validity passes through as for a stall
         though the VALUE does not. *)
      assert (Hain : List.In stok (get_args ctx node))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      destruct (Hrange stok Hain) as [Ha1 Ha2].
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  stok bufs) as [ae ve] eqn:E1.
      pose proof (IH stok pi ltac:(intros y Hy Hy2; exact (Hsam_sub y ltac:(lia) Hy2)) ltac:(intros y my mszy Hy Hy2 Hy3; exact (Hsam_same y my mszy ltac:(lia) Hy2 Hy3)) Ha1 ltac:(lia) ltac:(lia) Hpi Hpi') as Ha.
      rewrite E1 in Ha. cbn [snd] in Ha |- *. exact Ha.
    - (* A join is valid when both its arguments are, which is the ordering
         a second call on a port waits for. *)
      assert (Haa : List.In ja (get_args ctx node))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      assert (Hbb : List.In jb (get_args ctx node))
        by (unfold get_args; rewrite Hop; right; left; reflexivity).
      destruct (Hrange ja Haa) as [Hja1 Hja2].
      destruct (Hrange jb Hbb) as [Hjb1 Hjb2].
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  ja bufs) as [ae ve] eqn:E1.
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  jb bufs) as [be vb] eqn:E2.
      pose proof (IH ja pi ltac:(intros y Hy Hy2; exact (Hsam_sub y ltac:(lia) Hy2)) ltac:(intros y my mszy Hy Hy2 Hy3; exact (Hsam_same y my mszy ltac:(lia) Hy2 Hy3)) Hja1 ltac:(lia) ltac:(lia) Hpi Hpi') as Hxa.
      pose proof (IH jb pi ltac:(intros y Hy Hy2; exact (Hsam_sub y ltac:(lia) Hy2)) ltac:(intros y my mszy Hy Hy2 Hy3; exact (Hsam_same y my mszy ltac:(lia) Hy2 Hy3)) Hjb1 ltac:(lia) ltac:(lia) Hpi Hpi') as Hxb.
      rewrite E1 in Hxa. rewrite E2 in Hxb. cbn [snd] in Hxa, Hxb |- *.
      rewrite !valid_and_eval. rewrite Hxa, Hxb. reflexivity.
    - reflexivity.
  Qed.

  Lemma valid_public (act: tfs_action sched) (a_idx: a_index)
      (input input': sched_input_t) (ss ss': sched_sys_state) :
    act_idx_aligned ctx cost_limit act a_idx ->
    plumbing_not_root act ->
    drives_sized act ->
    guards_sized act ->
    valid_refs ctx cost_limit act a_idx ss  input  ->
    valid_refs ctx cost_limit act a_idx ss' input' ->
    settled act a_idx ss  input  ->
    settled act a_idx ss' input' ->
    valid_settled ctx cost_limit act a_idx ss  input  ->
    valid_settled ctx cost_limit act a_idx ss' input' ->
    pub_eq act a_idx input input' ss ss' ->
    (forall n_idx, (fst ss).[tf_dfg_v a_idx n_idx]
                 = (fst ss').[tf_dfg_v a_idx n_idx]) ->
    forall bufs,
      (forall e, List.In e bufs ->
         List.In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
      forall fuel n,
        (forall x, x < n ->
           BitsToLists.list_assoc bufs x = None ->
           BitsToLists.list_assoc (sample_bufs ctx cost_limit act a_idx) x = None) ->
        (forall x m msz, x < n ->
           BitsToLists.list_assoc bufs x = Some (m, msz) ->
           is_sample_of ctx cost_limit act x = true ->
           BitsToLists.list_assoc (sample_bufs ctx cost_limit act a_idx) x
             = Some (m, msz)) ->
        1 <= n ->
        n < length (graph (build_dfg ctx act)) ->
        n < fuel ->
        eval1 (snd (compile_dfg_expr ctx bneeds fuel a_idx
                      (build_dfg ctx act) n bufs)) ss input
        = eval1 (snd (compile_dfg_expr ctx bneeds fuel a_idx
                      (build_dfg ctx act) n bufs)) ss' input'.
  Proof.
    intros Halign Hpl Hdsz Hgsz Hrf Hrf' Hst Hst' Hvs Hvs' Hpub Hveq bufs Hsub fuel n
      Hsam_sub Hsam_same
      Hn1 Hnlen Hnfuel.
    exact (valid_public_gen act a_idx input input' ss ss' Halign Hpl Hdsz Hgsz
             Hrf Hrf' Hst Hst' Hvs Hvs' Hpub Hveq
             bufs Hsub fuel n [] Hsam_sub Hsam_same Hn1 Hnlen Hnfuel
             (pi_holds_nil act a_idx input ss) (pi_holds_nil act a_idx input' ss')).
  Qed.


  Local Notation src_st_env  := (ContextEnv.(env_t) (tf_states_type s_sz)).
  Local Notation src_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation src_sys_state := (src_st_env * src_out_env)%type.
  (* ------------------------------------------------------------------- *)
  (* The observable restatement: [pub_eq] follows from equality of the     *)
  (* pre- and post-action outputs alone, so latency is a function of data  *)
  (* an output observer already has.                                       *)
  (* ------------------------------------------------------------------- *)

  Local Notation spec_run act sp input :=
    (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act)
       sp input).

  Theorem obs_eq_pub_eq (act: tfs_action sched) (a_idx: a_index)
      (input input': input_t) (sinput sinput': sched_input_t)
      (sp sp': src_sys_state) (ss ss': sched_sys_state) :
    act_idx_aligned ctx cost_limit act a_idx ->
    (forall v, sinput  (inl v) = input  v) ->
    (forall v, sinput' (inl v) = input' v) ->
    (* the round trip, which V4 needs and V3 did not have to state *)
    settled act a_idx ss  sinput  ->
    settled act a_idx ss' sinput' ->
    (forall sv, (fst ss ).[tf_dfg_s sv] = (fst sp ).[sv]) ->
    (forall ov, (snd ss ).[ov] = (snd sp ).[ov]) ->
    (forall sv, (fst ss').[tf_dfg_s sv] = (fst sp').[sv]) ->
    (forall ov, (snd ss').[ov] = (snd sp').[ov]) ->
    (* PUBLIC outputs only, before and after: quantifying over [Secret] ones too
       would strengthen the hypothesis and so weaken the theorem. *)
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd sp).[ov] = (snd sp').[ov]) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd (spec_run act sp  input )).[ov]
              = (snd (spec_run act sp' input')).[ov]) ->
    (* ...and the attacker drives the same PUBLIC inputs in both runs.  Secret
       inputs are free: they come from inside the trust boundary. *)
    (forall v, tfs_spec_inputs_class ctx v = Public -> sinput (inl v) = sinput' (inl v)) ->
    pub_eq act a_idx sinput sinput' ss ss'.
  Proof.
    intros Halign Hsi Hsi' [Hans [_ [Hargs _]]] [Hans' [_ [Hargs' _]]]
      Hs Ho Hs' Ho' Hpre Hpost Hipub.
    destruct (dfg_action_semantics ctx cost_limit act a_idx sp ss input sinput
                Halign Hsi
                ltac:(intros n_idx p tok en d av en' Ho1 Ho2 Ho3 Ho4 Hg Hv;
                      exact (Hans n_idx p tok en d av en' Ho1 Ho2 Ho3 Ho4 Hv
                               (guard_pi_holds act a_idx sinput en ss Hg)))
                Hargs Hs Ho) as [_ [Hout _]].
    destruct (dfg_action_semantics ctx cost_limit act a_idx sp' ss' input' sinput'
                Halign Hsi'
                ltac:(intros n_idx p tok en d av en' Ho1 Ho2 Ho3 Ho4 Hg Hv;
                      exact (Hans' n_idx p tok en d av en' Ho1 Ho2 Ho3 Ho4 Hv
                               (guard_pi_holds act a_idx sinput' en ss' Hg)))
                Hargs' Hs' Ho') as [_ [Hout' _]].
    split; [ exact Hipub | split ].
    - intros o Hc. rewrite (Ho o), (Ho' o). exact (Hpre o Hc).
    - intros o r pi Hc Hin Hpi Hpi' Hv Hv'. unfold nval, node_ref_expr.
      rewrite (pub_eq_root_width act o r Hin).
      rewrite (Hout  o r pi Hin (pi_holds_guard act a_idx sinput  pi ss  Hpi ) Hv ),
              (Hout' o r pi Hin (pi_holds_guard act a_idx sinput' pi ss' Hpi') Hv').
      exact (Hpost o Hc).
  Qed.
  (* ------------------------------------------------------------------- *)
  (* PHASE 2: the validity registers run in lockstep between two states    *)
  (* with the same public view.  This is the statement that makes the done *)
  (* flag -- and hence the latency -- secret-independent.                  *)
  (* ------------------------------------------------------------------- *)

  (* V4 reads the public view off the SPEC, not off cycle 0.  A sample's
     reference value moves when its latch fires, so there is nothing at cycle 0
     to transport; the bridge lemma pins a valid root to the published output
     at whatever cycle it is read. *)
  Lemma pub_eq_run (act: tfs_action sched) (a_idx: a_index)
      (input input': input_t) (resp resp': nat -> resp_val)
      (sp0 sp0': src_sys_state) (ss0 ss0': sched_sys_state) (k: nat) :
    act_idx_aligned ctx cost_limit act a_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    start_rel ctx cost_limit sp0  ss0  ->
    start_rel ctx cost_limit sp0' ss0' ->
    Definitions.ip_contract ctx cost_limit act input  resp  ss0  ->
    Definitions.ip_contract ctx cost_limit act input' resp' ss0' ->
    (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input  resp  ss0 )) ->
    (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input' resp' ss0')) ->
    (forall v, tfs_spec_inputs_class ctx v = Public -> input v = input' v) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd sp0).[ov] = (snd sp0').[ov]) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd (spec_run act sp0  input )).[ov]
              = (snd (spec_run act sp0' input')).[ov]) ->
    pub_eq act a_idx
      (sched_input ctx cost_limit input  (resp  k))
      (sched_input ctx cost_limit input' (resp' k))
      (ss_run k act input resp ss0) (ss_run k act input' resp' ss0').
  Proof.
    intros Halign Hlen [Hoo [Hmm Hzz]] [Hoo' [Hmm' Hzz']] Hipc Hipc' Hnd Hnd'
      Hipub Hpre Hpost.
    apply (obs_eq_pub_eq act a_idx input input'
             (sched_input ctx cost_limit input  (resp  k))
             (sched_input ctx cost_limit input' (resp' k))
             sp0 sp0' _ _ Halign
             ltac:(intro v; reflexivity) ltac:(intro v; reflexivity)
             (settled_run act a_idx input  resp  ss0  k Halign Hlen Hzz  Hnd  Hipc )
             (settled_run act a_idx input' resp' ss0' k Halign Hlen Hzz' Hnd' Hipc'));
      [ intro sv | intro ov | intro sv | intro ov | exact Hpre | exact Hpost
      | intros v Hc; exact (Hipub v Hc) ].
    - rewrite (run_preserves_svar ctx cost_limit act input resp ss0 k Hnd sv).
      rewrite <- Hmm, getenv_maps_from. reflexivity.
    - rewrite (run_preserves_ovar ctx cost_limit act input resp ss0 k Hnd ov).
      rewrite Hoo. reflexivity.
    - rewrite (run_preserves_svar ctx cost_limit act input' resp' ss0' k Hnd' sv).
      rewrite <- Hmm', getenv_maps_from. reflexivity.
    - rewrite (run_preserves_ovar ctx cost_limit act input' resp' ss0' k Hnd' ov).
      rewrite Hoo'. reflexivity.
  Qed.


  (* ------------------------------------------------------------------- *)
  (* PHASE 2: the validity registers run in lockstep between two states    *)
  (* with the same public view.  This is the statement that makes the done *)
  (* flag -- and hence the latency -- secret-independent.                  *)
  (* ------------------------------------------------------------------- *)

  (* V4 makes this a JOINT induction: a stall's validity reads its own counter,
     so the counters have to run in lockstep too.  Both sides are decided by
     the gate, which [valid_public] equates.  Only STALL buffers are claimed --
     a plain buffer holds the node's value, which may well be secret. *)
  Theorem valid_stall_lockstep (act: tfs_action sched) (a_idx: a_index)
      (input input': input_t) (resp resp': nat -> resp_val)
      (sp0 sp0': src_sys_state) (ss0 ss0': sched_sys_state) :
    act_idx_aligned ctx cost_limit act a_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    plumbing_not_root act ->
    drives_sized act ->
    guards_sized act ->
    start_rel ctx cost_limit sp0  ss0  ->
    start_rel ctx cost_limit sp0' ss0' ->
    Definitions.ip_contract ctx cost_limit act input  resp  ss0  ->
    Definitions.ip_contract ctx cost_limit act input' resp' ss0' ->
    (forall v, tfs_spec_inputs_class ctx v = Public -> input v = input' v) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd sp0).[ov] = (snd sp0').[ov]) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd (spec_run act sp0  input )).[ov]
              = (snd (spec_run act sp0' input')).[ov]) ->
    forall k,
      (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input  resp  ss0 )) ->
      (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input' resp' ss0')) ->
      forall n_idx,
        (fst (ss_run k act input  resp  ss0 )).[tf_dfg_v a_idx n_idx]
        = (fst (ss_run k act input' resp' ss0')).[tf_dfg_v a_idx n_idx]
        /\ (stall_lat_of ctx cost_limit act (vreg_nid ctx cost_limit a_idx n_idx)
              <> None ->
            (fst (ss_run k act input  resp  ss0 )).[tf_dfg_b a_idx n_idx]
            = (fst (ss_run k act input' resp' ss0')).[tf_dfg_b a_idx n_idx]).
  Proof.
    intros Halign Hlen Hpl Hdsz Hgsz Hsr Hsr' Hipc Hipc' Hipub Hpre Hpost.
    destruct Hsr  as [Hoo  [Hmm  Hzz ]].
    destruct Hsr' as [Hoo' [Hmm' Hzz']].
    induction k as [| k IH]; intros Hnd Hnd' n_idx.
    { cbn [run_n]. split;
        [ rewrite (Hzz (tf_dfg_v a_idx n_idx) I), (Hzz' (tf_dfg_v a_idx n_idx) I)
        | intros _;
          rewrite (Hzz (tf_dfg_b a_idx n_idx) I), (Hzz' (tf_dfg_b a_idx n_idx) I) ];
        reflexivity. }
    assert (Hndk : forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input resp ss0))
      by (intros i Hi; apply Hnd; lia).
    assert (Hndk' : forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input' resp' ss0'))
      by (intros i Hi; apply Hnd'; lia).
    set (ssk  := ss_run k act input  resp  ss0 ) in *.
    set (ssk' := ss_run k act input' resp' ss0') in *.
    set (ik   := sched_input ctx cost_limit input  (resp  k)) in *.
    set (ik'  := sched_input ctx cost_limit input' (resp' k)) in *.
    assert (Hs  : ~ ss_done (ss_step act ssk  ik )) by (apply (Hnd  (S k)); lia).
    assert (Hs' : ~ ss_done (ss_step act ssk' ik')) by (apply (Hnd' (S k)); lia).
    change (ss_run (S k) act input  resp  ss0 ) with (ss_step act ssk  ik ).
    change (ss_run (S k) act input' resp' ss0') with (ss_step act ssk' ik').
    pose proof (buffer_after_cycle ctx cost_limit act a_idx n_idx ssk  ik  Halign Hs ) as Hb.
    pose proof (buffer_after_cycle ctx cost_limit act a_idx n_idx ssk' ik' Halign Hs') as Hb'.
    cbv zeta in Hb, Hb'.
    destruct Hb  as [Hbb  Hvv ]. destruct Hb' as [Hbb' Hvv'].
    destruct (vreg_nid_node_range ctx cost_limit act a_idx n_idx Halign)
      as [Hn1 Hnlen].
    unfold vreg_nid in Hn1, Hnlen.
    destruct (SchedulerRoundTrip.gate_table_sample_bufs ctx cost_limit act a_idx
                (fst (nth (index_to_nat n_idx)
                        (nth (index_to_nat a_idx) bneeds []) (0, (0, 0)))) Halign)
      as [Hsam_sub Hsam_same].
    destruct (valid_settled_run ctx cost_limit act a_idx input resp ss0 k Halign
                (fun q => Hzz (tf_dfg_v a_idx q) I)) as [_ [Hrf Hvs]].
    destruct (valid_settled_run ctx cost_limit act a_idx input' resp' ss0' k Halign
                (fun q => Hzz' (tf_dfg_v a_idx q) I)) as [_ [Hrf' Hvs']].
    (* the GATE reads the same in both runs *)
    assert (Hgate : eval1 (snd (compile_dfg_expr ctx bneeds
                        (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act)
                        (fst (nth (index_to_nat n_idx)
                                (nth (index_to_nat a_idx) bneeds []) (0, (0, 0))))
                        (filter (fun '(b_nid, _) => negb (Nat.eqb b_nid
                            (fst (nth (index_to_nat n_idx)
                                    (nth (index_to_nat a_idx) bneeds []) (0, (0, 0))))))
                           (nth (index_to_nat a_idx) bneeds [])))) ssk ik
                   = eval1 (snd (compile_dfg_expr ctx bneeds
                        (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act)
                        (fst (nth (index_to_nat n_idx)
                                (nth (index_to_nat a_idx) bneeds []) (0, (0, 0))))
                        (filter (fun '(b_nid, _) => negb (Nat.eqb b_nid
                            (fst (nth (index_to_nat n_idx)
                                    (nth (index_to_nat a_idx) bneeds []) (0, (0, 0))))))
                           (nth (index_to_nat a_idx) bneeds [])))) ssk' ik').
    { apply (valid_public act a_idx ik ik' ssk ssk' Halign Hpl Hdsz Hgsz
               Hrf Hrf'
               (settled_run act a_idx input  resp  ss0  k Halign Hlen Hzz  Hndk  Hipc )
               (settled_run act a_idx input' resp' ss0' k Halign Hlen Hzz' Hndk' Hipc')
               Hvs Hvs'
               (pub_eq_run act a_idx input input' resp resp' sp0 sp0' ss0 ss0' k
                  Halign Hlen (conj Hoo (conj Hmm Hzz)) (conj Hoo' (conj Hmm' Hzz'))
                  Hipc Hipc' Hndk Hndk' Hipub Hpre Hpost)
               (fun q => proj1 (IH Hndk Hndk' q)));
        [ intros e He; exact (proj1 (proj1 (filter_In _ e _) He))
        | exact Hsam_sub | exact Hsam_same
        | exact Hn1 | exact Hnlen | exact Hnlen ]. }
    rewrite Hvv, Hvv', Hbb, Hbb'.
    unfold SchedulerSimulationLemmas.buf_valid_expr,
           SchedulerSimulationLemmas.buf_value_expr.
    destruct (stall_lat_of ctx cost_limit act
                (fst (nth (index_to_nat n_idx)
                        (nth (index_to_nat a_idx) bneeds []) (0, (0, 0)))))
      as [l |] eqn:Hst.
    - assert (Hcnt := proj2 (IH Hndk Hndk' n_idx)
                        ltac:(unfold Definitions.vreg_nid;
                              rewrite Hst; discriminate)).
      split.
      + cbn [tf_eval_expr]. rewrite !convert_same.
        (* [cbn] rebuilds the register read under a second annotation *)
        match goal with
        | |- context [beq_dec ?r _] =>
            replace r with ((fst ssk).[tf_dfg_b a_idx n_idx]) by reflexivity
        end.
        match goal with
        | |- _ = Bits.and _ (if beq_dec ?r _ then _ else _) =>
            replace r with ((fst ssk').[tf_dfg_b a_idx n_idx]) by reflexivity
        end.
        rewrite Hcnt. f_equal. exact Hgate.
      + intros _. cbn [tf_eval_expr]. rewrite !convert_same.
        match goal with
        | |- (if _ then ?r else _) = _ =>
            replace r with ((fst ssk).[tf_dfg_b a_idx n_idx]) by reflexivity
        end.
        match goal with
        | |- _ = (if _ then ?r else _) =>
            replace r with ((fst ssk').[tf_dfg_b a_idx n_idx]) by reflexivity
        end.
        rewrite Hcnt, Hgate. reflexivity.
    - split; [ exact Hgate | intro Hne; exfalso; exact (Hne Hst) ].
  Qed.

  (* What the rest of the file consumes: the validity half alone. *)
  Theorem valid_lockstep (act: tfs_action sched) (a_idx: a_index)
      (input input': input_t) (resp resp': nat -> resp_val)
      (sp0 sp0': src_sys_state) (ss0 ss0': sched_sys_state) :
    act_idx_aligned ctx cost_limit act a_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    plumbing_not_root act ->
    drives_sized act ->
    guards_sized act ->
    start_rel ctx cost_limit sp0  ss0  ->
    start_rel ctx cost_limit sp0' ss0' ->
    Definitions.ip_contract ctx cost_limit act input  resp  ss0  ->
    Definitions.ip_contract ctx cost_limit act input' resp' ss0' ->
    (forall v, tfs_spec_inputs_class ctx v = Public -> input v = input' v) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd sp0).[ov] = (snd sp0').[ov]) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd (spec_run act sp0  input )).[ov]
              = (snd (spec_run act sp0' input')).[ov]) ->
    forall k,
      (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input  resp  ss0 )) ->
      (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input' resp' ss0')) ->
      forall n_idx,
        (fst (ss_run k act input  resp  ss0 )).[tf_dfg_v a_idx n_idx]
        = (fst (ss_run k act input' resp' ss0')).[tf_dfg_v a_idx n_idx].
  Proof.
    intros Halign Hlen Hpl Hdsz Hgsz Hsr Hsr' Hipc Hipc' Hipub Hpre Hpost k Hnd Hnd' n_idx.
    exact (proj1 (valid_stall_lockstep act a_idx input input' resp resp'
                    sp0 sp0' ss0 ss0' Halign Hlen Hpl Hdsz Hgsz Hsr Hsr'
                    Hipc Hipc' Hipub Hpre Hpost k Hnd Hnd' n_idx)).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* PHASE 3: the done flag is public.                                     *)
  (* The done register is assigned the AND-fold of the validity            *)
  (* expressions of the [var_map] roots, so Phase 2 transfers to it.       *)
  (* ------------------------------------------------------------------- *)

  Local Notation vm_roots act :=
    (nodup Nat.eq_dec (map snd (var_map (build_dfg ctx act)))).

  Local Notation root_valid act a_idx n :=
    (snd (compile_dfg_expr ctx bneeds (length (graph (build_dfg ctx act)))
            a_idx (build_dfg ctx act) n
            (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))).

  (* [sched_step_done_set] hides the validity list behind a per-state existential,
     so it cannot relate two runs; [done_exprs_concrete] exposes the list instead. *)
  Lemma done_val_concrete (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t) :
    act_idx_aligned ctx cost_limit act a_idx ->
    (fst (ss_step act ss input)).[tfs_done_signal sched]
    = fold_right Bits.and (Bits.ones 1)
        (map (fun e => eval1 e ss input)
           (map (fun n => root_valid act a_idx n) (vm_roots act))).
  Proof.
    intros Halign.
    destruct (done_exprs_concrete ctx cost_limit act a_idx Halign) as [rest Heq].
    rewrite sched_step_done. unfold find_st_val. rewrite Heq.
    rewrite find_st_update_assign_head. apply combine_valid_eval.
  Qed.

  Theorem done_public (act: tfs_action sched) (a_idx: a_index)
      (input input': sched_input_t) (ss ss': sched_sys_state) :
    act_idx_aligned ctx cost_limit act a_idx ->
    plumbing_not_root act ->
    drives_sized act ->
    guards_sized act ->
    valid_refs ctx cost_limit act a_idx ss  input  ->
    valid_refs ctx cost_limit act a_idx ss' input' ->
    settled act a_idx ss  input  ->
    settled act a_idx ss' input' ->
    valid_settled ctx cost_limit act a_idx ss  input  ->
    valid_settled ctx cost_limit act a_idx ss' input' ->
    pub_eq act a_idx input input' ss ss' ->
    (forall n_idx, (fst ss).[tf_dfg_v a_idx n_idx]
                 = (fst ss').[tf_dfg_v a_idx n_idx]) ->
    (fst (ss_step act ss  input )).[tfs_done_signal sched]
    = (fst (ss_step act ss' input')).[tfs_done_signal sched].
  Proof.
    intros Halign Hpl Hdsz Hgsz Hrf Hrf' Hst Hst' Hvs Hvs' Hpub Hveq.
    destruct (SchedulerRoundTrip.full_table_sample_bufs ctx cost_limit act a_idx
                Halign) as [Hsam_sub Hsam_same].
    rewrite (done_val_concrete act a_idx ss  input  Halign).
    rewrite (done_val_concrete act a_idx ss' input' Halign).
    f_equal. rewrite !map_map. apply map_ext_in. intros n Hn.
    apply nodup_In in Hn.
    destruct (var_map_node_range ctx cost_limit act n Hn) as [Hn1 Hnlen].
    exact (valid_public act a_idx input input' ss ss' Halign Hpl Hdsz Hgsz
             Hrf Hrf' Hst Hst' Hvs Hvs' Hpub Hveq
             _ (fun e He => He) _ n
             (fun x _ => Hsam_sub x) (fun x m msz _ => Hsam_same x m msz)
             Hn1 Hnlen Hnlen).
  Qed.

  Theorem done_lockstep (act: tfs_action sched) (a_idx: a_index)
      (input input': input_t) (resp resp': nat -> resp_val)
      (sp0 sp0': src_sys_state) (ss0 ss0': sched_sys_state) :
    act_idx_aligned ctx cost_limit act a_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    plumbing_not_root act ->
    drives_sized act ->
    guards_sized act ->
    start_rel ctx cost_limit sp0  ss0  ->
    start_rel ctx cost_limit sp0' ss0' ->
    Definitions.ip_contract ctx cost_limit act input  resp  ss0  ->
    Definitions.ip_contract ctx cost_limit act input' resp' ss0' ->
    (forall v, tfs_spec_inputs_class ctx v = Public -> input v = input' v) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd sp0).[ov] = (snd sp0').[ov]) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd (spec_run act sp0  input )).[ov]
              = (snd (spec_run act sp0' input')).[ov]) ->
    forall k,
      (forall i, 1 <= i < k -> ~ ss_done (ss_run i act input  resp  ss0 )) ->
      (forall i, 1 <= i < k -> ~ ss_done (ss_run i act input' resp' ss0')) ->
      (ss_done (ss_run k act input  resp  ss0 )
       <-> ss_done (ss_run k act input' resp' ss0')).
  Proof.
    intros Halign Hlen Hpl Hdsz Hgsz Hsr Hsr' Hipc Hipc' Hipub Hpre Hpost k Hnd Hnd'.
    pose proof Hsr  as Hsrc.  pose proof Hsr' as Hsrc'.
    destruct Hsrc  as [Hoo  [Hmm  Hzz ]].
    destruct Hsrc' as [Hoo' [Hmm' Hzz']].
    destruct k as [| k].
    { unfold done_set. cbn [run_n].
      rewrite (Hzz (tfs_done_signal sched) I), (Hzz' (tfs_done_signal sched) I).
      reflexivity. }
    assert (Hndk : forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input resp ss0))
      by (intros i Hi; apply Hnd; lia).
    assert (Hndk' : forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input' resp' ss0'))
      by (intros i Hi; apply Hnd'; lia).
    set (ssk  := ss_run k act input  resp  ss0 ) in *.
    set (ssk' := ss_run k act input' resp' ss0') in *.
    set (ik   := sched_input ctx cost_limit input  (resp  k)) in *.
    set (ik'  := sched_input ctx cost_limit input' (resp' k)) in *.
    change (ss_run (S k) act input  resp  ss0 ) with (ss_step act ssk  ik ).
    change (ss_run (S k) act input' resp' ss0') with (ss_step act ssk' ik').
    destruct (valid_settled_run ctx cost_limit act a_idx input resp ss0 k Halign
                (fun q => Hzz (tf_dfg_v a_idx q) I)) as [_ [Hrf Hvs]].
    destruct (valid_settled_run ctx cost_limit act a_idx input' resp' ss0' k Halign
                (fun q => Hzz' (tf_dfg_v a_idx q) I)) as [_ [Hrf' Hvs']].
    unfold done_set.
    rewrite (done_public act a_idx ik ik' ssk ssk' Halign Hpl Hdsz Hgsz
               Hrf Hrf'
               (settled_run act a_idx input  resp  ss0  k Halign Hlen Hzz  Hndk  Hipc )
               (settled_run act a_idx input' resp' ss0' k Halign Hlen Hzz' Hndk' Hipc')
               Hvs Hvs'
               (pub_eq_run act a_idx input input' resp resp' sp0 sp0' ss0 ss0' k
                  Halign Hlen Hsr Hsr' Hipc Hipc' Hndk Hndk' Hipub Hpre Hpost)
               (fun q => proj1 (valid_stall_lockstep act a_idx input input' resp resp'
                                  sp0 sp0' ss0 ss0' Halign Hlen Hpl Hdsz Hgsz Hsr Hsr'
                                  Hipc Hipc' Hipub Hpre Hpost k Hndk Hndk' q))).
    reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* PHASE 4: the first done cycle is unique, and the same for two states  *)
  (* with the same public view -- latency non-interference.                *)
  (* ------------------------------------------------------------------- *)

  Lemma first_done_unique (act: tfs_action sched) (input: input_t)
      (resp: nat -> resp_val) (ss0: sched_sys_state) (N N': nat) :
    first_done act input resp ss0 N -> first_done act input resp ss0 N' -> N = N'.
  Proof.
    intros [HN HltN] [HN' HltN'].
    destruct (Nat.lt_trichotomy N N') as [H | [H | H]].
    - destruct (HltN' N H HN).
    - exact H.
    - destruct (HltN N' H HN').
  Qed.

  (* B2.  V4 states it over the SPEC's public outputs rather than over [pub_eq]
     at cycle 0, which has no content before the latches fire.  That is the
     shape B1 already had, so the two now coincide; [_start] and
     [latency_from_outputs] below are the same statement under their own
     names. *)
  Theorem latency_noninterference (act: tfs_action sched) (a_idx: a_index)
      (input input': input_t) (resp resp': nat -> resp_val)
      (sp0 sp0': src_sys_state) (ss0 ss0': sched_sys_state) (N N': nat) :
    act_idx_aligned ctx cost_limit act a_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    plumbing_not_root act ->
    drives_sized act ->
    guards_sized act ->
    start_rel ctx cost_limit sp0  ss0  ->
    start_rel ctx cost_limit sp0' ss0' ->
    Definitions.ip_contract ctx cost_limit act input  resp  ss0  ->
    Definitions.ip_contract ctx cost_limit act input' resp' ss0' ->
    (* PUBLIC data only: the two runs may differ in secret state AND secret
       inputs, so everything constrained here is something the attacker already
       drives or observes. *)
    (forall v,  tfs_spec_inputs_class  ctx v  = Public -> input v = input' v) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd sp0).[ov] = (snd sp0').[ov]) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd (spec_run act sp0  input )).[ov]
              = (snd (spec_run act sp0' input')).[ov]) ->
    first_done act input  resp  ss0  N ->
    first_done act input' resp' ss0' N' ->
    N = N'.
  Proof.
    intros Halign Hlen Hpl Hdsz Hgsz Hsr Hsr' Hipc Hipc' Hipub Hpre Hpost
      [HN HltN] [HN' HltN'].
    destruct (Nat.lt_trichotomy N N') as [Hlt | [Heq | Hgt]]; [ | exact Heq | ].
    - destruct (HltN' N Hlt).
      apply (done_lockstep act a_idx input input' resp resp' sp0 sp0' ss0 ss0'
               Halign Hlen Hpl Hdsz Hgsz Hsr Hsr' Hipc Hipc' Hipub Hpre Hpost N
               (fun i Hi => HltN  i (proj2 Hi))
               (fun i Hi => HltN' i (Nat.lt_trans _ _ _ (proj2 Hi) Hlt))).
      exact HN.
    - destruct (HltN N' Hgt).
      apply (done_lockstep act a_idx input input' resp resp' sp0 sp0' ss0 ss0'
               Halign Hlen Hpl Hdsz Hgsz Hsr Hsr' Hipc Hipc' Hipub Hpre Hpost N'
               (fun i Hi => HltN  i (Nat.lt_trans _ _ _ (proj2 Hi) Hgt))
               (fun i Hi => HltN' i (proj2 Hi))).
      exact HN'.
  Qed.

  (* V3 read the zeroing side conditions off [start_rel] here; V4 needs
     [start_rel] in the theorem itself, so this is the same statement. *)
  Corollary latency_noninterference_start (act: tfs_action sched) (a_idx: a_index)
      (input input': input_t) (resp resp': nat -> resp_val)
      (sp0 sp0': src_sys_state) (ss0 ss0': sched_sys_state) (N N': nat) :
    act_idx_aligned ctx cost_limit act a_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    plumbing_not_root act ->
    drives_sized act ->
    guards_sized act ->
    start_rel ctx cost_limit sp0  ss0  ->
    start_rel ctx cost_limit sp0' ss0' ->
    Definitions.ip_contract ctx cost_limit act input  resp  ss0  ->
    Definitions.ip_contract ctx cost_limit act input' resp' ss0' ->
    (forall v,  tfs_spec_inputs_class  ctx v  = Public -> input v = input' v) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd sp0).[ov] = (snd sp0').[ov]) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd (spec_run act sp0  input )).[ov]
              = (snd (spec_run act sp0' input')).[ov]) ->
    first_done act input  resp  ss0  N ->
    first_done act input' resp' ss0' N' ->
    N = N'.
  Proof.
    intros Halign Hlen Hpl Hdsz Hgsz Hsr Hsr' Hipc Hipc' Hipub Hpre Hpost HN HN'.
    exact (latency_noninterference act a_idx input input' resp resp'
             sp0 sp0' ss0 ss0' N N' Halign Hlen Hpl Hdsz Hgsz Hsr Hsr'
             Hipc Hipc' Hipub Hpre Hpost HN HN').
  Qed.

  (* B1, the campaign's headline in observable terms: the cycle count depends
     only on the action, the input, and the outputs before and after. *)
  Corollary latency_from_outputs (act: tfs_action sched) (a_idx: a_index)
      (input input': input_t) (resp resp': nat -> resp_val)
      (sp0 sp0': src_sys_state) (ss0 ss0': sched_sys_state) (N N': nat) :
    act_idx_aligned ctx cost_limit act a_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    plumbing_not_root act ->
    drives_sized act ->
    guards_sized act ->
    start_rel ctx cost_limit sp0  ss0  ->
    start_rel ctx cost_limit sp0' ss0' ->
    Definitions.ip_contract ctx cost_limit act input  resp  ss0  ->
    Definitions.ip_contract ctx cost_limit act input' resp' ss0' ->
    (forall v,  tfs_spec_inputs_class  ctx v  = Public -> input v = input' v) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd sp0).[ov] = (snd sp0').[ov]) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd (spec_run act sp0  input )).[ov]
              = (snd (spec_run act sp0' input')).[ov]) ->
    first_done act input  resp  ss0  N ->
    first_done act input' resp' ss0' N' ->
    N = N'.
  Proof.
    intros Halign Hlen Hpl Hdsz Hgsz Hsr Hsr' Hipc Hipc' Hipub Hpre Hpost HN HN'.
    exact (latency_noninterference act a_idx input input' resp resp'
             sp0 sp0' ss0 ss0' N N' Halign Hlen Hpl Hdsz Hgsz Hsr Hsr'
             Hipc Hipc' Hipub Hpre Hpost HN HN').
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The IPR emulator.  It sees only the inputs, the current outputs and   *)
  (* the specification: outputs hold until the action completes, then take *)
  (* the specification's values.  The one free variable is the cycle count *)
  (* N, which [latency_from_outputs] pins to public data.                  *)
  (* ------------------------------------------------------------------- *)

  Lemma first_done_exists (act: tfs_action sched) (sp0: src_sys_state)
      (ss0: sched_sys_state) (input: input_t) (resp: nat -> resp_val) :
    start_rel ctx cost_limit sp0 ss0 ->
    Definitions.ip_contract ctx cost_limit act input resp ss0 ->
    exists N, first_done act input resp ss0 N.
  Proof.
    intros Hstart Hipc.
    destruct (variable_scheduler_correct ctx cost_limit act sp0 ss0 input resp
                Hstart Hipc) as [N [Hbefore [Hdone _]]].
    exists N. split; assumption.
  Qed.

  Theorem emulator_correct (act: tfs_action sched) (sp0: src_sys_state)
      (ss0: sched_sys_state) (input: input_t) (resp: nat -> resp_val) (N: nat) :
    start_rel ctx cost_limit sp0 ss0 ->
    Definitions.ip_contract ctx cost_limit act input resp ss0 ->
    first_done act input resp ss0 N ->
    forall k, k <= N ->
      forall ov, (snd (ss_run k act input resp ss0)).[ov]
               = emulate (snd sp0) (snd (spec_run act sp0 input)) N k ov.
  Proof.
    intros Hstart Hipc [Hdone Hbefore] k Hk ov. unfold Definitions.emulate.
    destruct (Nat.ltb_spec k N) as [Hlt | Hge].
    - assert (Hnd : forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input resp ss0))
        by (intros i Hi; apply Hbefore; lia).
      rewrite (out_run_stable act ss0 input resp ov k Hnd).
      rewrite (proj1 Hstart). reflexivity.
    - assert (HkN : k = N) by lia. subst k.
      destruct (scheduler_done_correct ctx cost_limit act sp0 ss0 input resp N
                  Hstart Hipc Hbefore Hdone) as [_ Hout].
      rewrite Hout. reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The latency function [L] itself, and its two properties: it is the    *)
  (* completion cycle, and it depends only on publicly visible data.       *)
  (* ------------------------------------------------------------------- *)

  Lemma done_test_true (act: tfs_action sched) (input: input_t)
      (resp: nat -> resp_val) (ss0: sched_sys_state) (k: nat) :
    done_test act input resp ss0 k = true <-> ss_done (ss_run k act input resp ss0).
  Proof.
    unfold done_test.
    destruct (done_set_dec ctx cost_limit (ss_run k act input resp ss0)) as [Hd | Hd].
    - split; [ intros _; exact Hd | reflexivity ].
    - split; [ discriminate | intro Hc; contradiction ].
  Qed.

  Theorem L_first_done (act: tfs_action sched) (sp0: src_sys_state)
      (ss0: sched_sys_state) (input: input_t) (resp: nat -> resp_val) :
    start_rel ctx cost_limit sp0 ss0 ->
    first_done act input resp ss0 (L act input resp ss0).
  Proof.
    intro Hstart.
    destruct (done_by_settle_bound ctx cost_limit act sp0 ss0 input resp Hstart)
      as [N [HNle HNdone]].
    destruct (first_true_spec (done_test act input resp ss0)
                (S (settle_bound ctx cost_limit act)) 0 N
                (Nat.le_0_l N) ltac:(lia)
                (proj2 (done_test_true act input resp ss0 N) HNdone)) as [H1 H2].
    split.
    - exact (proj1 (done_test_true act input resp ss0 _) H1).
    - intros i Hi Hc.
      pose proof (H2 i (Nat.le_0_l i) Hi) as Hfalse.
      rewrite (proj2 (done_test_true act input resp ss0 i) Hc) in Hfalse.
      discriminate Hfalse.
  Qed.

  (* [L] is a function of the action and the PUBLIC data -- the public inputs
     and the public outputs before and after.  Never of the secret state, and
     never of a secret input.  The IP answers are free: each run carries its
     own, constrained only by its own datasheet. *)
  Corollary L_public (act: tfs_action sched) (a_idx: a_index)
      (input input': input_t) (resp resp': nat -> resp_val)
      (sp0 sp0': src_sys_state) (ss0 ss0': sched_sys_state) :
    act_idx_aligned ctx cost_limit act a_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    plumbing_not_root act ->
    drives_sized act ->
    guards_sized act ->
    start_rel ctx cost_limit sp0  ss0  ->
    start_rel ctx cost_limit sp0' ss0' ->
    Definitions.ip_contract ctx cost_limit act input  resp  ss0  ->
    Definitions.ip_contract ctx cost_limit act input' resp' ss0' ->
    (* Public data only -- see [obs_eq_pub_eq]. *)
    (forall v,  tfs_spec_inputs_class  ctx v  = Public -> input v = input' v) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd sp0).[ov] = (snd sp0').[ov]) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd (spec_run act sp0  input )).[ov]
              = (snd (spec_run act sp0' input')).[ov]) ->
    L act input resp ss0 = L act input' resp' ss0'.
  Proof.
    intros Halign Hlen Hpl Hdsz Hgsz Hst Hst' Hipc Hipc' Hipub Hpre Hpost.
    exact (latency_from_outputs act a_idx input input' resp resp'
             sp0 sp0' ss0 ss0' _ _
             Halign Hlen Hpl Hdsz Hgsz Hst Hst' Hipc Hipc' Hipub Hpre Hpost
             (L_first_done act sp0  ss0  input  resp  Hst)
             (L_first_done act sp0' ss0' input' resp' Hst')).
  Qed.

  Corollary emulator_correct_L (act: tfs_action sched) (sp0: src_sys_state)
      (ss0: sched_sys_state) (input: input_t) (resp: nat -> resp_val) :
    start_rel ctx cost_limit sp0 ss0 ->
    Definitions.ip_contract ctx cost_limit act input resp ss0 ->
    forall k, k <= L act input resp ss0 ->
      forall ov, (snd (ss_run k act input resp ss0)).[ov]
               = emulate (snd sp0) (snd (spec_run act sp0 input))
                   (L act input resp ss0) k ov.
  Proof.
    intros Hstart Hipc.
    exact (emulator_correct act sp0 ss0 input resp (L act input resp ss0)
             Hstart Hipc (L_first_done act sp0 ss0 input resp Hstart)).
  Qed.
  (* ---- THE ATTACKER'S CLOCK IS THE RUN'S ---- *)

  (* A slot of [bufs] is indexed in the action's buffer table, so the compiled
     reference reads that register rather than falling through. *)
  Lemma buf_slot_indexed (act: tfs_action sched) (a_idx: a_index)
      (bufs: list (nid_t * (nat * sz_t))) (n j jsz: nat) :
    act_idx_aligned ctx cost_limit act a_idx ->
    (forall e, List.In e bufs ->
       List.In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
    BitsToLists.list_assoc bufs n = Some (j, jsz) ->
    exists n_idx,
      index_of_nat
        (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) j
      = Some n_idx.
  Proof.
    intros Halign Hsub Hla.
    assert (Hin_gsi : List.In (n, (j, jsz))
              (get_sizes_and_idx ctx (build_dfg ctx act)
                 (require_buffer ctx (build_dfg ctx act)
                    (calc_target_cycle cost_limit
                       (calc_backward_cost ctx cost_limit (build_dfg ctx act))))))
      by (rewrite <- (buffer_slot_eq ctx cost_limit act a_idx Halign);
          apply Hsub, wla_in, Hla).
    assert (Hlt : j < length
              (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])).
    { rewrite (buffer_slot_eq ctx cost_limit act a_idx Halign), gsi_length.
      exact (gsi_idx_bound ctx _ _ n j jsz Hin_gsi). }
    exact (index_of_nat_bounded Hlt).
  Qed.


  (* [avalid] is the validity bit the run carries, where the attacker's vector
     matches the registers and its values are the run's.  The two premises are
     [compile_subst]'s: the reference keeps the sample buffers, so a table the
     gate is read against must keep them at every id the walk reaches. *)
  Definition avalid_agrees (act: tfs_action sched) (a_idx: a_index)
      (vals: known (build_dfg ctx act)) (vv: vvec)
      (ss: sched_sys_state) (input: sched_input_t)
      (bufs: list (nid_t * (nat * sz_t))) : Prop :=
    forall fuel (pi: list lit) n,
      (forall x, x < n ->
         BitsToLists.list_assoc bufs x = None ->
         BitsToLists.list_assoc (sample_bufs ctx cost_limit act a_idx) x = None) ->
      (forall x m msz, x < n ->
         BitsToLists.list_assoc bufs x = Some (m, msz) ->
         is_sample_of ctx cost_limit act x = true ->
         BitsToLists.list_assoc (sample_bufs ctx cost_limit act a_idx) x
           = Some (m, msz)) ->
      pi_holds act a_idx input pi ss ->
      path_ok act a_idx ss input pi ->
      1 <= n ->
      n < length (graph (build_dfg ctx act)) ->
      n < fuel ->
      (avalid act vals vv bufs fuel pi n = true
       <-> eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                         (build_dfg ctx act) n bufs)) ss input = Bits.ones 1).

  Theorem avalid_correct (act: tfs_action sched) (a_idx: a_index)
      (vals: known (build_dfg ctx act)) (vv: vvec)
      (ss: sched_sys_state) (input: sched_input_t)
      (bufs: list (nid_t * (nat * sz_t))) :
    act_idx_aligned ctx cost_limit act a_idx ->
    valid_settled ctx cost_limit act a_idx ss input ->
    valid_refs ctx cost_limit act a_idx ss input ->
    (forall e, List.In e bufs ->
       List.In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
    vv_matches a_idx vv ss bufs ->
    vals_sound act a_idx vals ss input ->
    selectors_extractable act a_idx vals ss input ->
    avalid_agrees act a_idx vals vv ss input bufs.
  Proof.
    intros Halign Hvs Hrf Hsub Hvv Hvals Hsel fuel.
    induction fuel as [| fuel IH];
      intros pi n Hsam_sub Hsam_same Hpi Hpok Hn1 Hnlen Hnfuel; [ lia | ].
    (* the recursive step, at the ids this node can reach *)
    assert (Hone : forall x p, 1 <= x -> x < n ->
              pi_holds act a_idx input p ss ->
              path_ok act a_idx ss input p ->
              (avalid act vals vv bufs fuel p x = true
               <-> eval1 (snd (compile_dfg_expr_at ctx bneeds p fuel a_idx
                                 (build_dfg ctx act) x bufs)) ss input
                   = Bits.ones 1))
      by (intros x p Hx1 Hx2 Hp Hpo;
          exact (IH p x
                   ltac:(intros y Hy; exact (Hsam_sub y ltac:(lia)))
                   ltac:(intros y my mszy Hy; exact (Hsam_same y my mszy ltac:(lia)))
                   Hp Hpo Hx1 ltac:(lia) ltac:(lia))).
    destruct (BitsToLists.list_assoc bufs n) as [[j jsz] |] eqn:Hla.
    { destruct (buf_slot_indexed act a_idx bufs n j jsz Halign Hsub Hla)
        as [n_idx Hidx].
      cbn [avalid compile_dfg_expr_aux]. rewrite Hla, Hidx. cbv beta iota.
      destruct (op (nth n (graph (build_dfg ctx act))
                      {| nid := 0; op := DFG_Empty; sz := 0 |}));
        cbn [snd]; rewrite eval1_svar_v; exact (Hvv n j jsz n_idx Hla Hidx). }
    cbn [avalid compile_dfg_expr_aux]. rewrite Hla. cbv beta iota.
    unfold Definitions.node_op.
    assert (Hnode_in : List.In (nth n (graph (build_dfg ctx act))
                                  {| nid := 0; op := DFG_Empty; sz := 0 |})
                         (graph (build_dfg ctx act)))
      by (apply nth_In; exact Hnlen).
    assert (Hrange : forall x,
              List.In x (get_args ctx (nth n (graph (build_dfg ctx act))
                                         {| nid := 0; op := DFG_Empty; sz := 0 |})) ->
              1 <= x /\ x < n)
      by (intros x Hx; exact (node_args_range ctx cost_limit act n Hn1 Hnlen x Hx)).
    pose proof (wfg_build_dfg ctx cost_limit act _ Hnode_in) as Hfg.
    unfold node_args_sz in Hfg.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa
         | dp darg den | sp stok sen | ja jb | ] eqn:Hop.
    - split; [ intros _ | reflexivity ]. reflexivity.
    - split; [ intros _ | reflexivity ]. reflexivity.
    - destruct v; (split; [ intros _ | reflexivity ]); reflexivity.
    - destruct (Hrange arg ltac:(unfold get_args; rewrite Hop; left; reflexivity))
        as [Ha1 Ha2].
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  arg bufs) as [ae ve] eqn:E1.
      pose proof (Hone arg pi Ha1 Ha2 Hpi Hpok) as Ha. rewrite E1 in Ha.
      cbn [snd] in Ha |- *. exact Ha.
    - destruct (Hrange a1 ltac:(unfold get_args; rewrite Hop; left; reflexivity))
        as [Hb1 Hb2].
      destruct (Hrange a2 ltac:(unfold get_args; rewrite Hop; right; left; reflexivity))
        as [Hd1 Hd2].
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  a1 bufs) as [a1e v1e] eqn:E1.
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  a2 bufs) as [a2e v2e] eqn:E2.
      pose proof (Hone a1 pi Hb1 Hb2 Hpi Hpok) as Hx1. rewrite E1 in Hx1.
      pose proof (Hone a2 pi Hd1 Hd2 Hpi Hpok) as Hx2. rewrite E2 in Hx2.
      cbn [snd] in Hx1, Hx2 |- *. rewrite valid_and_eval.
      exact (and1_iff _ _ _ _ Hx1 Hx2).
    - destruct (Hrange arg ltac:(unfold get_args; rewrite Hop; left; reflexivity))
        as [Ha1 Ha2].
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  arg bufs) as [ae ve] eqn:E1.
      pose proof (Hone arg pi Ha1 Ha2 Hpi Hpok) as Ha. rewrite E1 in Ha.
      cbn [snd] in Ha |- *. exact Ha.
    - (* a phi: critical reads both arms, selecting reads the condition *)
      destruct (Hrange cnd ltac:(unfold get_args; rewrite Hop; left; reflexivity))
        as [Hc1 Hc2].
      destruct (Hrange tid ltac:(unfold get_args; rewrite Hop; right; left; reflexivity))
        as [Ht1 Ht2].
      destruct (Hrange eid ltac:(unfold get_args; rewrite Hop; right; right; left; reflexivity))
        as [He1 He2].
      destruct Hfg as [Hf1 [_ _]].
      destruct (wsz_node_sz ctx cost_limit act cnd 1 Hf1) as [Hclen Hcsz].
      destruct (phi_crit (get_tainted ctx (build_dfg ctx act))
                  (decl_facts ctx (build_dfg ctx act)) cnd pi) eqn:Hcrit;
        cbn [phi_path]; cbv beta iota.
      + destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    cnd bufs) as [ce cv] eqn:Ec.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    tid bufs) as [te tv] eqn:Et.
        destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    eid bufs) as [ee ev] eqn:Ee.
        pose proof (Hone cnd pi Hc1 Hc2 Hpi Hpok) as Hc. rewrite Ec in Hc.
        pose proof (Hone tid pi Ht1 Ht2 Hpi Hpok) as Ht. rewrite Et in Ht.
        pose proof (Hone eid pi He1 He2 Hpi Hpok) as He. rewrite Ee in He.
        cbn [snd] in Hc, Ht, He |- *. rewrite !valid_and_eval.
        exact (and1_iff _ _ _ _ (and1_iff _ _ _ _ Ht He) Hc).
      + destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                    cnd bufs) as [ce cv] eqn:Ec.
        destruct (compile_dfg_expr_at ctx bneeds ((cnd, true) :: pi) fuel a_idx
                    (build_dfg ctx act) tid bufs) as [te tv] eqn:Et.
        destruct (compile_dfg_expr_at ctx bneeds ((cnd, false) :: pi) fuel a_idx
                    (build_dfg ctx act) eid bufs) as [ee ev] eqn:Ee.
        pose proof (Hone cnd pi Hc1 Hc2 Hpi Hpok) as Hc. rewrite Ec in Hc.
        cbn [snd] in Hc |- *. rewrite valid_and_eval.
        destruct (avalid act vals vv bufs fuel pi cnd) eqn:Hav; cbn [andb].
        * (* the condition has settled, so the arm it names is the one read *)
          assert (Hcv : eval1 cv ss input = Bits.ones 1) by (apply Hc; reflexivity).
          rewrite Hcv, Bits.and_ones_l.
          assert (Hvalc : eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                            (build_dfg ctx act) cnd bufs)) ss input = Bits.ones 1)
            by (rewrite Ec; cbn [snd]; exact Hcv).
          pose proof (compile_subst_valid_gen_at ctx cost_limit act a_idx ss input
                        Halign Hvs bufs Hsub fuel cnd 1 pi
                        ltac:(intros y Hy; exact (Hsam_sub y ltac:(lia)))
                        ltac:(intros y my mszy Hy; exact (Hsam_same y my mszy ltac:(lia)))
                        Hc1 Hclen ltac:(lia) (eq_sym Hcsz) Hvalc) as S1.
          rewrite Ec in S1. cbn [fst] in S1.
          rewrite (compile_fst_pi_irrel ctx cost_limit _ _ a_idx _
                     (sample_bufs ctx cost_limit act a_idx) fuel cnd pi []) in S1.
          rewrite (compile_fuel_irrel ctx cost_limit act a_idx
                     (sample_bufs ctx cost_limit act a_idx) cnd Hc1 Hclen
                     fuel (length (graph (build_dfg ctx act))) ltac:(lia) Hclen)
            in S1.
          assert (Hrvc : rvalid act a_idx pi cnd ss input = Bits.ones 1).
          { rewrite <- (compile_fuel_irrel_gen ctx cost_limit act a_idx
                          (sample_bufs ctx cost_limit act a_idx) _ _ cnd Hc1 Hclen
                          fuel (length (graph (build_dfg ctx act))) pi
                          ltac:(lia) Hclen).
            exact (compile_subst_ref_valid_gen_at ctx cost_limit act a_idx ss input
                     Halign Hvs Hrf bufs Hsub fuel cnd pi
                     ltac:(intros y Hy; exact (Hsam_sub y ltac:(lia)))
                     ltac:(intros y my mszy Hy; exact (Hsam_same y my mszy ltac:(lia)))
                     Hc1 Hclen ltac:(lia) Hvalc). }
          destruct (Hsel n cnd tid eid pi
                      ltac:(unfold Definitions.node_op; rewrite Hop; reflexivity)
                      Hcrit Hpi Hpok Hrvc) as [v Hb].
          rewrite Hb. cbn beta iota.
          pose proof (Hvals cnd v pi Hb Hpi Hrvc) as Hcl.
          remember (nonzero v) as b eqn:Hbdef.
          assert (Hbv : nval ctx cost_limit act a_idx ss input 1 cnd
                        = Definitions.bit_of b).
          { subst b.
            exact (bit_of_nonzero
                     (fun w => nval ctx cost_limit act a_idx ss input w cnd)
                     _ v Hcsz Hcl). }
          assert (Hce : eval1 ce ss input = Definitions.bit_of b).
          { rewrite S1. unfold nval, node_ref_expr in Hbv. exact Hbv. }
          (* the arm the condition names is read under the extended path, and
             that path holds: [b] IS the condition's bit *)
          pose proof (pi_holds_cons act a_idx input cnd b pi ss Hpi Hbv) as Hpib.
          assert (Hpokb : path_ok act a_idx ss input ((cnd, b) :: pi)).
          { split; [ exact Hpok | split; [ | split; [ exact Hpi | exact Hrvc ] ] ].
            exists n, tid, eid. split; [ unfold Definitions.node_op; exact Hop | exact Hcrit ]. }
          assert (Hcase : (tv = tf_const 1 /\ ev = tf_const 1)
                          \/ valid_expr_if ctx bneeds ce tv ev
                             = tf_expr_if ce tv ev).
          { unfold valid_expr_if.
            destruct tv as [vt| | | | | |]; try (right; reflexivity).
            destruct vt as [|[|vt]]; try (right; reflexivity).
            destruct ev as [vee| | | | | |]; try (right; reflexivity).
            destruct vee as [|[|vee]]; try (right; reflexivity).
            left; split; reflexivity. }
          destruct Hcase as [[Htc Hec] | Hcs].
          -- (* both arms are unconditionally valid *)
             rewrite Htc, Hec. cbn [valid_expr_if].
             split; [ intros _; reflexivity | intros _ ].
             destruct b.
             ++ pose proof (Hone tid ((cnd, true) :: pi) Ht1 Ht2 Hpib Hpokb) as Ht.
                rewrite Et in Ht. cbn [snd] in Ht. apply Ht.
                rewrite Htc. reflexivity.
             ++ pose proof (Hone eid ((cnd, false) :: pi) He1 He2 Hpib Hpokb) as He.
                rewrite Ee in He. cbn [snd] in He. apply He.
                rewrite Hec. reflexivity.
          -- rewrite Hcs. cbn [tf_eval_expr]. rewrite Hce.
             destruct b.
             ++ match goal with
                | |- context [@beq_dec ?T ?E ?a ?z] =>
                    destruct (@beq_dec T E a z) eqn:Hbd
                end.
                ** exfalso. apply beq_dec_iff in Hbd.
                   exact (ones1_neq_zero Hbd).
                ** pose proof (Hone tid ((cnd, true) :: pi) Ht1 Ht2 Hpib Hpokb) as Ht.
                   rewrite Et in Ht. cbn [snd] in Ht. exact Ht.
             ++ match goal with
                | |- context [@beq_dec ?T ?E ?a ?z] =>
                    replace (@beq_dec T E a z) with true
                      by (symmetry; apply beq_dec_iff; reflexivity)
                end.
                pose proof (Hone eid ((cnd, false) :: pi) He1 He2 Hpib Hpokb) as He.
                rewrite Ee in He. cbn [snd] in He. exact He.
        * (* the condition has not settled, and nothing downstream has *)
          assert (Hcz : eval1 cv ss input = Bits.zero).
          { destruct (SchedulerSimulationLemmas.bits1_cases (eval1 cv ss input))
              as [Ho | Hz]; [ | exact Hz ].
            exfalso. discriminate (proj2 Hc Ho). }
          rewrite Hcz, bits1_and_zero_l.
          split; [ discriminate | intro Hc0 ].
          exfalso. exact (ones1_neq_zero (eq_sym Hc0)).
    - destruct (Hrange sa ltac:(unfold get_args; rewrite Hop; left; reflexivity))
        as [Ha1 Ha2].
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  sa bufs) as [ae ve] eqn:E1.
      pose proof (Hone sa pi Ha1 Ha2 Hpi Hpok) as Ha. rewrite E1 in Ha.
      cbn [snd] in Ha |- *. exact Ha.
    - (* a drive waits on its argument AND on every literal of its guard *)
      destruct (Hrange darg ltac:(unfold get_args; rewrite Hop; left; reflexivity))
        as [Ha1 Ha2].
      assert (Hfold : forall (gs: list lit) (bb: bool)
                        (base: @tf_expr (tfs_states sched) (tfs_inputs sched) o_var),
                (forall l, List.In l gs -> 1 <= fst l /\ fst l < n) ->
                (bb = true <-> eval1 base ss input = Bits.ones 1) ->
                (fold_right (fun l acc =>
                   andb (avalid act vals vv bufs fuel pi (fst l)) acc) bb gs = true
                 <-> eval1 (fold_right (fun l acc =>
                       valid_expr_and ctx bneeds
                         (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                                 (build_dfg ctx act) (fst l) bufs)) acc)
                       base gs) ss input = Bits.ones 1)).
      { induction gs as [| l rest IHgs]; intros bb base Hr Hb;
          cbn [fold_right]; [ exact Hb | ].
        rewrite valid_and_eval.
        destruct (Hr l (or_introl eq_refl)) as [Hl1 Hl2].
        exact (and1_iff _ _ _ _ (Hone (fst l) pi Hl1 Hl2 Hpi Hpok)
                 (IHgs bb base ltac:(intros l' Hl'; apply Hr; right; exact Hl') Hb)). }
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  darg bufs) as [ae ve] eqn:E1.
      pose proof (Hone darg pi Ha1 Ha2 Hpi Hpok) as Ha. rewrite E1 in Ha.
      cbn [snd] in Ha |- *.
      apply Hfold; [ | exact Ha ].
      intros l Hl. apply Hrange.
      unfold get_args; rewrite Hop; right; apply in_map; exact Hl.
    - destruct (Hrange stok ltac:(unfold get_args; rewrite Hop; left; reflexivity))
        as [Ha1 Ha2].
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  stok bufs) as [ae ve] eqn:E1.
      pose proof (Hone stok pi Ha1 Ha2 Hpi Hpok) as Ha. rewrite E1 in Ha.
      cbn [snd] in Ha |- *. exact Ha.
    - destruct (Hrange ja ltac:(unfold get_args; rewrite Hop; left; reflexivity))
        as [Hja1 Hja2].
      destruct (Hrange jb ltac:(unfold get_args; rewrite Hop; right; left; reflexivity))
        as [Hjb1 Hjb2].
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  ja bufs) as [ae ve] eqn:E1.
      destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act)
                  jb bufs) as [be vb] eqn:E2.
      pose proof (Hone ja pi Hja1 Hja2 Hpi Hpok) as Hxa. rewrite E1 in Hxa.
      pose proof (Hone jb pi Hjb1 Hjb2 Hpi Hpok) as Hxb. rewrite E2 in Hxb.
      cbn [snd] in Hxa, Hxb |- *. rewrite valid_and_eval.
      exact (and1_iff _ _ _ _ Hxa Hxb).
    - split; [ discriminate | intro H0 ].
      exfalso. exact (ones1_neq_zero (eq_sym H0)).
  Qed.

  (* The arguments of a settled phi: the condition always, and the arm the
     condition names. *)
  Lemma phi_args_settled (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t) (n c t e: nid_t) :
    Definitions.node_op ctx cost_limit act n = DFG_Phi c t e ->
    1 <= c -> 1 <= t -> 1 <= e ->
    n < length (graph (build_dfg ctx act)) ->
    settled_at act a_idx ss input n ->
    settled_at act a_idx ss input c
    /\ (eval1 (node_ref_expr ctx cost_limit act a_idx c) ss input <> Bits.zero ->
        settled_at act a_idx ss input t)
    /\ (eval1 (node_ref_expr ctx cost_limit act a_idx c) ss input = Bits.zero ->
        settled_at act a_idx ss input e).
  Proof.
    intros Hop Hc1 Ht1 He1 Hnlen [pi [Hpi Hv]].
    destruct (phi_crit (get_tainted ctx (build_dfg ctx act))
                (decl_facts ctx (build_dfg ctx act)) c pi) eqn:Hcrit.
    - destruct (nrv_peel_phi_crit ctx cost_limit act a_idx n c t e pi ss input
                  Hop Hcrit Hc1 Ht1 He1 Hnlen Hv) as [Hc [Ht He]].
      split; [ exists pi; split; [ exact Hpi | exact Hc ] | ].
      split; intros _;
        [ exists pi; split; [ exact Hpi | exact Ht ]
        | exists pi; split; [ exact Hpi | exact He ] ].
    - destruct (nrv_peel_phi_sel ctx cost_limit act a_idx n c t e pi ss input
                  Hop Hcrit Hc1 Ht1 He1 Hnlen Hv) as [Hc [Ht He]].
      split; [ exists pi; split; [ exact Hpi | exact Hc ] | ].
      split.
      + intro Hnz. exists ((c, true) :: pi). split; [ | exact (Ht Hnz) ].
        apply (pi_holds_cons act a_idx input c true pi ss
                 Hpi).
        unfold nval. exact (proj1 (bits1_nonzero_ones _) Hnz).
      + intro Hz. exists ((c, false) :: pi). split; [ | exact (He Hz) ].
        apply (pi_holds_cons act a_idx input c false pi ss
                 Hpi).
        unfold nval. exact Hz.
  Qed.

  (* ---- THE SHADOW MACHINE RUNS WITH THE DESIGN ---- *)

  Lemma nth_map_lt {A B} (f: A -> B) (l: list A) (j: nat) (da: A) (db: B) :
    j < length l -> nth j (map f l) db = f (nth j l da).
  Proof.
    intro Hj.
    rewrite (nth_indep (map f l) db (f da))
      by (rewrite map_length; exact Hj).
    apply map_nth.
  Qed.

  (* Slot [n_idx] of a step is the step of slot [n_idx]: the shadow lists are
     indexed by the slot number, which is the entry's position. *)
  Lemma sstep_slot (act: tfs_action sched) (a_idx: a_index)
      (vals: known (build_dfg ctx act)) (st: Definitions.sstate)
      (n_idx : Vect.index (length (nth (index_to_nat a_idx) bneeds []))) :
    slot_valid (fst (sstep act a_idx vals st)) (index_to_nat n_idx)
      = fst (slot_step act a_idx vals st
               (nth (index_to_nat n_idx) (nth (index_to_nat a_idx) bneeds [])
                  (0, (0, 0))))
    /\ nth (index_to_nat n_idx) (snd (sstep act a_idx vals st)) 0
      = snd (slot_step act a_idx vals st
               (nth (index_to_nat n_idx) (nth (index_to_nat a_idx) bneeds [])
                  (0, (0, 0)))).
  Proof.
    unfold Definitions.sstep, Definitions.slot_valid. cbn [fst snd].
    rewrite !map_map. split.
    - apply (nth_map_lt (fun e => fst (slot_step act a_idx vals st e))
               (nth (index_to_nat a_idx) bneeds []) (index_to_nat n_idx)
               (0, (0, 0)) false).
      apply index_to_nat_bounded.
    - apply (nth_map_lt (fun e => snd (slot_step act a_idx vals st e))
               (nth (index_to_nat a_idx) bneeds []) (index_to_nat n_idx)
               (0, (0, 0)) 0).
      apply index_to_nat_bounded.
  Qed.

  (* The slot stored at position [n_idx] is numbered [n_idx], so the shadow
     lists are indexed by position and by slot number alike. *)
  Lemma slot_idx_at (act: tfs_action sched) (a_idx: a_index) (m: nat) :
    act_idx_aligned ctx cost_limit act a_idx ->
    m < length (nth (index_to_nat a_idx) bneeds []) ->
    fst (snd (nth m (nth (index_to_nat a_idx) bneeds []) (0, (0, 0)))) = m.
  Proof.
    intros Halign Hm.
    rewrite (buffer_slot_eq ctx cost_limit act a_idx Halign) in Hm |- *.
    rewrite gsi_length in Hm.
    exact (gsi_idx_at ctx _ _ m Hm).
  Qed.

  (* THE SHADOW MACHINE IS THE REGISTERS: at every pre-done cycle the attacker's
     validity bits are the design's, and its counts are the stall counters.
     Values never enter, so this is the whole of what the latency reads. *)
  Theorem srun_matches (act: tfs_action sched) (a_idx: a_index)
      (vals: known (build_dfg ctx act))
      (input: input_t) (resp: nat -> resp_val) (ss0: sched_sys_state) :
    act_idx_aligned ctx cost_limit act a_idx ->
    (forall x, Definitions.zeroed_at_start ctx cost_limit x ->
       (fst ss0).[x] = Bits.zero) ->
    (forall k, (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input resp ss0)) ->
       selectors_extractable act a_idx vals (ss_run k act input resp ss0)
         (sched_input ctx cost_limit input (resp k))) ->
    (forall k, (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input resp ss0)) ->
       vals_sound act a_idx vals (ss_run k act input resp ss0)
         (sched_input ctx cost_limit input (resp k))) ->
    forall k,
      (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input resp ss0)) ->
      forall n_idx,
        (slot_valid (fst (srun act a_idx vals k)) (index_to_nat n_idx) = true
         <-> (fst (ss_run k act input resp ss0)).[tf_dfg_v a_idx n_idx]
             = Bits.ones 1)
        /\ (forall l,
              stall_lat_of ctx cost_limit act (vreg_nid ctx cost_limit a_idx n_idx)
                = Some l ->
              nth (index_to_nat n_idx) (snd (srun act a_idx vals k)) 0
              = Bits.to_nat
                  ((fst (ss_run k act input resp ss0)).[tf_dfg_b a_idx n_idx])
              /\ nth (index_to_nat n_idx) (snd (srun act a_idx vals k)) 0
                 <= pred l).
  Proof.
    intros Halign Hz Hsel Hvals.
    induction k as [| k IH]; intros Hnd n_idx.
    { cbn [Definitions.srun run_n].
      unfold Definitions.sstart, Definitions.slot_valid. cbn [fst snd].
      rewrite !nth_repeat. split.
      - rewrite (Hz (tf_dfg_v a_idx n_idx) I). split; [ discriminate | ].
        intro Hc. exfalso. exact (ones1_neq_zero (eq_sym Hc)).
      - intros l _. rewrite (Hz (tf_dfg_b a_idx n_idx) I).
        split; [ | lia ].
        change (@Bits.zero (ss_sz (tf_dfg_b a_idx n_idx)))
          with (Bits.of_nat (ss_sz (tf_dfg_b a_idx n_idx)) 0).
        symmetry. apply Bits.to_nat_of_nat. unfold pow2. lia. }
    assert (Hndk : forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input resp ss0))
      by (intros i Hi; apply Hnd; lia).
    assert (Hs : ~ ss_done (ss_step act (ss_run k act input resp ss0)
                              (sched_input ctx cost_limit input (resp k))))
      by (apply (Hnd (S k)); lia).
    change (ss_run (S k) act input resp ss0)
      with (ss_step act (ss_run k act input resp ss0)
              (sched_input ctx cost_limit input (resp k))).
    cbn [Definitions.srun].
    destruct (vreg_nid_node_range ctx cost_limit act a_idx n_idx Halign)
      as [Hn1 Hnlen].
    unfold vreg_nid in Hn1, Hnlen.
    pose proof (buffer_after_cycle ctx cost_limit act a_idx n_idx
                  (ss_run k act input resp ss0)
                  (sched_input ctx cost_limit input (resp k)) Halign Hs) as Hb.
    cbv zeta in Hb. destruct Hb as [Hbb Hvv].
    destruct (sstep_slot act a_idx vals (srun act a_idx vals k) n_idx)
      as [Hsv Hsc].
    (* the gate, which is the whole of the attacker's work *)
    assert (Hgate : slot_gate act a_idx vals (fst (srun act a_idx vals k))
                      (fst (nth (index_to_nat n_idx)
                              (nth (index_to_nat a_idx) bneeds []) (0, (0, 0))))
                    = true
                    <-> eval1 (snd (compile_dfg_expr ctx bneeds
                          (length (graph (build_dfg ctx act))) a_idx
                          (build_dfg ctx act)
                          (fst (nth (index_to_nat n_idx)
                                  (nth (index_to_nat a_idx) bneeds []) (0, (0, 0))))
                          (filter (fun '(b_nid, _) => negb (Nat.eqb b_nid
                              (fst (nth (index_to_nat n_idx)
                                      (nth (index_to_nat a_idx) bneeds [])
                                      (0, (0, 0))))))
                             (nth (index_to_nat a_idx) bneeds []))))
                        (ss_run k act input resp ss0)
                        (sched_input ctx cost_limit input (resp k))
                        = Bits.ones 1).
    { destruct (SchedulerRoundTrip.gate_table_sample_bufs ctx cost_limit act a_idx
                  (fst (nth (index_to_nat n_idx)
                          (nth (index_to_nat a_idx) bneeds []) (0, (0, 0))))
                  Halign) as [Hsub1 Hsame1].
      destruct (valid_settled_run ctx cost_limit act a_idx input resp ss0 k Halign
                  (fun q => Hz (tf_dfg_v a_idx q) I)) as [_ [Hrf Hvs]].
      assert (Hvvm : vv_matches a_idx (fst (srun act a_idx vals k))
                       (ss_run k act input resp ss0)
                       (Definitions.gate_bufs ctx cost_limit a_idx
                          (fst (nth (index_to_nat n_idx)
                                  (nth (index_to_nat a_idx) bneeds [])
                                  (0, (0, 0)))))).
      { intros m j jsz m_idx Hla Hidx.
        rewrite <- (index_to_nat_of_nat j m_idx Hidx).
        exact (proj1 (IH Hndk m_idx)). }
      unfold Definitions.slot_gate, Definitions.gate_bufs in Hvvm |- *.
      exact (avalid_correct act a_idx vals (fst (srun act a_idx vals k))
               (ss_run k act input resp ss0)
               (sched_input ctx cost_limit input (resp k))
               (filter (fun '(b, _) => negb (Nat.eqb b
                   (fst (nth (index_to_nat n_idx)
                           (nth (index_to_nat a_idx) bneeds []) (0, (0, 0))))))
                  (nth (index_to_nat a_idx) bneeds []))
               Halign Hvs Hrf
               (fun e He => proj1 (proj1 (filter_In _ e _) He))
               Hvvm (Hvals k Hndk) (Hsel k Hndk)
               (length (graph (build_dfg ctx act))) [] _ Hsub1 Hsame1
               (pi_holds_nil act a_idx _ _) I Hn1 Hnlen Hnlen). }
    (* the gate as the design's own zero test reads it *)
    assert (Hgz : (if beq_dec (eval1 (snd (compile_dfg_expr ctx bneeds
                        (length (graph (build_dfg ctx act))) a_idx
                        (build_dfg ctx act)
                        (fst (nth (index_to_nat n_idx)
                                (nth (index_to_nat a_idx) bneeds []) (0, (0, 0))))
                        (filter (fun '(b_nid, _) => negb (Nat.eqb b_nid
                            (fst (nth (index_to_nat n_idx)
                                    (nth (index_to_nat a_idx) bneeds [])
                                    (0, (0, 0))))))
                           (nth (index_to_nat a_idx) bneeds []))))
                      (ss_run k act input resp ss0)
                      (sched_input ctx cost_limit input (resp k)))
                      Bits.zero
                   then false else true)
                  = slot_gate act a_idx vals (fst (srun act a_idx vals k))
                      (fst (nth (index_to_nat n_idx)
                              (nth (index_to_nat a_idx) bneeds []) (0, (0, 0))))).
    { match goal with
      | |- (if @beq_dec ?T ?E ?e _ then _ else _) = _ =>
          destruct (bits1_cases e) as [Ho | Hzo]
      end.
      - rewrite Ho.
        replace (beq_dec (Bits.ones 1) Bits.zero) with false
          by (vm_compute; reflexivity).
        symmetry. apply Hgate. exact Ho.
      - rewrite Hzo, beq_dec_refl. symmetry.
        destruct (slot_gate act a_idx vals (fst (srun act a_idx vals k))
                    (fst (nth (index_to_nat n_idx)
                            (nth (index_to_nat a_idx) bneeds []) (0, (0, 0)))))
          eqn:Hsg; [ | reflexivity ].
        exfalso. rewrite (proj1 Hgate eq_refl) in Hzo.
        exact (ones1_neq_zero Hzo). }
    rewrite Hsv, Hsc, Hvv, Hbb.
    unfold Definitions.slot_step, SchedulerSimulationLemmas.buf_valid_expr.
    cbn [fst snd]. rewrite (slot_idx_at act a_idx _ Halign (index_to_nat_bounded n_idx)).
    destruct (stall_lat_of ctx cost_limit act
                (fst (nth (index_to_nat n_idx)
                        (nth (index_to_nat a_idx) bneeds []) (0, (0, 0)))))
      as [l |] eqn:Hst.
    - (* a stall: the bit rises when the count saturates, and the count climbs *)
      assert (Hstv : stall_lat_of ctx cost_limit act
                       (vreg_nid ctx cost_limit a_idx n_idx) = Some l)
        by (unfold vreg_nid; exact Hst).
      destruct (proj2 (IH Hndk n_idx) l Hstv) as [Hcnt Hcle].
      destruct (stall_counter_wide ctx cost_limit act a_idx n_idx l Halign Hstv)
        as [Hl Hwide].
      cbn [fst snd]. split.
      + cbn [tf_eval_expr]. rewrite !convert_same.
        match goal with
        | |- _ <-> Bits.and _ (if @beq_dec ?T ?E ?r _ then _ else _) = _ =>
            replace r with ((fst (ss_run k act input resp ss0)).[tf_dfg_b a_idx n_idx])
              by reflexivity
        end.
        apply and1_iff; [ exact Hgate | ].
        match goal with
        | |- _ <-> (if @beq_dec ?T ?E ?a ?b then _ else _) = _ =>
            destruct (@beq_dec T E a b) eqn:Hb
        end.
        * apply beq_dec_iff in Hb.
          split; [ intros _; reflexivity | intros _ ].
          apply Nat.eqb_eq. rewrite Hcnt, Hb.
          apply Bits.to_nat_of_nat. exact Hwide.
        * split.
          -- intro He. exfalso. apply Nat.eqb_eq in He.
             apply (proj1 (beq_dec_false_iff _ _ _) Hb).
             apply (bits_to_nat_inj (ss_sz (tf_dfg_b a_idx n_idx))).
             rewrite <- Hcnt, He.
             symmetry. apply Bits.to_nat_of_nat. exact Hwide.
          -- intro H0. exfalso. revert H0. vm_compute. discriminate.
      + intros l' Hst'.
        assert (Hll : l' = l)
          by (unfold vreg_nid in Hst'; rewrite Hst in Hst'; injection Hst' as <-;
              reflexivity).
        subst l'.
        rewrite (stall_counter_step ctx cost_limit act a_idx n_idx
                   (ss_run k act input resp ss0)
                   (sched_input ctx cost_limit input (resp k)) l _ _ _ Hstv Hwide
                   ltac:(lia)).
        rewrite Hgz, <- Hcnt.
        split; [ reflexivity | ].
        destruct (andb (slot_gate act a_idx vals (fst (srun act a_idx vals k))
                          (fst (nth (index_to_nat n_idx)
                                  (nth (index_to_nat a_idx) bneeds [])
                                  (0, (0, 0)))))
                    (negb (Nat.eqb (nth (index_to_nat n_idx)
                                      (snd (srun act a_idx vals k)) 0) (pred l))))
          eqn:Hadv; [ | exact Hcle ].
        apply andb_prop in Hadv. destruct Hadv as [_ Hne].
        apply negb_true_iff, Nat.eqb_neq in Hne. lia.
    - (* every other slot: the bit IS the gate, and no count is claimed *)
      cbn [fst snd]. split; [ exact Hgate | ].
      intros l Hst'. exfalso. unfold vreg_nid in Hst'.
      rewrite Hst in Hst'. discriminate Hst'.
  Qed.

  (* ---- THE LATENCY OVER PUBLIC DATA IS THE LATENCY ---- *)

  (* The done register is the AND-fold of the roots' validities, and [adone] is
     the same conjunction taken over booleans. *)
  Lemma adone_matches (act: tfs_action sched) (a_idx: a_index)
      (vals: known (build_dfg ctx act))
      (input: input_t) (resp: nat -> resp_val) (ss0: sched_sys_state) (k: nat) :
    act_idx_aligned ctx cost_limit act a_idx ->
    (forall x, Definitions.zeroed_at_start ctx cost_limit x ->
       (fst ss0).[x] = Bits.zero) ->
    (forall j, (forall i, 1 <= i <= j -> ~ ss_done (ss_run i act input resp ss0)) ->
       selectors_extractable act a_idx vals (ss_run j act input resp ss0)
         (sched_input ctx cost_limit input (resp j))) ->
    (forall j, (forall i, 1 <= i <= j -> ~ ss_done (ss_run i act input resp ss0)) ->
       vals_sound act a_idx vals (ss_run j act input resp ss0)
         (sched_input ctx cost_limit input (resp j))) ->
    (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input resp ss0)) ->
    (adone act a_idx vals (fst (srun act a_idx vals k)) = true
     <-> ss_done (ss_run (S k) act input resp ss0)).
  Proof.
    intros Halign Hz Hsel Hvals Hnd.
    destruct (SchedulerRoundTrip.full_table_sample_bufs ctx cost_limit act a_idx
                Halign) as [Hsub1 Hsame1].
    destruct (valid_settled_run ctx cost_limit act a_idx input resp ss0 k Halign
                (fun q => Hz (tf_dfg_v a_idx q) I)) as [_ [Hrf Hvs]].
    assert (Hvvm : vv_matches a_idx (fst (srun act a_idx vals k))
                     (ss_run k act input resp ss0)
                     (nth (index_to_nat a_idx) bneeds [])).
    { intros m j jsz m_idx Hla Hidx.
      rewrite <- (index_to_nat_of_nat j m_idx Hidx).
      exact (proj1 (srun_matches act a_idx vals input resp ss0 Halign Hz Hsel
                      Hvals k Hnd m_idx)). }
    assert (Hroots : forallb (fun r => avalid act vals
                                (fst (srun act a_idx vals k))
                                (nth (index_to_nat a_idx) bneeds [])
                                (length (graph (build_dfg ctx act))) [] r)
                       (vm_roots act) = true
                     <-> fold_right Bits.and (Bits.ones 1)
                           (map (fun r => eval1 (root_valid act a_idx r)
                                   (ss_run k act input resp ss0)
                                   (sched_input ctx cost_limit input (resp k)))
                              (vm_roots act))
                         = Bits.ones 1).
    { apply forallb_fold_and1. intros r Hr. apply nodup_In in Hr.
      destruct (var_map_node_range ctx cost_limit act r Hr) as [Hr1 Hrlen].
      exact (avalid_correct act a_idx vals (fst (srun act a_idx vals k))
               (ss_run k act input resp ss0)
               (sched_input ctx cost_limit input (resp k))
               (nth (index_to_nat a_idx) bneeds [])
               Halign Hvs Hrf (fun e He => He) Hvvm (Hvals k Hnd) (Hsel k Hnd)
               (length (graph (build_dfg ctx act))) [] r
               (fun x _ => Hsub1 x) (fun x m msz _ => Hsame1 x m msz)
               (pi_holds_nil act a_idx _ _) I Hr1 Hrlen Hrlen). }
    unfold Definitions.adone, ss_done, done_set.
    change (ss_run (S k) act input resp ss0)
      with (ss_step act (ss_run k act input resp ss0)
              (sched_input ctx cost_limit input (resp k))).
    rewrite (done_val_concrete act a_idx (ss_run k act input resp ss0)
               (sched_input ctx cost_limit input (resp k)) Halign), map_map.
    split.
    - intros H Hc. rewrite (proj1 Hroots H) in Hc. exact (ones1_neq_zero Hc).
    - intro H. apply (proj2 Hroots), (proj1 (bits1_nonzero_ones _)). exact H.
  Qed.

  (* THE HEADLINE, INTENSIONALLY: the cycle count the design takes IS the one
     the attacker computes from public data.  [L_pub] reads no state, no input
     and no IP answer -- only the action, its slot, and the values the
     declassification rules recover. *)
  Theorem L_pub_correct (act: tfs_action sched) (a_idx: a_index)
      (vals: known (build_dfg ctx act))
      (input: input_t) (resp: nat -> resp_val) (ss0: sched_sys_state) :
    act_idx_aligned ctx cost_limit act a_idx ->
    (forall x, Definitions.zeroed_at_start ctx cost_limit x ->
       (fst ss0).[x] = Bits.zero) ->
    (forall j, (forall i, 1 <= i <= j -> ~ ss_done (ss_run i act input resp ss0)) ->
       selectors_extractable act a_idx vals (ss_run j act input resp ss0)
         (sched_input ctx cost_limit input (resp j))) ->
    (forall j, (forall i, 1 <= i <= j -> ~ ss_done (ss_run i act input resp ss0)) ->
       vals_sound act a_idx vals (ss_run j act input resp ss0)
         (sched_input ctx cost_limit input (resp j))) ->
    L act input resp ss0 = L_pub_at act a_idx vals.
  Proof.
    intros Halign Hz Hsel Hvals.
    unfold Definitions.L, Definitions.L_pub.
    apply first_true_ext. intros j _ Hbefore.
    destruct j as [| m].
    - (* cycle zero: the design resets the flag *)
      unfold Definitions.pdone_test.
      destruct (done_test act input resp ss0 0) eqn:Hd0; [ | reflexivity ].
      exfalso. apply (proj1 (done_test_true act input resp ss0 0)) in Hd0.
      unfold ss_done, done_set in Hd0. cbn [run_n] in Hd0.
      exact (Hd0 (Hz (tfs_done_signal sched) I)).
    - assert (Hnd : forall i, 1 <= i <= m ->
                ~ ss_done (ss_run i act input resp ss0)).
      { intros i Hi Hc.
        pose proof (Hbefore i ltac:(lia)) as Hf.
        rewrite (proj2 (done_test_true act input resp ss0 i) Hc) in Hf.
        discriminate Hf. }
      unfold Definitions.pdone_test.
      destruct (adone act a_idx vals (fst (srun act a_idx vals m))) eqn:Ha.
      + apply (proj2 (done_test_true act input resp ss0 (S m))).
        exact (proj1 (adone_matches act a_idx vals input resp ss0 m Halign Hz
                        Hsel Hvals Hnd) Ha).
      + destruct (done_test act input resp ss0 (S m)) eqn:Hd; [ | reflexivity ].
        exfalso.
        rewrite (proj2 (adone_matches act a_idx vals input resp ss0 m Halign Hz
                          Hsel Hvals Hnd)
                   (proj1 (done_test_true act input resp ss0 (S m)) Hd)) in Ha.
        discriminate Ha.
  Qed.

  (* The completion cycle IS the public one: done at [L_pub], and at no cycle
     before it.  [Theorems/IPR.v] states the emulator over this. *)
  Corollary L_pub_first_done (act: tfs_action sched) (a_idx: a_index)
      (vals: known (build_dfg ctx act))
      (sp0: src_sys_state) (ss0: sched_sys_state)
      (input: input_t) (resp: nat -> resp_val) :
    act_idx_aligned ctx cost_limit act a_idx ->
    start_rel ctx cost_limit sp0 ss0 ->
    (forall j, (forall i, 1 <= i <= j -> ~ ss_done (ss_run i act input resp ss0)) ->
       selectors_extractable act a_idx vals (ss_run j act input resp ss0)
         (sched_input ctx cost_limit input (resp j))) ->
    (forall j, (forall i, 1 <= i <= j -> ~ ss_done (ss_run i act input resp ss0)) ->
       vals_sound act a_idx vals (ss_run j act input resp ss0)
         (sched_input ctx cost_limit input (resp j))) ->
    first_done act input resp ss0 (L_pub_at act a_idx vals).
  Proof.
    intros Halign Hstart Hsel Hvals.
    rewrite <- (L_pub_correct act a_idx vals input resp ss0 Halign
                  (proj2 (proj2 Hstart)) Hsel Hvals).
    exact (L_first_done act sp0 ss0 input resp Hstart).
  Qed.

End IPRProof.

