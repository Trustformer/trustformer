(*! The proofs behind Theorems/IPR.v, and the intermediate results they are
    built from: that taint propagates along arguments, that a node the
    hardware marks valid holds its reference value, and that a shadow machine
    over the attacker's recovered values completes on the same cycle as the
    design.  The latency guarantee itself is stated in Theorems/IPR.v. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Export Trustformer.Theorems.Definitions.
Require Export Trustformer.Theorems.Internal.ProofDefinitions.
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

  (* Bound here at this section's [f]. *)
  Local Notation first_true := (AttackerClock.first_true f).

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

(* A one-bit node's value is the bit its condition reading names. *)
Lemma bit_of_nonzero (f: forall w, bits_t w) (w: nat) (v: bits_t w) :
  w = 1 -> f w = v -> f 1 = ProofDefinitions.bit_of (nonzero v).
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
    AttackerClock.first_true f fuel k = AttackerClock.first_true g fuel k.
Proof.
  induction fuel as [| fuel IH]; intros k H; [ reflexivity | ].
  cbn [AttackerClock.first_true].
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

  (* Bound at this section's context. *)
  Local Notation sample_args_settled := (ProofDefinitions.sample_args_settled ctx cost_limit).
  Local Notation sample_guards_settled := (ProofDefinitions.sample_guards_settled ctx cost_limit).
  Local Notation samples_answered := (ProofDefinitions.samples_answered ctx cost_limit).
  Local Notation samples_zeroed := (ProofDefinitions.samples_zeroed ctx cost_limit).
  Local Notation settled := (ProofDefinitions.settled ctx cost_limit).

  (* Bound here at this section's context. *)
  Local Notation L := (ProofDefinitions.L ctx cost_limit).
  Local Notation bit_of := ProofDefinitions.bit_of.
  Local Notation done_test := (ProofDefinitions.done_test ctx cost_limit).
  Local Notation drives_sized := (ProofDefinitions.drives_sized ctx cost_limit).
  Local Notation emulate := (Definitions.emulate ctx).
  Local Notation first_done := (Definitions.first_done ctx cost_limit).
  Local Notation guards_sized := (ProofDefinitions.guards_sized ctx cost_limit).
  Local Notation is_plumbing := (ProofDefinitions.is_plumbing ctx cost_limit).
  Local Notation pi_holds := (ProofDefinitions.pi_holds ctx cost_limit).
  Local Notation plumbing_not_root := (ProofDefinitions.plumbing_not_root ctx cost_limit).

  (* The attacker's clock, and what the proof says about it. *)
  Local Notation vvec := AttackerClock.vvec.
  Local Notation sstate := AttackerClock.sstate.
  Local Notation slot_valid := AttackerClock.slot_valid.
  Local Notation avalid := (AttackerClock.avalid ctx cost_limit).
  Local Notation vv_matches := (ProofDefinitions.vv_matches ctx cost_limit).
  Local Notation settled_at := (ProofDefinitions.settled_at ctx cost_limit).
  Local Notation vals_sound := (ProofDefinitions.vals_sound ctx cost_limit).
  Local Notation selectors_extractable :=
    (ProofDefinitions.selectors_extractable ctx cost_limit).
  Local Notation path_ok := (ProofDefinitions.path_ok ctx cost_limit).
  Local Notation gate_bufs := (AttackerClock.gate_bufs ctx cost_limit).
  Local Notation slot_gate := (AttackerClock.slot_gate ctx cost_limit).
  Local Notation slot_step := (AttackerClock.slot_step ctx cost_limit).
  Local Notation sstep := (AttackerClock.sstep ctx cost_limit).
  Local Notation sstart := (AttackerClock.sstart ctx cost_limit).
  Local Notation srun := (AttackerClock.srun ctx cost_limit).
  Local Notation adone := (AttackerClock.adone ctx cost_limit).
  Local Notation pdone_test := (AttackerClock.pdone_test ctx cost_limit).
  Local Notation L_pub_at := (AttackerClock.L_pub_at ctx cost_limit).

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
    unfold ProofDefinitions.sample_drive_head,
           AttackerClock.node_op in Hsd.
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
    unfold ProofDefinitions.sample_drive,
           AttackerClock.node_op in Hsd.
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
    unfold ProofDefinitions.sample_drive_head,
           AttackerClock.node_op in Hsd.
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
      + apply Hpl. unfold is_plumbing, AttackerClock.node_op.
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
    unfold ProofDefinitions.sample_drive,
           AttackerClock.node_op in Hsd.
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
          by (apply Hpl; unfold is_plumbing, AttackerClock.node_op;
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

  (* [pi_holds] is the scheduler's [en_holds], read at one bit. *)
  Lemma pi_holds_guard (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (en: list lit) (ss: sched_sys_state) :
    pi_holds act a_idx input en ss ->
    SchedulerRoundTrip.en_holds ctx cost_limit act a_idx ss input en.
  Proof.
    intros H c b Hin. specialize (H c b Hin).
    unfold ProofDefinitions.nval, bit_of in H. split.
    - intro Hb. subst b. rewrite H. exact ones1_neq_zero.
    - intro Hb. subst b. exact H.
  Qed.

  Lemma guard_pi_holds (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (en: list lit) (ss: sched_sys_state) :
    SchedulerRoundTrip.en_holds ctx cost_limit act a_idx ss input en ->
    pi_holds act a_idx input en ss.
  Proof.
    intros H c b Hin. destruct (H c b Hin) as [Ht Hf].
    unfold ProofDefinitions.nval, bit_of. destruct b.
    - destruct (bits1_cases (eval1 (node_ref_expr ctx cost_limit act a_idx c) ss input))
        as [Ho | Hz]; [ exact Ho | exfalso; exact (Ht eq_refl Hz) ].
    - exact (Hf eq_refl).
  Qed.

  Lemma mem_nid_In (n: nid_t) (l: list nid_t) : mem_nid n l = true -> List.In n l.
  Proof.
    unfold mem_nid. intro H. apply existsb_exists in H.
    destruct H as [x [Hin Heq]]. apply Nat.eqb_eq in Heq. subst x. exact Hin.
  Qed.

  Local Notation nsz act n :=
    (sz (nth n (graph (build_dfg ctx act))
           {| nid := 0; op := DFG_Empty; sz := 0 |})).

  (* A public output's root has the output's own width. *)
  Lemma root_width (act: tfs_action sched) (o: o_var) (r: nid_t) :
    List.In (DFG_OVar o, r) (var_map (build_dfg ctx act)) ->
    nsz act r = tfs_outputs_size sched o.
  Proof.
    intro Hin.
    exact (proj2 (wsz_node_sz ctx cost_limit act r _
                    (wvsz_build_dfg ctx cost_limit act _ r Hin))).
  Qed.

  Lemma guard_incl_refl (g: list lit) : guard_incl g g = true.
  Proof.
    unfold guard_incl. apply forallb_forall. intros a Ha.
    apply existsb_exists. exists a. split; [ exact Ha | ].
    unfold lit_eqb. rewrite Nat.eqb_refl, Bool.eqb_reflx. reflexivity.
  Qed.

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

  (* One combined guard per way of picking a fact for each source; each
     source's own guard is part of the combination. *)
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

  (* ------------------------------------------------------------------- *)
  (* What a pre-done cycle leaves alone.  Output registers
     hold, and a VALID node keeps its reference value. *)
  (* ------------------------------------------------------------------- *)

  Local Notation ss_step := (sched_step ctx cost_limit).
  Local Notation ss_run  := (run_n ctx cost_limit).
  Local Notation ss_done := (done_set ctx cost_limit).
  Local Notation src_st_env  := (ContextEnv.(env_t) (tf_states_type s_sz)).
  Local Notation src_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation src_sys_state := (src_st_env * src_out_env)%type.
  Local Notation spec_run act sp input :=
    (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act)
       sp input).

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

  Lemma mem_nid_not_In (n: nid_t) (l: list nid_t) :
    mem_nid n l = false -> ~ List.In n l.
  Proof.
    unfold mem_nid. intros H Hin.
    assert (Hex : existsb (Nat.eqb n) l = true)
      by (apply existsb_exists; exists n; split; [ exact Hin | apply Nat.eqb_refl ]).
    rewrite H in Hex. discriminate.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The done flag, read off the hardware.                                 *)
  (* The done register is assigned the AND-fold of the validity            *)
  (* expressions of the [var_map] roots.                                   *)
  (* ------------------------------------------------------------------- *)

  Local Notation vm_roots act :=
    (nodup Nat.eq_dec (map snd (var_map (build_dfg ctx act)))).

  Local Notation root_valid act a_idx n :=
    (snd (compile_dfg_expr ctx bneeds (length (graph (build_dfg ctx act)))
            a_idx (build_dfg ctx act) n
            (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))).

  (* [sched_step_done_set] hides the validity list behind a per-state existential;
     [done_exprs_concrete] exposes it, as [adone_matches] needs. *)
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


  (* ------------------------------------------------------------------- *)
  (* The first done cycle is unique.                                       *)
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


  (* ------------------------------------------------------------------- *)
  (* The IPR emulator.  It sees only the inputs, the current outputs and   *)
  (* the specification: outputs hold until the action completes, then take *)
  (* the specification's values.  The one free variable is the cycle count *)
  (* N, which [Extract.L_is_public] pins to public data.                 *)
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
    unfold AttackerClock.node_op.
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
                      ltac:(unfold AttackerClock.node_op; rewrite Hop; reflexivity)
                      Hcrit Hpi Hpok Hrvc) as [v Hb].
          rewrite Hb. cbn beta iota.
          pose proof (Hvals cnd v pi Hb Hpi Hrvc) as Hcl.
          remember (nonzero v) as b eqn:Hbdef.
          assert (Hbv : nval ctx cost_limit act a_idx ss input 1 cnd
                        = ProofDefinitions.bit_of b).
          { subst b.
            exact (bit_of_nonzero
                     (fun w => nval ctx cost_limit act a_idx ss input w cnd)
                     _ v Hcsz Hcl). }
          assert (Hce : eval1 ce ss input = ProofDefinitions.bit_of b).
          { rewrite S1. unfold nval, node_ref_expr in Hbv. exact Hbv. }
          (* the arm the condition names is read under the extended path, and
             that path holds: [b] IS the condition's bit *)
          pose proof (pi_holds_cons act a_idx input cnd b pi ss Hpi Hbv) as Hpib.
          assert (Hpokb : path_ok act a_idx ss input ((cnd, b) :: pi)).
          { split; [ exact Hpok | split; [ | split; [ exact Hpi | exact Hrvc ] ] ].
            exists n, tid, eid. split; [ unfold AttackerClock.node_op; exact Hop | exact Hcrit ]. }
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
      (vals: known (build_dfg ctx act)) (st: AttackerClock.sstate)
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
    unfold AttackerClock.sstep, AttackerClock.slot_valid. cbn [fst snd].
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
    { cbn [AttackerClock.srun run_n].
      unfold AttackerClock.sstart, AttackerClock.slot_valid. cbn [fst snd].
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
    cbn [AttackerClock.srun].
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
                       (AttackerClock.gate_bufs ctx cost_limit a_idx
                          (fst (nth (index_to_nat n_idx)
                                  (nth (index_to_nat a_idx) bneeds [])
                                  (0, (0, 0)))))).
      { intros m j jsz m_idx Hla Hidx.
        rewrite <- (index_to_nat_of_nat j m_idx Hidx).
        exact (proj1 (IH Hndk m_idx)). }
      unfold AttackerClock.slot_gate, AttackerClock.gate_bufs in Hvvm |- *.
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
    unfold AttackerClock.slot_step, SchedulerSimulationLemmas.buf_valid_expr.
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
    unfold AttackerClock.adone, ss_done, done_set.
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
    unfold ProofDefinitions.L, Definitions.L_pub.
    apply first_true_ext. intros j _ Hbefore.
    destruct j as [| m].
    - (* cycle zero: the design resets the flag *)
      unfold AttackerClock.pdone_test.
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
      unfold AttackerClock.pdone_test.
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

