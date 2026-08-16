(*! Information-Preserving Refinement.

    Campaign: agents/ipr-proof/PLAN.md

    The end goal is that an action's latency is a function of attacker-visible
    data only.  This file currently holds the groundwork for Phase 1 (taint
    soundness): the fold-accumulator reasoning for [get_tainted], and the
    propagation fact that a node inherits its arguments' taint.
!*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.
Require Import Trustformer.Properties.SchedulerSimulation.

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

  Fixpoint first_true (fuel k: nat) : nat :=
    match fuel with
    | 0 => k
    | S fuel' => if f k then k else first_true fuel' (S k)
    end.

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

Section IPR.
  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation sched := (tfs_schedule ctx cost_limit).
  Local Notation s_var := (tfs_spec_states ctx).
  Local Notation i_var := (tfs_spec_inputs ctx).
  Local Notation o_var := (tfs_spec_outputs ctx).
  Local Notation node_t := (@dfg_node_t s_var i_var o_var).

  Local Notation s_sz := (tfs_spec_states_size ctx).
  Local Notation i_sz := (tfs_spec_inputs_size ctx).
  Local Notation o_sz := (tfs_spec_outputs_size ctx).

  Hint Extern 0 (FiniteType s_var) => exact (tfs_spec_states_fin ctx)  : typeclass_instances.
  Hint Extern 0 (FiniteType i_var) => exact (tfs_spec_inputs_fin ctx)  : typeclass_instances.
  Hint Extern 0 (FiniteType o_var) => exact (tfs_spec_outputs_fin ctx) : typeclass_instances.
  Hint Extern 0 (FiniteType (tfs_states sched))  => exact (tfs_states_fin sched)  : typeclass_instances.
  Hint Extern 0 (FiniteType (tfs_outputs sched)) => exact (tfs_outputs_fin sched) : typeclass_instances.
  (* [tfs_ctx sched] and [ctx] are convertible but not syntactically equal, and the
     goal appears under both spellings; [exact] fails harmlessly if neither matches. *)
  Hint Extern 0 (tf_externs (tfs_spec_externs ctx)) =>
    exact (tfs_spec_externs_sig ctx) : typeclass_instances.
  Hint Extern 1 (tf_externs _) => exact (tfs_spec_externs_sig ctx) : typeclass_instances.

  Local Notation sched_st_env  := (ContextEnv.(env_t) (tf_states_type (tfs_states_size sched))).
  Local Notation sched_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation sched_sys_state := (sched_st_env * sched_out_env)%type.
  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).
  Local Notation a_index := (Vect.index (length (buffer_needs ctx cost_limit))).

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

  (* Widths are the nodes' own declared widths throughout: [node_args_sz] says
     every consumer reads its arguments at exactly their declared size, so this
     is no weaker than quantifying over all widths -- and unlike that version it
     is implied by plain equality of the observable outputs. *)
  Definition pub_eq (act: tfs_action sched) (a_idx: a_index) (input: input_t)
      (ss ss': sched_sys_state) : Prop :=
    (forall o : o_var, (snd ss).[o] = (snd ss').[o])
    /\ (forall (o: o_var) (r: nid_t),
          List.In (DFG_OVar o, r) (var_map (build_dfg ctx act)) ->
          nval ctx cost_limit act a_idx ss input (nsz act r) r
          = nval ctx cost_limit act a_idx ss' input (nsz act r) r).

  Definition derivable (act: tfs_action sched) (a_idx: a_index) (input: input_t)
      (n: nid_t) : Prop :=
    forall ss ss',
      pub_eq act a_idx input ss ss' ->
      nval ctx cost_limit act a_idx ss input (nsz act n) n
      = nval ctx cost_limit act a_idx ss' input (nsz act n) n.

  (* ------------------------------------------------------------------- *)
  (* (D1) for the blackbox instantiation: the seed of the taint fold is    *)
  (* derivable.  Phase 1 consumes this and nothing else about the seed, so *)
  (* the whitebox campaign only has to re-prove *this* lemma for its own   *)
  (* [untainted_roots].                                                     *)
  (* ------------------------------------------------------------------- *)

  Lemma public_dst_derivable (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (o: o_var) (r: nid_t) :
    List.In (DFG_OVar o, r) (var_map (build_dfg ctx act)) ->
    derivable act a_idx input r.
  Proof. intros Hin ss ss' [_ Hroots]. exact (Hroots o r Hin). Qed.

  Lemma public_dsts_derivable (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (n: nid_t) :
    List.In n (public_dsts ctx (build_dfg ctx act)) ->
    derivable act a_idx input n.
  Proof.
    unfold public_dsts. intro Hin.
    apply in_map_iff in Hin. destruct Hin as [[v r] [Hsnd Hfil]].
    simpl in Hsnd. subst r.
    apply filter_In in Hfil. destruct Hfil as [Hvm Hv].
    destruct v as [sv | ov]; [ discriminate Hv | ].
    exact (public_dst_derivable act a_idx input ov n Hvm).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The user's obligation for the unconditional declassification          *)
  (* instances their rules emit: derivable sources give a derivable        *)
  (* target.  [instance_sound] below is its guarded form, which implies    *)
  (* this one because [pi_holds []] is trivial.                            *)
  (* ------------------------------------------------------------------- *)

  Definition uncond_sound (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) : Prop :=
    forall i,
      List.In i (uncond_instances ctx (build_dfg ctx act)) ->
      (forall s, List.In s (di_sources i) -> derivable act a_idx input s) ->
      derivable act a_idx input (di_target i).

  (* Discharged by the user, per context; the rule library in coq/Rules/ proves
     it for the rules it ships. *)
  Context (Hdecls : forall act a_idx input, uncond_sound act a_idx input).

  Lemma mem_nid_In (n: nid_t) (l: list nid_t) : mem_nid n l = true -> List.In n l.
  Proof.
    unfold mem_nid. intro H. apply existsb_exists in H.
    destruct H as [x [Hin Heq]]. apply Nat.eqb_eq in Heq. subst x. exact Hin.
  Qed.

  Lemma saturate_step_derivable (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (acc: list nid_t) :
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
      (input: input_t) (fuel: nat) (acc: list nid_t) :
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

  (* Constants and inputs are the same in any two runs. *)
  Lemma trivial_derivable (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (n: nid_t) :
    List.In n (trivially_public ctx (build_dfg ctx act)) ->
    derivable act a_idx input n.
  Proof.
    unfold trivially_public. intro Hin.
    apply filter_In in Hin. destruct Hin as [Hseq Hop].
    apply in_seq in Hseq. destruct Hseq as [Hn1 Hn2].
    assert (Hlen : n < length (graph (build_dfg ctx act))) by lia.
    intros ss ss' _. unfold nval.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | xf xarg | ] eqn:Hopn;
      try discriminate.
    - rewrite (nre_const ctx cost_limit act a_idx n c Hn1 Hlen Hopn). reflexivity.
    - rewrite (nre_input ctx cost_limit act a_idx n v Hn1 Hlen Hopn). reflexivity.
  Qed.

  Lemma untainted_roots_derivable (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (n: nid_t) :
    List.In n (untainted_roots ctx (build_dfg ctx act)) ->
    derivable act a_idx input n.
  Proof.
    unfold untainted_roots.
    apply (saturate_derivable act a_idx input).
    intros m Hm. apply in_app_or in Hm. destruct Hm as [Hm | Hm].
    - exact (public_dsts_derivable act a_idx input m Hm).
    - exact (trivial_derivable act a_idx input m Hm).
  Qed.

  (* The width in [pub_eq]'s second conjunct is the output variable's own width,
     so that conjunct really is "the two states publish the same values" -- which
     is what lets latency be indexed by observable data rather than by state.
     Stated at [tfs_outputs_size sched] rather than the convertible
     [dfg_var_size], so that it rewrites against [dfg_action_semantics]. *)
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
      (input: input_t) (ss ss': sched_sys_state) :
    publishes_nothing act ->
    (forall o : o_var, (snd ss).[o] = (snd ss').[o]) ->
    pub_eq act a_idx input ss ss'.
  Proof.
    intros Hno Hout. split; [ exact Hout | ].
    intros o r Hin. destruct (Hno o r Hin).
  Qed.

  Lemma svar_nval (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: input_t) (szB: nat) (n: nid_t)
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
      (a_idx: a_index) (input: input_t) (n: nid_t) (sv: s_var) :
    publishes_nothing act ->
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    op (nth n (graph (build_dfg ctx act))
          {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Var (DFG_SVar sv) ->
    derivable act a_idx input n ->
    forall (ss ss': sched_sys_state),
      (forall o : o_var, (snd ss).[o] = (snd ss').[o]) ->
      convert (szB := nsz act n) (fst ss ).[tf_dfg_s sv]
      = convert (szB := nsz act n) (fst ss').[tf_dfg_s sv].
  Proof.
    intros Hno H1 H2 Hop Hder ss ss' Hout.
    rewrite <- (svar_nval act a_idx ss  input _ n sv H1 H2 Hop).
    rewrite <- (svar_nval act a_idx ss' input _ n sv H1 H2 Hop).
    apply Hder. apply pub_eq_publishes_nothing; assumption.
  Qed.

  (* ... and that consequent is false as soon as the register can hold two
     values the node's width still tells apart. At width 0 a register really is
     derivable, so this hypothesis is exactly [0 < width] rather than an
     artefact. [nsz act n] is the register's own width for every node [build_dfg]
     actually builds, but no lemma records that, so it is left explicit here. *)
  Theorem svar_not_derivable (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (n: nid_t) (sv: s_var) :
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
    pose proof (svar_derivable_forces_secret_public act a_idx input n sv
                  Hno H1 H2 Hop Hder
                  (ContextEnv.(putenv) base (tf_dfg_s sv) b1, o0)
                  (ContextEnv.(putenv) base (tf_dfg_s sv) b2, o0)
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
      (input: input_t) :
    forall n,
      1 <= n -> n < length (graph (build_dfg ctx act)) ->
      ~ List.In n (get_tainted ctx (build_dfg ctx act)) ->
      derivable act a_idx input n.
  Proof.
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

    intros ss ss' Hpub. unfold nval.
    pose proof (wfg_build_dfg ctx cost_limit act _ Hin) as Hfg.

    (* [node_args_sz] pins the width each argument is consumed at, so a fact at
       the argument's declared width is exactly what every case needs. *)
    assert (Hder_at : forall x W,
              List.In x (get_args ctx (nth n (graph (build_dfg ctx act))
                                         {| nid := 0; op := DFG_Empty; sz := 0 |})) ->
              wsz ctx (build_dfg ctx act) x W ->
              tf_eval_expr (tfs_states_size sched) i_sz (tfs_outputs_size sched)
                (szB := W) (node_ref_expr ctx cost_limit act a_idx x) ss input
              = tf_eval_expr (tfs_states_size sched) i_sz (tfs_outputs_size sched)
                (szB := W) (node_ref_expr ctx cost_limit act a_idx x) ss' input).
    { intros x W Hx Hwsz.
      destruct (wsz_node_sz ctx cost_limit act x W Hwsz) as [_ Hxsz].
      rewrite <- Hxsz. exact (Hargder x Hx ss ss' Hpub). }

    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | iv | [sv | ov] | uop arg | bop a1 a2 | src | cnd tid eid | xf xarg | ]
      eqn:Eop.

    - rewrite (nre_const ctx cost_limit act a_idx n c H1 Hlen Eop).
      cbn [tf_eval_expr]. reflexivity.

    - rewrite (nre_input ctx cost_limit act a_idx n iv H1 Hlen Eop).
      cbn [tf_eval_expr]. reflexivity.

    - (* a secret read is always tainted, so this case cannot arise *)
      exfalso.
      assert (Ht := svar_tainted act _ sv Hin Eop Hnr').
      rewrite Hnid in Ht. exact (Hnt Ht).

    - rewrite (nre_ovar ctx cost_limit act a_idx n ov H1 Hlen Eop).
      (* [nval] reads outputs at [tfs_outputs_size sched], [pub_eq] at the
         convertible [tfs_spec_outputs_size ctx], so [apply] not [rewrite]. *)
      cbn [tf_eval_expr]. destruct Hpub as [Hout _]. f_equal. apply Hout.

    - assert (Ha : List.In arg (get_args ctx (nth n (graph (build_dfg ctx act))
                                                {| nid := 0; op := DFG_Empty; sz := 0 |})))
        by (unfold get_args; rewrite Eop; left; reflexivity).
      unfold node_args_sz in Hfg. rewrite Eop in Hfg.
      rewrite (nre_unary ctx cost_limit act a_idx n uop arg H1 Hlen Eop).
      (* destruct first: [tf_resize] binds its own width in the match pattern *)
      cbn [tf_eval_expr]. destruct uop;
        rewrite (Hder_at arg _ Ha Hfg); reflexivity.

    - assert (Ha1 : List.In a1 (get_args ctx (nth n (graph (build_dfg ctx act))
                                                {| nid := 0; op := DFG_Empty; sz := 0 |})))
        by (unfold get_args; rewrite Eop; left; reflexivity).
      assert (Ha2 : List.In a2 (get_args ctx (nth n (graph (build_dfg ctx act))
                                                {| nid := 0; op := DFG_Empty; sz := 0 |})))
        by (unfold get_args; rewrite Eop; right; left; reflexivity).
      unfold node_args_sz in Hfg. rewrite Eop in Hfg.
      rewrite (nre_binary ctx cost_limit act a_idx n bop a1 a2 H1 Hlen Eop).
      destruct bop; destruct Hfg as [Hg1 Hg2]; cbn [tf_eval_expr];
        rewrite (Hder_at a1 _ Ha1 Hg1), (Hder_at a2 _ Ha2 Hg2); reflexivity.

    - assert (Ha : List.In src (get_args ctx (nth n (graph (build_dfg ctx act))
                                                {| nid := 0; op := DFG_Empty; sz := 0 |})))
        by (unfold get_args; rewrite Eop; left; reflexivity).
      (* [DFG_Resize] resizes from the argument's declared width by construction,
         which is why [node_args_sz] records no constraint for it. *)
      pose proof (Hargder src Ha ss ss' Hpub) as E. unfold nval in E.
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
      unfold node_args_sz in Hfg. rewrite Eop in Hfg.
      destruct Hfg as [Hgc [Hgt Hge]].
      rewrite (nre_phi ctx cost_limit act a_idx n cnd tid eid H1 Hlen Eop).
      cbn [tf_eval_expr].
      rewrite (Hder_at cnd _ Hc Hgc), (Hder_at tid _ Ht Hgt),
              (Hder_at eid _ He Hge). reflexivity.

    - (* a call's result is a function of its argument, so it is derivable
         exactly when the argument is *)
      assert (Ha : List.In xarg (get_args ctx (nth n (graph (build_dfg ctx act))
                                                {| nid := 0; op := DFG_Empty; sz := 0 |})))
        by (unfold get_args; rewrite Eop; left; reflexivity).
      unfold node_args_sz in Hfg. rewrite Eop in Hfg.
      rewrite (nre_ext ctx cost_limit act a_idx n xf xarg H1 Hlen Eop).
      cbn [tf_eval_expr]. rewrite (Hder_at xarg _ Ha Hfg). reflexivity.

    - assert (Hemp : node_ref_expr ctx cost_limit act a_idx n = tf_const 0).
      { rewrite (nre_unfold ctx cost_limit act a_idx n H1 Hlen).
        cbn [compile_dfg_expr BitsToLists.list_assoc]. rewrite Eop. reflexivity. }
      rewrite Hemp. cbn [tf_eval_expr]. reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* GUARDED DERIVABILITY.  A whitebox rule usually only declassifies a    *)
  (* condition on some paths (the lock is open only when the guess was      *)
  (* right), so the compiler decides criticality per phi OCCURRENCE from    *)
  (* the path of selector literals it is under.  [lit] / [guard_incl] are  *)
  (* the scheduler's (coq/Scheduler/VariableScheduler.v); only their       *)
  (* semantics live here.                                                  *)
  (* ------------------------------------------------------------------- *)

  Definition bit_of (b: bool) : bits_t 1 := if b then Bits.ones 1 else Bits.zero.

  Definition pi_holds (act: tfs_action sched) (a_idx: a_index) (input: input_t)
      (pi: list lit) (ss: sched_sys_state) : Prop :=
    forall c b, List.In (c, b) pi ->
      nval ctx cost_limit act a_idx ss input 1 c = bit_of b.

  Lemma pi_holds_nil (act: tfs_action sched) (a_idx: a_index) (input: input_t)
      (ss: sched_sys_state) : pi_holds act a_idx input [] ss.
  Proof. intros c b Hin; destruct Hin. Qed.

  Lemma guard_incl_holds (act: tfs_action sched) (a_idx: a_index) (input: input_t)
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

  Lemma pi_holds_app (act: tfs_action sched) (a_idx: a_index) (input: input_t)
      (g1 g2: list lit) (ss: sched_sys_state) :
    pi_holds act a_idx input (g1 ++ g2) ss ->
    pi_holds act a_idx input g1 ss /\ pi_holds act a_idx input g2 ss.
  Proof.
    intro H. split; intros c b Hin; apply H; apply in_or_app;
      [ left | right ]; exact Hin.
  Qed.

  Definition gderivable (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (g: list lit) (n: nid_t) : Prop :=
    forall ss ss',
      pub_eq act a_idx input ss ss' ->
      pi_holds act a_idx input g ss ->
      pi_holds act a_idx input g ss' ->
      nval ctx cost_limit act a_idx ss  input (nsz act n) n
      = nval ctx cost_limit act a_idx ss' input (nsz act n) n.

  (* A fact learned under fewer conditions still holds under more. *)
  Lemma gderivable_weaken (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (g g': list lit) (n: nid_t) :
    guard_incl g g' = true ->
    gderivable act a_idx input g n ->
    gderivable act a_idx input g' n.
  Proof.
    intros Hincl Hg ss ss' Hpub Hp Hp'.
    exact (Hg ss ss' Hpub
             (guard_incl_holds act a_idx input g g' ss  Hincl Hp)
             (guard_incl_holds act a_idx input g g' ss' Hincl Hp')).
  Qed.

  Lemma derivable_gderivable (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (g: list lit) (n: nid_t) :
    derivable act a_idx input n -> gderivable act a_idx input g n.
  Proof. intros Hd ss ss' Hpub _ _. exact (Hd ss ss' Hpub). Qed.

  (* An unconditionally derivable node is derivable under any guard. *)
  Lemma untainted_gderivable (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (g: list lit) (n: nid_t) :
    1 <= n ->
    n < length (graph (build_dfg ctx act)) ->
    ~ List.In n (get_tainted ctx (build_dfg ctx act)) ->
    gderivable act a_idx input g n.
  Proof.
    intros Hn1 Hnlen Hnt.
    exact (derivable_gderivable act a_idx input g n
             (untainted_derivable act a_idx input n Hn1 Hnlen Hnt)).
  Qed.

  (* The uniform user obligation on a single declassification instance: it is
     [uncond_sound]'s premise plus the instance's own guard. *)
  Definition instance_sound (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (i: decl_instance) : Prop :=
    forall ss ss',
      pub_eq act a_idx input ss ss' ->
      pi_holds act a_idx input (di_guard i) ss ->
      pi_holds act a_idx input (di_guard i) ss' ->
      (forall s, List.In s (di_sources i) ->
         nval ctx cost_limit act a_idx ss  input (nsz act s) s
         = nval ctx cost_limit act a_idx ss' input (nsz act s) s) ->
      nval ctx cost_limit act a_idx ss  input (nsz act (di_target i)) (di_target i)
      = nval ctx cost_limit act a_idx ss' input (nsz act (di_target i)) (di_target i).

  (* CHAINING.  A rule whose sources are themselves only known under [g]
     yields its target under both guards. *)
  Theorem decl_compose (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (i: decl_instance) (g: list lit) :
    instance_sound act a_idx input i ->
    (forall s, List.In s (di_sources i) -> gderivable act a_idx input g s) ->
    gderivable act a_idx input (di_guard i ++ g) (di_target i).
  Proof.
    intros Hi Hsrc ss ss' Hpub Hp Hp'.
    destruct (pi_holds_app act a_idx input _ _ ss  Hp)  as [Hp1  Hp2 ].
    destruct (pi_holds_app act a_idx input _ _ ss' Hp') as [Hp1' Hp2'].
    exact (Hi ss ss' Hpub Hp1 Hp1'
             (fun s Hs => Hsrc s Hs ss ss' Hpub Hp2 Hp2')).
  Qed.

  Lemma guard_incl_refl (g: list lit) : guard_incl g g = true.
  Proof.
    unfold guard_incl. apply forallb_forall. intros a Ha.
    apply existsb_exists. exists a. split; [ exact Ha | ].
    unfold lit_eqb. rewrite Nat.eqb_refl, Bool.eqb_reflx. reflexivity.
  Qed.

  Corollary decl_direct (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (i: decl_instance) :
    instance_sound act a_idx input i ->
    (forall s, List.In s (di_sources i) ->
       1 <= s /\ s < length (graph (build_dfg ctx act))
       /\ ~ List.In s (get_tainted ctx (build_dfg ctx act))) ->
    gderivable act a_idx input (di_guard i) (di_target i).
  Proof.
    intros Hi Hsrc.
    apply (gderivable_weaken act a_idx input (di_guard i ++ []) (di_guard i));
      [ rewrite app_nil_r; apply guard_incl_refl | ].
    apply (decl_compose act a_idx input i []); [ exact Hi | ].
    intros s Hs. destruct (Hsrc s Hs) as [Hs1 [Hs2 Hs3]].
    exact (untainted_gderivable act a_idx input [] s Hs1 Hs2 Hs3).
  Qed.

  (* What the compiler's own producer owes the proof: every fact it records is
     really a guarded derivability.  Note there is no disjunctive [gderivable]:
     "derivable under (A or B)" is not provable -- the two runs could satisfy
     different disjuncts and genuinely differ -- so a node derivable on several
     paths gets several entries, each with its own conjunctive guard, and the
     compiler only ever uses the entry its current path implies. *)
  Definition base_sound (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (base: list gfact) : Prop :=
    forall c g, List.In (c, g) base -> gderivable act a_idx input g c.

  Definition decl_sound (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) : Prop :=
    base_sound act a_idx input (decl_facts ctx (build_dfg ctx act)).

  (* Bridge to the unconditional obligation, so the rules in coq/Rules/ can
     discharge [Hdecls] from the same [instance_sound] proof. *)
  Lemma uncond_guard_nil (dfg: @dfg_state_t s_var i_var o_var (tfs_spec_externs ctx)) (i: decl_instance) :
    List.In i (uncond_instances ctx dfg) -> di_guard i = [].
  Proof.
    unfold uncond_instances. intro Hin.
    apply filter_In in Hin. destruct Hin as [_ Hg].
    destruct (di_guard i); [ reflexivity | discriminate ].
  Qed.

  Theorem uncond_sound_of_instances (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) :
    (forall i, List.In i (uncond_instances ctx (build_dfg ctx act)) ->
       instance_sound act a_idx input i) ->
    uncond_sound act a_idx input.
  Proof.
    intros Hall i Hi Hsrc ss ss' Hpub.
    pose proof (uncond_guard_nil (build_dfg ctx act) i Hi) as Hg.
    apply (Hall i Hi ss ss' Hpub);
      [ rewrite Hg; intros c b Hin; destruct Hin
      | rewrite Hg; intros c b Hin; destruct Hin
      | intros s Hs; exact (Hsrc s Hs ss ss' Hpub) ].
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

  Lemma gadd_of_sound (act: tfs_action sched) (a_idx: a_index) (input: input_t)
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

  Lemma gfold_sound (act: tfs_action sched) (a_idx: a_index) (input: input_t)
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

  Lemma gstep1_sound (act: tfs_action sched) (a_idx: a_index) (input: input_t)
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
      (input: input_t) :
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
      (input: input_t) :
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
      (input: input_t) :
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

  Lemma seed_sound (act: tfs_action sched) (a_idx: a_index) (input: input_t) :
    base_sound act a_idx input
      (map (fun n => (n, [])) (untainted_roots ctx (build_dfg ctx act))).
  Proof.
    intros c g Hin. apply in_map_iff in Hin.
    destruct Hin as [n [Heq Hn]]. injection Heq as Hc Hg. subst c g.
    exact (derivable_gderivable act a_idx input [] n
             (untainted_roots_derivable act a_idx input n Hn)).
  Qed.

  Theorem decl_sound_of_instances (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) :
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
  (* PHASE 2, step 1: the public view survives a pre-done cycle.           *)
  (* [nval] reads only [tf_dfg_s] and the outputs, and a non-done cycle    *)
  (* writes neither, so both conjuncts of [pub_eq] are stable.            *)
  (* ------------------------------------------------------------------- *)

  Local Notation ss_step := (sched_step ctx cost_limit).
  Local Notation ss_run  := (run_n ctx cost_limit).
  Local Notation ss_done := (done_set ctx cost_limit).

  Lemma nval_step_stable (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: input_t) (szB: nat) (n: nid_t) :
    ~ ss_done (ss_step act ss input) ->
    nval ctx cost_limit act a_idx (ss_step act ss input) input szB n
    = nval ctx cost_limit act a_idx ss input szB n.
  Proof.
    intro Hnd. unfold nval, node_ref_expr.
    apply (compile_nobuf_step_stable ctx cost_limit act a_idx ss input Hnd).
  Qed.

  Lemma nval_run_stable (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: input_t) (szB: nat) (n: nid_t) (k: nat) :
    (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input ss)) ->
    nval ctx cost_limit act a_idx (ss_run k act input ss) input szB n
    = nval ctx cost_limit act a_idx ss input szB n.
  Proof.
    induction k as [| k IH]; intro Hnd; [ reflexivity | ].
    cbn [run_n]. rewrite nval_step_stable.
    - apply IH. intros i Hi. apply Hnd. lia.
    - change (ss_step act (ss_run k act input ss) input)
        with (ss_run (S k) act input ss).
      apply Hnd. lia.
  Qed.

  Lemma out_run_stable (act: tfs_action sched) (ss: sched_sys_state)
      (input: input_t) (o: o_var) (k: nat) :
    (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input ss)) ->
    (snd (ss_run k act input ss)).[o] = (snd ss).[o].
  Proof.
    induction k as [| k IH]; intro Hnd; [ reflexivity | ].
    cbn [run_n]. rewrite sched_step_preserves_ovar.
    - apply IH. intros i Hi. apply Hnd. lia.
    - change (ss_step act (ss_run k act input ss) input)
        with (ss_run (S k) act input ss).
      apply Hnd. lia.
  Qed.

  Theorem pub_eq_run (act: tfs_action sched) (a_idx: a_index) (input: input_t)
      (ss ss': sched_sys_state) (k: nat) :
    (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input ss)) ->
    (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input ss')) ->
    pub_eq act a_idx input ss ss' ->
    pub_eq act a_idx input (ss_run k act input ss) (ss_run k act input ss').
  Proof.
    intros Hnd Hnd' [Hout Hroots]. split.
    - intro o. rewrite (out_run_stable act ss input o k Hnd).
      rewrite (out_run_stable act ss' input o k Hnd'). exact (Hout o).
    - intros o r Hin.
      rewrite (nval_run_stable act a_idx ss  input _ r k Hnd).
      rewrite (nval_run_stable act a_idx ss' input _ r k Hnd').
      exact (Hroots o r Hin).
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

  Local Notation ss_sz := (tfs_states_size sched).
  Local Notation oo_sz := (tfs_outputs_size sched).
  Local Notation eval1 e ss input :=
    (tf_eval_expr ss_sz i_sz oo_sz (szB := 1) e ss input).

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

  Lemma valid_public_gen (act: tfs_action sched) (a_idx: a_index) (input: input_t)
      (ss ss': sched_sys_state) :
    act_idx_aligned ctx cost_limit act a_idx ->
    valid_settled ctx cost_limit act a_idx ss input ->
    valid_settled ctx cost_limit act a_idx ss' input ->
    pub_eq act a_idx input ss ss' ->
    (forall n_idx, (fst ss).[tf_dfg_v a_idx n_idx]
                 = (fst ss').[tf_dfg_v a_idx n_idx]) ->
    forall bufs,
      (forall e, List.In e bufs ->
         List.In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
      forall fuel n (pi: list lit),
        1 <= n ->
        n < length (graph (build_dfg ctx act)) ->
        n < fuel ->
        pi_holds act a_idx input pi ss ->
        pi_holds act a_idx input pi ss' ->
        eval1 (snd (compile_dfg_expr_at ctx cost_limit pi fuel a_idx
                      (build_dfg ctx act) n bufs)) ss input
        = eval1 (snd (compile_dfg_expr_at ctx cost_limit pi fuel a_idx
                      (build_dfg ctx act) n bufs)) ss' input.
  Proof.
    intros Halign Hvs Hvs' Hpub Hveq bufs Hsub fuel.
    induction fuel as [| fuel IH]; intros n pi Hn1 Hnlen Hnfuel Hpi Hpi'; [ lia | ].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:Hla.
    { cbn [compile_dfg_expr_aux]. rewrite Hla. cbv beta iota.
      destruct (index_of_nat
                  (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))
                  m) as [n_idx' |]; cbn [snd]; [ | reflexivity ].
      rewrite !eval1_svar_v. apply Hveq. }
    cbn [compile_dfg_expr_aux]. rewrite Hla. cbv beta iota.
    set (node := nth n (graph (build_dfg ctx act))
                   {| nid := 0; op := DFG_Empty; sz := 0 |}) in *.
    assert (Hnode_in : List.In node (graph (build_dfg ctx act)))
      by (unfold node; apply nth_In; exact Hnlen).
    assert (Hrange : forall x, List.In x (get_args ctx node) -> 1 <= x /\ x < n)
      by (intros x Hx; exact (node_args_range ctx cost_limit act n Hn1 Hnlen x Hx)).
    pose proof (wfg_build_dfg ctx cost_limit act node Hnode_in) as Hfg.
    destruct (op node) as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | xf xarg | ]
      eqn:Hop.
    - reflexivity.
    - reflexivity.
    - destruct v; reflexivity.
    - assert (Hain : List.In arg (get_args ctx node))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      destruct (Hrange arg Hain) as [Ha1 Ha2].
      destruct (compile_dfg_expr_at ctx cost_limit pi fuel a_idx (build_dfg ctx act)
                  arg bufs) as [ae ve] eqn:E1.
      pose proof (IH arg pi Ha1 ltac:(lia) ltac:(lia) Hpi Hpi') as Ha.
      rewrite E1 in Ha. cbn [snd] in Ha |- *. exact Ha.
    - assert (Ha1in : List.In a1 (get_args ctx node))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      assert (Ha2in : List.In a2 (get_args ctx node))
        by (unfold get_args; rewrite Hop; right; left; reflexivity).
      destruct (Hrange a1 Ha1in) as [Hb1 Hb2].
      destruct (Hrange a2 Ha2in) as [Hd1 Hd2].
      destruct (compile_dfg_expr_at ctx cost_limit pi fuel a_idx (build_dfg ctx act)
                  a1 bufs) as [a1e v1e] eqn:E1.
      destruct (compile_dfg_expr_at ctx cost_limit pi fuel a_idx (build_dfg ctx act)
                  a2 bufs) as [a2e v2e] eqn:E2.
      pose proof (IH a1 pi Hb1 ltac:(lia) ltac:(lia) Hpi Hpi') as Hx1.
      pose proof (IH a2 pi Hd1 ltac:(lia) ltac:(lia) Hpi Hpi') as Hx2.
      rewrite E1 in Hx1. rewrite E2 in Hx2. cbn [snd] in Hx1, Hx2 |- *.
      rewrite !valid_and_eval. rewrite Hx1, Hx2. reflexivity.
    - assert (Hain : List.In arg (get_args ctx node))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      destruct (Hrange arg Hain) as [Ha1 Ha2].
      destruct (compile_dfg_expr_at ctx cost_limit pi fuel a_idx (build_dfg ctx act)
                  arg bufs) as [ae ve] eqn:E1.
      pose proof (IH arg pi Ha1 ltac:(lia) ltac:(lia) Hpi Hpi') as Ha.
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
        destruct (compile_dfg_expr_at ctx cost_limit pi fuel a_idx (build_dfg ctx act)
                    cnd bufs) as [ce cv] eqn:Ec.
        destruct (compile_dfg_expr_at ctx cost_limit pi fuel a_idx (build_dfg ctx act)
                    tid bufs) as [te tv] eqn:Et.
        destruct (compile_dfg_expr_at ctx cost_limit pi fuel a_idx (build_dfg ctx act)
                    eid bufs) as [ee ev] eqn:Ee.
        pose proof (IH cnd pi Hc1 ltac:(lia) ltac:(lia) Hpi Hpi') as Hcc.
        pose proof (IH tid pi Ht1 ltac:(lia) ltac:(lia) Hpi Hpi') as Hct.
        pose proof (IH eid pi He1 ltac:(lia) ltac:(lia) Hpi Hpi') as Hce.
        rewrite Ec in Hcc. rewrite Et in Hct. rewrite Ee in Hce.
        cbn [snd] in Hcc, Hct, Hce |- *.
        rewrite !valid_and_eval. rewrite Hcc, Hct, Hce. reflexivity.
      + (* non-critical HERE: either the condition is untainted, or the analysis
           declassified it under a guard this path implies *)
        destruct (compile_dfg_expr_at ctx cost_limit pi fuel a_idx (build_dfg ctx act)
                    cnd bufs) as [ce cv] eqn:Ec.
        destruct (compile_dfg_expr_at ctx cost_limit ((cnd, true) :: pi) fuel a_idx
                    (build_dfg ctx act) tid bufs) as [te tv] eqn:Et.
        destruct (compile_dfg_expr_at ctx cost_limit ((cnd, false) :: pi) fuel a_idx
                    (build_dfg ctx act) eid bufs) as [ee ev] eqn:Ee.
        pose proof (IH cnd pi Hc1 ltac:(lia) ltac:(lia) Hpi Hpi') as Hcc.
        rewrite Ec in Hcc. cbn [snd] in Hcc |- *.
        assert (Hcder : gderivable act a_idx input pi cnd).
        { unfold phi_crit in Hcrit. apply andb_false_iff in Hcrit.
          destruct Hcrit as [Hmt | Hdg].
          - exact (untainted_gderivable act a_idx input pi cnd Hc1 Hclen
                     (mem_nid_not_In cnd _ Hmt)).
          - apply Bool.negb_false_iff in Hdg.
            unfold declassified_at in Hdg. apply existsb_exists in Hdg.
            destruct Hdg as [g [Hg Hincl]].
            exact (gderivable_weaken act a_idx input g pi cnd Hincl
                     (Hdguard act a_idx input cnd g (gfacts_of_In _ _ _ Hg))). }
        rewrite !valid_and_eval. rewrite Hcc.
        destruct (bits1_cases (eval1 cv ss' input)) as [Hones | Hzero];
          [ | rewrite Hzero, !and1_zero_l; reflexivity ].
        f_equal.
        assert (Hvalc : eval1 (snd (compile_dfg_expr_at ctx cost_limit pi fuel a_idx
                          (build_dfg ctx act) cnd bufs)) ss input = Bits.ones 1)
          by (rewrite Ec; cbn [snd]; rewrite Hcc; exact Hones).
        assert (Hvalc' : eval1 (snd (compile_dfg_expr_at ctx cost_limit pi fuel a_idx
                          (build_dfg ctx act) cnd bufs)) ss' input = Bits.ones 1)
          by (rewrite Ec; cbn [snd]; exact Hones).
        pose proof (compile_subst_valid_gen ctx cost_limit act a_idx ss input
                      Halign Hvs bufs Hsub fuel cnd 1 pi Hc1 Hclen ltac:(lia)
                      (eq_sym Hcsz) Hvalc) as S1.
        pose proof (compile_subst_valid_gen ctx cost_limit act a_idx ss' input
                      Halign Hvs' bufs Hsub fuel cnd 1 pi Hc1 Hclen ltac:(lia)
                      (eq_sym Hcsz) Hvalc') as S2.
        rewrite Ec in S1, S2. cbn [fst] in S1, S2.
        rewrite (compile_fst_pi_irrel ctx cost_limit _ _ a_idx _ [] fuel cnd pi [])
          in S1, S2.
        rewrite (compile_fuel_irrel ctx cost_limit act a_idx [] cnd Hc1 Hclen
                   fuel (length (graph (build_dfg ctx act))) ltac:(lia) Hclen)
          in S1, S2.
        assert (Href : eval1 ce ss input
                       = nval ctx cost_limit act a_idx ss input 1 cnd)
          by (rewrite S1; unfold nval, node_ref_expr; reflexivity).
        assert (Href' : eval1 ce ss' input
                        = nval ctx cost_limit act a_idx ss' input 1 cnd)
          by (rewrite S2; unfold nval, node_ref_expr; reflexivity).
        assert (Hcev : eval1 ce ss input = eval1 ce ss' input).
        { rewrite Href, Href'.
          pose proof (Hcder ss ss' Hpub Hpi Hpi') as Hcd.
          rewrite Hcsz in Hcd. exact Hcd. }
        assert (Hcase : (tv = tf_const 1 /\ ev = tf_const 1)
                        \/ valid_expr_if ctx cost_limit ce tv ev
                           = tf_expr_if ce tv ev).
        { unfold valid_expr_if.
          destruct tv as [vt| | | | | | |]; try (right; reflexivity).
          destruct vt as [|[|vt]]; try (right; reflexivity).
          destruct ev as [vee| | | | | | |]; try (right; reflexivity).
          destruct vee as [|[|vee]]; try (right; reflexivity).
          left; split; reflexivity. }
        destruct Hcase as [[Htc Hec] | Hcs].
        * subst tv ev. reflexivity.
        * rewrite Hcs. cbn [tf_eval_expr]. rewrite Hcev.
          destruct (beq_dec (eval1 ce ss' input) Bits.zero) eqn:Hb.
          -- (* else branch selected: extend the path with [cnd = 0] *)
             assert (Hz : eval1 ce ss' input = Bits.zero)
               by (apply beq_dec_iff in Hb; exact Hb).
             assert (Hp0 : pi_holds act a_idx input ((cnd, false) :: pi) ss).
             { intros c b Hin. destruct Hin as [Heq | Hin].
               - injection Heq as Hc Hbv. subst c b. unfold bit_of.
                 rewrite <- Href, Hcev. exact Hz.
               - exact (Hpi _ _ Hin). }
             assert (Hp0' : pi_holds act a_idx input ((cnd, false) :: pi) ss').
             { intros c b Hin. destruct Hin as [Heq | Hin].
               - injection Heq as Hc Hbv. subst c b. unfold bit_of.
                 rewrite <- Href'. exact Hz.
               - exact (Hpi' _ _ Hin). }
             pose proof (IH eid ((cnd, false) :: pi) He1 ltac:(lia) ltac:(lia)
                           Hp0 Hp0') as Hce.
             rewrite Ee in Hce. cbn [snd] in Hce. exact Hce.
          -- (* then branch selected: extend the path with [cnd = 1] *)
             assert (Hz : eval1 ce ss' input = Bits.ones 1).
             { destruct (bits1_cases (eval1 ce ss' input)) as [Ho | Hzz];
                 [ exact Ho | ].
               rewrite Hzz, beq_dec_refl in Hb. discriminate. }
             assert (Hp1 : pi_holds act a_idx input ((cnd, true) :: pi) ss).
             { intros c b Hin. destruct Hin as [Heq | Hin].
               - injection Heq as Hc Hbv. subst c b. unfold bit_of.
                 rewrite <- Href, Hcev. exact Hz.
               - exact (Hpi _ _ Hin). }
             assert (Hp1' : pi_holds act a_idx input ((cnd, true) :: pi) ss').
             { intros c b Hin. destruct Hin as [Heq | Hin].
               - injection Heq as Hc Hbv. subst c b. unfold bit_of.
                 rewrite <- Href'. exact Hz.
               - exact (Hpi' _ _ Hin). }
             pose proof (IH tid ((cnd, true) :: pi) Ht1 ltac:(lia) ltac:(lia)
                           Hp1 Hp1') as Hct.
             rewrite Et in Hct. cbn [snd] in Hct. exact Hct.
    - (* Ext: validity is the argument's *)
      assert (Hain : List.In xarg (get_args ctx node))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      destruct (Hrange xarg Hain) as [Ha1 Ha2].
      destruct (compile_dfg_expr_at ctx cost_limit pi fuel a_idx (build_dfg ctx act)
                  xarg bufs) as [ae ve] eqn:E1.
      pose proof (IH xarg pi Ha1 ltac:(lia) ltac:(lia) Hpi Hpi') as Ha.
      rewrite E1 in Ha. cbn [snd] in Ha |- *. exact Ha.
    - reflexivity.
  Qed.

  Lemma valid_public (act: tfs_action sched) (a_idx: a_index) (input: input_t)
      (ss ss': sched_sys_state) :
    act_idx_aligned ctx cost_limit act a_idx ->
    valid_settled ctx cost_limit act a_idx ss input ->
    valid_settled ctx cost_limit act a_idx ss' input ->
    pub_eq act a_idx input ss ss' ->
    (forall n_idx, (fst ss).[tf_dfg_v a_idx n_idx]
                 = (fst ss').[tf_dfg_v a_idx n_idx]) ->
    forall bufs,
      (forall e, List.In e bufs ->
         List.In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
      forall fuel n,
        1 <= n ->
        n < length (graph (build_dfg ctx act)) ->
        n < fuel ->
        eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx
                      (build_dfg ctx act) n bufs)) ss input
        = eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx
                      (build_dfg ctx act) n bufs)) ss' input.
  Proof.
    intros Halign Hvs Hvs' Hpub Hveq bufs Hsub fuel n Hn1 Hnlen Hnfuel.
    exact (valid_public_gen act a_idx input ss ss' Halign Hvs Hvs' Hpub Hveq
             bufs Hsub fuel n [] Hn1 Hnlen Hnfuel
             (pi_holds_nil act a_idx input ss) (pi_holds_nil act a_idx input ss')).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* PHASE 2: the validity registers run in lockstep between two states    *)
  (* with the same public view.  This is the statement that makes the done *)
  (* flag -- and hence the latency -- secret-independent.                  *)
  (* ------------------------------------------------------------------- *)

  Theorem valid_lockstep (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (ss0 ss0': sched_sys_state) :
    act_idx_aligned ctx cost_limit act a_idx ->
    (forall n_idx, (fst ss0).[tf_dfg_v a_idx n_idx] = Bits.zero) ->
    (forall n_idx, (fst ss0').[tf_dfg_v a_idx n_idx] = Bits.zero) ->
    pub_eq act a_idx input ss0 ss0' ->
    forall k,
      (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input ss0)) ->
      (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input ss0')) ->
      forall n_idx,
        (fst (ss_run k act input ss0)).[tf_dfg_v a_idx n_idx]
        = (fst (ss_run k act input ss0')).[tf_dfg_v a_idx n_idx].
  Proof.
    intros Halign Hz Hz' Hpub k.
    induction k as [| k IH]; intros Hnd Hnd' n_idx.
    { cbn [run_n]. rewrite Hz, Hz'. reflexivity. }
    assert (Hndk : forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input ss0))
      by (intros i Hi; apply Hnd; lia).
    assert (Hndk' : forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input ss0'))
      by (intros i Hi; apply Hnd'; lia).
    set (ssk  := ss_run k act input ss0)  in *.
    set (ssk' := ss_run k act input ss0') in *.
    assert (Hs  : ~ ss_done (ss_step act ssk  input)) by (apply (Hnd  (S k)); lia).
    assert (Hs' : ~ ss_done (ss_step act ssk' input)) by (apply (Hnd' (S k)); lia).
    change (ss_run (S k) act input ss0)  with (ss_step act ssk  input).
    change (ss_run (S k) act input ss0') with (ss_step act ssk' input).
    pose proof (buffer_after_cycle ctx cost_limit act a_idx n_idx ssk input
                  Halign Hs) as Hb.
    pose proof (buffer_after_cycle ctx cost_limit act a_idx n_idx ssk' input
                  Halign Hs') as Hb'.
    cbv zeta in Hb, Hb'.
    destruct Hb as [_ Hv]. destruct Hb' as [_ Hv'].
    rewrite Hv, Hv'.
    destruct (vreg_nid_node_range ctx cost_limit act a_idx n_idx Halign)
      as [Hn1 Hnlen].
    unfold vreg_nid in Hn1, Hnlen.
    apply (valid_public act a_idx input ssk ssk' Halign
             (valid_settled_run ctx cost_limit act a_idx input ss0  k Halign Hz)
             (valid_settled_run ctx cost_limit act a_idx input ss0' k Halign Hz')
             (pub_eq_run act a_idx input ss0 ss0' k Hndk Hndk' Hpub)
             (IH Hndk Hndk')).
    - intros e He. exact (proj1 (proj1 (filter_In _ e _) He)).
    - exact Hn1.
    - exact Hnlen.
    - exact Hnlen.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* PHASE 3: the done flag is public.                                     *)
  (* The done register is assigned the AND-fold of the validity            *)
  (* expressions of the [var_map] roots, so Phase 2 transfers to it.       *)
  (* ------------------------------------------------------------------- *)

  Local Notation vm_roots act :=
    (nodup Nat.eq_dec (map snd (var_map (build_dfg ctx act)))).

  Local Notation root_valid act a_idx n :=
    (snd (compile_dfg_expr ctx cost_limit (length (graph (build_dfg ctx act)))
            a_idx (build_dfg ctx act) n
            (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))).

  (* [sched_step_done_set] hides the validity list behind a per-state existential,
     so it cannot relate two runs; [done_exprs_concrete] exposes the list instead. *)
  Lemma done_val_concrete (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: input_t) :
    act_idx_aligned ctx cost_limit act a_idx ->
    (fst (ss_step act ss input)).[tfs_done_signal sched]
    = fold_right Bits.and (Bits.ones 1)
        (map (fun e => eval1 e ss input)
           (map (fun n => root_valid act a_idx n) (vm_roots act))).
  Proof.
    intro Halign.
    destruct (done_exprs_concrete ctx cost_limit act a_idx Halign) as [rest Heq].
    rewrite sched_step_done. unfold find_st_val. rewrite Heq.
    rewrite find_st_update_assign_head. apply combine_valid_eval.
  Qed.

  Theorem done_public (act: tfs_action sched) (a_idx: a_index) (input: input_t)
      (ss ss': sched_sys_state) :
    act_idx_aligned ctx cost_limit act a_idx ->
    valid_settled ctx cost_limit act a_idx ss input ->
    valid_settled ctx cost_limit act a_idx ss' input ->
    pub_eq act a_idx input ss ss' ->
    (forall n_idx, (fst ss).[tf_dfg_v a_idx n_idx]
                 = (fst ss').[tf_dfg_v a_idx n_idx]) ->
    (fst (ss_step act ss input)).[tfs_done_signal sched]
    = (fst (ss_step act ss' input)).[tfs_done_signal sched].
  Proof.
    intros Halign Hvs Hvs' Hpub Hveq.
    rewrite (done_val_concrete act a_idx ss input Halign).
    rewrite (done_val_concrete act a_idx ss' input Halign).
    f_equal. rewrite !map_map. apply map_ext_in. intros n Hn.
    apply nodup_In in Hn.
    destruct (var_map_node_range ctx cost_limit act n Hn) as [Hn1 Hnlen].
    exact (valid_public act a_idx input ss ss' Halign Hvs Hvs' Hpub Hveq
             _ (fun e He => He) _ n Hn1 Hnlen Hnlen).
  Qed.

  Theorem done_lockstep (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (ss0 ss0': sched_sys_state) :
    act_idx_aligned ctx cost_limit act a_idx ->
    (fst ss0 ).[tfs_done_signal sched] = Bits.zero ->
    (fst ss0').[tfs_done_signal sched] = Bits.zero ->
    (forall n_idx, (fst ss0 ).[tf_dfg_v a_idx n_idx] = Bits.zero) ->
    (forall n_idx, (fst ss0').[tf_dfg_v a_idx n_idx] = Bits.zero) ->
    pub_eq act a_idx input ss0 ss0' ->
    forall k,
      (forall i, 1 <= i < k -> ~ ss_done (ss_run i act input ss0 )) ->
      (forall i, 1 <= i < k -> ~ ss_done (ss_run i act input ss0')) ->
      (ss_done (ss_run k act input ss0) <-> ss_done (ss_run k act input ss0')).
  Proof.
    intros Halign Hd0 Hd0' Hz Hz' Hpub k Hnd Hnd'.
    destruct k as [| k].
    { unfold done_set. cbn [run_n]. rewrite Hd0, Hd0'. reflexivity. }
    assert (Hndk : forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input ss0))
      by (intros i Hi; apply Hnd; lia).
    assert (Hndk' : forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input ss0'))
      by (intros i Hi; apply Hnd'; lia).
    set (ssk  := ss_run k act input ss0)  in *.
    set (ssk' := ss_run k act input ss0') in *.
    change (ss_run (S k) act input ss0)  with (ss_step act ssk  input).
    change (ss_run (S k) act input ss0') with (ss_step act ssk' input).
    unfold done_set.
    rewrite (done_public act a_idx input ssk ssk' Halign
               (valid_settled_run ctx cost_limit act a_idx input ss0  k Halign Hz)
               (valid_settled_run ctx cost_limit act a_idx input ss0' k Halign Hz')
               (pub_eq_run act a_idx input ss0 ss0' k Hndk Hndk' Hpub)
               (valid_lockstep act a_idx input ss0 ss0' Halign Hz Hz' Hpub k
                  Hndk Hndk')).
    reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* PHASE 4: the first done cycle is unique, and the same for two states  *)
  (* with the same public view -- latency non-interference.                *)
  (* ------------------------------------------------------------------- *)

  Definition first_done (act: tfs_action sched) (input: input_t)
      (ss0: sched_sys_state) (N: nat) : Prop :=
    ss_done (ss_run N act input ss0)
    /\ forall i, i < N -> ~ ss_done (ss_run i act input ss0).

  Lemma first_done_unique (act: tfs_action sched) (input: input_t)
      (ss0: sched_sys_state) (N N': nat) :
    first_done act input ss0 N -> first_done act input ss0 N' -> N = N'.
  Proof.
    intros [HN HltN] [HN' HltN'].
    destruct (Nat.lt_trichotomy N N') as [H | [H | H]].
    - destruct (HltN' N H HN).
    - exact H.
    - destruct (HltN N' H HN').
  Qed.

  Local Notation src_st_env  := (ContextEnv.(env_t) (tf_states_type s_sz)).
  Local Notation src_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation src_sys_state := (src_st_env * src_out_env)%type.

  Theorem latency_noninterference (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (ss0 ss0': sched_sys_state) (N N': nat) :
    act_idx_aligned ctx cost_limit act a_idx ->
    (fst ss0 ).[tfs_done_signal sched] = Bits.zero ->
    (fst ss0').[tfs_done_signal sched] = Bits.zero ->
    (forall n_idx, (fst ss0 ).[tf_dfg_v a_idx n_idx] = Bits.zero) ->
    (forall n_idx, (fst ss0').[tf_dfg_v a_idx n_idx] = Bits.zero) ->
    pub_eq act a_idx input ss0 ss0' ->
    first_done act input ss0  N ->
    first_done act input ss0' N' ->
    N = N'.
  Proof.
    intros Halign Hd0 Hd0' Hz Hz' Hpub [HN HltN] [HN' HltN'].
    destruct (Nat.lt_trichotomy N N') as [Hlt | [Heq | Hgt]]; [ | exact Heq | ].
    - destruct (HltN' N Hlt).
      apply (done_lockstep act a_idx input ss0 ss0' Halign Hd0 Hd0' Hz Hz' Hpub N
               (fun i Hi => HltN  i (proj2 Hi))
               (fun i Hi => HltN' i (Nat.lt_trans _ _ _ (proj2 Hi) Hlt))).
      exact HN.
    - destruct (HltN N' Hgt).
      apply (done_lockstep act a_idx input ss0 ss0' Halign Hd0 Hd0' Hz Hz' Hpub N'
               (fun i Hi => HltN  i (Nat.lt_trans _ _ _ (proj2 Hi) Hgt))
               (fun i Hi => HltN' i (proj2 Hi))).
      exact HN'.
  Qed.

  (* The zeroing side conditions are exactly what [start_rel] provides. *)
  Corollary latency_noninterference_start (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (sp0 sp0': src_sys_state) (ss0 ss0': sched_sys_state)
      (N N': nat) :
    act_idx_aligned ctx cost_limit act a_idx ->
    start_rel ctx cost_limit sp0  ss0  ->
    start_rel ctx cost_limit sp0' ss0' ->
    pub_eq act a_idx input ss0 ss0' ->
    first_done act input ss0  N ->
    first_done act input ss0' N' ->
    N = N'.
  Proof.
    intros Halign [_ [_ Hz]] [_ [_ Hz']] Hpub HN HN'.
    exact (latency_noninterference act a_idx input ss0 ss0' N N' Halign
             (Hz  (tfs_done_signal sched) I) (Hz' (tfs_done_signal sched) I)
             (fun n_idx => Hz  (tf_dfg_v a_idx n_idx) I)
             (fun n_idx => Hz' (tf_dfg_v a_idx n_idx) I)
             Hpub HN HN').
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The observable restatement: [pub_eq] follows from equality of the     *)
  (* pre- and post-action outputs alone, so latency is a function of data  *)
  (* an output observer already has.                                       *)
  (* ------------------------------------------------------------------- *)

  Local Notation spec_run act sp input :=
    (tf_ops_run s_sz i_sz o_sz (tfs_spec_action_ops ctx act) sp input).

  Theorem obs_eq_pub_eq (act: tfs_action sched) (a_idx: a_index) (input: input_t)
      (sp sp': src_sys_state) (ss ss': sched_sys_state) :
    act_idx_aligned ctx cost_limit act a_idx ->
    (forall sv, (fst ss ).[tf_dfg_s sv] = (fst sp ).[sv]) ->
    (forall ov, (snd ss ).[ov] = (snd sp ).[ov]) ->
    (forall sv, (fst ss').[tf_dfg_s sv] = (fst sp').[sv]) ->
    (forall ov, (snd ss').[ov] = (snd sp').[ov]) ->
    (forall ov, (snd sp).[ov] = (snd sp').[ov]) ->
    (forall ov, (snd (spec_run act sp  input)).[ov]
              = (snd (spec_run act sp' input)).[ov]) ->
    pub_eq act a_idx input ss ss'.
  Proof.
    intros Halign Hs Ho Hs' Ho' Hpre Hpost.
    destruct (dfg_action_semantics ctx cost_limit act a_idx sp ss input
                Halign Hs Ho) as [_ [Hout _]].
    destruct (dfg_action_semantics ctx cost_limit act a_idx sp' ss' input
                Halign Hs' Ho') as [_ [Hout' _]].
    split.
    - intro o. rewrite (Ho o), (Ho' o). exact (Hpre o).
    - intros o r Hin. unfold nval, node_ref_expr.
      rewrite (pub_eq_root_width act o r Hin).
      rewrite (Hout o r Hin), (Hout' o r Hin). exact (Hpost o).
  Qed.

  (* The campaign's headline, in observable terms: the cycle count depends only
     on the action, the input, and the outputs before and after. *)
  Corollary latency_from_outputs (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (sp0 sp0': src_sys_state) (ss0 ss0': sched_sys_state)
      (N N': nat) :
    act_idx_aligned ctx cost_limit act a_idx ->
    start_rel ctx cost_limit sp0  ss0  ->
    start_rel ctx cost_limit sp0' ss0' ->
    (forall ov, (snd sp0).[ov] = (snd sp0').[ov]) ->
    (forall ov, (snd (spec_run act sp0  input)).[ov]
              = (snd (spec_run act sp0' input)).[ov]) ->
    first_done act input ss0  N ->
    first_done act input ss0' N' ->
    N = N'.
  Proof.
    intros Halign Hst Hst' Hpre Hpost HN HN'.
    assert (Hsr : forall (sp: src_sys_state) (ss: sched_sys_state),
              start_rel ctx cost_limit sp ss ->
              (forall sv, (fst ss).[tf_dfg_s sv] = (fst sp).[sv])
              /\ (forall ov, (snd ss).[ov] = (snd sp).[ov])).
    { intros sp ss [Hsnd [Hmap _]]. split.
      - intro sv. rewrite <- Hmap, getenv_maps_from. reflexivity.
      - intro ov. rewrite Hsnd. reflexivity. }
    destruct (Hsr sp0  ss0  Hst)  as [Hs0  Ho0 ].
    destruct (Hsr sp0' ss0' Hst') as [Hs0' Ho0'].
    exact (latency_noninterference_start act a_idx input sp0 sp0' ss0 ss0' N N'
             Halign Hst Hst'
             (obs_eq_pub_eq act a_idx input sp0 sp0' ss0 ss0'
                Halign Hs0 Ho0 Hs0' Ho0' Hpre Hpost)
             HN HN').
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The IPR emulator.  It sees only the inputs, the current outputs and   *)
  (* the specification: outputs hold until the action completes, then take *)
  (* the specification's values.  The one free variable is the cycle count *)
  (* N, which [latency_from_outputs] pins to public data.                  *)
  (* ------------------------------------------------------------------- *)

  Lemma first_done_exists (act: tfs_action sched) (sp0: src_sys_state)
      (ss0: sched_sys_state) (input: input_t) :
    start_rel ctx cost_limit sp0 ss0 ->
    exists N, first_done act input ss0 N.
  Proof.
    intro Hstart.
    destruct (variable_scheduler_correct ctx cost_limit act sp0 ss0 input Hstart)
      as [N [Hbefore [Hdone _]]].
    exists N. split; assumption.
  Qed.

  Definition emulate (act: tfs_action sched) (input: input_t)
      (sp0: src_sys_state) (N k: nat) (ov: o_var) :=
    if Nat.ltb k N then (snd sp0).[ov] else (snd (spec_run act sp0 input)).[ov].

  Theorem emulator_correct (act: tfs_action sched) (sp0: src_sys_state)
      (ss0: sched_sys_state) (input: input_t) (N: nat) :
    start_rel ctx cost_limit sp0 ss0 ->
    first_done act input ss0 N ->
    forall k, k <= N ->
      forall ov, (snd (ss_run k act input ss0)).[ov]
               = emulate act input sp0 N k ov.
  Proof.
    intros Hstart [Hdone Hbefore] k Hk ov. unfold emulate.
    destruct (Nat.ltb_spec k N) as [Hlt | Hge].
    - assert (Hnd : forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input ss0))
        by (intros i Hi; apply Hbefore; lia).
      rewrite (out_run_stable act ss0 input ov k Hnd).
      rewrite (proj1 Hstart). reflexivity.
    - assert (HkN : k = N) by lia. subst k.
      destruct (scheduler_done_correct ctx cost_limit act sp0 ss0 input N
                  Hstart Hbefore Hdone) as [_ Hout].
      rewrite Hout. reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The latency function [L] itself, and its two properties: it is the    *)
  (* completion cycle, and it depends only on publicly visible data.       *)
  (* ------------------------------------------------------------------- *)

  Definition done_test (act: tfs_action sched) (input: input_t)
      (ss0: sched_sys_state) (k: nat) : bool :=
    if done_set_dec ctx cost_limit (ss_run k act input ss0) then true else false.

  Lemma done_test_true (act: tfs_action sched) (input: input_t)
      (ss0: sched_sys_state) (k: nat) :
    done_test act input ss0 k = true <-> ss_done (ss_run k act input ss0).
  Proof.
    unfold done_test.
    destruct (done_set_dec ctx cost_limit (ss_run k act input ss0)) as [Hd | Hd].
    - split; [ intros _; exact Hd | reflexivity ].
    - split; [ discriminate | intro Hc; contradiction ].
  Qed.

  Definition L (act: tfs_action sched) (input: input_t)
      (ss0: sched_sys_state) : nat :=
    first_true (done_test act input ss0) (S (settle_bound ctx cost_limit act)) 0.

  Theorem L_first_done (act: tfs_action sched) (sp0: src_sys_state)
      (ss0: sched_sys_state) (input: input_t) :
    start_rel ctx cost_limit sp0 ss0 ->
    first_done act input ss0 (L act input ss0).
  Proof.
    intro Hstart.
    destruct (done_by_settle_bound ctx cost_limit act sp0 ss0 input Hstart)
      as [N [HNle HNdone]].
    destruct (first_true_spec (done_test act input ss0)
                (S (settle_bound ctx cost_limit act)) 0 N
                (Nat.le_0_l N) ltac:(lia)
                (proj2 (done_test_true act input ss0 N) HNdone)) as [H1 H2].
    split.
    - exact (proj1 (done_test_true act input ss0 _) H1).
    - intros i Hi Hc.
      pose proof (H2 i (Nat.le_0_l i) Hi) as Hfalse.
      rewrite (proj2 (done_test_true act input ss0 i) Hc) in Hfalse.
      discriminate Hfalse.
  Qed.

  (* [L] is a function of the action, the input, and the outputs before and
     after -- never of the secret state. *)
  Corollary L_public (act: tfs_action sched) (a_idx: a_index) (input: input_t)
      (sp0 sp0': src_sys_state) (ss0 ss0': sched_sys_state) :
    act_idx_aligned ctx cost_limit act a_idx ->
    start_rel ctx cost_limit sp0  ss0  ->
    start_rel ctx cost_limit sp0' ss0' ->
    (forall ov, (snd sp0).[ov] = (snd sp0').[ov]) ->
    (forall ov, (snd (spec_run act sp0  input)).[ov]
              = (snd (spec_run act sp0' input)).[ov]) ->
    L act input ss0 = L act input ss0'.
  Proof.
    intros Halign Hst Hst' Hpre Hpost.
    exact (latency_from_outputs act a_idx input sp0 sp0' ss0 ss0' _ _
             Halign Hst Hst' Hpre Hpost
             (L_first_done act sp0  ss0  input Hst)
             (L_first_done act sp0' ss0' input Hst')).
  Qed.

  Corollary emulator_correct_L (act: tfs_action sched) (sp0: src_sys_state)
      (ss0: sched_sys_state) (input: input_t) :
    start_rel ctx cost_limit sp0 ss0 ->
    forall k, k <= L act input ss0 ->
      forall ov, (snd (ss_run k act input ss0)).[ov]
               = emulate act input sp0 (L act input ss0) k ov.
  Proof.
    intro Hstart.
    exact (emulator_correct act sp0 ss0 input (L act input ss0) Hstart
             (L_first_done act sp0 ss0 input Hstart)).
  Qed.
End IPR.

Print Assumptions taint_propagates.
Print Assumptions untainted_roots_derivable.
Print Assumptions svar_not_derivable.
Print Assumptions untainted_derivable.
Print Assumptions pub_eq_run.
Print Assumptions valid_lockstep.
Print Assumptions done_lockstep.
Print Assumptions latency_noninterference_start.
Print Assumptions latency_from_outputs.
Print Assumptions emulator_correct.
Print Assumptions L_public.
Print Assumptions emulator_correct_L.
