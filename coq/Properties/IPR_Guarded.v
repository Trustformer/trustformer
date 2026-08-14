(*! Information-Preserving Refinement under GUARDED untainting.

    Campaign: agents/whitebox-untainting/PLAN.md

    `IPR.v` proves that latency is public when every phi with a secret condition
    is compiled constant-time.  Here the same chain is re-proved when the
    analysis may declassify a condition *conditionally* -- "c is derivable
    whenever we are on this path" -- which is what the paper's backward
    untainting actually produces.

    A path guard is a list of selector literals, threaded through the compile
    recursion; [path_ok] is the checker that validates an untrusted analysis,
    and [decl_compose] is the rule that lets one declassification rest on
    another.  Every result degenerates to its `IPR.v` counterpart when nothing
    is declassified (see the `_recovered` corollaries).
!*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.
Require Import Trustformer.Properties.SchedulerSimulation.
Require Import Trustformer.Properties.IPR.

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

Section IPRGuarded.
  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).
  (* the unconditional half of the user's obligation, as in IPR.v *)
  Context (Hdecls : forall act a_idx input, uncond_sound ctx cost_limit act a_idx input).

  Local Notation sched := (tfs_schedule ctx cost_limit).
  Local Notation s_var := (tfs_spec_states ctx).
  Local Notation i_var := (tfs_spec_inputs ctx).
  Local Notation o_var := (tfs_spec_outputs ctx).

  Local Notation i_sz := (tfs_spec_inputs_size ctx).
  (* [o_sz] and [oo_sz] are convertible but NOT interchangeable: using the wrong
     one elaborates a different FiniteType instance and breaks [rewrite]. *)
  Local Notation o_sz := (tfs_spec_outputs_size ctx).
  Local Notation ss_sz := (tfs_states_size sched).
  Local Notation oo_sz := (tfs_outputs_size sched).

  (* Without these, [ContextEnv] resolution for the scheduler's register types
     diverges instead of failing. *)
  Hint Extern 0 (FiniteType s_var) => exact (tfs_spec_states_fin ctx)  : typeclass_instances.
  Hint Extern 0 (FiniteType i_var) => exact (tfs_spec_inputs_fin ctx)  : typeclass_instances.
  Hint Extern 0 (FiniteType o_var) => exact (tfs_spec_outputs_fin ctx) : typeclass_instances.
  Hint Extern 0 (FiniteType (tfs_states sched))  => exact (tfs_states_fin sched)  : typeclass_instances.
  Hint Extern 0 (FiniteType (tfs_outputs sched)) => exact (tfs_outputs_fin sched) : typeclass_instances.

  Local Notation sched_st_env  := (ContextEnv.(env_t) (tf_states_type (tfs_states_size sched))).
  Local Notation sched_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation sched_sys_state := (sched_st_env * sched_out_env)%type.
  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).
  Local Notation a_index := (Vect.index (length (buffer_needs ctx cost_limit))).
  Local Notation dfg_t := (@dfg_state_t s_var i_var o_var).

  Local Notation eval1 e ss input :=
    (tf_eval_expr ss_sz i_sz oo_sz (szB := 1) e ss input).

  (* ------------------------------------------------------------------ *)
  (* Guards.  [lit] / [guard_incl] / [path_ok] are the scheduler's         *)
  (* (coq/Scheduler/VariableScheduler.v); only their semantics live here.  *)
  (* ------------------------------------------------------------------ *)

  Definition bit_of (b: bool) : bits_t 1 := if b then Bits.ones 1 else Bits.zero.

  Definition pi_holds (act: tfs_action sched) (a_idx: a_index) (input: input_t)
      (pi: list lit) (ss: sched_sys_state) : Prop :=
    forall c b, List.In (c, b) pi ->
      nval ctx cost_limit act a_idx ss input 1 c = bit_of b.

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

  (* ------------------------------------------------------------------ *)
  (* Guarded derivability, and the algebra the analysis reasons with.     *)
  (* ------------------------------------------------------------------ *)

  (* what the analysis publishes *)
  Variable critb : nid_t -> bool.
  Variable guard_of : nid_t -> list lit.
  (* keyed by the buffer slot number returned by [list_assoc bufs] *)
  Variable buf_guard : nat -> list lit.

  Local Notation nsz act n :=
    (sz (nth n (graph (build_dfg ctx act)) {| nid := 0; op := DFG_Empty; sz := 0 |})).

  Definition gderivable (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (g: list lit) (n: nid_t) : Prop :=
    forall ss ss',
      pub_eq ctx cost_limit act a_idx input ss ss' ->
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

  (* An unconditionally derivable node is derivable under any guard. *)
  Lemma untainted_gderivable (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (g: list lit) (n: nid_t) :
    1 <= n ->
    n < length (graph (build_dfg ctx act)) ->
    ~ List.In n (get_tainted ctx (build_dfg ctx act)) ->
    gderivable act a_idx input g n.
  Proof.
    intros Hn1 Hnlen Hnt ss ss' Hpub _ _.
    exact (untainted_derivable ctx cost_limit Hdecls act a_idx input n Hn1 Hnlen Hnt
             ss ss' Hpub).
  Qed.

  (* [decl_instance] is the scheduler-layer record (coq/Scheduler/DFG.v): the
     obligation below is about the very data the user supplies. *)

  (* The uniform user obligation: blackbox is [sources = []] and [guard = []],
     an unconditional inverter has [guard = []], a phi rule has a guard. *)
  Definition instance_sound (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (i: decl_instance) : Prop :=
    forall ss ss',
      pub_eq ctx cost_limit act a_idx input ss ss' ->
      pi_holds act a_idx input (di_guard i) ss ->
      pi_holds act a_idx input (di_guard i) ss' ->
      (forall s, List.In s (di_sources i) ->
         nval ctx cost_limit act a_idx ss  input (nsz act s) s
         = nval ctx cost_limit act a_idx ss' input (nsz act s) s) ->
      nval ctx cost_limit act a_idx ss  input
        (nsz act (di_target i)) (di_target i)
      = nval ctx cost_limit act a_idx ss' input
        (nsz act (di_target i)) (di_target i).

  (* CHAINING.  A rule whose sources are themselves only known under [g]
     yields its target under both guards.  This is what lets guarded facts
     be derived from other guarded facts rather than only from unconditional
     ones. *)
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

  (* The two degenerate uses, spelled out. *)
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
      [ unfold guard_incl; rewrite app_nil_r; apply forallb_forall;
        intros a Ha; apply existsb_exists; exists a; split;
        [ exact Ha | unfold lit_eqb; rewrite Nat.eqb_refl, Bool.eqb_reflx;
          reflexivity ] | ].
    apply (decl_compose act a_idx input i []); [ exact Hi | ].
    intros s Hs. destruct (Hsrc s Hs) as [H1 [H2 H3]].
    exact (untainted_gderivable act a_idx input [] s H1 H2 H3).
  Qed.

  (* What the analysis owes the proof: every condition it declassifies is
     guarded-derivable under the guard it published. *)
  Definition analysis_sound (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) : Prop :=
    forall c, critb c = false -> gderivable act a_idx input (guard_of c) c.

  (* Bridge to IPR.v's unconditional obligation, so the rules in coq/Rules/
     discharge [Hdecls] directly. *)
  Lemma uncond_guard_nil (dfg: @dfg_state_t s_var i_var o_var) (i: decl_instance) :
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
    uncond_sound ctx cost_limit act a_idx input.
  Proof.
    intros Hall i Hi Hsrc ss ss' Hpub.
    pose proof (uncond_guard_nil (build_dfg ctx act) i Hi) as Hg.
    apply (Hall i Hi ss ss' Hpub);
      [ rewrite Hg; intros c b Hin; destruct Hin
      | rewrite Hg; intros c b Hin; destruct Hin
      | intros s Hs; exact (Hsrc s Hs ss ss' Hpub) ].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The checker, from the scheduler layer, applied to this analysis.     *)
  (* ------------------------------------------------------------------ *)

  Local Notation path_ok := (path_ok ctx critb guard_of buf_guard).

  Lemma valid_public_guarded (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (ss ss': sched_sys_state) :
    (* the compiler acts on the analysis: a declassified condition is compiled
       non-critically *)
    (forall c, critb c = false -> ~ List.In c (get_tainted ctx (build_dfg ctx act))) ->
    (* guarded derivability, as supplied by the whitebox analysis *)
    analysis_sound act a_idx input ->
    act_idx_aligned ctx cost_limit act a_idx ->
    valid_settled ctx cost_limit act a_idx ss input ->
    valid_settled ctx cost_limit act a_idx ss' input ->
    pub_eq ctx cost_limit act a_idx input ss ss' ->
    (* the validity registers agree only under their own guards *)
    (forall n_idx,
        pi_holds act a_idx input (buf_guard (index_to_nat n_idx)) ss ->
        pi_holds act a_idx input (buf_guard (index_to_nat n_idx)) ss' ->
        (fst ss).[tf_dfg_v a_idx n_idx]
        = (fst ss').[tf_dfg_v a_idx n_idx]) ->
    forall bufs,
      (forall e, List.In e bufs ->
         List.In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
      forall fuel n pi,
        1 <= n ->
        n < length (graph (build_dfg ctx act)) ->
        n < fuel ->
        path_ok fuel (build_dfg ctx act) n bufs pi = true ->
        pi_holds act a_idx input pi ss ->
        pi_holds act a_idx input pi ss' ->
        eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx
                      (build_dfg ctx act) n bufs)) ss input
        = eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx
                      (build_dfg ctx act) n bufs)) ss' input.
  Proof.
    intros Hlink Hguard Halign Hvs Hvs' Hpub Hveq bufs Hsub fuel.
    induction fuel as [| fuel IH]; intros n pi Hn1 Hnlen Hnfuel Hok Hpi Hpi'; [ lia | ].
    cbn [path_ok] in Hok.
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:Hla.
    { cbn [compile_dfg_expr]. rewrite Hla. cbv beta iota.
      cbv beta iota in Hok.
      destruct (index_of_nat
                  (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))
                  m) as [n_idx' |] eqn:Hni; cbn [snd]; [ | reflexivity ].
      rewrite !eval1_svar_v.
      assert (Hmi : index_to_nat n_idx' = m)
        by (apply index_to_nat_of_nat; exact Hni).
      apply Hveq; rewrite Hmi;
        [ exact (guard_incl_holds act a_idx input _ _ ss  Hok Hpi)
        | exact (guard_incl_holds act a_idx input _ _ ss' Hok Hpi') ]. }
    cbv beta iota in Hok.
    cbn [compile_dfg_expr]. rewrite Hla. cbv beta iota.
    set (node := nth n (graph (build_dfg ctx act))
                   {| nid := 0; op := DFG_Empty; sz := 0 |}) in *.
    assert (Hnode_in : List.In node (graph (build_dfg ctx act)))
      by (unfold node; apply nth_In; exact Hnlen).
    pose proof (wfg_build_dfg ctx cost_limit act node Hnode_in) as Hfg.
    assert (Hrange : forall x, List.In x (get_args ctx node) -> 1 <= x /\ x < n)
      by (intros x Hx; exact (node_args_range ctx cost_limit act n Hn1 Hnlen x Hx)).
    destruct (op node) as [cst | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | ]
      eqn:Hop; cbv beta iota in Hok.
    - reflexivity.
    - reflexivity.
    - destruct v; reflexivity.
    - assert (Hain : List.In arg (get_args ctx node))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      destruct (Hrange arg Hain) as [Ha1 Ha2].
      destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                  arg bufs) as [ae ve] eqn:E1.
      pose proof (IH arg pi Ha1 ltac:(lia) ltac:(lia) Hok Hpi Hpi') as Ha.
      rewrite E1 in Ha. cbn [snd] in Ha |- *. exact Ha.
    - assert (Ha1in : List.In a1 (get_args ctx node))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      assert (Ha2in : List.In a2 (get_args ctx node))
        by (unfold get_args; rewrite Hop; right; left; reflexivity).
      destruct (Hrange a1 Ha1in) as [Hb1 Hb2].
      destruct (Hrange a2 Ha2in) as [Hd1 Hd2].
      apply andb_prop in Hok. destruct Hok as [Hok1 Hok2].
      destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                  a1 bufs) as [a1e v1e] eqn:E1.
      destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                  a2 bufs) as [a2e v2e] eqn:E2.
      pose proof (IH a1 pi Hb1 ltac:(lia) ltac:(lia) Hok1 Hpi Hpi') as Hx1.
      pose proof (IH a2 pi Hd1 ltac:(lia) ltac:(lia) Hok2 Hpi Hpi') as Hx2.
      rewrite E1 in Hx1. rewrite E2 in Hx2. cbn [snd] in Hx1, Hx2 |- *.
      rewrite !valid_and_eval. rewrite Hx1, Hx2. reflexivity.
    - assert (Hain : List.In arg (get_args ctx node))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      destruct (Hrange arg Hain) as [Ha1 Ha2].
      destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                  arg bufs) as [ae ve] eqn:E1.
      pose proof (IH arg pi Ha1 ltac:(lia) ltac:(lia) Hok Hpi Hpi') as Ha.
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
      apply andb_prop in Hok. destruct Hok as [Hokc Hokb].
      destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                  cnd bufs) as [ce cv] eqn:Ec.
      destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                  tid bufs) as [te tv] eqn:Et.
      destruct (compile_dfg_expr ctx cost_limit fuel a_idx (build_dfg ctx act)
                  eid bufs) as [ee ev] eqn:Ee.
      pose proof (IH cnd pi Hc1 ltac:(lia) ltac:(lia) Hokc Hpi Hpi') as Hcc.
      rewrite Ec in Hcc. cbn [snd] in Hcc |- *.
      unfold node_args_sz in Hfg. rewrite Hop in Hfg.
      destruct Hfg as [Hf1 [Hf2 Hf3]].
      destruct (wsz_node_sz ctx cost_limit act cnd 1 Hf1) as [Hclen Hcsz].
      destruct (critb cnd) eqn:Hcb.
      + (* the analysis keeps this phi critical: both branches under the same path *)
        apply andb_prop in Hokb. destruct Hokb as [Hokt Hoke].
        pose proof (IH tid pi Ht1 ltac:(lia) ltac:(lia) Hokt Hpi Hpi') as Hct.
        pose proof (IH eid pi He1 ltac:(lia) ltac:(lia) Hoke Hpi Hpi') as Hce.
        rewrite Et in Hct. rewrite Ee in Hce. cbn [snd] in Hct, Hce.
        destruct (mem cnd (get_tainted ctx (build_dfg ctx act))) as [Hm | Hnm].
        * rewrite !valid_and_eval. rewrite Hcc, Hct, Hce. reflexivity.
        * (* blackbox case, unchanged from [valid_public] *)
          rewrite !valid_and_eval. rewrite Hcc.
          destruct (bits1_cases (eval1 cv ss' input)) as [Hones | Hzero];
            [ | rewrite Hzero, !and1_zero_l; reflexivity ].
          f_equal.
          assert (Hcnt : ~ List.In cnd (get_tainted ctx (build_dfg ctx act)))
            by (intro Hin; exact (Hnm (In_member _ _ Hin))).
          assert (Hvalc : eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx
                            (build_dfg ctx act) cnd bufs)) ss input = Bits.ones 1)
            by (rewrite Ec; cbn [snd]; rewrite Hcc; exact Hones).
          assert (Hvalc' : eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx
                            (build_dfg ctx act) cnd bufs)) ss' input = Bits.ones 1)
            by (rewrite Ec; cbn [snd]; exact Hones).
          pose proof (compile_subst_valid ctx cost_limit act a_idx ss input
                        Halign Hvs bufs Hsub fuel cnd 1 Hc1 Hclen ltac:(lia)
                        (eq_sym Hcsz) Hvalc) as S1.
          pose proof (compile_subst_valid ctx cost_limit act a_idx ss' input
                        Halign Hvs' bufs Hsub fuel cnd 1 Hc1 Hclen ltac:(lia)
                        (eq_sym Hcsz) Hvalc') as S2.
          rewrite Ec in S1, S2. cbn [fst] in S1, S2.
          assert (Hcev : eval1 ce ss input = eval1 ce ss' input).
          { rewrite S1, S2.
            rewrite (compile_fuel_irrel ctx cost_limit act a_idx [] cnd Hc1 Hclen
                       fuel (length (graph (build_dfg ctx act))) ltac:(lia) Hclen).
            pose proof (untainted_derivable ctx cost_limit Hdecls act a_idx input cnd
                          Hc1 Hclen Hcnt ss ss' Hpub) as Hcd.
            rewrite Hcsz in Hcd. exact Hcd. }
          assert (Hcase : (tv = tf_const 1 /\ ev = tf_const 1)
                          \/ valid_expr_if ctx cost_limit ce tv ev
                             = tf_expr_if ce tv ev).
          { unfold valid_expr_if.
            destruct tv as [vt| | | | | |]; try (right; reflexivity).
            destruct vt as [|[|vt]]; try (right; reflexivity).
            destruct ev as [vee| | | | | |]; try (right; reflexivity).
            destruct vee as [|[|vee]]; try (right; reflexivity).
            left; split; reflexivity. }
          destruct Hcase as [[Htc Hec] | Hcs].
          -- subst tv ev. reflexivity.
          -- rewrite Hcs. cbn [tf_eval_expr].
             rewrite Hcev, Hct, Hce. reflexivity.
      + (* the analysis declassifies the condition under [guard_of cnd] *)
        apply andb_prop in Hokb. destruct Hokb as [Hokb Hoke].
        apply andb_prop in Hokb. destruct Hokb as [Hincl Hokt].
        assert (Hcnt : ~ List.In cnd (get_tainted ctx (build_dfg ctx act)))
          by (apply Hlink; exact Hcb).
        destruct (mem cnd (get_tainted ctx (build_dfg ctx act))) as [Hm | Hnm].
        { exfalso. apply Hcnt. exact (member_In _ _ Hm). }
        rewrite !valid_and_eval. rewrite Hcc.
        destruct (bits1_cases (eval1 cv ss' input)) as [Hones | Hzero];
          [ | rewrite Hzero, !and1_zero_l; reflexivity ].
        f_equal.
        assert (Hvalc : eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx
                          (build_dfg ctx act) cnd bufs)) ss input = Bits.ones 1)
          by (rewrite Ec; cbn [snd]; rewrite Hcc; exact Hones).
        assert (Hvalc' : eval1 (snd (compile_dfg_expr ctx cost_limit fuel a_idx
                          (build_dfg ctx act) cnd bufs)) ss' input = Bits.ones 1)
          by (rewrite Ec; cbn [snd]; exact Hones).
        pose proof (compile_subst_valid ctx cost_limit act a_idx ss input
                      Halign Hvs bufs Hsub fuel cnd 1 Hc1 Hclen ltac:(lia)
                      (eq_sym Hcsz) Hvalc) as S1.
        pose proof (compile_subst_valid ctx cost_limit act a_idx ss' input
                      Halign Hvs' bufs Hsub fuel cnd 1 Hc1 Hclen ltac:(lia)
                      (eq_sym Hcsz) Hvalc') as S2.
        rewrite Ec in S1, S2. cbn [fst] in S1, S2.
        assert (Href : eval1 ce ss input
                       = nval ctx cost_limit act a_idx ss input 1 cnd).
        { rewrite S1.
          rewrite (compile_fuel_irrel ctx cost_limit act a_idx [] cnd Hc1 Hclen
                     fuel (length (graph (build_dfg ctx act))) ltac:(lia) Hclen).
          unfold nval, node_ref_expr. reflexivity. }
        assert (Href' : eval1 ce ss' input
                        = nval ctx cost_limit act a_idx ss' input 1 cnd).
        { rewrite S2.
          rewrite (compile_fuel_irrel ctx cost_limit act a_idx [] cnd Hc1 Hclen
                     fuel (length (graph (build_dfg ctx act))) ltac:(lia) Hclen).
          unfold nval, node_ref_expr. reflexivity. }
        assert (Hcev : eval1 ce ss input = eval1 ce ss' input).
        { rewrite Href, Href'.
          pose proof (Hguard cnd Hcb ss ss' Hpub
                        (guard_incl_holds act a_idx input _ _ ss  Hincl Hpi)
                        (guard_incl_holds act a_idx input _ _ ss' Hincl Hpi'))
            as Hcd.
          rewrite Hcsz in Hcd. exact Hcd. }
        assert (Hcase : (tv = tf_const 1 /\ ev = tf_const 1)
                        \/ valid_expr_if ctx cost_limit ce tv ev
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
                           Hoke Hp0 Hp0') as Hce.
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
                           Hokt Hp1 Hp1') as Hct.
             rewrite Et in Hct. cbn [snd] in Hct. exact Hct.
    - reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Conservativity: an analysis that declassifies nothing satisfies the  *)
  (* checker on every path, and the guarded lemma degenerates to the      *)
  (* existing [valid_public].                                            *)
  (* ------------------------------------------------------------------ *)

  Lemma path_ok_all_critical (act: tfs_action sched) :
    (forall c, critb c = true) ->
    (forall m, buf_guard m = []) ->
    forall bufs fuel n pi,
      1 <= n ->
      n < length (graph (build_dfg ctx act)) ->
      n < fuel ->
      path_ok fuel (build_dfg ctx act) n bufs pi = true.
  Proof.
    intros Hcb Hbg bufs fuel.
    induction fuel as [| fuel IH]; intros n pi Hn1 Hnlen Hnfuel; [ lia | ].
    cbn [path_ok].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:Hla;
      [ rewrite Hbg; reflexivity | ].
    cbv beta iota.
    set (node := nth n (graph (build_dfg ctx act))
                   {| nid := 0; op := DFG_Empty; sz := 0 |}) in *.
    assert (Hrange : forall x, List.In x (get_args ctx node) -> 1 <= x /\ x < n)
      by (intros x Hx; exact (node_args_range ctx cost_limit act n Hn1 Hnlen x Hx)).
    destruct (op node) as [cst | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | ]
      eqn:Hop; cbv beta iota; try reflexivity.
    - assert (Hain : List.In arg (get_args ctx node))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      destruct (Hrange arg Hain) as [Ha1 Ha2].
      apply IH; [ exact Ha1 | lia | lia ].
    - assert (Ha1in : List.In a1 (get_args ctx node))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      assert (Ha2in : List.In a2 (get_args ctx node))
        by (unfold get_args; rewrite Hop; right; left; reflexivity).
      destruct (Hrange a1 Ha1in) as [Hb1 Hb2].
      destruct (Hrange a2 Ha2in) as [Hd1 Hd2].
      apply andb_true_intro. split; apply IH; solve [ assumption | lia ].
    - assert (Hain : List.In arg (get_args ctx node))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      destruct (Hrange arg Hain) as [Ha1 Ha2].
      apply IH; [ exact Ha1 | lia | lia ].
    - assert (Hcin : List.In cnd (get_args ctx node))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      assert (Htin : List.In tid (get_args ctx node))
        by (unfold get_args; rewrite Hop; right; left; reflexivity).
      assert (Hein : List.In eid (get_args ctx node))
        by (unfold get_args; rewrite Hop; right; right; left; reflexivity).
      destruct (Hrange cnd Hcin) as [Hc1 Hc2].
      destruct (Hrange tid Htin) as [Ht1 Ht2].
      destruct (Hrange eid Hein) as [He1 He2].
      rewrite Hcb.
      apply andb_true_intro. split; [ apply IH; solve [ assumption | lia ] | ].
      apply andb_true_intro. split; apply IH; solve [ assumption | lia ].
  Qed.

  Corollary valid_public_recovered (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (ss ss': sched_sys_state) :
    (forall c, critb c = true) ->
    (forall m, buf_guard m = []) ->
    act_idx_aligned ctx cost_limit act a_idx ->
    valid_settled ctx cost_limit act a_idx ss input ->
    valid_settled ctx cost_limit act a_idx ss' input ->
    pub_eq ctx cost_limit act a_idx input ss ss' ->
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
    intros Hcb Hbg Halign Hvs Hvs' Hpub Hveq bufs Hsub fuel n Hn1 Hnlen Hnfuel.
    apply (valid_public_guarded act a_idx input ss ss'
             ltac:(intros c Hc; rewrite Hcb in Hc; discriminate)
             ltac:(intros c Hc; rewrite Hcb in Hc; discriminate)
             Halign Hvs Hvs' Hpub
             (fun n_idx _ _ => Hveq n_idx) bufs Hsub fuel n []);
      [ exact Hn1 | exact Hnlen | exact Hnfuel
      | exact (path_ok_all_critical act Hcb Hbg bufs fuel n [] Hn1 Hnlen Hnfuel)
      | intros c b Hin; destruct Hin
      | intros c b Hin; destruct Hin ].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Per-register guards through the cycle induction.  A guard is stated  *)
  (* over [nval], which [nval_run_stable] shows is invariant across an    *)
  (* action's pre-done cycles, so it needs no temporal machinery.         *)
  (* ------------------------------------------------------------------ *)

  Local Notation ss_step := (sched_step ctx cost_limit).
  Local Notation ss_run  := (run_n ctx cost_limit).
  Local Notation ss_done := (done_set ctx cost_limit).

  Lemma pi_holds_run (act: tfs_action sched) (a_idx: a_index) (input: input_t)
      (ss0: sched_sys_state) (g: list lit) (k: nat) :
    (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input ss0)) ->
    pi_holds act a_idx input g (ss_run k act input ss0) ->
    pi_holds act a_idx input g ss0.
  Proof.
    intros Hnd H c b Hin. specialize (H c b Hin).
    rewrite (nval_run_stable ctx cost_limit act a_idx ss0 input 1 c k Hnd) in H.
    exact H.
  Qed.

  Lemma pi_holds_run_back (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (ss0: sched_sys_state) (g: list lit) (k: nat) :
    (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input ss0)) ->
    pi_holds act a_idx input g ss0 ->
    pi_holds act a_idx input g (ss_run k act input ss0).
  Proof.
    intros Hnd H c b Hin. specialize (H c b Hin).
    rewrite (nval_run_stable ctx cost_limit act a_idx ss0 input 1 c k Hnd).
    exact H.
  Qed.

  Theorem valid_lockstep_guarded (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (ss0 ss0': sched_sys_state) :
    (forall c, critb c = false ->
       ~ List.In c (get_tainted ctx (build_dfg ctx act))) ->
    analysis_sound act a_idx input ->
    (* the checker accepts each buffer root under that register's own guard *)
    (forall n_idx bufs,
        (forall e, List.In e bufs ->
           List.In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
        path_ok (length (graph (build_dfg ctx act))) (build_dfg ctx act)
          (vreg_nid ctx cost_limit a_idx n_idx) bufs
          (buf_guard (index_to_nat n_idx)) = true) ->
    act_idx_aligned ctx cost_limit act a_idx ->
    (forall n_idx, (fst ss0).[tf_dfg_v a_idx n_idx] = Bits.zero) ->
    (forall n_idx, (fst ss0').[tf_dfg_v a_idx n_idx] = Bits.zero) ->
    pub_eq ctx cost_limit act a_idx input ss0 ss0' ->
    forall k,
      (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input ss0)) ->
      (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input ss0')) ->
      forall n_idx,
        pi_holds act a_idx input (buf_guard (index_to_nat n_idx)) ss0 ->
        pi_holds act a_idx input (buf_guard (index_to_nat n_idx)) ss0' ->
        (fst (ss_run k act input ss0)).[tf_dfg_v a_idx n_idx]
        = (fst (ss_run k act input ss0')).[tf_dfg_v a_idx n_idx].
  Proof.
    intros Hlink Hguard Hchk Halign Hz Hz' Hpub k.
    induction k as [| k IH]; intros Hnd Hnd' n_idx Hg Hg'.
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
    pose proof (pub_eq_run ctx cost_limit act a_idx input ss0 ss0' k
                  Hndk Hndk' Hpub) as Hpubk.
    destruct (vreg_nid_node_range ctx cost_limit act a_idx n_idx Halign)
      as [Hn1 Hnlen].
    specialize (Hchk n_idx).
    unfold vreg_nid in Hn1, Hnlen, Hchk.
    apply (valid_public_guarded act a_idx input ssk ssk')
      with (pi := buf_guard (index_to_nat n_idx)).
    - exact Hlink.
    - exact Hguard.
    - exact Halign.
    - exact (valid_settled_run ctx cost_limit act a_idx input ss0  k Halign Hz).
    - exact (valid_settled_run ctx cost_limit act a_idx input ss0' k Halign Hz').
    - exact Hpubk.
    - intros n_idx2 Hp Hp'.
      exact (IH Hndk Hndk' n_idx2
               (pi_holds_run act a_idx input ss0  _ k Hndk  Hp)
               (pi_holds_run act a_idx input ss0' _ k Hndk' Hp')).
    - intros e He. exact (proj1 (proj1 (filter_In _ e _) He)).
    - exact Hn1.
    - exact Hnlen.
    - exact Hnlen.
    - apply Hchk. intros e He. exact (proj1 (proj1 (filter_In _ e _) He)).
    - exact (pi_holds_run_back act a_idx input ss0  _ k Hndk  Hg).
    - exact (pi_holds_run_back act a_idx input ss0' _ k Hndk' Hg').
  Qed.

  Corollary valid_lockstep_recovered (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (ss0 ss0': sched_sys_state) :
    (forall c, critb c = true) ->
    (forall m, buf_guard m = []) ->
    act_idx_aligned ctx cost_limit act a_idx ->
    (forall n_idx, (fst ss0).[tf_dfg_v a_idx n_idx] = Bits.zero) ->
    (forall n_idx, (fst ss0').[tf_dfg_v a_idx n_idx] = Bits.zero) ->
    pub_eq ctx cost_limit act a_idx input ss0 ss0' ->
    forall k,
      (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input ss0)) ->
      (forall i, 1 <= i <= k -> ~ ss_done (ss_run i act input ss0')) ->
      forall n_idx,
        (fst (ss_run k act input ss0)).[tf_dfg_v a_idx n_idx]
        = (fst (ss_run k act input ss0')).[tf_dfg_v a_idx n_idx].
  Proof.
    intros Hcb Hbg Halign Hz Hz' Hpub k Hnd Hnd' n_idx.
    apply (valid_lockstep_guarded act a_idx input ss0 ss0'
             ltac:(intros c Hc; rewrite Hcb in Hc; discriminate)
             ltac:(intros c Hc; rewrite Hcb in Hc; discriminate)); auto.
    - intros n_idx2 bufs Hsub.
      destruct (vreg_nid_node_range ctx cost_limit act a_idx n_idx2 Halign)
        as [Hn1 Hnlen].
      exact (path_ok_all_critical act Hcb Hbg bufs _ _ _ Hn1 Hnlen Hnlen).
    - rewrite Hbg. intros c b Hin. destruct Hin.
    - rewrite Hbg. intros c b Hin. destruct Hin.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The done flag, and hence latency.  Roots are read unconditionally,   *)
  (* so they are checked at the empty path; registers read under a phi    *)
  (* still get an extended path and may keep non-empty guards.            *)
  (* ------------------------------------------------------------------ *)

  Local Notation vm_roots act :=
    (nodup Nat.eq_dec (map snd (var_map (build_dfg ctx act)))).

  Definition roots_checked (act: tfs_action sched) (a_idx: a_index) : Prop :=
    forall n bufs,
      List.In n (map snd (var_map (build_dfg ctx act))) ->
      (forall e, List.In e bufs ->
         List.In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
      path_ok (length (graph (build_dfg ctx act))) (build_dfg ctx act) n bufs []
      = true.

  Theorem done_public_guarded (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (ss ss': sched_sys_state) :
    (forall c, critb c = false ->
       ~ List.In c (get_tainted ctx (build_dfg ctx act))) ->
    analysis_sound act a_idx input ->
    roots_checked act a_idx ->
    act_idx_aligned ctx cost_limit act a_idx ->
    valid_settled ctx cost_limit act a_idx ss input ->
    valid_settled ctx cost_limit act a_idx ss' input ->
    pub_eq ctx cost_limit act a_idx input ss ss' ->
    (forall n_idx,
        pi_holds act a_idx input (buf_guard (index_to_nat n_idx)) ss ->
        pi_holds act a_idx input (buf_guard (index_to_nat n_idx)) ss' ->
        (fst ss).[tf_dfg_v a_idx n_idx]
        = (fst ss').[tf_dfg_v a_idx n_idx]) ->
    (fst (ss_step act ss input)).[tfs_done_signal sched]
    = (fst (ss_step act ss' input)).[tfs_done_signal sched].
  Proof.
    intros Hlink Hguard Hchk Halign Hvs Hvs' Hpub Hveq.
    rewrite (done_val_concrete ctx cost_limit act a_idx ss  input Halign).
    rewrite (done_val_concrete ctx cost_limit act a_idx ss' input Halign).
    f_equal. rewrite !map_map. apply map_ext_in. intros n Hn.
    apply nodup_In in Hn.
    destruct (var_map_node_range ctx cost_limit act n Hn) as [Hn1 Hnlen].
    apply (valid_public_guarded act a_idx input ss ss') with (pi := []).
    - exact Hlink.
    - exact Hguard.
    - exact Halign.
    - exact Hvs.
    - exact Hvs'.
    - exact Hpub.
    - exact Hveq.
    - exact (fun e He => He).
    - exact Hn1.
    - exact Hnlen.
    - exact Hnlen.
    - exact (Hchk n _ Hn (fun e He => He)).
    - intros c b Hin. destruct Hin.
    - intros c b Hin. destruct Hin.
  Qed.

  Theorem done_lockstep_guarded (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (ss0 ss0': sched_sys_state) :
    (forall c, critb c = false ->
       ~ List.In c (get_tainted ctx (build_dfg ctx act))) ->
    analysis_sound act a_idx input ->
    roots_checked act a_idx ->
    (forall n_idx bufs,
        (forall e, List.In e bufs ->
           List.In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
        path_ok (length (graph (build_dfg ctx act))) (build_dfg ctx act)
          (vreg_nid ctx cost_limit a_idx n_idx) bufs
          (buf_guard (index_to_nat n_idx)) = true) ->
    act_idx_aligned ctx cost_limit act a_idx ->
    (fst ss0 ).[tfs_done_signal sched] = Bits.zero ->
    (fst ss0').[tfs_done_signal sched] = Bits.zero ->
    (forall n_idx, (fst ss0 ).[tf_dfg_v a_idx n_idx] = Bits.zero) ->
    (forall n_idx, (fst ss0').[tf_dfg_v a_idx n_idx] = Bits.zero) ->
    pub_eq ctx cost_limit act a_idx input ss0 ss0' ->
    forall k,
      (forall i, 1 <= i < k -> ~ ss_done (ss_run i act input ss0 )) ->
      (forall i, 1 <= i < k -> ~ ss_done (ss_run i act input ss0')) ->
      (ss_done (ss_run k act input ss0) <-> ss_done (ss_run k act input ss0')).
  Proof.
    intros Hlink Hguard Hchk Hbchk Halign Hd0 Hd0' Hz Hz' Hpub k Hnd Hnd'.
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
    rewrite (done_public_guarded act a_idx input ssk ssk' Hlink Hguard Hchk Halign
               (valid_settled_run ctx cost_limit act a_idx input ss0  k Halign Hz)
               (valid_settled_run ctx cost_limit act a_idx input ss0' k Halign Hz')
               (pub_eq_run ctx cost_limit act a_idx input ss0 ss0' k
                  Hndk Hndk' Hpub)
               (fun n_idx Hp Hp' =>
                  valid_lockstep_guarded act a_idx input ss0 ss0'
                    Hlink Hguard Hbchk Halign Hz Hz' Hpub k Hndk Hndk' n_idx
                    (pi_holds_run act a_idx input ss0  _ k Hndk  Hp)
                    (pi_holds_run act a_idx input ss0' _ k Hndk' Hp'))).
    reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The campaign's headline, guarded: latency still depends only on the  *)
  (* action, the input and the outputs before and after.                  *)
  (* ------------------------------------------------------------------ *)

  Definition buffers_checked (act: tfs_action sched) (a_idx: a_index) : Prop :=
    forall n_idx bufs,
      (forall e, List.In e bufs ->
         List.In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) ->
      path_ok (length (graph (build_dfg ctx act))) (build_dfg ctx act)
        (vreg_nid ctx cost_limit a_idx n_idx) bufs
        (buf_guard (index_to_nat n_idx)) = true.

  Local Notation src_st_env  := (ContextEnv.(env_t) (tf_states_type (tfs_spec_states_size ctx))).
  Local Notation src_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation src_sys_state := (src_st_env * src_out_env)%type.

  Local Notation spec_run act sp input :=
    (tf_ops_run (tfs_spec_states_size ctx) i_sz o_sz
       (tfs_spec_action_ops ctx act) sp input).

  Theorem latency_noninterference_guarded (act: tfs_action sched)
      (a_idx: a_index) (input: input_t) (ss0 ss0': sched_sys_state) (N N': nat) :
    (forall c, critb c = false ->
       ~ List.In c (get_tainted ctx (build_dfg ctx act))) ->
    analysis_sound act a_idx input ->
    roots_checked act a_idx ->
    buffers_checked act a_idx ->
    act_idx_aligned ctx cost_limit act a_idx ->
    (fst ss0 ).[tfs_done_signal sched] = Bits.zero ->
    (fst ss0').[tfs_done_signal sched] = Bits.zero ->
    (forall n_idx, (fst ss0 ).[tf_dfg_v a_idx n_idx] = Bits.zero) ->
    (forall n_idx, (fst ss0').[tf_dfg_v a_idx n_idx] = Bits.zero) ->
    pub_eq ctx cost_limit act a_idx input ss0 ss0' ->
    first_done ctx cost_limit act input ss0  N ->
    first_done ctx cost_limit act input ss0' N' ->
    N = N'.
  Proof.
    intros Hlink Hguard Hchk Hbchk Halign Hd0 Hd0' Hz Hz' Hpub
           [HN HltN] [HN' HltN'].
    destruct (Nat.lt_trichotomy N N') as [Hlt | [Heq | Hgt]]; [ | exact Heq | ].
    - destruct (HltN' N Hlt).
      apply (done_lockstep_guarded act a_idx input ss0 ss0' Hlink Hguard Hchk
               Hbchk Halign Hd0 Hd0' Hz Hz' Hpub N
               (fun i Hi => HltN  i (proj2 Hi))
               (fun i Hi => HltN' i (Nat.lt_trans _ _ _ (proj2 Hi) Hlt))).
      exact HN.
    - destruct (HltN N' Hgt).
      apply (done_lockstep_guarded act a_idx input ss0 ss0' Hlink Hguard Hchk
               Hbchk Halign Hd0 Hd0' Hz Hz' Hpub N'
               (fun i Hi => HltN  i (Nat.lt_trans _ _ _ (proj2 Hi) Hgt))
               (fun i Hi => HltN' i (proj2 Hi))).
      exact HN'.
  Qed.

  Corollary latency_from_outputs_guarded (act: tfs_action sched)
      (a_idx: a_index) (input: input_t) (sp0 sp0': src_sys_state)
      (ss0 ss0': sched_sys_state) (N N': nat) :
    (forall c, critb c = false ->
       ~ List.In c (get_tainted ctx (build_dfg ctx act))) ->
    analysis_sound act a_idx input ->
    roots_checked act a_idx ->
    buffers_checked act a_idx ->
    act_idx_aligned ctx cost_limit act a_idx ->
    start_rel ctx cost_limit sp0  ss0  ->
    start_rel ctx cost_limit sp0' ss0' ->
    (forall ov, (snd sp0).[ov] = (snd sp0').[ov]) ->
    (forall ov, (snd (spec_run act sp0  input)).[ov]
              = (snd (spec_run act sp0' input)).[ov]) ->
    first_done ctx cost_limit act input ss0  N ->
    first_done ctx cost_limit act input ss0' N' ->
    N = N'.
  Proof.
    intros Hlink Hguard Hchk Hbchk Halign Hst Hst' Hpre Hpost HN HN'.
    assert (Hsr : forall (sp: src_sys_state) (ss: sched_sys_state),
              start_rel ctx cost_limit sp ss ->
              (forall sv, (fst ss).[tf_dfg_s sv] = (fst sp).[sv])
              /\ (forall ov, (snd ss).[ov] = (snd sp).[ov])).
    { intros sp ss [Hsnd [Hmap _]]. split.
      - intro sv. rewrite <- Hmap, getenv_maps_from. reflexivity.
      - intro ov. rewrite Hsnd. reflexivity. }
    destruct (Hsr sp0  ss0  Hst)  as [Hs0  Ho0 ].
    destruct (Hsr sp0' ss0' Hst') as [Hs0' Ho0'].
    destruct Hst  as [_ [_ Hzz ]].
    destruct Hst' as [_ [_ Hzz']].
    exact (latency_noninterference_guarded act a_idx input ss0 ss0' N N'
             Hlink Hguard Hchk Hbchk Halign
             (Hzz  (tfs_done_signal sched) I) (Hzz' (tfs_done_signal sched) I)
             (fun n_idx => Hzz  (tf_dfg_v a_idx n_idx) I)
             (fun n_idx => Hzz' (tf_dfg_v a_idx n_idx) I)
             (obs_eq_pub_eq ctx cost_limit act a_idx input sp0 sp0' ss0 ss0'
                Halign Hs0 Ho0 Hs0' Ho0' Hpre Hpost)
             HN HN').
  Qed.

  Corollary L_public_guarded (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (sp0 sp0': src_sys_state) (ss0 ss0': sched_sys_state) :
    (forall c, critb c = false ->
       ~ List.In c (get_tainted ctx (build_dfg ctx act))) ->
    analysis_sound act a_idx input ->
    roots_checked act a_idx ->
    buffers_checked act a_idx ->
    act_idx_aligned ctx cost_limit act a_idx ->
    start_rel ctx cost_limit sp0  ss0  ->
    start_rel ctx cost_limit sp0' ss0' ->
    (forall ov, (snd sp0).[ov] = (snd sp0').[ov]) ->
    (forall ov, (snd (spec_run act sp0  input)).[ov]
              = (snd (spec_run act sp0' input)).[ov]) ->
    L ctx cost_limit act input ss0 = L ctx cost_limit act input ss0'.
  Proof.
    intros Hlink Hguard Hchk Hbchk Halign Hst Hst' Hpre Hpost.
    exact (latency_from_outputs_guarded act a_idx input sp0 sp0' ss0 ss0' _ _
             Hlink Hguard Hchk Hbchk Halign Hst Hst' Hpre Hpost
             (L_first_done ctx cost_limit act sp0  ss0  input Hst)
             (L_first_done ctx cost_limit act sp0' ss0' input Hst')).
  Qed.

  (* End-to-end conservativity: an analysis that declassifies nothing yields
     exactly the current [L_public]. *)
  Corollary L_public_recovered (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (sp0 sp0': src_sys_state) (ss0 ss0': sched_sys_state) :
    (forall c, critb c = true) ->
    (forall m, buf_guard m = []) ->
    act_idx_aligned ctx cost_limit act a_idx ->
    start_rel ctx cost_limit sp0  ss0  ->
    start_rel ctx cost_limit sp0' ss0' ->
    (forall ov, (snd sp0).[ov] = (snd sp0').[ov]) ->
    (forall ov, (snd (spec_run act sp0  input)).[ov]
              = (snd (spec_run act sp0' input)).[ov]) ->
    L ctx cost_limit act input ss0 = L ctx cost_limit act input ss0'.
  Proof.
    intros Hcb Hbg Halign Hst Hst' Hpre Hpost.
    apply (L_public_guarded act a_idx input sp0 sp0' ss0 ss0').
    - intros c Hc. rewrite Hcb in Hc. discriminate.
    - intros c Hc. rewrite Hcb in Hc. discriminate.
    - intros n bufs Hn Hsub.
      destruct (var_map_node_range ctx cost_limit act n Hn) as [Hn1 Hnlen].
      exact (path_ok_all_critical act Hcb Hbg bufs _ _ _ Hn1 Hnlen Hnlen).
    - intros n_idx bufs Hsub.
      destruct (vreg_nid_node_range ctx cost_limit act a_idx n_idx Halign)
        as [Hn1 Hnlen].
      unfold vreg_nid.
      exact (path_ok_all_critical act Hcb Hbg bufs _ _ _ Hn1 Hnlen Hnlen).
    - exact Halign.
    - exact Hst.
    - exact Hst'.
    - exact Hpre.
    - exact Hpost.
  Qed.

End IPRGuarded.

Print Assumptions valid_public_guarded.
Print Assumptions decl_compose.
Print Assumptions decl_direct.
Print Assumptions untainted_gderivable.
Print Assumptions valid_public_recovered.
Print Assumptions valid_lockstep_guarded.
Print Assumptions valid_lockstep_recovered.
Print Assumptions done_public_guarded.
Print Assumptions done_lockstep_guarded.
Print Assumptions latency_noninterference_guarded.
Print Assumptions latency_from_outputs_guarded.
Print Assumptions L_public_guarded.
Print Assumptions L_public_recovered.
