(*! Declassification rule: for `n = Phi c t e`, wherever `c` holds the node's
    value IS the then-branch's -- the paper's PhiAUT, the one rule with a
    NON-EMPTY guard.  Both directions, downward giving the lockbox pattern. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

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

Definition phibranch_rule {s i o p} : decl_rule s i o p :=
  fun dfg =>
    flat_map
      (fun n =>
         let dflt := {| nid := 0; op := DFG_Empty; sz := 0 |} in
         match op (nth n (graph dfg) dflt) with
         | DFG_Phi cnd tid eid =>
             [ {| di_target := n;   di_sources := [tid]; di_guard := [(cnd, true)] |}
             ; {| di_target := tid; di_sources := [n];   di_guard := [(cnd, true)] |}
             ; {| di_target := n;   di_sources := [eid]; di_guard := [(cnd, false)] |}
             ; {| di_target := eid; di_sources := [n];   di_guard := [(cnd, false)] |} ]
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

  (* Under the guard the phi's reference expression reduces to the branch's,
     at the branch's own width.  This is the whole content of the rule; the
     four instances are the four ways of reading the resulting equation. *)
  Lemma phi_selects (act: tfs_action sched) (a_idx: a_index) (input: sched_input_t)
      (ss: sched_sys_state) (n cnd tid eid: nid_t) (b: bool) :
    1 <= n ->
    n < length (graph (build_dfg ctx act)) ->
    op (nth n (graph (build_dfg ctx act))
          {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Phi cnd tid eid ->
    nval ctx cost_limit act a_idx ss input 1 cnd = bit_of b ->
    nval ctx cost_limit act a_idx ss input (nsz act n) n
    = nval ctx cost_limit act a_idx ss input (nsz act n) (if b then tid else eid).
  Proof.
    intros Hn1 Hlen Hop Hcnd.
    pose proof (nre_phi ctx cost_limit act a_idx n cnd tid eid Hn1 Hlen Hop) as Hnre.
    unfold nval in Hcnd |- *. rewrite Hnre. cbn [tf_eval_expr].
    destruct b; unfold bit_of in Hcnd.
    - assert (Hnz : beq_dec (tf_eval_expr (tfs_states_size sched) (tfs_inputs_size sched)
                               (tfs_outputs_size sched) (szB := 1)
                               (node_ref_expr ctx cost_limit act a_idx cnd) ss input)
                      Bits.zero = false).
      { rewrite Hcnd. destruct (beq_dec (Bits.ones 1) Bits.zero) eqn:Hb;
          [ | reflexivity ].
        exfalso. apply beq_dec_iff in Hb. discriminate. }
      rewrite Hnz. reflexivity.
    - assert (Hz : beq_dec (tf_eval_expr (tfs_states_size sched) (tfs_inputs_size sched)
                              (tfs_outputs_size sched) (szB := 1)
                              (node_ref_expr ctx cost_limit act a_idx cnd) ss input)
                     Bits.zero = true)
        by (rewrite Hcnd; apply beq_dec_refl).
      rewrite Hz. reflexivity.
  Qed.


  (* A declassification reads its SOURCES, so they have to have settled.  Under
     V4 a node's reference value moves when a call it feeds on answers, so this
     is a real obligation and not bookkeeping: a rule that fires on a phi whose
     condition has not arrived is reading the wire, not the value.  It holds of
     any phi built from combinational sources, which is what the rule is for. *)
  Definition phibranch_settled (act: tfs_action sched) (a_idx: a_index) : Prop :=
    forall n cnd tid eid,
      node_op ctx cost_limit act n = DFG_Phi cnd tid eid ->
      forall (p: list lit) (ss: sched_sys_state) (inp: sched_input_t),

        rvalid act a_idx p n ss inp = Bits.ones 1.
  Theorem phibranch_rule_sound (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (i: decl_instance) :
    List.In i (phibranch_rule (build_dfg ctx act)) ->
    phibranch_settled act a_idx ->
    instance_sound ctx cost_limit act a_idx input i.
  Proof.
    unfold phibranch_rule. intros Hin Hset.
    apply in_flat_map in Hin. destruct Hin as [n [Hseq Hi]].
    apply in_seq in Hseq. destruct Hseq as [Hn1 Hn2].
    assert (Hlen : n < length (graph (build_dfg ctx act))) by lia.
    cbv zeta in Hi.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa | dp darg den | sp stok sen | ja jb | ] eqn:Hop;
      cbn [List.In] in Hi; try contradiction.

    (* widths: both branches carry the node's own width *)
    assert (Hnode_in : List.In (nth n (graph (build_dfg ctx act))
                                  {| nid := 0; op := DFG_Empty; sz := 0 |})
                         (graph (build_dfg ctx act)))
      by (apply nth_In; exact Hlen).
    pose proof (wfg_build_dfg ctx cost_limit act _ Hnode_in) as Hfg.
    unfold node_args_sz in Hfg. rewrite Hop in Hfg.
    destruct Hfg as [_ [Hft Hfe]].
    destruct (wsz_node_sz ctx cost_limit act tid _ Hft) as [_ Htsz].
    destruct (wsz_node_sz ctx cost_limit act eid _ Hfe) as [_ Hesz].

    (* the guard names the selector, so [pi_holds] is exactly its value *)
    (* generalised over the input: the two runs carry their own *)
    assert (Hsel : forall (b: bool) (inp: sched_input_t) (ss: sched_sys_state),
              pi_holds ctx cost_limit act a_idx inp [(cnd, b)] ss ->
              nval ctx cost_limit act a_idx ss inp
                (nsz act n) n
              = nval ctx cost_limit act a_idx ss inp
                (nsz act n) (if b then tid else eid)).
    { intros b inp ss Hp.
      exact (phi_selects act a_idx inp ss n cnd tid eid b Hn1 Hlen Hop
               (Hp cnd b (or_introl eq_refl))). }

    destruct (node_args_range ctx cost_limit act n Hn1 Hlen cnd
                ltac:(unfold get_args; rewrite Hop; left; reflexivity)) as [Hc1 _].
    destruct (node_args_range ctx cost_limit act n Hn1 Hlen tid
                ltac:(unfold get_args; rewrite Hop; right; left; reflexivity))
      as [Ht1 _].
    destruct (node_args_range ctx cost_limit act n Hn1 Hlen eid
                ltac:(unfold get_args; rewrite Hop; right; right; left; reflexivity))
      as [He1 _].
    assert (Hopn : node_op ctx cost_limit act n = DFG_Phi cnd tid eid)
      by (unfold SchedulerSimulationBase.node_op; rewrite Hop; reflexivity).

    (* An arm's validity, from the phi's: the critical shape waits on both arms
       at the unextended path, the selecting one on the arm it picks. *)
    assert (Harm : forall (p: list lit) (b: bool) (inp: sched_input_t) (ss: sched_sys_state),
              pi_holds ctx cost_limit act a_idx inp [(cnd, b)] ss ->
              rvalid act a_idx p n ss inp = Bits.ones 1 ->
              rvalid act a_idx (if phi_crit (get_tainted ctx (build_dfg ctx act))
                                  (decl_facts ctx (build_dfg ctx act)) cnd p
                                then p else (cnd, b) :: p)
                (if b then tid else eid) ss inp = Bits.ones 1).
    { intros p b inp s Hp Hvn.
      destruct (phi_crit (get_tainted ctx (build_dfg ctx act))
                  (decl_facts ctx (build_dfg ctx act)) cnd p) eqn:Hcrit.
      - destruct (nrv_peel_phi_crit ctx cost_limit act a_idx n cnd tid eid p s inp
                    Hopn Hcrit Hc1 Ht1 He1 Hlen Hvn) as [_ [Htv Hev]].
        destruct b; assumption.
      - destruct (nrv_peel_phi_sel ctx cost_limit act a_idx n cnd tid eid p s inp
                    Hopn Hcrit Hc1 Ht1 He1 Hlen Hvn) as [_ [Htv Hev]].
        pose proof (Hp cnd b (or_introl eq_refl)) as Hcv.
        unfold SchedulerSimulationBase.nval, bit_of in Hcv.
        destruct b.
        + apply Htv. rewrite Hcv. exact ones1_neq_zero.
        + apply Hev. exact Hcv. }

    (* ... and the path the arm is valid at is one the run took *)
    assert (Hpath : forall (p: list lit) (b: bool) (inp: sched_input_t) (ss: sched_sys_state),
              pi_holds ctx cost_limit act a_idx inp p ss ->
              pi_holds ctx cost_limit act a_idx inp [(cnd, b)] ss ->
              pi_holds ctx cost_limit act a_idx inp
                (if phi_crit (get_tainted ctx (build_dfg ctx act))
                     (decl_facts ctx (build_dfg ctx act)) cnd p
                 then p else (cnd, b) :: p) ss).
    { intros p b inp s Hpp Hp.
      destruct (phi_crit (get_tainted ctx (build_dfg ctx act))
                  (decl_facts ctx (build_dfg ctx act)) cnd p);
        [ exact Hpp
        | exact (pi_holds_cons ctx cost_limit act a_idx inp cnd b p s Hpp
                   (Hp cnd b (or_introl eq_refl))) ]. }

    destruct Hi as [Hi | [Hi | [Hi | [Hi | []]]]]; subst i;
      intros ss ss' input' pi0 Hpub Hp Hp' Hsrc Hpi Hpi' Hv Hv';
      cbn [di_sources di_target di_guard] in Hsrc, Hp, Hp', Hv, Hv' |- *.
    - rewrite (Hsel true input ss Hp), (Hsel true input' ss' Hp'), <- Htsz.
      exact (Hsrc tid _ (or_introl eq_refl)
               (Hpath pi0 true input  ss  Hpi  Hp )
               (Hpath pi0 true input' ss' Hpi' Hp')
               (Harm pi0 true input  ss  Hp  Hv )
               (Harm pi0 true input' ss' Hp' Hv')).
    - (* BLOCKED under V4: the phi's validity needs its CONDITION's, which the
         arm's validity does not give. *)
      rewrite Htsz, <- (Hsel true input ss Hp), <- (Hsel true input' ss' Hp').
      exact (Hsrc n pi0 (or_introl eq_refl) Hpi Hpi'
               (Hset n cnd tid eid Hopn pi0 ss  input )
               (Hset n cnd tid eid Hopn pi0 ss' input')).
    - rewrite (Hsel false input ss Hp), (Hsel false input' ss' Hp'), <- Hesz.
      exact (Hsrc eid _ (or_introl eq_refl)
               (Hpath pi0 false input  ss  Hpi  Hp )
               (Hpath pi0 false input' ss' Hpi' Hp')
               (Harm pi0 false input  ss  Hp  Hv )
               (Harm pi0 false input' ss' Hp' Hv')).
    - (* BLOCKED, as above. *)
      rewrite Hesz, <- (Hsel false input ss Hp), <- (Hsel false input' ss' Hp').
      exact (Hsrc n pi0 (or_introl eq_refl) Hpi Hpi'
               (Hset n cnd tid eid Hopn pi0 ss  input )
               (Hset n cnd tid eid Hopn pi0 ss' input')).
  Qed.

End Soundness.

Print Assumptions phibranch_rule_sound.
