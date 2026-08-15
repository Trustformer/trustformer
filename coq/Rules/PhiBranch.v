(*! Declassification rule: a phi and its selected branch agree on that branch.

    For `n = Phi c t e`, whenever `c` holds the node's value IS the then-branch's
    value, so each determines the other.  This is the paper's PhiAUT, and it is
    the first shipped rule with a NON-EMPTY guard: the fact is only true on the
    path where the selector has the matching value.

    Both directions are emitted.  Downward (`n` justifies `t`) is what carries a
    published output into a nested conditional -- the lockbox pattern, where the
    inner phi is derivable only under the outer selector.
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

Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

Definition phibranch_rule {s i o} : decl_rule s i o :=
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
  Local Notation a_index := (Vect.index (length (buffer_needs ctx cost_limit))).

  Local Notation nsz act n :=
    (sz (nth n (graph (build_dfg ctx act)) {| nid := 0; op := DFG_Empty; sz := 0 |})).

  (* Under the guard the phi's reference expression reduces to the branch's,
     at the branch's own width.  This is the whole content of the rule; the
     four instances are the four ways of reading the resulting equation. *)
  Lemma phi_selects (act: tfs_action sched) (a_idx: a_index) (input: input_t)
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
    - assert (Hnz : beq_dec (tf_eval_expr (tfs_states_size sched) i_sz
                               (tfs_outputs_size sched) (szB := 1)
                               (node_ref_expr ctx cost_limit act a_idx cnd) ss input)
                      Bits.zero = false).
      { rewrite Hcnd. destruct (beq_dec (Bits.ones 1) Bits.zero) eqn:Hb;
          [ | reflexivity ].
        exfalso. apply beq_dec_iff in Hb. discriminate. }
      rewrite Hnz. reflexivity.
    - assert (Hz : beq_dec (tf_eval_expr (tfs_states_size sched) i_sz
                              (tfs_outputs_size sched) (szB := 1)
                              (node_ref_expr ctx cost_limit act a_idx cnd) ss input)
                     Bits.zero = true)
        by (rewrite Hcnd; apply beq_dec_refl).
      rewrite Hz. reflexivity.
  Qed.

  Theorem phibranch_rule_sound (act: tfs_action sched) (a_idx: a_index)
      (input: input_t) (i: decl_instance) :
    List.In i (phibranch_rule (build_dfg ctx act)) ->
    instance_sound ctx cost_limit act a_idx input i.
  Proof.
    unfold phibranch_rule. intro Hin.
    apply in_flat_map in Hin. destruct Hin as [n [Hseq Hi]].
    apply in_seq in Hseq. destruct Hseq as [Hn1 Hn2].
    assert (Hlen : n < length (graph (build_dfg ctx act))) by lia.
    cbv zeta in Hi.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | ] eqn:Hop;
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
    assert (Hsel : forall (b: bool) (ss: sched_sys_state),
              pi_holds ctx cost_limit act a_idx input [(cnd, b)] ss ->
              nval ctx cost_limit act a_idx ss input
                (nsz act n) n
              = nval ctx cost_limit act a_idx ss input
                (nsz act n) (if b then tid else eid)).
    { intros b ss Hp.
      exact (phi_selects act a_idx input ss n cnd tid eid b Hn1 Hlen Hop
               (Hp cnd b (or_introl eq_refl))). }

    destruct Hi as [Hi | [Hi | [Hi | [Hi | []]]]]; subst i;
      intros ss ss' Hpub Hp Hp' Hsrc;
      cbn [di_sources di_target di_guard] in Hsrc, Hp, Hp' |- *.
    - rewrite (Hsel true ss Hp), (Hsel true ss' Hp'), <- Htsz.
      exact (Hsrc tid (or_introl eq_refl)).
    - rewrite Htsz, <- (Hsel true ss Hp), <- (Hsel true ss' Hp').
      exact (Hsrc n (or_introl eq_refl)).
    - rewrite (Hsel false ss Hp), (Hsel false ss' Hp'), <- Hesz.
      exact (Hsrc eid (or_introl eq_refl)).
    - rewrite Hesz, <- (Hsel false ss Hp), <- (Hsel false ss' Hp').
      exact (Hsrc n (or_introl eq_refl)).
  Qed.

End Soundness.

Print Assumptions phibranch_rule_sound.
