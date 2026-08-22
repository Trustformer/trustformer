Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.DFG.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.
Require Import Trustformer.Properties.IPR.
Require Import Trustformer.Rules.Negation.
Require Import Trustformer.Rules.PhiBranch.
Require Import Trustformer.Rules.PhiConst.

Require Import Coq.Lists.List.
Import ListNotations.

(*
    Contrast test for whitebox untainting.

    One specification, two contexts: without declassification rules the phi on
    the secret is critical, and with the negation rule it is not -- because the
    specification already publishes `!secret`, so the attacker can invert it.

    This is what `TaintRegression.v` cannot show: that supplying a rule changes
    the analysis, and that the resulting design still satisfies the IPR
    obligation.
 *)

Section FunctionalSpecification.

    Definition w := 32.

    Inductive fs_action := act_neg.

    Inductive fs_states := st_secret.

    Inductive fs_inputs := in_pub.

    Inductive fs_outputs :=
    | out_neg
    | out_pub
    .

    Definition fs_states_size (_: fs_states) : nat := w.
    Definition fs_inputs_size (_: fs_inputs) : nat := w.
    Definition fs_outputs_size (_: fs_outputs) : nat := w.

    Definition fs_states_t := tf_states_type fs_states_size.

    Definition fs_states_init (x: fs_states) : (fs_states_t x) :=
        match x with
        | st_secret => Bits.zero
        end.

    (* The spec publishes the bitwise negation of the secret, then branches on
       the secret itself. *)
    Definition fs_transitions (act: fs_action)
        : (@tf_ops fs_states fs_inputs fs_outputs) :=
        match act with
        | act_neg =>
            {[
                let $out_neg := !$st_secret;
                (if $st_secret then let $out_pub := #1 else let $out_pub := #0)
            ]}
        end.

End FunctionalSpecification.

Section Contrast.

    Definition mk_ctx (decls: list (decl_rule fs_states fs_inputs fs_outputs))
        : TFSchedContext := {|
        tfs_spec_states := fs_states;
        tfs_spec_states_fin := _;
        tfs_spec_states_size := fs_states_size;
        tfs_spec_states_init := fs_states_init;

        tfs_spec_inputs := fs_inputs;
        tfs_spec_inputs_fin := _;
        tfs_spec_inputs_size := fs_inputs_size;

        tfs_spec_outputs := fs_outputs;
        tfs_spec_outputs_fin := _;
        tfs_spec_outputs_size := fs_outputs_size;

        tfs_spec_action := fs_action;
        tfs_spec_action_fin := _;
        tfs_spec_action_ops := fs_transitions;
        tfs_spec_decls := decls
    |}.

    Definition ctx_blackbox := mk_ctx [].
    Definition ctx_whitebox := mk_ctx [neg_rule].

    (* Criticality is per phi OCCURRENCE, so the count is taken from the
       compiler's own diagnostic rather than from a per-node approximation. *)
    Definition critical_count (ctx: TFSchedContext)
        (dfg: @dfg_state_t (tfs_spec_states ctx) (tfs_spec_inputs ctx)
                (tfs_spec_outputs ctx)) : nat :=
        List.length (crit_report_all ctx dfg).

    (* Without a rule the branch on the secret must be constant-time. *)
    Example blackbox_is_critical :
      critical_count ctx_blackbox (build_dfg ctx_blackbox act_neg) = 1.
    Proof. vm_compute. reflexivity. Qed.

    (* ...and the report says why, rather than failing to optimise silently. *)
    Example blackbox_reason_is_no_rule :
      exists c, crit_report_all ctx_blackbox (build_dfg ctx_blackbox act_neg)
                = [CR_no_rule c].
    Proof. eexists. vm_compute. reflexivity. Qed.

    (* With the negation rule the secret is recoverable from [out_neg], so the
       branch is allowed to have data-dependent latency. *)
    Example whitebox_is_not_critical :
      critical_count ctx_whitebox (build_dfg ctx_whitebox act_neg) = 0.
    Proof. vm_compute. reflexivity. Qed.

    (* The saturation adds each target once: without the dedupe in
       [saturate_step] the accumulator grows on every one of the
       [length (graph dfg)] iterations. *)
    Example saturation_adds_one_root :
      List.length (untainted_roots ctx_whitebox (build_dfg ctx_whitebox act_neg))
      = S (List.length (public_dsts ctx_whitebox (build_dfg ctx_whitebox act_neg)
                        ++ trivially_public ctx_whitebox
                             (build_dfg ctx_whitebox act_neg))).
    Proof. vm_compute. reflexivity. Qed.

End Contrast.

Section Obligation.

    (* The declassification the whitebox context relies on is discharged by the
       rule library, so the IPR theorems apply to the variable-latency design. *)
    Theorem whitebox_decls_sound :
      forall act a_idx input, uncond_sound ctx_whitebox 10 act a_idx input.
    Proof.
      intros act a_idx input.
      apply (uncond_sound_of_instances ctx_whitebox 10).
      intros i Hi.
      unfold uncond_instances, decl_instances in Hi.
      apply filter_In in Hi. destruct Hi as [Hi _].
      apply in_flat_map in Hi. destruct Hi as [r [Hr Hi]].
      cbn in Hr. destruct Hr as [Hr | []]. subst r.
      exact (neg_rule_sound ctx_whitebox 10 act a_idx input i Hi).
    Qed.

    (* Same rule, guarded form: this is what the compiler's per-occurrence
       criticality test consults. *)
    Theorem whitebox_decl_guard_sound :
      forall act a_idx input, decl_sound ctx_whitebox 10 act a_idx input.
    Proof.
      intros act a_idx input.
      apply (decl_sound_of_instances ctx_whitebox 10 whitebox_decls_sound).
      intros i Hi.
      unfold decl_instances in Hi.
      apply in_flat_map in Hi. destruct Hi as [r [Hr Hi]].
      cbn in Hr. destruct Hr as [Hr | []]. subst r.
      exact (neg_rule_sound ctx_whitebox 10 act a_idx input i Hi).
    Qed.

End Obligation.

Print Assumptions whitebox_decls_sound.
Print Assumptions whitebox_decl_guard_sound.

(* ==================================================================== *)
(* A GUARDED declassification.  The inner selector is recoverable only    *)
(* on the path where the outer one is true, so whether it may be         *)
(* declassified depends on the phi OCCURRENCE, not on the node.          *)
(* ==================================================================== *)

Section GuardedSpecification.

    Inductive gs_action := gs_act.

    Inductive gs_states := gs_st_outer | gs_st_inner.

    Inductive gs_inputs := gs_in_x.

    Inductive gs_outputs := gs_out_neg | gs_out_sel.

    Definition gs_states_size (_: gs_states) : nat := w.
    Definition gs_inputs_size (_: gs_inputs) : nat := w.
    Definition gs_outputs_size (_: gs_outputs) : nat := w.

    Definition gs_states_t := tf_states_type gs_states_size.

    Definition gs_states_init (x: gs_states) : (gs_states_t x) :=
        match x with
        | gs_st_outer => Bits.zero
        | gs_st_inner => Bits.zero
        end.

    Definition gs_transitions (act: gs_action)
        : (@tf_ops gs_states gs_inputs gs_outputs) :=
        match act with
        | gs_act =>
            {[
                let $gs_out_neg := !$gs_st_outer;
                if $gs_st_outer then
                    if $gs_st_inner then let $gs_out_sel := #1
                    else let $gs_out_sel := #2
                else let $gs_out_sel := #0
            ]}
        end.

End GuardedSpecification.

Section GuardedContrast.

    Definition mk_gctx (decls: list (decl_rule gs_states gs_inputs gs_outputs))
        : TFSchedContext := {|
        tfs_spec_states := gs_states;
        tfs_spec_states_fin := _;
        tfs_spec_states_size := gs_states_size;
        tfs_spec_states_init := gs_states_init;

        tfs_spec_inputs := gs_inputs;
        tfs_spec_inputs_fin := _;
        tfs_spec_inputs_size := gs_inputs_size;

        tfs_spec_outputs := gs_outputs;
        tfs_spec_outputs_fin := _;
        tfs_spec_outputs_size := gs_outputs_size;

        tfs_spec_action := gs_action;
        tfs_spec_action_fin := _;
        tfs_spec_action_ops := gs_transitions;
        tfs_spec_decls := decls
    |}.

    (* PhiCUT recovers the inner selector from the inner phi, and PhiAUT makes
       the inner phi derivable from the published output -- but only under
       [(outer, true)].  Without a rule for [outer] the compiler never reaches
       that path. *)
    Definition gctx_guarded := mk_gctx [phibranch_rule; phiconst_rule].

    (* Publishing [!outer] declassifies the outer selector unconditionally, so
       the outer phi is non-critical, the path gains [(outer, true)], and the
       inner guard is then implied. *)
    Definition gctx_open := mk_gctx [neg_rule; phibranch_rule; phiconst_rule].

    (* Node 3 is the outer selector, node 5 the inner one.  The inner IS
       declassified -- under three different guards, none of which this
       occurrence's path supplies -- and the report says so instead of staying
       silent.  The self-referential guards are sound and not useless: an
       occurrence of the same condition nested under itself does meet them. *)
    Example guarded_inner_unreachable :
      crit_report_all gctx_guarded (build_dfg gctx_guarded gs_act)
      = [CR_no_rule 3;
         CR_guard_unmet 5 [[(5, true)]; [(5, false)]; [(3, true)]]].
    Proof. vm_compute. reflexivity. Qed.

    (* Declassifying the outer selector makes its phi non-critical, which
       extends the path with [(3, true)] -- and the inner guard is then met.
       No per-NODE criticality can express this: node 5 is declassifiable in
       one occurrence and not in another. *)
    Example open_nothing_critical :
      crit_report_all gctx_open (build_dfg gctx_open gs_act) = [].
    Proof. vm_compute. reflexivity. Qed.

End GuardedContrast.

Section GuardedObligation.

    Theorem gopen_decls_sound :
      forall act a_idx input, uncond_sound gctx_open 10 act a_idx input.
    Proof.
      intros act a_idx input.
      apply (uncond_sound_of_instances gctx_open 10).
      intros i Hi.
      unfold uncond_instances, decl_instances in Hi.
      apply filter_In in Hi. destruct Hi as [Hi _].
      apply in_flat_map in Hi. destruct Hi as [r [Hr Hi]].
      cbn in Hr. destruct Hr as [Hr | [Hr | [Hr | []]]]; subst r.
      - exact (neg_rule_sound gctx_open 10 act a_idx input i Hi).
      - exact (phibranch_rule_sound gctx_open 10 act a_idx input i Hi).
      - exact (phiconst_rule_sound gctx_open 10 act a_idx input i Hi).
    Qed.

    Theorem gopen_decl_guard_sound :
      forall act a_idx input, decl_sound gctx_open 10 act a_idx input.
    Proof.
      intros act a_idx input.
      apply (decl_sound_of_instances gctx_open 10 gopen_decls_sound).
      intros i Hi. unfold decl_instances in Hi.
      apply in_flat_map in Hi. destruct Hi as [r [Hr Hi]].
      cbn in Hr. destruct Hr as [Hr | [Hr | [Hr | []]]]; subst r.
      - exact (neg_rule_sound gctx_open 10 act a_idx input i Hi).
      - exact (phibranch_rule_sound gctx_open 10 act a_idx input i Hi).
      - exact (phiconst_rule_sound gctx_open 10 act a_idx input i Hi).
    Qed.

End GuardedObligation.

Print Assumptions gopen_decl_guard_sound.
