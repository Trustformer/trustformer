Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.DFG.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.
Require Import Trustformer.Properties.IPR.
Require Import Trustformer.Properties.IPR_Guarded.
Require Import Trustformer.Rules.Negation.

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

    Definition critical_count (ctx: TFSchedContext)
        (dfg: @dfg_state_t (tfs_spec_states ctx) (tfs_spec_inputs ctx)
                (tfs_spec_outputs ctx)) : nat :=
        let tainted := get_tainted ctx dfg in
        List.length (List.filter (fun n =>
            match op n with
            | DFG_Phi c _ _ => existsb (Nat.eqb c) tainted
            | _ => false
            end) (graph dfg)).

    (* Without a rule the branch on the secret must be constant-time. *)
    Example blackbox_is_critical :
      critical_count ctx_blackbox (build_dfg ctx_blackbox act_neg) = 1.
    Proof. vm_compute. reflexivity. Qed.

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
      = S (List.length (public_dsts ctx_whitebox (build_dfg ctx_whitebox act_neg))).
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

End Obligation.

Print Assumptions whitebox_decls_sound.
