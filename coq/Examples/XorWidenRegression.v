(*! Regression for the two rules no other example exercises.

    `xor_rule` is the paper's "binary operations under the condition that one
    operand is known": publishing `secret ^ mask` with a public `mask` input
    declassifies `secret`.  This only works because both saturations seed with
    the trivially-public nodes -- a mask supplied as an INPUT is never a public
    destination.

    `widen_rule` covers the other half: a narrow secret published at a wider
    output goes through a widening resize, which keeps every bit.
!*)

Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.DFG.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.
Require Import Trustformer.Properties.IPR.
Require Import Trustformer.Rules.Xor.
Require Import Trustformer.Rules.Widening.

Require Import Coq.Lists.List.
Import ListNotations.

Section Specification.

    Definition wide := 32.
    Definition narrow := 2.

    Inductive rw_action := rw_act.

    Inductive rw_states := rw_st_secret | rw_st_small.

    Inductive rw_inputs := rw_in_mask.

    Inductive rw_outputs := rw_out_masked | rw_out_small | rw_out_res.

    Definition rw_states_size (x: rw_states) : nat :=
      match x with
      | rw_st_secret => wide
      | rw_st_small => narrow
      end.

    Definition rw_inputs_size (_: rw_inputs) : nat := wide.

    Definition rw_outputs_size (_: rw_outputs) : nat := wide.

    Definition rw_states_t := tf_states_type rw_states_size.

    Definition rw_states_init (x: rw_states) : (rw_states_t x) :=
      match x with
      | rw_st_secret => Bits.zero
      | rw_st_small => Bits.zero
      end.

    (* [rw_out_small := $rw_st_small] widens 2 -> 32, so the builder emits a
       [DFG_Resize].  Both branches of the phi are distinct constants, but the
       point here is the CONDITION: it reads the two secrets, and only the xor
       and resize rules can recover them. *)
    Definition rw_transitions (act: rw_action)
      : (@tf_ops rw_states rw_inputs rw_outputs) :=
      match act with
      | rw_act =>
          {[
            let $rw_out_masked := $rw_st_secret ^ $rw_in_mask;
            let $rw_out_small := $rw_st_small;
            if ($rw_st_secret ==[wide] $rw_st_small) then
              let $rw_out_res := #1
            else
              let $rw_out_res := #0
          ]}
      end.

End Specification.

Section Contrast.

    Definition mk_rw (decls: list (decl_rule rw_states rw_inputs rw_outputs))
      : TFSchedContext := {|
      tfs_spec_states := rw_states;
      tfs_spec_states_fin := _;
      tfs_spec_states_size := rw_states_size;
      tfs_spec_states_init := rw_states_init;

      tfs_spec_inputs := rw_inputs;
      tfs_spec_inputs_fin := _;
      tfs_spec_inputs_size := rw_inputs_size;

      tfs_spec_outputs := rw_outputs;
      tfs_spec_outputs_fin := _;
      tfs_spec_outputs_size := rw_outputs_size;

      tfs_spec_action := rw_action;
      tfs_spec_action_fin := _;
      tfs_spec_action_ops := rw_transitions;
      tfs_spec_decls := decls
    |}.

    Definition rw_blackbox := mk_rw [].
    Definition rw_whitebox := mk_rw [xor_rule; widen_rule].

    (* Both rules actually produce instances on this graph. *)
    Example rules_fire :
      0 < List.length (xor_rule (build_dfg rw_whitebox rw_act))
      /\ 0 < List.length (widen_rule (build_dfg rw_whitebox rw_act)).
    Proof. split; vm_compute; repeat constructor. Qed.

    Example blackbox_is_critical :
      List.length (crit_report_all rw_blackbox (build_dfg rw_blackbox rw_act)) <> 0.
    Proof. vm_compute. discriminate. Qed.

    Example whitebox_is_not_critical :
      crit_report_all rw_whitebox (build_dfg rw_whitebox rw_act) = [].
    Proof. vm_compute. reflexivity. Qed.

End Contrast.

Section Obligations.

    Theorem rw_decls_sound :
      forall act a_idx input, uncond_sound rw_whitebox 10 act a_idx input.
    Proof.
      intros act a_idx input.
      apply (uncond_sound_of_instances rw_whitebox 10).
      intros i Hi.
      unfold uncond_instances, decl_instances in Hi.
      apply filter_In in Hi. destruct Hi as [Hi _].
      apply in_flat_map in Hi. destruct Hi as [r [Hr Hi]].
      cbn in Hr. destruct Hr as [Hr | [Hr | []]]; subst r.
      - exact (xor_rule_sound rw_whitebox 10 act a_idx input i Hi).
      - exact (widen_rule_sound rw_whitebox 10 act a_idx input i Hi).
    Qed.

    Theorem rw_decl_guard_sound :
      forall act a_idx input, decl_sound rw_whitebox 10 act a_idx input.
    Proof.
      intros act a_idx input.
      apply (decl_sound_of_instances rw_whitebox 10 rw_decls_sound).
      intros i Hi. unfold decl_instances in Hi.
      apply in_flat_map in Hi. destruct Hi as [r [Hr Hi]].
      cbn in Hr. destruct Hr as [Hr | [Hr | []]]; subst r.
      - exact (xor_rule_sound rw_whitebox 10 act a_idx input i Hi).
      - exact (widen_rule_sound rw_whitebox 10 act a_idx input i Hi).
    Qed.

End Obligations.

Print Assumptions whitebox_is_not_critical.
Print Assumptions rw_decl_guard_sound.
