(*! Phase F: the paper's lockbox, as an acceptance test.

    `paper/sections/05_design/03_taint_analysis.tex`, "Backwards Untainting",
    makes two concrete claims:

      - standard lockbox (`tries` secret, fig. A5): ALL phi nodes are critical;
      - modified lockbox (`tries` public, fig. B5): NO phi node is critical,
        because `==[sz]` is conditionally untainted under `!=[2] = true` and
        every phi depending on it lies on a path where `!=[2]` is true.

    The two contexts below differ only in whether the specification publishes
    `tries`.  Everything else -- the rule set, the analysis, the compiler -- is
    identical.
!*)

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

Section Specification.

    Definition lsz := 32.
    Definition tsz := 2.

    Inductive lb_action := lb_act_test.

    Inductive lb_states := lb_st_pin | lb_st_secret | lb_st_tries.

    Inductive lb_inputs := lb_in_pin.

    Inductive lb_outputs := lb_out_status | lb_out_secret | lb_out_tries.

    Definition lb_states_size (x: lb_states) : nat :=
      match x with
      | lb_st_pin => lsz
      | lb_st_secret => lsz
      | lb_st_tries => tsz
      end.

    Definition lb_inputs_size (_: lb_inputs) : nat := lsz.

    Definition lb_outputs_size (x: lb_outputs) : nat :=
      match x with
      | lb_out_status => lsz
      | lb_out_secret => lsz
      | lb_out_tries => tsz
      end.

    Definition lb_states_t := tf_states_type lb_states_size.

    Definition lb_states_init (x: lb_states) : (lb_states_t x) :=
      match x with
      | lb_st_pin => Bits.zero
      | lb_st_secret => Bits.zero
      | lb_st_tries => Bits.zero
      end.

    (* fig. A5: tries is secret, nothing about it is published. *)
    Definition lb_secret_tries (act: lb_action)
      : (@tf_ops lb_states lb_inputs lb_outputs tf_no_externs) :=
      match act with
      | lb_act_test =>
          {[
            if ($lb_st_tries !=[tsz] #0) then
              (if ($lb_st_pin ==[lsz] $lb_in_pin) then
                 let $lb_out_secret := $lb_st_secret;
                 let $lb_out_status := #1
               else
                 let $lb_out_status := #0;
                 let $lb_st_tries := $lb_st_tries - #1)
            else
              let $lb_out_status := #0
          ]}
      end.

    (* fig. B5: the user may see how many tries are left. *)
    Definition lb_public_tries (act: lb_action)
      : (@tf_ops lb_states lb_inputs lb_outputs tf_no_externs) :=
      match act with
      | lb_act_test =>
          {[
            let $lb_out_tries := $lb_st_tries;
            if ($lb_st_tries !=[tsz] #0) then
              (if ($lb_st_pin ==[lsz] $lb_in_pin) then
                 let $lb_out_secret := $lb_st_secret;
                 let $lb_out_status := #1
               else
                 let $lb_out_status := #0;
                 let $lb_st_tries := $lb_st_tries - #1)
            else
              let $lb_out_status := #0
          ]}
      end.

End Specification.

Section Contexts.

    Definition mk_lb (ops: lb_action -> @tf_ops lb_states lb_inputs lb_outputs tf_no_externs)
        (decls: list (decl_rule lb_states lb_inputs lb_outputs tf_no_externs))
      : TFSchedContext := {|
      tfs_spec_states := lb_states;
      tfs_spec_states_fin := _;
      tfs_spec_states_size := lb_states_size;
      tfs_spec_states_init := lb_states_init;

      tfs_spec_inputs := lb_inputs;
      tfs_spec_inputs_fin := _;
      tfs_spec_inputs_size := lb_inputs_size;

      tfs_spec_outputs := lb_outputs;
      tfs_spec_outputs_fin := _;
      tfs_spec_outputs_size := lb_outputs_size;

      tfs_spec_externs := tf_no_externs;
      tfs_spec_externs_sig := tf_no_externs_sig;

      tfs_spec_action := lb_action;
      tfs_spec_action_fin := _;
      tfs_spec_action_ops := ops;
      tfs_spec_decls := decls
    |}.

    Definition lb_rules : list (decl_rule lb_states lb_inputs lb_outputs tf_no_externs) :=
      [neg_rule; phibranch_rule; phiconst_rule].

    Definition ctx_A := mk_lb lb_secret_tries lb_rules.
    Definition ctx_B := mk_lb lb_public_tries lb_rules.

    (* Both specifications elaborate to the same graph size, so the contrast is
       about the analysis and not about the shape of the design. *)
    Example lb_same_graph_size :
      length (graph (build_dfg ctx_A lb_act_test)) = 27
      /\ length (graph (build_dfg ctx_B lb_act_test)) = 27.
    Proof. split; vm_compute; reflexivity. Qed.

    (* fig. A5.  Node 3 is [!=[tsz]] and node 6 is [==[lsz]].  Nothing
       declassifies the tries comparison, so its phis stay critical; the pin
       comparison IS declassified -- PhiCUT recovers it from a phi with two
       distinct constant branches -- but only under [(3, true)], a path the
       compiler never reaches because the outer phi is critical and therefore
       does not extend the path.  This is the paper's "all phi nodes are
       critical". *)
    Example lb_secret_tries_all_critical :
      crit_report_all ctx_A (build_dfg ctx_A lb_act_test)
      = [CR_no_rule 3;
         CR_guard_unmet 6 [[(6, true)]; [(6, false)]; [(3, true)]];
         CR_no_rule 3;
         CR_guard_unmet 6 [[(6, true)]; [(6, false)]; [(3, true)]];
         CR_no_rule 3;
         CR_guard_unmet 6 [[(6, true)]; [(6, false)]; [(3, true)]];
         CR_no_rule 3; CR_no_rule 3;
         CR_guard_unmet 6 [[(6, true)]; [(6, false)]; [(3, true)]]].
    Proof. vm_compute. reflexivity. Qed.

    (* fig. B5.  Publishing [tries] makes node 3 derivable, so its phis are
       non-critical and DO extend the path with [(3, true)] -- which is exactly
       the guard the pin comparison needed.  The paper's "none of the phi nodes
       require constant time enforcement, since all phi nodes depending on
       ==[sz] lie on paths where !=[2] evaluates to true". *)
    Example lb_public_tries_none_critical :
      crit_report_all ctx_B (build_dfg ctx_B lb_act_test) = [].
    Proof. vm_compute. reflexivity. Qed.

End Contexts.

Section Obligations.

    (* The whitebox result is only meaningful if the rules it rests on are
       discharged, so the IPR theorems apply to the variable-latency design. *)
    Theorem lb_decls_sound :
      forall act a_idx input, uncond_sound ctx_B 10 act a_idx input.
    Proof.
      intros act a_idx input.
      apply (uncond_sound_of_instances ctx_B 10).
      intros i Hi.
      unfold uncond_instances, decl_instances in Hi.
      apply filter_In in Hi. destruct Hi as [Hi _].
      apply in_flat_map in Hi. destruct Hi as [r [Hr Hi]].
      cbn in Hr. destruct Hr as [Hr | [Hr | [Hr | []]]]; subst r.
      - exact (neg_rule_sound ctx_B 10 act a_idx input i Hi).
      - exact (phibranch_rule_sound ctx_B 10 act a_idx input i Hi).
      - exact (phiconst_rule_sound ctx_B 10 act a_idx input i Hi).
    Qed.

    Theorem lb_decl_guard_sound :
      forall act a_idx input, decl_sound ctx_B 10 act a_idx input.
    Proof.
      intros act a_idx input.
      apply (decl_sound_of_instances ctx_B 10 lb_decls_sound).
      intros i Hi. unfold decl_instances in Hi.
      apply in_flat_map in Hi. destruct Hi as [r [Hr Hi]].
      cbn in Hr. destruct Hr as [Hr | [Hr | [Hr | []]]]; subst r.
      - exact (neg_rule_sound ctx_B 10 act a_idx input i Hi).
      - exact (phibranch_rule_sound ctx_B 10 act a_idx input i Hi).
      - exact (phiconst_rule_sound ctx_B 10 act a_idx input i Hi).
    Qed.

End Obligations.

Print Assumptions lb_public_tries_none_critical.
Print Assumptions lb_decl_guard_sound.
