Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.DFG.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.
Require Import Trustformer.Properties.IPR.
Require Import Trustformer.Rules.PhiConst.
Require Import Trustformer.Rules.PhiBranch.
Require Import Trustformer.Examples.LockboxTries.

Require Import Coq.Lists.List.
Import ListNotations.

(*
    The taint-analysis claims the paper makes about its running example, as
    machine-checked facts.

    fig:dfgA5 (paper/sections/05_design/03_taint_analysis.tex): with [tries]
    secret, *every* phi is critical, so [action_test] must be constant time.
 *)

Section FigureA.

    Definition dfgA := build_dfg tfs_ctx fs_act_test.

    Definition node_at {s i o} (dfg: @dfg_state_t s i o) (n: nid_t)
        : @dfg_op_t s i o :=
        match nth_error (graph dfg) n with
        | Some nd => op nd
        | None => DFG_Empty
        end.

    Definition phi_nodes {s i o} (dfg: @dfg_state_t s i o)
        : list (@dfg_node_t s i o) :=
        filter (fun n => match op n with DFG_Phi _ _ _ => true | _ => false end)
               (graph dfg).

    (* The two branch conditions of fig:example-spec, in the order the builder
       emits them. *)
    Example condition_nodes :
      node_at dfgA 3 = DFG_Binary (tf_cmp tsz tf_neq) 1 2
      /\ node_at dfgA 6 = DFG_Binary (tf_cmp sz tf_eq) 4 5.
    Proof. split; vm_compute; reflexivity. Qed.

    (* [$tries - #1] survives all the way into the graph: the first use of
       arithmetic by any example in this tree. *)
    Example decrement_is_compiled :
      node_at dfgA 12 = DFG_Binary tf_sub 1 11.
    Proof. vm_compute. reflexivity. Qed.

    (* Both conditions read secret state, so both are tainted. *)
    Example conditions_are_tainted :
      In 3 (get_tainted tfs_ctx dfgA) /\ In 6 (get_tainted tfs_ctx dfgA).
    Proof. vm_compute. split; tauto. Qed.

    (* The paper's claim: *all* phi nodes are critical.  The compiler visits
       each of them exactly once here, so the two counts agreeing is the claim. *)
    Example every_phi_is_critical :
      List.length (crit_report_all tfs_ctx dfgA) = List.length (phi_nodes dfgA).
    Proof. vm_compute. reflexivity. Qed.

    (* ...and each one is critical because its condition is tainted and no
       declassification rule was supplied, not for some other reason. *)
    Example all_critical_for_lack_of_a_rule :
      crit_report_all tfs_ctx dfgA
      = [CR_no_rule 3; CR_no_rule 6; CR_no_rule 3; CR_no_rule 6; CR_no_rule 3;
         CR_no_rule 6].
    Proof. vm_compute. reflexivity. Qed.

End FigureA.

(*
    fig:dfgB5: the same module with a *public* [tries] -- the specification lets
    the user see how many attempts are left.  Per the attacker model
    (01_functional_spec.tex, footnote), public state is an output variable.
 *)

Section FigureB.

    Inductive fsB_states :=
    | fsB_st_pin
    | fsB_st_secret
    .

    Inductive fsB_inputs :=
    | fsB_in_pin
    | fsB_in_secret
    .

    Inductive fsB_outputs :=
    | fsB_out_status
    | fsB_out_secret
    | fsB_out_tries
    .

    Definition fsB_states_size (x: fsB_states) : nat := sz.
    Definition fsB_inputs_size (x: fsB_inputs) : nat := sz.

    Definition fsB_outputs_size (x: fsB_outputs) : nat :=
    match x with
    | fsB_out_status => sz
    | fsB_out_secret => sz
    | fsB_out_tries => tsz
    end.

    Definition fsB_states_init (x: fsB_states) : bits_t (fsB_states_size x) :=
        Bits.zero.

    Definition fsB_transitions (act: fs_action)
        : (@tf_ops fsB_states fsB_inputs fsB_outputs) :=
        match act with
        | fs_act_set =>
            {[
                let $fsB_st_pin := $fsB_in_pin;
                let $fsB_st_secret := $fsB_in_secret;
                let $fsB_out_tries := #tries_reset
            ]}
        | fs_act_test =>
            {[
                if ($fsB_out_tries !=[tsz] #0) then
                    (if ($fsB_st_pin ==[sz] $fsB_in_pin) then
                        let $fsB_out_secret := $fsB_st_secret;
                        let $fsB_out_status := #1;
                        let $fsB_out_tries := #tries_reset
                    else
                        let $fsB_out_status := #0;
                        let $fsB_out_tries := $fsB_out_tries - #1)
                else
                    let $fsB_out_status := #0
            ]}
        end.

    Definition mk_ctxB (decls: list (decl_rule fsB_states fsB_inputs fsB_outputs))
        : TFSchedContext := {|
        tfs_spec_states := fsB_states;
        tfs_spec_states_fin := _;
        tfs_spec_states_size := fsB_states_size;
        tfs_spec_states_init := fsB_states_init;

        tfs_spec_inputs := fsB_inputs;
        tfs_spec_inputs_fin := _;
        tfs_spec_inputs_size := fsB_inputs_size;

        tfs_spec_outputs := fsB_outputs;
        tfs_spec_outputs_fin := _;
        tfs_spec_outputs_size := fsB_outputs_size;

        tfs_spec_action := fs_action;
        tfs_spec_action_fin := _;
        tfs_spec_action_ops := fsB_transitions;
        tfs_spec_decls := decls
    |}.

    Definition ctxB_blackbox := mk_ctxB [].
    Definition ctxB_whitebox := mk_ctxB [phiconst_rule; phibranch_rule].

    Definition dfgB := build_dfg ctxB_blackbox fs_act_test.

    (* [tries] now enters the graph as an output read, and the graph is otherwise
       node-for-node the one of fig:dfgA5. *)
    Example tries_is_public :
      node_at dfgB 1 = DFG_Var (DFG_OVar fsB_out_tries).
    Proof. vm_compute. reflexivity. Qed.

    (* Forward taint plus the blackbox untainting that is already fused into
       [get_tainted]: the [tries != 0] branch is free, only the pin check is
       critical.  Exactly the three occurrences the paper counts
       (03_taint_analysis.tex L127, L203). *)
    Example only_the_pin_check_is_critical :
      crit_report_all ctxB_blackbox dfgB
      = [CR_no_rule 6; CR_no_rule 6; CR_no_rule 6].
    Proof. vm_compute. reflexivity. Qed.

    (* The action assigns exactly the three variables the specification writes.
       A variable a branch merely READS is not an assignment and must not
       appear here -- it used to, which is what produced the identity phi the
       figure does not draw. *)
    Example var_map_is_the_written_variables :
      map fst (var_map dfgB)
      = [DFG_OVar fsB_out_tries; DFG_OVar fsB_out_status; DFG_OVar fsB_out_secret].
    Proof. vm_compute. reflexivity. Qed.

    (* 03_taint_analysis.tex L198: the attacker deduces the outcome of the pin
       check from [out_status] and [tries], so no branch has to be constant time.
       [phiconst_rule] is the paper's PhiCUT, [phibranch_rule] its PhiAUT. *)
    Example whitebox_removes_all_criticality :
      crit_report_all ctxB_whitebox (build_dfg ctxB_whitebox fs_act_test) = [].
    Proof. vm_compute. reflexivity. Qed.

    Definition mk_ctxA (decls: list (decl_rule fs_states fs_inputs fs_outputs))
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

    Definition ctxA_whitebox := mk_ctxA [phiconst_rule; phibranch_rule].

    (* 03_taint_analysis.tex L202: untainting must not untaint too much.  The
       same two rules buy nothing back in fig:dfgA5, and the diagnostic says why
       per occurrence: [tries] has no rule at all, and the declassification of
       the pin check needs the path literal [(3, true)], which is unavailable
       because the phi that would provide it is itself critical. *)
    Example secret_tries_defeats_the_same_rules :
      crit_report_all ctxA_whitebox (build_dfg ctxA_whitebox fs_act_test)
      = [CR_no_rule 3;
         CR_guard_unmet 6 [[(6, true)]; [(6, false)]; [(3, true)]];
         CR_no_rule 3;
         CR_guard_unmet 6 [[(6, true)]; [(6, false)]; [(3, true)]];
         CR_no_rule 3;
         CR_guard_unmet 6 [[(6, true)]; [(6, false)]; [(3, true)]]].
    Proof. vm_compute. reflexivity. Qed.

End FigureB.

(*
    The declassifications fig:dfgB5 relies on are discharged by the rule
    library, so the IPR theorems apply to the variable-latency lockbox.
 *)

Section Obligation.

    Theorem lockboxB_uncond_sound :
      forall act a_idx input, uncond_sound ctxB_whitebox 10 act a_idx input.
    Proof.
      intros act a_idx input.
      apply (uncond_sound_of_instances ctxB_whitebox 10).
      intros i Hi.
      unfold uncond_instances, decl_instances in Hi.
      apply filter_In in Hi. destruct Hi as [Hi _].
      apply in_flat_map in Hi. destruct Hi as [r [Hr Hi]].
      cbn in Hr. destruct Hr as [Hr | [Hr | []]]; subst r.
      - exact (phiconst_rule_sound ctxB_whitebox 10 act a_idx input i Hi).
      - exact (phibranch_rule_sound ctxB_whitebox 10 act a_idx input i Hi).
    Qed.

    Theorem lockboxB_decl_guard_sound :
      forall act a_idx input, decl_sound ctxB_whitebox 10 act a_idx input.
    Proof.
      intros act a_idx input.
      apply (decl_sound_of_instances ctxB_whitebox 10 lockboxB_uncond_sound).
      intros i Hi.
      unfold decl_instances in Hi.
      apply in_flat_map in Hi. destruct Hi as [r [Hr Hi]].
      cbn in Hr. destruct Hr as [Hr | [Hr | []]]; subst r.
      - exact (phiconst_rule_sound ctxB_whitebox 10 act a_idx input i Hi).
      - exact (phibranch_rule_sound ctxB_whitebox 10 act a_idx input i Hi).
    Qed.

End Obligation.

Print Assumptions lockboxB_uncond_sound.
Print Assumptions lockboxB_decl_guard_sound.

(*
    Cycle bounds.  [action_bounds] reports the best and worst case a *circuit*
    can exhibit; the latency of one concrete input is [L] in Properties/IPR.v,
    which exists for the proofs and is not meant to be evaluated.
    [fst = snd] certifies that the action is constant time.
 *)

Section Bounds.

    Definition ctxA_blackbox := mk_ctxA [].

    (* With [tries] secret every phi is critical, so both branches of the
       decrement are always evaluated and the action is constant time: the two
       bounds coincide.  03_taint_analysis.tex L129 quotes two cycles for
       [action_test]; that is what the scheduler produces at a cost limit of 4. *)
    Example lockbox_takes_two_cycles :
      action_bounds ctxA_blackbox 4 (build_dfg ctxA_blackbox fs_act_test) = (2, 2).
    Proof. vm_compute. reflexivity. Qed.

    (* At the cost limit the other examples use, the whole action is one
       combinational cycle -- which is what the emitted Verilog shows. *)
    Example lockbox_is_combinational_at_10 :
      action_bounds ctxA_blackbox 10 (build_dfg ctxA_blackbox fs_act_test) = (1, 1).
    Proof. vm_compute. reflexivity. Qed.

    (* Making [tries] public separates the bounds: the guard [tries != 0] is no
       longer tainted, so its phi selects instead of ANDing both branches, and
       the locked-out case never pays for the [tries - 1] stage.  One cycle when
       [tries] is exhausted, two when it is not.  This is only visible because a
       source node is never buffered -- the shared [tries] read would otherwise
       drag the fast branch into the second stage as well. *)
    Example public_tries_separates_the_bounds :
      action_bounds ctxB_blackbox 4 (build_dfg ctxB_blackbox fs_act_test) = (1, 2)
      /\ action_bounds ctxB_whitebox 4 (build_dfg ctxB_whitebox fs_act_test) = (1, 2).
    Proof. split; vm_compute; reflexivity. Qed.

    (* The separation is a property of the schedule, not of one cost limit: it
       shows up at every limit that splits the action at all. *)
    Example public_tries_sweep :
      map (fun c => action_bounds ctxB_whitebox c (build_dfg ctxB_whitebox fs_act_test))
          [1; 2; 3; 4; 5]
      = [(3, 5); (2, 3); (1, 2); (1, 2); (1, 1)].
    Proof. vm_compute. reflexivity. Qed.

End Bounds.

(*
    04_hardware_generation.tex §"Valid signal generation" works its example on
    exactly this action at exactly this schedule: four valid signals, for
    [out_secret], [tries], [out_status] and [buf].  At cost limit 4 there is
    precisely one buffer -- node 12, the [tries - 1] subtraction -- so it IS the
    paper's [buf].
 *)

Section ValidSignals.

    (* [valid_expr_and] absorbs [tf_const 1], so a [done] signal that reduces to
       a single valid variable is the statement that every OTHER root's valid
       signal is [Const 0b1].  The paper: "the valid signal expressions for
       out_secret, out_status and buf are all Const 0b1 since they only depend
       on source nodes".  [buf]'s own valid is [Const 1] too -- which is only
       true because a source node is no longer buffered: the [tries] read it
       depends on used to be a buffer, and a buffer's valid signal is a
       variable, not a constant.
       The buffer's valid register is bound out of the schedule itself rather
       than written down, so the assertion needs no [Vect.index] literals. *)
    Example valid_signals_all_phis_critical :
      match fst (schedule ctxA_blackbox 4 fs_act_test) with
      | [ tf_assign dst_done e_done;
          tf_assign _ e_buf;
          tf_assign v_buf e_valid ] =>
            dst_done = tf_dfg_done
            /\ e_valid = tf_const 1
            /\ e_buf = {[$(tf_dfg_s fs_st_tries) - #1]}
            /\ e_done = tf_svar v_buf
      | _ => False
      end.
    Proof. vm_compute. repeat split; reflexivity. Qed.

    (* The non-critical case.  The paper says: "If tries is <> 0 and
       pin = in_pin then the valid signal is the current valid signal of buf,
       else it is the constant true."  The compiler says the opposite on the
       INNER test, and the compiler is right: [tries - 1] -- the only buffered
       node -- sits in the WRONG-pin branch (LockboxTries.v, [fs_act_test]),
       while the matching-pin branch assigns the constant [tries_reset], which
       is a source node and valid at once.  So the wait on [buf] happens exactly
       when [tries <> 0] AND [pin <> in_pin]. *)
    Example valid_signals_no_phi_critical :
      match fst (schedule ctxB_whitebox 4 fs_act_test) with
      | [ tf_assign dst_done e_done;
          tf_assign _ e_buf;
          tf_assign v_buf e_valid ] =>
            dst_done = tf_dfg_done
            /\ e_valid = tf_const 1
            /\ e_buf = {[$fsB_out_tries - #1]}
            /\ e_done =
                 tf_expr_if {[$fsB_out_tries !=[tsz] #0]}
                   (tf_expr_if {[$(tf_dfg_s fsB_st_pin) ==[sz] $fsB_in_pin]}
                      (tf_const 1)
                      (tf_svar v_buf))
                   (tf_const 1)
      | _ => False
      end.
    Proof. vm_compute. repeat split; reflexivity. Qed.

End ValidSignals.

(*
    ...but the bounds do separate when the branches are unbalanced, and that
    separation is exactly what criticality removes.  Same design twice, once
    branching on an input and once on the secret.
 *)

Section BoundsContrast.

    Inductive sk_action := sk_act.
    Inductive sk_states := sk_secret.
    Inductive sk_inputs := sk_in.
    Inductive sk_outputs := sk_out.

    Definition sk_ssz (_: sk_states) : nat := 32.
    Definition sk_isz (_: sk_inputs) : nat := 32.
    Definition sk_osz (_: sk_outputs) : nat := 32.
    Definition sk_init (x: sk_states) : bits_t (sk_ssz x) := Bits.zero.

    Definition sk_ops (cond: @tf_expr sk_states sk_inputs sk_outputs)
        : (@tf_ops sk_states sk_inputs sk_outputs) :=
        {[
          if `cond`
          then let $sk_out := $sk_secret * $sk_secret * $sk_secret
          else let $sk_out := #1
        ]}.

    Definition mk_sk_ctx (cond: @tf_expr sk_states sk_inputs sk_outputs)
        : TFSchedContext := {|
        tfs_spec_states := sk_states;
        tfs_spec_states_fin := _;
        tfs_spec_states_size := sk_ssz;
        tfs_spec_states_init := sk_init;
        tfs_spec_inputs := sk_inputs;
        tfs_spec_inputs_fin := _;
        tfs_spec_inputs_size := sk_isz;
        tfs_spec_outputs := sk_outputs;
        tfs_spec_outputs_fin := _;
        tfs_spec_outputs_size := sk_osz;
        tfs_spec_action := sk_action;
        tfs_spec_action_fin := _;
        tfs_spec_action_ops := fun _ => sk_ops cond;
        tfs_spec_decls := []
    |}.

    Definition sk_public := mk_sk_ctx {[ $sk_in ==[32] #0 ]}.
    Definition sk_private := mk_sk_ctx {[ $sk_secret ==[32] #0 ]}.

    (* Public selector: the phi is not critical, so the cheap branch may finish
       early and the action has data-dependent latency. *)
    Example public_selector_is_variable :
      crit_report_all sk_public (build_dfg sk_public sk_act) = []
      /\ action_bounds sk_public 4 (build_dfg sk_public sk_act) = (1, 3).
    Proof. split; vm_compute; reflexivity. Qed.

    (* Secret selector: the phi is critical, both branch validities are ANDed,
       and the bounds collapse onto the worst case.  The gap between the two
       examples is the price of constant time. *)
    Example secret_selector_is_constant_time :
      action_bounds sk_private 4 (build_dfg sk_private sk_act) = (3, 3).
    Proof. vm_compute. reflexivity. Qed.

End BoundsContrast.
