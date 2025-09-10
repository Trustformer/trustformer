Require Import Koika.Frontend.
Require Import Koika.Std.
Require Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.

Require Import Trustformer.TestDesign2.TrustformerSyntax.
Require Import Trustformer.TestDesign2.TrustformerSemantics.
Require Import Trustformer.TestDesign2.TrustformerSynthesis.

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Section FunctionalSpecification.

    Definition sz := 32.
    Definition bits_false := Bits.of_nat sz 0.
    Definition bits_true := Bits.neg (bits_false).

    Inductive fs_action :=
    | fs_act_nop
    .

    Inductive fs_states :=
    | fs_st_val
    .

    Definition fs_states_t (x: fs_states) : type :=
    match x with
    | fs_st_val => bits_t sz
    end.

    Definition fs_states_init (x: fs_states) : (fs_states_t x) :=
    match x with
    | fs_st_val => Bits.zero
    end.

    Definition fs_transitions
        (act: fs_action)
        :
        (tf_ops)
        :=
        match act with
        | fs_act_nop => tf_nop
        end.

    Definition fs_step := tf_op_step fs_states _ fs_states_t. 
    
    Section Examples.

        Definition s_init := ContextEnv.(create) fs_states_init.

        Definition s1_trans := fs_transitions fs_act_nop.
        Definition s1_state := fs_step s_init s1_trans.

        Example s_example : ContextEnv.(getenv) s_init fs_st_val = bits_false.
        Proof. reflexivity. Qed.
        Example s1_example : ContextEnv.(getenv) s1_state fs_st_val = bits_false.
        Proof. ssimpl. Qed.  
    End Examples.

End FunctionalSpecification.


Section Synthesis.

    Definition tf_ctx : TFSynthContext := {|
        tf_spec_states := fs_states;
        tf_spec_states_fin := _; 
        tf_spec_states_t := fs_states_t;
        tf_spec_states_init := fs_states_init;
        tf_spec_action := fs_action;
        tf_spec_action_fin := _; 
        tf_spec_action_ops := fs_transitions
    |}.

    Definition R := TrustformerSynthesis.R tf_ctx.
    Check R.
    Definition r := TrustformerSynthesis.r tf_ctx.
    Check r.
    Definition Sigma := TrustformerSynthesis.Sigma.
    Check Sigma.

    Definition rules := TrustformerSynthesis.rules tf_ctx.
    Check rules.
    Definition system_schedule := TrustformerSynthesis.system_schedule tf_ctx.
    Check system_schedule.

    Definition checked_rules := tc_rules R Sigma rules.

    Definition package :=
      {| ip_koika := {| koika_reg_types := R;
                        koika_reg_names := TrustformerSynthesis.reg_names tf_ctx;
                        koika_reg_init := r;
                        koika_ext_fn_types := Sigma;
                        koika_rules := checked_rules;
                        koika_rule_names := TrustformerSynthesis.rule_names tf_ctx;
                        koika_rule_external := (fun _ => false);
                        koika_scheduler := system_schedule;
                        koika_module_name := "TestDesign2" |};

      ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn; efs_method := false |};
                  sp_prelude := None |};

      ip_verilog := {| vp_ext_fn_specs := ext_fn_specs |} |}.

End Synthesis.

(* Extraction *)

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "TestDesign2.ml" prog.

Section UntypedCorrectness.

    (* TODO generalize: each cycle could be a different omega *)
    Context (sigma: ext_fn_t -> val -> val).

    Definition _ur (x: reg_t tf_ctx) := val_of_value (r x).

    Definition initial_hw_state := 
        ContextEnv.(create) _ur.
    Check initial_hw_state.

    Definition next_hw_cycle (hw_reg_state: env_t ContextEnv (fun _ : reg_t tf_ctx => val)) := 
        UntypedSemantics.interp_cycle rules hw_reg_state sigma system_schedule.
    
    Definition _fs_cmd_encoding (a: fs_action) :=
      Bits.of_nat cmd_reg_size (@finite_index fs_action _ a).

    Definition _encoded_cmd (a: fs_action) : type_denote (maybe (bits_t sz)) :=
        (Ob~1, (_fs_cmd_encoding a, tt)).

    Definition encoded_cmd (a: fs_action) := val_of_value (_encoded_cmd a).

    Definition StateR (hw_reg_state: env_t ContextEnv (fun _ : reg_t tf_ctx => val)) (fs_state: ContextEnv.(env_t) fs_states_t) :=
        forall x, hw_reg_state.[tf_reg tf_ctx x] = val_of_value (fs_state.[x]).
    
    Theorem InitState_correct :
        StateR initial_hw_state (ContextEnv.(create) fs_states_init).
    Proof.
        unfold initial_hw_state, fs_states_init. intros x. sauto lq: on.
    Qed.

    Definition val_true := Bits ( [ true ] ).

    Theorem NextState_correct:
        forall cmd fs_state hw_reg_state, 
        (  sigma ext_in_cmd val_true = encoded_cmd cmd
        /\ StateR hw_reg_state fs_state
        ) ->
        StateR (next_hw_cycle hw_reg_state) (fs_step fs_state (fs_transitions cmd)).
    Proof.
        intros cmd fs_state hw_reg_state H.
        destruct H as [H_cmd H_state].
        intros state_var.
        unfold next_hw_cycle, StateR in *.
        destruct cmd, state_var.

        unfold UntypedSemantics.interp_cycle.
        unfold UntypedLogs.commit_update.
        rewrite getenv_create.
        vm_compute (fs_step _ _). rewrite <- H_state.
        vm_compute (system_schedule).
        
        destruct (UntypedLogs.latest_write _ _) eqn:H_latest.
        - unfold UntypedLogs.latest_write, UntypedSemantics.interp_scheduler, UntypedSemantics.interp_scheduler' in H_latest.
          destruct (UntypedSemantics.interp_rule _ _ _ _) eqn:H_irule.
          + unfold UntypedSemantics.interp_rule in H_irule.
            destruct (UntypedSemantics.interp_action _ _ _ _) as [res|] eqn:H_action_result.
              * destruct res as [[l_res u] c]. injection H_irule as ->.
                unfold UntypedSemantics.interp_action in H_action_result.
                unfold rules, TrustformerSynthesis.rules, _rule_cmd, _rule_read_state_vars, _rule_aux, _rule_write_state_vars, op_to_uaction, all_spec_states in H_action_result.
                vm_compute finite_elements in H_action_result.
                repeat unfold fold_right in H_action_result.
                vm_compute action_index in H_action_result.
                vm_compute _reg_name in H_action_result.
                unfold cmd_reg_size in H_action_result.
                unfold desugar_action, desugar_action' in H_action_result.
                unfold encoded_cmd, _encoded_cmd, _fs_cmd_encoding in H_cmd.
                timeout 30 cbn in H_action_result.
                unfold val_true in H_cmd.
                rewrite H_cmd in H_action_result.
                (* ERROR: the next step times out :( *)
                timeout 5 simpl in H_action_result.
                injection H_action_result as H_l_eq.
                rewrite <- H_l_eq in H_latest. timeout 5 simpl in H_latest.
                injection H_latest as H_t_eq. (*hammer:*) sfirstorder.
                * timeout 20 sauto.
            + timeout 30 sauto. 
        - (*hammer:*) sauto.
    Qed.

End UntypedCorrectness.

(* Section Correctness.

    Arguments id _ _ / : assert.
    Arguments env_t: simpl never.
    Arguments vect: simpl never.
    Arguments may_read /.
    Arguments may_write /.

    (* TODO generalize: each cycle could be a different omega *)
    Context (σ: forall f, Sig_denote (Sigma f)).

    Definition explicit_schedule := system_schedule.
    Eval compute in explicit_schedule.

    Definition next_hw_cycle (hw_reg_state: ContextEnv.(env_t) R) := 
        TypedSemantics.interp_cycle σ checked_rules system_schedule hw_reg_state.
    
    Definition initial_hw_state : ContextEnv.(env_t) R := ContextEnv.(create) r.

    Definition fs_action_encoding (a: fs_action) :=
      Bits.of_nat cmd_reg_size (@finite_index fs_action _ a).

    (* helpers for encoding the action/command *)
    Definition encoded_action (a: fs_action) : type_denote (maybe (bits_t sz)) :=
        (Ob~1, (fs_action_encoding a, tt)).

    Lemma retSig_eq_bits : retSig (Sigma ext_in_cmd) = maybe (bits_t sz).
    Proof. simpl. reflexivity. Qed.

    Definition StateR (hw_reg_state: ContextEnv.(env_t) R) (fs_state: ContextEnv.(env_t) fs_states_t) : Prop :=
        forall x, hw_reg_state.[tf_reg tf_ctx x] = fs_state.[x].

    Theorem InitState_correct :
        StateR initial_hw_state (ContextEnv.(create) fs_states_init).
    Proof.
        unfold initial_hw_state, fs_states_init. intros x; (* hammer: *) sauto lq: on.
    Qed.

    Ltac sorry := timeout 5 sauto.
    Ltac help := timeout 5 ssimpl.

    Theorem NextCycle_State_correct:
        forall cmd fs_state hw_reg_state, 
        (  σ ext_in_cmd (Ob~1) = encoded_action cmd
        /\ StateR hw_reg_state fs_state
        ) ->
        StateR (next_hw_cycle hw_reg_state) (fs_step fs_state (fs_transitions cmd)).
    Proof.
        intros cmd fs_state hw_reg_state H.
        destruct H as [H_cmd H_state].
        intros state_var.
        unfold next_hw_cycle, StateR in *.
        destruct cmd, state_var.

        unfold interp_cycle.
        rewrite SemProps.getenv_commit_update.
        vm_compute (fs_step _ _). rewrite <- H_state.
        vm_compute (system_schedule).
        
        destruct (latest_write _ _) eqn:H_latest.
        - unfold latest_write, interp_scheduler, interp_scheduler' in H_latest.
            destruct (interp_rule _ _ _ _) eqn:H_irule.
            + rewrite SemProps.log_find_app in H_latest. 
                unfold interp_rule in H_irule.
                destruct (interp_action _ _ _ _) as [res|] eqn:H_action_result.
                * destruct res as [[l_res u] c]. simpl in H_irule. injection H_irule as ->.
                unfold interp_action in H_action_result.
                unfold checked_rules, _rule_cmd, _rule_read_state_vars, _rule_aux, _rule_write_state_vars, op_to_uaction, all_spec_states in H_action_result.
                vm_compute finite_elements in H_action_result.
                repeat unfold fold_right in H_action_result.
                vm_compute action_index in H_action_result.
                vm_compute _reg_name in H_action_result.
                unfold cmd_reg_size in H_action_result.
                unfold desugar_action, desugar_action' in H_action_result.
                unfold encoded_action, fs_action_encoding in H_cmd.
                timeout 30 cbn in H_action_result.
                rewrite H_cmd in H_action_result.
                (* ERROR: the next step times out :( *)
                timeout 1000 simpl in H_action_result.
                rewrite H_cmd in H_action_result. timeout 5 simpl in H_action_result.
                injection H_action_result as H_l_eq.
                rewrite <- H_l_eq in H_latest. timeout 5 simpl in H_latest.
                injection H_latest as H_t_eq. (*hammer:*) sfirstorder.
                * (*hammer:*) hauto lq: on.
            + rewrite SemProps.log_find_empty in H_latest. (*hammer:*) hauto lq: on.
        - (*hammer:*) sauto.
    Qed.

End Correctness. *)