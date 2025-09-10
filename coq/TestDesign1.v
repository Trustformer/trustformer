Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.
Require Koika.Properties.SemanticProperties.
Module SemProps := Koika.Properties.SemanticProperties.
Require Import Streams.
Require Import Coq.Logic.Eqdep_dec.
Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.
Hammer_version.

Module TestDesign1.

  Section Operations.
    
    Inductive fs_ops :=
    | fs_nop.

  End Operations.

  Section FSpec.

    Definition sz := 32.
    Definition bits_false := Bits.of_nat sz 0.
    Definition bits_true := Bits.neg (bits_false).

    Inductive fs_action_t :=
    | fs_act_nop
    .
    Instance fs_actions_finite : FiniteType fs_action_t := _.
    Definition fs_action_encoding (a: fs_action_t) : bits_t sz :=
    match a with
    | fs_act_nop => Bits.of_nat sz 0
    end.
    

    Inductive fs_states_var :=
    | fs_st_val
    .
    Definition fs_states_type (x: fs_states_var) : type :=
    match x with
    | fs_st_val => bits_t sz
    end.
    Definition fs_states_init (x: fs_states_var) : (fs_states_type x) :=
    match x with
    | fs_st_val => Bits.zero
    end.
    
    Definition fs_transitions
      (act: fs_action_t)
      :
      (fs_ops)
      :=
      match act with
      | fs_act_nop => fs_nop
      end.

    Definition fs_op_step
      (state: ContextEnv.(env_t) fs_states_type)
      (state_op: fs_ops)
      : 
      (ContextEnv.(env_t) fs_states_type) :=
      match state_op with
      | fs_nop => state
      end.

    Section Examples.
      Definition s_init := ContextEnv.(create) fs_states_init.

      Definition s1_trans := fs_transitions fs_act_nop.
      Definition s1_state := (fs_op_step s_init s1_trans).

      Example s_example : ContextEnv.(getenv) s_init fs_st_val = bits_false.
      Proof. reflexivity. Qed.
      Example s1_example : ContextEnv.(getenv) s1_state fs_st_val = bits_false.
      Proof. ssimpl. Qed.  
    End Examples.
  End FSpec.

  (* =============================================================================== *)
  (* The stuff starting from here should not require changes when changing the above *)
  (* =============================================================================== *)

  Section Trustformer.

    Inductive reg_t := 
    | st_reg (x : fs_states_var).

    Definition R (r: reg_t) :=
    match r with
    | st_reg x => fs_states_type x
    end.

    Definition r (reg: reg_t) : R reg :=
      match reg with
      | st_reg x => fs_states_init x
      end.

    Inductive ext_fn_t := 
    | ext_in_cmd.

    Definition Sigma (fn: ext_fn_t) :=
      match fn with
      | ext_in_cmd => {$ bits_t 1 ~> maybe (bits_t sz) $}
      end.

    Definition ext_fn_specs (fn : ext_fn_t) := 
      match fn with
      | ext_in_cmd => {| efr_name := "in_cmd"; 
                        efr_internal := false |}
      end.
    
    Inductive rule_name_t :=
    | rule_cmd (cmd: fs_action_t)
    .

    Definition system_schedule_cmds : scheduler  :=
      List.fold_right (fun t acc => rule_cmd t |> acc) Done (@finite_elements fs_action_t _).
    Definition system_schedule := system_schedule_cmds.
    Eval compute in system_schedule.
    
    Definition op_to_uaction (x: fs_states_var) (op: fs_ops) (code: uaction reg_t ext_fn_t) : uaction reg_t ext_fn_t :=
      match op with
      | fs_nop => code
      end.

    Definition _rule_aux
      (state_op: fs_ops)
      (code: uaction reg_t ext_fn_t)
      : uaction reg_t ext_fn_t :=
        let state_code := List.fold_right (fun x acc => op_to_uaction x state_op acc) code (@finite_elements fs_states_var _) in
        state_code.

    (* Helper function that reads all state registers into variables *)
    (* TODO: a final version should only read the needed variables, to minimize dependencies *)
    Definition _rule_read_state_vars (code: uaction reg_t ext_fn_t) : uaction reg_t ext_fn_t  := 
      List.fold_right (fun x acc => 
        UBind (show x) {{ read0(st_reg x) }} acc
      ) code (@finite_elements fs_states_var _).
    
    (* Helper function that writes back all state variables *)
    (* TODO: a final version should only write the modified variables, to minimize dependencies *) 
    Definition _rule_write_state_vars (code: uaction reg_t ext_fn_t) : uaction reg_t ext_fn_t  := 
      List.fold_right (fun x acc => 
        USeq {{ write0(st_reg x, `UVar (show x)`) }} acc
      ) code (@finite_elements fs_states_var _).

    Definition _rule_cmd cmd : uaction reg_t ext_fn_t :=
      let state_ops := fs_transitions cmd in
      _rule_read_state_vars (
        _rule_aux state_ops (
          _rule_write_state_vars {{ pass }})).

    Eval compute in _rule_cmd fs_act_nop.

    Definition rules :=
      tc_rules R Sigma
        (fun rl =>  match rl with
          | rule_cmd cmd => 
            let cmd_enc := fs_action_encoding cmd in
            {{
                  let in_cmd := extcall ext_in_cmd(Ob~1) in
                  guard(get(in_cmd, valid) && get(in_cmd, data) == #cmd_enc);
                  `_rule_cmd cmd`
            }}
          end).

    Definition package :=
      {| ip_koika := {| koika_reg_types := R;
                        koika_reg_init := r;
                        koika_ext_fn_types := Sigma;
                        koika_rules := rules;
                        koika_rule_external := (fun _ => false);
                        koika_scheduler := system_schedule;
                        koika_module_name := "TestDesign1" |};

      ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn; efs_method := false |};
                  sp_prelude := None |};

      ip_verilog := {| vp_ext_fn_specs := ext_fn_specs |} |}.
    
    Section Correctness.

      Arguments id _ _ / : assert.
      Arguments env_t: simpl never.
      Arguments vect: simpl never.
      Arguments may_read /.
      Arguments may_write /.

      (* TODO generalize: each cycle could be a different omega *)
      Context (σ: forall f, Sig_denote (Sigma f)).

      Section Spec1.

        Definition explicit_schedule := system_schedule.
        Eval compute in explicit_schedule.

        Definition next_hw_cycle (hw_reg_state: ContextEnv.(env_t) R) := 
            TypedSemantics.interp_cycle σ rules system_schedule hw_reg_state.
        
        Definition initial_hw_state : ContextEnv.(env_t) R := ContextEnv.(create) r.

        (* helpers for encoding the action/command *)
        Definition encoded_action (a: fs_action_t) : type_denote (maybe (bits_t sz)) :=
          (Ob~1, (fs_action_encoding a, tt)).

        Lemma retSig_eq_bits : retSig (Sigma ext_in_cmd) = maybe (bits_t sz).
        Proof. simpl. reflexivity. Qed.

        Definition StateR (hw_reg_state: ContextEnv.(env_t) R) (fs_state: ContextEnv.(env_t) fs_states_type) : Prop :=
          forall x, hw_reg_state.[st_reg x] = fs_state.[x].

        Theorem InitState_correct :
          StateR initial_hw_state (ContextEnv.(create) fs_states_init).
        Proof.
          unfold initial_hw_state, fs_states_init. intros x; sauto.
        Qed.

        Ltac sorry := timeout 5 sauto.
        Ltac help := timeout 5 ssimpl.

        Theorem NextCycle_State_correct:
          forall cmd fs_state hw_reg_state, 
          (  σ ext_in_cmd (Ob~1) = encoded_action cmd
          /\ StateR hw_reg_state fs_state
          ) ->
          StateR (next_hw_cycle hw_reg_state) (fs_op_step fs_state (fs_transitions cmd)).
        Proof.
          (*
          intros cmd fs_state hw_reg_state H.
          destruct H as [H_cmd H_state].
          intros state_var.
          unfold next_hw_cycle, StateR in *.
          destruct cmd, state_var.

          unfold interp_cycle.
          rewrite SemProps.getenv_commit_update.

          unfold interp_scheduler, interp_scheduler'.
          unfold system_schedule, system_schedule_cmds, finite_elements, List.fold_right.
          cbv -[latest_write interp_rule vect vect_const log_empty log_app getenv ContextEnv].

          unfold interp_rule.
          unfold interp_action.

          repeat rewrite H_state.
          *)

          intros cmd fs_state hw_reg_state H.
          destruct H as [H_cmd H_state].
          intros state_var.
          unfold next_hw_cycle, StateR in *.
          destruct cmd, state_var.

          unfold interp_cycle.
          rewrite SemProps.getenv_commit_update.
          vm_compute (fs_op_step fs_state (fs_transitions fs_act_nop)). rewrite <- H_state.
          unfold system_schedule, system_schedule_cmds, finite_elements, List.fold_right.

          destruct (latest_write _ _) eqn:H_latest.
          - unfold latest_write, interp_scheduler, interp_scheduler' in H_latest.
            destruct (interp_rule _ _ _ _) eqn:H_irule.
            + rewrite SemProps.log_find_app in H_latest. 
              unfold interp_rule in H_irule.
              destruct (interp_action _ _ _ _) as [res|] eqn:H_action_result.
              * destruct res as [[l_res u] c]. simpl in H_irule. injection H_irule as ->.
                unfold interp_action, rules in H_action_result. timeout 5 simpl in H_action_result.
                rewrite H_cmd in H_action_result. timeout 5 simpl in H_action_result.
                injection H_action_result as H_l_eq.
                rewrite <- H_l_eq in H_latest. timeout 5 simpl in H_latest.
                injection H_latest as H_t_eq. (*hammer:*) sfirstorder.
              * (*hammer:*) hauto lq: on.
            + rewrite SemProps.log_find_empty in H_latest. (*hammer:*) hauto lq: on.
          - (*hammer:*) sauto.
        Qed.

      End Spec1.
    End Correctness.
  End Trustformer.
End TestDesign1.

(* ==== Synthesis ==== *)
Definition prog := Interop.Backends.register TestDesign1.package.
Set Extraction Output Directory "build".
Extraction "TestDesign1.ml" prog.