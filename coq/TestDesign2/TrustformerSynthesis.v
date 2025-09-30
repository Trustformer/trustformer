Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.
Require Koika.Properties.SemanticProperties.
Require Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.

Require Import Trustformer.TestDesign2.TrustformerSyntax.
Require Import Trustformer.TestDesign2.TrustformerSemantics.
Require Trustformer.TestDesign2.UntypedProperties.CommonProperties.

Require Import Streams.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Init.Tactics.
Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Record TFSynthContext := {
  tf_spec_states : Type;
  tf_spec_states_fin : FiniteType tf_spec_states;
  tf_spec_states_names : Show tf_spec_states;
  tf_spec_states_t : tf_spec_states -> type;
  tf_spec_states_init : forall x: tf_spec_states, tf_spec_states_t x;
  tf_spec_action : Type;
  tf_spec_action_fin : FiniteType tf_spec_action;
  tf_spec_action_names : Show tf_spec_action;
  tf_spec_action_ops : tf_spec_action -> tf_ops (* TODO: more than just a single op *)
}.

Section TrustformerSynthesis.

    Context (tf_synth_ctx: TFSynthContext).

    Definition spec_states := tf_spec_states tf_synth_ctx.
    Definition spec_states_fin := tf_spec_states_fin tf_synth_ctx.
    Definition spec_states_t := tf_spec_states_t tf_synth_ctx.
    Definition spec_states_init := tf_spec_states_init tf_synth_ctx.
    Definition spec_action := tf_spec_action tf_synth_ctx.
    Definition spec_action_fin := tf_spec_action_fin tf_synth_ctx.
    Definition spec_action_ops := tf_spec_action_ops tf_synth_ctx.

    Definition all_spec_states := @finite_elements spec_states spec_states_fin.
    Definition all_spec_actions := @finite_elements spec_action spec_action_fin.

    Definition state_index := @finite_index spec_states spec_states_fin.
    Definition action_index := @finite_index spec_action spec_action_fin.

    Instance show_spec_states : Show spec_states := tf_spec_states_names tf_synth_ctx.
    Instance show_spec_action : Show spec_action := tf_spec_action_names tf_synth_ctx.

    (* ====== ====== *)

    Inductive reg_t := 
    | tf_reg (x : spec_states).

    Instance reg_t_finite : FiniteType reg_t.
    Proof.
      econstructor.
      instantiate (1 := fun x => match x with tf_reg y => state_index y end).
      instantiate (1 := map (fun x => tf_reg x) all_spec_states).
      - intros [x]. rewrite nth_error_map. unfold all_spec_states. rewrite (@finite_surjective spec_states spec_states_fin _). ssimpl.
      - rewrite map_map. unfold all_spec_states. 
        assert ((fun x : spec_states => state_index x) = state_index).
        + ssimpl.
        + rewrite H. unfold state_index. exact finite_injective.
    Qed.

    Definition _reg_name (x: spec_states) : string :=
      "tf_st_" ++ show (state_index x).

    Instance reg_names : Show reg_t :=
      { show := fun r => match r with
          | tf_reg x => String.append "reg_" (show x)
          end
      }.

    Definition R (r: reg_t) :=
    match r with
    | tf_reg x => spec_states_t x
    end.

    Definition r (reg: reg_t) : R reg :=
      match reg with
      | tf_reg x => spec_states_init x
      end.

    Inductive ext_fn_t := 
    | ext_in_cmd.

    Definition cmd_reg_size := 32. (* TODO: determine size depending on length of list *)

    Definition Sigma (fn: ext_fn_t) :=
      match fn with
      | ext_in_cmd => {$ bits_t 1 ~> maybe (bits_t cmd_reg_size) $}
      end.

    Definition ext_fn_specs (fn : ext_fn_t) := 
      match fn with
      | ext_in_cmd => {| efr_name := "in_cmd"; 
                        efr_internal := false |}
      end.
    
    Inductive rule_name_t :=
    | rule_cmd (cmd: spec_action)
    .

    Instance rule_names : Show rule_name_t :=
      { show := fun r => match r with
          | rule_cmd cmd => String.append "rule_cmd_" (show cmd)
          end
      }.

    Definition system_schedule_actions : scheduler  :=
      List.fold_right (fun t acc => rule_cmd t |> acc) Done all_spec_actions.

    Definition system_schedule := system_schedule_actions.
    Eval compute in system_schedule.
    
    Definition op_to_uaction (x: spec_states) (op: tf_ops) (code: uaction reg_t ext_fn_t) : uaction reg_t ext_fn_t :=
      match op with
      | spec_nop => code
      end.

    Definition _rule_aux
      (state_op: tf_ops)
      (code: uaction reg_t ext_fn_t)
      : uaction reg_t ext_fn_t :=
        let state_code := List.fold_right (fun x acc => op_to_uaction x state_op acc) code all_spec_states in
        state_code.

    (* Helper function that reads all state registers into variables *)
    (* TODO: a final version should only read the needed variables, to minimize dependencies *)
    Definition _rule_read_state_vars (code: uaction reg_t ext_fn_t) : uaction reg_t ext_fn_t  := 
      List.fold_right (fun x acc => 
        UBind (_reg_name x) {{ read0(tf_reg x) }} acc
      ) code all_spec_states.

    (* Helper function that writes back all state variables *)
    (* TODO: a final version should only write the modified variables, to minimize dependencies *) 
    Definition _rule_write_state_vars (code: uaction reg_t ext_fn_t) : uaction reg_t ext_fn_t  := 
      List.fold_right (fun x acc => 
        USeq {{ write0(tf_reg x, `UVar (_reg_name x)`) }} acc
      ) code all_spec_states.

    Definition _rule_cmd cmd : uaction reg_t ext_fn_t :=
      let state_ops := spec_action_ops cmd in
      _rule_read_state_vars (
        _rule_aux state_ops (
          _rule_write_state_vars {{ pass }})).

    Definition rules :=
        (fun rl =>  match rl with
          | rule_cmd cmd => 
            let cmd_enc := Bits.of_nat cmd_reg_size (action_index cmd) in
            {{
                  let in_cmd := extcall ext_in_cmd(Ob~1) in
                  guard(get(in_cmd, valid) && get(in_cmd, data) == #cmd_enc);
                  `_rule_cmd cmd`
            }}
          end).

End TrustformerSynthesis.


(* This allows us to override the type checking tactic, for more fine grained control *)

Ltac _tc_rules R Sigma uactions :=
  let rule_name_t := _arg_type uactions in
  let res := constr:(fun r: rule_name_t =>
                      ltac:(destruct r eqn:? ;
                            lazymatch goal with
                            | [ H: _ = ?rr |- _ ] =>
                              let ua := constr:(uactions rr) in
                              let ua := (eval hnf in ua) in
                              _tc_action R Sigma (@List.nil (var_t * type)) constr:(unit_t) ua
                            end)) in
  exact res.

Notation tc_rules R Sigma actions :=
  (ltac:(_tc_rules R Sigma actions)) (only parsing).
(* 
Section CompositionalCorrectness.

    (* TODO generalize: each cycle could be a different omega *)
    Context (sigma: ext_fn_t -> val -> val).

    (* Generalize over any input to the synthesis *)
    Context (any_fs_states: Type).
    Context (any_fs_states_fin : FiniteType any_fs_states).
    Context (any_fs_states_names : Show any_fs_states).
    Context (any_fs_states_t : any_fs_states -> type).
    Context (any_fs_states_init : forall x: any_fs_states, any_fs_states_t x).
    Context (any_fs_action : Type).
    Context (any_fs_action_fin : FiniteType any_fs_action).
    Context (any_fs_action_names : Show any_fs_action).
    Context (any_fs_action_ops : any_fs_action -> tf_ops).

    (* We craft the tx_context here as it leads to cleaner proofs than generalizing over it*)
    Definition tf_ctx := {|
      tf_spec_states := any_fs_states;
      tf_spec_states_fin := any_fs_states_fin;
      tf_spec_states_names := any_fs_states_names;
      tf_spec_states_t := any_fs_states_t;
      tf_spec_states_init := any_fs_states_init;
      tf_spec_action := any_fs_action;
      tf_spec_action_fin := any_fs_action_fin;
      tf_spec_action_names := any_fs_action_names;
      tf_spec_action_ops := any_fs_action_ops
    |}.

    (* Obtain the various outputs of the synthesis *)
    Definition any_R := R tf_ctx.
    Definition any_r := r tf_ctx.
    Definition any_rules := rules tf_ctx.
    Definition any_system_schedule := system_schedule tf_ctx.
    Definition any_reg_t := reg_t tf_ctx.
    Instance any_reg_t_finite : FiniteType (any_reg_t) := reg_t_finite tf_ctx.



  (* Prove that op_to_uaction adds accesses like tf_op_step (one operation matches) *)

    (* Define what functional specification we compare against *)
    Definition any_fs_op_step :=  tf_op_step any_fs_states _ any_fs_states_t.

  (* Prove _rule_aux adds accesses like functional spec (one action matches)*)

  (* Prove _rule_cmd adds accesses like functional spec (all actions match) *)

    Definition _fs_cmd_encoding (a: any_fs_action) :=
      Bits.of_nat cmd_reg_size (@finite_index any_fs_action _ a).
    Definition _encoded_cmd (a: any_fs_action) : type_denote (maybe (bits_t cmd_reg_size)) :=
        (Ob~1, (_fs_cmd_encoding a, tt)).
    Definition encoded_cmd (a: any_fs_action) := val_of_value (_encoded_cmd a).

    Definition val_true := Bits ( [true] ).
    Eval compute in val_true.

  (* Prove next HW cycle = next Spec cycle *)
    Definition _ur (x: any_reg_t) := val_of_value (any_r x).
    Definition initial_hw_state := 
        ContextEnv.(create) _ur.
    Check initial_hw_state.

    Definition next_hw_cycle (hw_reg_state: env_t ContextEnv (fun _ : any_reg_t => val)) := 
    UntypedSemantics.interp_cycle any_rules hw_reg_state sigma any_system_schedule.

    (* TODO: Update once we have operation lists as input *)
    Definition any_fs_step :=  tf_op_step any_fs_states _ any_fs_states_t.

    Definition StateR (hw_reg_state: env_t ContextEnv (fun _ : any_reg_t => val)) (fs_state: ContextEnv.(env_t) any_fs_states_t) :=
        forall x, hw_reg_state.[tf_reg tf_ctx x] = val_of_value (fs_state.[x]).
    
    Theorem InitState_correct :
        StateR initial_hw_state (ContextEnv.(create) any_fs_states_init).
    Proof.
        unfold initial_hw_state. intros x.
        rewrite getenv_create. rewrite getenv_create. (* hammer. *)  hauto lq: on.
    Qed.

    Theorem NextState_correct:
        forall cmd fs_state hw_reg_state, 
        (  sigma ext_in_cmd val_true = encoded_cmd cmd
        /\ StateR hw_reg_state fs_state
        ) ->
        StateR (next_hw_cycle hw_reg_state) (any_fs_step fs_state (any_fs_action_ops cmd)).
    Proof.
        intros cmd fs_state hw_reg_state H.
        destruct H as [H_sigma_eq_cmd H_state].

        (* We consider each state var individually *)
        intros state_var.
        (* Create next state definitions & specialize state equivalence to the vars we consider *)
        set (any_fs_step fs_state (any_fs_action_ops cmd)) as fs_state'.
        unfold next_hw_cycle, StateR in *.
        specialize (H_state state_var). (* Use pose if we need H_state for state!=state_var *)
        unfold any_reg_t in *.

        (* Compute what the next functional state will be, then use the hypothesis to relate it to the previous hardware state *)
        unfold any_fs_step, tf_op_step in fs_state'.
        destruct any_fs_action_ops eqn:H_ops.
        subst fs_state'. rewrite <- H_state. clear H_state. clear H_ops.

        (* Make rules clearly readable *)
        set (all_rules := any_rules) in *.
        unfold any_rules, rules in all_rules.

        (* Make schedule clearly readable *)
        set (all_schedules := any_system_schedule) in *.
        unfold any_system_schedule, system_schedule_actions, system_schedule, system_schedule_actions in all_schedules.

        (* Compute the next hw state *)

        unfold UntypedSemantics.interp_cycle, UntypedLogs.commit_update.
        rewrite getenv_create.

        destruct (UntypedLogs.latest_write _ _) eqn:H_last_write.
        (* We had a write to this state register since the last cycle *)
        + (* We know this should lead to a contradiction *)
          unfold UntypedLogs.latest_write in H_last_write.

          unfold UntypedSemantics.interp_scheduler, UntypedSemantics.interp_scheduler' in H_last_write.                  

          induction all_schedules.
          
          * (* The schedule is empty, so there cannot have been any writes *)
            rewrite CommonProperties.log_find_empty in H_last_write.
            discriminate H_last_write.
          
          * (* The schedule is non-empty, so we can analyze the first rule *)
            apply IHall_schedules. clear IHall_schedules. destruct UntypedSemantics.interp_rule eqn:H_rule.
            - admit.

            - timeout 10 sauto. 
            (* Set Printing All. Show. *)
            (* assert (
              (@UntypedLogs.log_app val (reg_t tf_ctx) (@ContextEnv (reg_t tf_ctx) any_reg_t_finite) l
              (@UntypedLogs.log_empty val (reg_t tf_ctx) (@ContextEnv (reg_t tf_ctx) any_reg_t_finite))) 
              = (@UntypedLogs.log_empty val (reg_t tf_ctx) (@ContextEnv (reg_t tf_ctx) any_reg_t_finite))).
            {  
              clear H_last_write. timeout 10 simpl.
              apply ccreate_funext. 
              intros k H_member.
              
              timeout 10 simpl in H_rule. unfold UntypedSemantics.interp_rule, UntypedSemantics.interp_action in H_rule.
              subst all_rules. timeout 10 simpl in H_rule.
              destruct r0. timeout 10 simpl in H_rule.

              set (sigma_val := sigma ext_in_cmd (Bits (vect_to_list Ob~1))) in H_rule.
              assert (HSigmaValCmd: sigma_val = encoded_cmd cmd).
              { unfold sigma_val. exact H_sigma_eq_cmd. }
              rewrite HSigmaValCmd in *. clear sigma_val HSigmaValCmd. clear H_sigma_eq_cmd.
              unfold encoded_cmd, _encoded_cmd, _fs_cmd_encoding in H_rule. 
              
              timeout 10 simpl in H_rule.
            } *)
            assert (l = (@UntypedLogs.log_empty val (reg_t tf_ctx) (@ContextEnv (reg_t tf_ctx) any_reg_t_finite))).
            {
              clear H_last_write.

              timeout 10 simpl in H_rule. unfold UntypedSemantics.interp_rule in H_rule. unfold UntypedSemantics.interp_action in H_rule.
              subst all_rules. timeout 10 simpl in H_rule.
              (* Lets go over the possible rule types, here it could only be a rule_cmd *)
              destruct r0. timeout 10 simpl in H_rule.

              (* Lets resolve what the command input value is *)
              set (sigma_val := sigma ext_in_cmd (Bits (vect_to_list Ob~1))) in H_rule.
              assert (HSigmaValCmd: sigma_val = encoded_cmd cmd).
              { unfold sigma_val. exact H_sigma_eq_cmd. }
              rewrite HSigmaValCmd in *. clear sigma_val HSigmaValCmd. clear H_sigma_eq_cmd.
              unfold encoded_cmd, _encoded_cmd, _fs_cmd_encoding in H_rule.

              (* the command for the rule we look at (cmd0) is either mapped to the same index or not as what we got as input (cmd)*)
              destruct (Nat.eq_dec (finite_index cmd0) (finite_index cmd)).
              - rewrite <- e in *. clear e.
                (* The command matches, so the guard should pass and we should interpret the rule body *)
                unfold val_of_value in H_rule.
                remember (BitsToLists.get_field _ _ ) as get_valid eqn:H_get_valid.
                timeout 10 simpl in H_get_valid. rewrite H_get_valid in H_rule. clear H_get_valid. clear get_valid.
                unfold action_index in H_rule.

                destruct (let/opt3 action_log, v, Gamma := _ in _) as [res|] eqn:Heq.
                + admit.
                + discriminate H_rule.


                
                
              - (* The command does not match, so the guard should fail and we should get None *)
                admit.


              
            } rewrite H in *. clear H.
            rewrite CommonProperties.log_app_empty_l in H_last_write.
            timeout 10 sauto.
          * destruct UntypedSemantics.interp_rule eqn:H_rule.
            - apply IHall_schedules1. clear IHall_schedules2. clear IHall_schedules1.
              assert (l = (@UntypedLogs.log_empty val (reg_t tf_ctx) (@ContextEnv (reg_t tf_ctx) any_reg_t_finite))).
              { admit. } rewrite H in H_last_write. clear H. 
              rewrite CommonProperties.log_app_empty_l in H_last_write. timeout 10 sauto. 
            - apply IHall_schedules2. clear IHall_schedules2. clear IHall_schedules1.
              timeout 10 sauto.
          * apply IHall_schedules. clear IHall_schedules. timeout 10 sauto.
        + timeout 10 sauto.
    Admitted.

End CompositionalCorrectness.

Section UntypedCorrectness.

    (* ================================================================================== *)
    (* ================================================================================== *)
    (* =================================   READ ME      ================================= *)
    (* ================================================================================== *)
    (* ================================================================================== *)

    (*
        The likely thing to do is, proving that _rule_cmd cmd adds the accesses to the log
        that match the tf_op_step for the corresponding command.

        Then, we can work on the proof below.

        We might need to go even simpler and show that interp_action for _rule_aux adds the
        accesses to the log that match tf_op_step for a single tf_op.
    *)

    (* ================================================================================== *)
    (* ================================================================================== *)
    (* ================================================================================== *)



    (* TODO generalize: each cycle could be a different omega *)
    Context (sigma: ext_fn_t -> val -> val).

    Context (any_fs_states: Type).
    Context (any_fs_states_fin : FiniteType any_fs_states).
    Context (any_fs_states_names : Show any_fs_states).
    Context (any_fs_states_t : any_fs_states -> type).
    Context (any_fs_states_init : forall x: any_fs_states, any_fs_states_t x).
    Context (any_fs_action : Type).
    Context (any_fs_action_fin : FiniteType any_fs_action).
    Context (any_fs_action_names : Show any_fs_action).
    Context (any_fs_action_ops : any_fs_action -> tf_ops).

    Definition tf_ctx := {|
      tf_spec_states := any_fs_states;
      tf_spec_states_fin := any_fs_states_fin;
      tf_spec_states_names := any_fs_states_names;
      tf_spec_states_t := any_fs_states_t;
      tf_spec_states_init := any_fs_states_init;
      tf_spec_action := any_fs_action;
      tf_spec_action_fin := any_fs_action_fin;
      tf_spec_action_names := any_fs_action_names;
      tf_spec_action_ops := any_fs_action_ops
    |}.

    Definition any_R := R tf_ctx.
    Definition any_r := r tf_ctx.
    Definition any_rules := rules tf_ctx.
    Definition any_system_schedule := system_schedule tf_ctx.
    Definition any_reg_t := reg_t tf_ctx.
    Instance any_reg_t_finite : FiniteType (any_reg_t) := reg_t_finite tf_ctx.

    Definition any_fs_step :=  tf_op_step any_fs_states _ any_fs_states_t.

    Definition _ur (x: any_reg_t) := val_of_value (any_r x).
    Definition initial_hw_state := 
        ContextEnv.(create) _ur.
    Check initial_hw_state.

    Definition next_hw_cycle (hw_reg_state: env_t ContextEnv (fun _ : any_reg_t => val)) := 
        UntypedSemantics.interp_cycle any_rules hw_reg_state sigma any_system_schedule.
    
    Definition _fs_cmd_encoding (a: any_fs_action) :=
      Bits.of_nat cmd_reg_size (@finite_index any_fs_action _ a).
    Definition _encoded_cmd (a: any_fs_action) : type_denote (maybe (bits_t cmd_reg_size)) :=
        (Ob~1, (_fs_cmd_encoding a, tt)).
    Definition encoded_cmd (a: any_fs_action) := val_of_value (_encoded_cmd a).

    Definition StateR (hw_reg_state: env_t ContextEnv (fun _ : any_reg_t => val)) (fs_state: ContextEnv.(env_t) any_fs_states_t) :=
        forall x, hw_reg_state.[tf_reg tf_ctx x] = val_of_value (fs_state.[x]).
    
    Theorem InitState_correct :
        StateR initial_hw_state (ContextEnv.(create) any_fs_states_init).
    Proof.
        unfold initial_hw_state. intros x.
        rewrite getenv_create. rewrite getenv_create. (* hammer. *)  hauto lq: on.
    Qed.

    Definition val_true := Bits ( [true] ).
    Eval compute in val_true.

    Theorem NextState_correct:
        forall cmd fs_state hw_reg_state, 
        (  sigma ext_in_cmd val_true = encoded_cmd cmd
        /\ StateR hw_reg_state fs_state
        ) ->
        StateR (next_hw_cycle hw_reg_state) (any_fs_step fs_state (any_fs_action_ops cmd)).
    Proof.
        intros cmd fs_state hw_reg_state H.
        destruct H as [H_sigma_eq_cmd H_state].

        (* We consider each state var individually *)
        intros state_var.
        (* Create next state definitions & specialize state equivalence to the vars we consider *)
        set (any_fs_step fs_state (any_fs_action_ops cmd)) as fs_state'.
        unfold next_hw_cycle, StateR in *.
        specialize (H_state state_var). (* Use pose if we need H_state for state!=state_var *)
        unfold any_reg_t in *.

        (* Compute what the next functional state will be, then use the hypothesis to relate it to the previous hardware state *)
        unfold any_fs_step, tf_op_step in fs_state'.
        destruct any_fs_action_ops eqn:H_ops.
        subst fs_state'. rewrite <- H_state. clear H_state. clear H_ops.

        (* Make rules clearly readable *)
        set (all_rules := any_rules) in *.
        unfold any_rules, rules in all_rules.

        (* Make schedule clearly readable *)
        set (all_schedules := any_system_schedule) in *.
        unfold any_system_schedule, system_schedule_actions, system_schedule, system_schedule_actions in all_schedules.

        (* Compute the next hw state *)

        unfold UntypedSemantics.interp_cycle, UntypedLogs.commit_update.
        rewrite getenv_create.

        destruct (UntypedLogs.latest_write _ _) eqn:H_last_write.
        (* We had a write to this state register since the last cycle *)
        + (* We know this should lead to a contradiction *)
          unfold UntypedLogs.latest_write in H_last_write.

          unfold UntypedSemantics.interp_scheduler, UntypedSemantics.interp_scheduler' in H_last_write.
                  

          induction all_schedules.
          
          * (* The schedule is empty, so there cannot have been any writes *)
            rewrite CommonProperties.log_find_empty in H_last_write.
            discriminate H_last_write.
          
          * (* The schedule is non-empty, so we can analyze the first rule *)
            apply IHall_schedules. clear IHall_schedules. destruct UntypedSemantics.interp_rule eqn:H_rule.
            (* Set Printing All. Show. *)
            (* assert (
              (@UntypedLogs.log_app val (reg_t tf_ctx) (@ContextEnv (reg_t tf_ctx) any_reg_t_finite) l
              (@UntypedLogs.log_empty val (reg_t tf_ctx) (@ContextEnv (reg_t tf_ctx) any_reg_t_finite))) 
              = (@UntypedLogs.log_empty val (reg_t tf_ctx) (@ContextEnv (reg_t tf_ctx) any_reg_t_finite))).
            {  
              clear H_last_write. timeout 10 simpl.
              apply ccreate_funext. 
              intros k H_member.
              
              timeout 10 simpl in H_rule. unfold UntypedSemantics.interp_rule, UntypedSemantics.interp_action in H_rule.
              subst all_rules. timeout 10 simpl in H_rule.
              destruct r0. timeout 10 simpl in H_rule.

              set (sigma_val := sigma ext_in_cmd (Bits (vect_to_list Ob~1))) in H_rule.
              assert (HSigmaValCmd: sigma_val = encoded_cmd cmd).
              { unfold sigma_val. exact H_sigma_eq_cmd. }
              rewrite HSigmaValCmd in *. clear sigma_val HSigmaValCmd. clear H_sigma_eq_cmd.
              unfold encoded_cmd, _encoded_cmd, _fs_cmd_encoding in H_rule. 
              
              timeout 10 simpl in H_rule.
            } *)
            assert (l = (@UntypedLogs.log_empty val (reg_t tf_ctx) (@ContextEnv (reg_t tf_ctx) any_reg_t_finite))).
            {
              clear H_last_write.

              timeout 10 simpl in H_rule. unfold UntypedSemantics.interp_rule, UntypedSemantics.interp_action in H_rule.
              subst all_rules. timeout 10 simpl in H_rule.
              (* Lets go over the possible rule types, here it could only be a rule_cmd *)
              destruct r0. timeout 10 simpl in H_rule.

              (* Lets resolve what the command input value is *)
              set (sigma_val := sigma ext_in_cmd (Bits (vect_to_list Ob~1))) in H_rule.
              assert (HSigmaValCmd: sigma_val = encoded_cmd cmd).
              { unfold sigma_val. exact H_sigma_eq_cmd. }
              rewrite HSigmaValCmd in *. clear sigma_val HSigmaValCmd. clear H_sigma_eq_cmd.
              unfold encoded_cmd, _encoded_cmd, _fs_cmd_encoding in H_rule.

              (* the command for the rule we look at (cmd0) is either mapped to the same index or not as what we got as input (cmd)*)
              destruct (Nat.eq_dec (finite_index cmd0) (finite_index cmd)).
              - rewrite <- e in *. clear e.
                (* The command matches, so the guard should pass and we should interpret the rule body *)
                unfold val_of_value in H_rule.
                remember (BitsToLists.get_field _ _ ) as get_valid eqn:H_get_valid.
                timeout 10 simpl in H_get_valid. rewrite H_get_valid in H_rule. clear H_get_valid. clear get_valid.
                unfold action_index in H_rule.

                destruct (let/opt3 action_log, v, Gamma := _ in _) as [res|] eqn:Heq.
                + admit.
                + discriminate H_rule.


                
                
              - (* The command does not match, so the guard should fail and we should get None *)
                admit.


              
            } rewrite H in *. clear H.
            rewrite CommonProperties.log_app_empty_l in H_last_write.
            timeout 10 sauto. timeout 10 sauto.
          * destruct UntypedSemantics.interp_rule eqn:H_rule.
            - apply IHall_schedules1. clear IHall_schedules2. clear IHall_schedules1.
              assert (l = (@UntypedLogs.log_empty val (reg_t tf_ctx) (@ContextEnv (reg_t tf_ctx) any_reg_t_finite))).
              { admit. } rewrite H in H_last_write. clear H. 
              rewrite CommonProperties.log_app_empty_l in H_last_write. timeout 10 sauto. 
            - apply IHall_schedules2. clear IHall_schedules2. clear IHall_schedules1.
              timeout 10 sauto.
          * apply IHall_schedules. clear IHall_schedules. timeout 10 sauto.
        + timeout 10 sauto.
    Admitted.
End UntypedCorrectness. *)

(* 
Section UntypedCorrectness.

    (* TODO generalize: each cycle could be a different omega *)
    Context (sigma: ext_fn_t -> val -> val).
    Context (tf_ctx: TFSynthContext).

    Definition any_R := R tf_ctx.
    Definition any_r := r tf_ctx.
    Definition any_rules := rules tf_ctx.
    Definition any_system_schedule := system_schedule tf_ctx.
    Definition any_reg_t := reg_t tf_ctx.
    Instance any_reg_t_finite : FiniteType (any_reg_t) := reg_t_finite tf_ctx.

    Definition any_fs_states := tf_spec_states tf_ctx.
    Instance any_fs_states_fin : FiniteType (any_fs_states) := tf_spec_states_fin tf_ctx.
    Definition any_fs_states_t := tf_spec_states_t tf_ctx.
    Definition any_fs_states_init := tf_spec_states_init tf_ctx.
    Definition any_fs_action := tf_spec_action tf_ctx.
    Instance any_fs_action_fin : FiniteType (any_fs_action) := tf_spec_action_fin tf_ctx.
    Definition any_fs_action_ops := tf_spec_action_ops tf_ctx.

    Definition any_fs_step :=  tf_op_step any_fs_states _ any_fs_states_t.

    Definition _ur (x: any_reg_t) := val_of_value (any_r x).
    Definition initial_hw_state := 
        ContextEnv.(create) _ur.
    Check initial_hw_state.

    Definition next_hw_cycle (hw_reg_state: env_t ContextEnv (fun _ : any_reg_t => val)) := 
        UntypedSemantics.interp_cycle any_rules hw_reg_state sigma any_system_schedule.
    
    Definition _fs_cmd_encoding (a: any_fs_action) :=
      Bits.of_nat cmd_reg_size (@finite_index any_fs_action _ a).
    Definition _encoded_cmd (a: any_fs_action) : type_denote (maybe (bits_t cmd_reg_size)) :=
        (Ob~1, (_fs_cmd_encoding a, tt)).
    Definition encoded_cmd (a: any_fs_action) := val_of_value (_encoded_cmd a).

    Definition StateR (hw_reg_state: env_t ContextEnv (fun _ : any_reg_t => val)) (fs_state: ContextEnv.(env_t) any_fs_states_t) :=
        forall x, hw_reg_state.[tf_reg tf_ctx x] = val_of_value (fs_state.[x]).
    
    Theorem InitState_correct :
        StateR initial_hw_state (ContextEnv.(create) any_fs_states_init).
    Proof.
        unfold initial_hw_state, any_fs_states_init. intros x.
        rewrite getenv_create. rewrite getenv_create. (* hammer. *)  hauto lq: on.
    Qed.

    Definition val_true := Bits ( [ true ] ).

    Theorem NextState_correct:
        forall cmd fs_state hw_reg_state, 
        (  sigma ext_in_cmd val_true = encoded_cmd cmd
        /\ StateR hw_reg_state fs_state
        ) ->
        StateR (next_hw_cycle hw_reg_state) (any_fs_step fs_state (any_fs_action_ops cmd)).
    Proof.
        (* intros cmd fs_state hw_reg_state H.
        destruct H as [H_cmd H_state].
        intros state_var.
        unfold next_hw_cycle, StateR in *.

        unfold UntypedSemantics.interp_cycle.
        unfold UntypedLogs.commit_update.
        rewrite getenv_create.
        
        destruct (UntypedLogs.latest_write _ _) eqn:H_latest.
        - destruct any_system_schedule eqn:H_sched.
          + unfold UntypedLogs.latest_write, UntypedSemantics.interp_scheduler, UntypedSemantics.interp_scheduler' in H_latest.
            rewrite UntypedProperties.log_find_empty in H_latest.
            discriminate H_latest.
          + set (Log := (UntypedSemantics.interp_scheduler any_rules hw_reg_state sigma (r0 |> s))) in *. *)
        intros cmd fs_state hw_reg_state H.
        destruct H as [H_sigma_eq_cmd H_state].
        intros state_var.

        set (any_fs_step fs_state (any_fs_action_ops cmd)) as fs_state'.
        unfold next_hw_cycle, StateR in *.
        specialize (H_state state_var). (* Use pose if we need H_state for state!=state_var *)

        set (UntypedSemantics.interp_cycle any_rules hw_reg_state sigma any_system_schedule) as hw_reg_state'.

        unfold any_fs_step, tf_op_step in fs_state'.
        destruct any_fs_action_ops eqn:H_ops.
        subst fs_state'. rewrite <- H_state. clear H_state.

        set (all_rules := any_rules) in *.
        unfold any_rules, rules in all_rules.

        (* ------- *)

        unfold UntypedSemantics.interp_cycle.
        unfold UntypedLogs.commit_update.
        rewrite getenv_create.
        
        destruct (UntypedLogs.latest_write _ _) eqn:H_latest.
        - destruct any_system_schedule eqn:H_sched.
          + unfold UntypedLogs.latest_write, UntypedSemantics.interp_scheduler, UntypedSemantics.interp_scheduler' in H_latest.
            rewrite UntypedProperties.log_find_empty in H_latest.
            discriminate H_latest.
          + set (Log := (UntypedSemantics.interp_scheduler any_rules hw_reg_state sigma (r0 |> s))) in *.

    Qed.
End UntypedCorrectness. *)

            

