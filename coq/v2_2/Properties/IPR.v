Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.
Require Koika.Properties.SemanticProperties.
Require Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.

Require Import Trustformer.v2_2.Syntax.
Require Import Trustformer.v2_2.Semantics.
Require Import Trustformer.v2_2.Synthesis.
Require Import Trustformer.v2_2.Utils.
Require Trustformer.v2_2.Properties.Common.
From Koika.Utils Require Import Tactics.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Streams.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Init.Tactics.

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.


Ltac unfold_tfctx := repeat (
  unfold tf_spec_states in * || unfold tf_spec_states_fin in * || unfold tf_spec_states_names in * || unfold tf_spec_states_size in * 
  || unfold tf_spec_states_init in * 
  
  || unfold tf_spec_inputs in * || unfold tf_spec_inputs_fin in * || unfold tf_spec_inputs_names in * || unfold tf_spec_inputs_size in * 
  
  || unfold tf_spec_outputs in * || unfold tf_spec_outputs_fin in * || unfold tf_spec_outputs_names in * || unfold tf_spec_outputs_size in * 
  
  || unfold tf_spec_action in * || unfold tf_spec_action_fin in * || unfold tf_spec_action_names in * 
  
  || unfold tf_spec_action_ops in *).

Ltac unfold_specs := repeat (
  unfold spec_states in * || unfold spec_states_fin in * || unfold spec_states_size in * || unfold spec_states_t in *
    || unfold spec_states_init in * || unfold spec_all_states in * || unfold spec_state_index in * || unfold spec_state_num in * 
    
    || unfold spec_inputs in * || unfold spec_inputs_fin in * || unfold spec_inputs_size in * || unfold spec_inputs_t in * 
    || unfold spec_all_inputs in * || unfold spec_input_index in * || unfold spec_input_num in * 
    
    || unfold spec_outputs in * || unfold spec_outputs_fin in * || unfold spec_outputs_size in * || unfold spec_outputs_t in * 
    || unfold spec_all_outputs in * || unfold spec_output_index in * || unfold spec_output_num in * 
    
    || unfold spec_action in * || unfold spec_action_fin in * || unfold spec_all_actions in * || unfold spec_action_index in * 
    || unfold spec_action_num in * 
    
    || unfold spec_action_ops in *).

Ltac unfold_specs_tfctx := unfold_specs ; unfold_tfctx.

Section CompositionalCorrectness.

  (* Opaque finite_elements. *)
  Arguments finite_elements : simpl never.

  (* Generalize over any input to the synthesis *)
  Context (some_fs_states: Type).
  Context (some_fs_states_fin : FiniteType some_fs_states).
  Context (some_fs_states_names : Show some_fs_states).
  Context (some_fs_states_size : some_fs_states -> nat).
  Context (some_fs_states_init : forall x: some_fs_states, tf_states_type some_fs_states some_fs_states_size x).

  Context (some_fs_inputs : Type).
  Context (some_fs_inputs_fin : FiniteType some_fs_inputs).
  Context (some_fs_inputs_names : Show some_fs_inputs).
  Context (some_fs_inputs_size : some_fs_inputs -> nat).

  Context (some_fs_outputs : Type).
  Context (some_fs_outputs_fin : FiniteType some_fs_outputs).
  Context (some_fs_outputs_names : Show some_fs_outputs).
  Context (some_fs_outputs_size : some_fs_outputs -> nat).

  Context (some_fs_action : Type).
  Context (some_fs_action_fin : FiniteType some_fs_action).
  Context (some_fs_action_names : Show some_fs_action).
  Context (some_fs_action_ops : some_fs_action -> tf_ops some_fs_states some_fs_inputs some_fs_outputs).

  (* We craft the tx_context here as it leads to cleaner proofs than generalizing over it*)
  Definition tf_ctx := {|
    tf_spec_states := some_fs_states;
    tf_spec_states_fin := some_fs_states_fin;
    tf_spec_states_names := some_fs_states_names;
    tf_spec_states_size := some_fs_states_size;
    tf_spec_states_init := some_fs_states_init;

    tf_spec_inputs := some_fs_inputs;
    tf_spec_inputs_fin := some_fs_inputs_fin;
    tf_spec_inputs_names := some_fs_inputs_names;
    tf_spec_inputs_size := some_fs_inputs_size;

    tf_spec_outputs := some_fs_outputs;
    tf_spec_outputs_fin := some_fs_outputs_fin;
    tf_spec_outputs_names := some_fs_outputs_names;
    tf_spec_outputs_size := some_fs_outputs_size;

    tf_spec_action := some_fs_action;
    tf_spec_action_fin := some_fs_action_fin;
    tf_spec_action_names := some_fs_action_names;
    tf_spec_action_ops := some_fs_action_ops
  |}.
  Definition some_fs_states_t := tf_states_type some_fs_states some_fs_states_size.

  Context (sigma: (ext_fn_t tf_ctx) -> val -> val).
  Context (sigma_valid: 
    forall f x, 
    exists (f_t : retSig (Sigma tf_ctx f)),
    sigma f x = val_of_value f_t
  ).

  (* Obtain the various outputs of the synthesis *)
  Definition some_R := R tf_ctx.
  Definition some_r := r tf_ctx.
  Definition some_rules := rules tf_ctx.
  Definition some_system_schedule := system_schedule tf_ctx.
  Definition some_reg_t := reg_t tf_ctx.
  Definition some_cmd_reg_size := cmd_reg_size tf_ctx.

  Instance some_reg_t_finite : FiniteType (some_reg_t) := _reg_t_finite tf_ctx.
  Definition some_reg_t_elements := @finite_elements some_reg_t some_reg_t_finite.
  Definition some_fs_state_elements := @finite_elements some_fs_states some_fs_states_fin.
  Definition some_fs_output_elements := @finite_elements some_fs_outputs some_fs_outputs_fin.


  (* Encoding of commands as bitvectors *)
  Definition _fs_cmd_encoding (a: some_fs_action) :=
    Bits.of_nat some_cmd_reg_size (@finite_index some_fs_action _ a).
  Definition _encoded_cmd (a: some_fs_action) : type_denote (maybe (bits_t some_cmd_reg_size)) :=
      (Ob~1, (_fs_cmd_encoding a, tt)).
  Definition encoded_cmd (a: some_fs_action) := val_of_value (_encoded_cmd a).

  Definition val_true := Bits ( [true] ).

  Ltac unfold_some_specs := 
    repeat (unfold some_fs_states_t in * || unfold some_R in * || unfold some_r in * || unfold some_rules in * || unfold some_system_schedule in * 
    || unfold some_reg_t in * || unfold some_cmd_reg_size in * || unfold some_reg_t_elements in * || unfold some_fs_state_elements in * || unfold some_fs_output_elements in * 
    (* || unfold encoded_cmd in * || unfold _encoded_cmd in * || unfold _fs_cmd_encoding in *  *)
    ).

  Ltac unfold_all := unfold_some_specs ; unfold_specs_tfctx.

  Ltac clean := 
    (* the list of all regs is verbose this should clean it up a bit *)
      try match goal with
      | [ all_regs := _ |- _ ] => subst all_regs
      | _ => idtac
      end;
      try set (all_regs := (map _ _ ++ map _ _  ++ map _ _)) in *;
      try match goal with
      | [ all_regs := _ |- _ ] => try (assert (all_regs = @finite_elements some_reg_t some_reg_t_finite) as _aux_H_all_regs by reflexivity; rewrite _aux_H_all_regs in *; clear _aux_H_all_regs; clear all_regs)
      | _ => idtac
      end
      .

  Ltac unfold_clean := unfold_all ; clean.
      
  Ltac squash := unfold_all ; timeout 10 cbn -[vect_to_list UntypedLogs.log_existsb UntypedLogs.log_empty _reg_name _out_name] 
                 ; repeat f_equal.
  Ltac squash2 := unfold_all ; timeout 10 cbn -[vect_to_list UntypedLogs.log_existsb UntypedLogs.log_empty _reg_name _out_name] ; clean.

  (* Ltac squash_log := repeat (unfold getenv || rewrite !cassoc_ccreate || rewrite app_nil_l || rewrite app_nil_r). *)

  (* Properties about the encoding of commands *)
  Section Encoding.

    Lemma encoded_cmd_inj :
      forall (a1 a2 : some_fs_action),
      encoded_cmd a1 = encoded_cmd a2 -> a1 = a2.
    Proof.
      intros a1 a2 H_eq.
      unfold encoded_cmd, _encoded_cmd in H_eq.
      unfold _fs_cmd_encoding in H_eq.
      timeout 10 simpl in H_eq.
      apply f_equal with (f:=ubits_of_value) in H_eq.
      timeout 10 cbn -[vect_to_list] in H_eq.
      apply app_inj_tail in H_eq.
      destruct H_eq as [H_bits_eq H_ob_eq]. clear H_ob_eq.
      apply vect_to_list_inj in H_bits_eq.
      apply f_equal with (f:=Bits.to_nat) in H_bits_eq.
      rewrite Bits.to_nat_of_nat in H_bits_eq.
      rewrite Bits.to_nat_of_nat in H_bits_eq.
      - apply finite_index_injective. exact H_bits_eq.
      - rewrite pow2_correct. unfold some_cmd_reg_size, cmd_reg_size. apply Common.finite_bits_needed_correct.
      - rewrite pow2_correct. unfold some_cmd_reg_size, cmd_reg_size. apply Common.finite_bits_needed_correct.
    Qed.

    Lemma encoded_cmd_inj' :
      forall (a1 a2 : some_fs_action),
      a1 <> a2 -> encoded_cmd a1 <> encoded_cmd a2.
    Proof.
      intros a1 a2 H_neq. intros H_eq.
      apply encoded_cmd_inj in H_eq.
      contradiction.
    Qed.    

    Lemma sigma_ext_in_cmd_is_struct :
      forall (cmd : some_fs_action) vars,
      exists valid' cmd_encoding,
      sigma (ext_in_cmd tf_ctx) vars = Struct (Maybe (bits_t some_cmd_reg_size)) [Bits [valid']; Bits cmd_encoding].
    Proof.
      intros.
      specialize (sigma_valid (ext_in_cmd tf_ctx) vars).
      unfold retSig, Sigma, val_of_value, some_cmd_reg_size in *.
      destruct sigma_valid as [f_t Heq].
      destruct f_t as [b v_and_unit].
      destruct v_and_unit as [v H_unit].
      rewrite Heq. eexists _,_.
      simpl. reflexivity.
    Qed.   

    Lemma cmd_rule_eq_dec_equal:
      forall (cmd1 cmd2: some_fs_action),
        (rule_cmd tf_ctx cmd1) = (rule_cmd tf_ctx cmd2) <-> cmd1 = cmd2.
    Proof.
        intros. split.
        - intros H_eq. inversion H_eq. reflexivity.
        - intros H_eq. rewrite H_eq. reflexivity.
    Qed.

    Lemma reg_name_inj :
      forall r1 r2,
        (_reg_name tf_ctx r1) = (_reg_name tf_ctx r2) -> r1 = r2.
    Proof.
      intros. unfold _reg_name in H.
      timeout 10 simpl in H. unfold spec_state_index in H.
      injection H. intros.
      apply finite_index_injective.
      apply string_id_of_nat_inj in H0.
      timeout 10 sauto.
    Qed.

  End Encoding. 

  (* Other helpful definitions *)
  Definition hw_env_t := env_t ContextEnv (fun _ : some_reg_t => val).

  (* Sometimes coq can not figure out some of the types for ULog, these should work  *)
  Definition ULog_V := val.
  Definition ULog_reg_t := reg_t tf_ctx.
  Definition ULog_Renv := (@ContextEnv some_reg_t some_reg_t_finite).

  Definition ULog_ULog := (@UntypedLogs._ULog ULog_V ULog_reg_t ULog_Renv).

  Section ActionInterpretation.

    Definition Gamma_after_act_read_state_vars (hw_reg_state: hw_env_t) (Gamma: list (string * val)) sched_log action_log state_list :=
      let state_values := List.map (fun s =>
        let v := match UntypedLogs.latest_write0 (REnv:=ULog_Renv) (UntypedLogs.log_app action_log sched_log) (tf_reg tf_ctx s) with
                | Some v => v
                | None => hw_reg_state.[(tf_reg tf_ctx s)]
                end
        in (_reg_name tf_ctx s, v)
      ) (List.rev state_list) in
      state_values ++ Gamma.
    
    Definition log_after_act_read_state_vars (hw_reg_state: hw_env_t) (sched_log: ULog_ULog) action_log state_list :=
      List.fold_left (fun (acc_log: UntypedLogs._ULog) s =>
        UntypedLogs.log_cons (REnv:=ULog_Renv) (tf_reg tf_ctx s) (UntypedLogs.LE Logs.LogRead P1 (Bits [])) acc_log
      ) state_list action_log.

    Lemma interp_act_read_state_vars {REnv : Env some_reg_t} : 
      forall (hw_reg_state: hw_env_t) (Gamma: list (string * val)) sched_log action_log code state_list,

      (* Precondition: Ensure all reads performed by the wrapper will succeed. *)
      (forall (reg: some_reg_t), UntypedLogs.log_existsb sched_log reg UntypedLogs.is_write1 = false) ->

      (* ---------------- *)

      UntypedSemantics.interp_action hw_reg_state sigma Gamma sched_log action_log (_rule_read_state_vars_rec tf_ctx state_list code) =
      
      (* 1. Pre-calculate the values of all state registers that would be read. *)
      let newGamma := Gamma_after_act_read_state_vars hw_reg_state Gamma sched_log action_log state_list in

      (* 2. Pre-calculate the log entries that would be generated by these reads. *)
      let read_logs := log_after_act_read_state_vars hw_reg_state sched_log action_log state_list in

      (* 3. The result is equivalent to interpreting [code] with the pre-calculated
            context and log, then packaging the result. The final Gamma is unchanged
            because UBind cleans up after itself. *)
      match UntypedSemantics.interp_action hw_reg_state sigma newGamma sched_log read_logs code with
      | Some (final_log, v, Gamma') => Some (final_log, v, skipn (List.length state_list) Gamma')
      | None => None
      end.
    Proof.
      intros. unfold Gamma_after_act_read_state_vars, log_after_act_read_state_vars in *.
      unfold ULog_ULog, ULog_Renv, ULog_reg_t, ULog_V in *.

      generalize dependent Gamma.
      generalize dependent action_log.
      induction state_list.
      {
        intros. timeout 10 simpl.
        case_eq (UntypedSemantics.interp_action hw_reg_state sigma Gamma sched_log action_log code).
        - intros. destruct p as [ [final_log v] Gamma']. reflexivity.
        - intros. reflexivity.
      }
      {
        intros. timeout 10 simpl. unfold opt_bind.
        rewrite H. timeout 10 simpl.

        rewrite IHstate_list. clear IHstate_list.
        timeout 10 simpl.

        match goal with
        | [ |- match ?E with _ => _ end = _ ] =>
          remember E as LM
        end.
        match goal with
        | [ |- _ = match ?E with _ => _ end ] =>
          remember E as RM
        end.
        match goal with
        | [ HeqLM : _ = match ?E with _ => _ end |- _] =>
          remember E as LMM
        end.
        rewrite HeqLM. clear HeqLM.

        assert (Heq: LMM = RM). 
        {
          rewrite HeqLMM. rewrite HeqRM.
          clear HeqLMM. clear HeqRM.
          f_equal.
          {
            unfold UntypedLogs.latest_write0.
            rewrite map_app. timeout 10 simpl.
            rewrite <- app_assoc. timeout 10 simpl.
            
            match goal with
            | [ |- ?A ++ ?C = ?B ++ ?C ] =>
              assert (A = B)
            end.
            {
              f_equal. extensionality s. f_equal. 
              set (lhs := UntypedLogs.log_find _ _ _).
              set (rhs := UntypedLogs.log_find _ _ _).
              assert (lhs = rhs) as H0.
              {
                subst lhs; subst rhs.
                destruct (eq_dec (tf_reg tf_ctx s) (tf_reg tf_ctx a)).
                {
                  rewrite e. clear e.
                  timeout 10 simpl.
                  unfold UntypedLogs.log_find.
                  unfold getenv. cbn.
                  rewrite !cassoc_ccreate. 
                  rewrite !cassoc_creplace_eq. cbn.
                  reflexivity. 
                } {
                  timeout 10 simpl.
                  unfold UntypedLogs.log_find.
                  unfold getenv. cbn.
                  rewrite !cassoc_ccreate. 
                  rewrite !cassoc_creplace_neq_k.
                  timeout 10 sauto.
                  timeout 10 sauto.
                }
              } rewrite H0. reflexivity.
            } rewrite H0. reflexivity. 
          }
        } 
        
        rewrite Heq. clear Heq. clear HeqLMM. clear HeqRM.

        case_eq RM.
        {
          intros. destruct p as [p0 Gamma']. destruct p0 as [final_log v].
          f_equal. destruct Gamma' as [| h t] eqn:E. 
          { 
            rewrite skipn_nil. reflexivity.
          } {
            f_equal. remember (Datatypes.length _) as len.
            destruct len.
            - rewrite skipn_O. rewrite skipn_O. reflexivity.
            - rewrite skipn_cons. assert (tl (skipn len t) = skipn 1 (skipn len t)) as H_tl_is_skipn1.
              {
                destruct (skipn len t) eqn:E2.
                { rewrite skipn_nil. reflexivity. }
                { reflexivity. }
              } rewrite H_tl_is_skipn1. clear H_tl_is_skipn1.
              rewrite skipn_skipn. reflexivity.  
          }
        }
        {
          intros. reflexivity.
        }
      }
    Qed. 

    Lemma log_after_act_read_state_vars_no_state_read_writes:
      forall hw_reg_state l act,
      UntypedLogs.log_existsb (log_after_act_read_state_vars hw_reg_state UntypedLogs.log_empty UntypedLogs.log_empty l) (tf_reg tf_ctx act) UntypedLogs.is_read0 = false
      /\
      UntypedLogs.log_existsb (log_after_act_read_state_vars hw_reg_state UntypedLogs.log_empty UntypedLogs.log_empty l) (tf_reg tf_ctx act) UntypedLogs.is_write0 = false
      /\
      UntypedLogs.log_existsb (log_after_act_read_state_vars hw_reg_state UntypedLogs.log_empty UntypedLogs.log_empty l) (tf_reg tf_ctx act) UntypedLogs.is_write1 = false.
    Proof.
      intros.
      unfold log_after_act_read_state_vars.
      unfold UntypedLogs.log_existsb in *. cbn in *.
      set (c_nil := ccreate _ _).
      assert (
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_read0 kind prt) (getenv ULog_Renv c_nil (tf_reg tf_ctx act)) = false
        /\
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_write0 kind prt) (getenv ULog_Renv c_nil (tf_reg tf_ctx act)) = false
        /\
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_write1 kind prt) (getenv ULog_Renv c_nil (tf_reg tf_ctx act)) = false
      ).
      {
        subst c_nil. unfold getenv. cbn. rewrite cassoc_ccreate. cbn. (* hammer. *) timeout 10 sfirstorder.
      }

      generalize dependent c_nil.
      induction l; intros. exact H.
      unfold UntypedLogs.log_existsb in *. cbn in *. unfold getenv in *. cbn in *.
      set (cons1 := UntypedLogs.log_cons _ _ _).
      specialize (IHl cons1).
      assert (
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_read0 kind prt) (cassoc (finite_member (tf_reg tf_ctx act)) cons1) = false
        /\
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_write0 kind prt) (cassoc (finite_member (tf_reg tf_ctx act)) cons1) = false
        /\
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_write1 kind prt) (cassoc (finite_member (tf_reg tf_ctx act)) cons1) = false
      ).
      { 
        subst cons1. unfold UntypedLogs.log_cons. cbn. unfold ULog_Renv. destruct (eq_dec (tf_reg tf_ctx act) (tf_reg tf_ctx a)).
        { rewrite e in *. rewrite Common.cassoc_put_eq. cbn. unfold getenv. cbn. exact H. }
        { rewrite Common.cassoc_put_neq. 2: { timeout 10 hauto. } exact H. }
      }
      specialize (IHl H0). exact IHl.
    Qed.

    Lemma log_after_act_read_state_vars_no_output_read_writes:
      forall hw_reg_state l out,
      UntypedLogs.log_existsb (log_after_act_read_state_vars hw_reg_state UntypedLogs.log_empty UntypedLogs.log_empty l) (tf_out tf_ctx out) UntypedLogs.is_read0 = false
      /\
      UntypedLogs.log_existsb (log_after_act_read_state_vars hw_reg_state UntypedLogs.log_empty UntypedLogs.log_empty l) (tf_out tf_ctx out) UntypedLogs.is_read1 = false
      /\
      UntypedLogs.log_existsb (log_after_act_read_state_vars hw_reg_state UntypedLogs.log_empty UntypedLogs.log_empty l) (tf_out tf_ctx out) UntypedLogs.is_write0 = false
      /\
      UntypedLogs.log_existsb (log_after_act_read_state_vars hw_reg_state UntypedLogs.log_empty UntypedLogs.log_empty l) (tf_out tf_ctx out) UntypedLogs.is_write1 = false.
    Proof.
      intros.
      unfold log_after_act_read_state_vars.
      unfold UntypedLogs.log_existsb in *. cbn in *.
      set (c_nil := ccreate _ _).
      assert (
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_read0 kind prt) (getenv ULog_Renv c_nil (tf_out tf_ctx out)) = false
        /\
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_read1 kind prt) (getenv ULog_Renv c_nil (tf_out tf_ctx out)) = false
        /\
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_write0 kind prt) (getenv ULog_Renv c_nil (tf_out tf_ctx out)) = false
        /\
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_write1 kind prt) (getenv ULog_Renv c_nil (tf_out tf_ctx out)) = false
      ).
      {
        subst c_nil. unfold getenv. cbn. rewrite cassoc_ccreate. cbn. (* hammer. *) timeout 10 sfirstorder.
      }

      generalize dependent c_nil.
      induction l; intros. exact H.
      unfold UntypedLogs.log_existsb in *. cbn in *. unfold getenv in *. cbn in *.
      set (cons1 := UntypedLogs.log_cons _ _ _).
      specialize (IHl cons1).
      assert (
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_read0 kind prt) (cassoc (finite_member (tf_out tf_ctx out)) cons1) = false
        /\
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_read1 kind prt) (cassoc (finite_member (tf_out tf_ctx out)) cons1) = false
        /\
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_write0 kind prt) (cassoc (finite_member (tf_out tf_ctx out)) cons1) = false
        /\
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_write1 kind prt) (cassoc (finite_member (tf_out tf_ctx out)) cons1) = false
      ).
      { 
        subst cons1. unfold UntypedLogs.log_cons. cbn. unfold ULog_Renv. rewrite Common.cassoc_put_neq. 2: { timeout 10 hauto. } exact H.
      }
      specialize (IHl H0). exact IHl.
    Qed.

    Definition written_outputs (state_op: tf_ops (spec_states tf_ctx) (spec_inputs tf_ctx) (spec_outputs tf_ctx)) := 
        List.filter (fun o => if (spec_no_output_dec tf_ctx o state_op) then false else true) some_fs_output_elements.

    Definition log_after_act_write_output_vars (hw_reg_state: hw_env_t) (sched_log: ULog_ULog) action_log output_list Gamma :=
      let val_for_output := fun o => match BitsToLists.list_assoc Gamma (_out_name tf_ctx o) with
        | Some v => v
        | None => Bits []  (* Default value if not found, should not happen due to precondition *)
        end
      in
        List.fold_left (fun (acc_log: UntypedLogs._ULog) o =>
          UntypedLogs.log_cons (REnv:=ULog_Renv) (tf_out tf_ctx o) (UntypedLogs.LE Logs.LogWrite P0 (val_for_output o)) acc_log
        ) output_list action_log.

    Lemma interp_act_write_output_vars {REnv : Env some_reg_t} : 
      forall (hw_reg_state: hw_env_t) (Gamma: list (string * val)) sched_log action_log state_op,

        (* Precondition: Ensure all writes performed by the wrapper will succeed. *)
        (forall o, 
            let reg := tf_out tf_ctx o in 
            let combined_log := 
                (@ccreate some_reg_t (fun _ : some_reg_t => list (UntypedLogs.LogEntry val)) (@finite_elements some_reg_t some_reg_t_finite) 
                  (fun (k : some_reg_t) (_ : @member some_reg_t k (@finite_elements some_reg_t some_reg_t_finite)) =>
                    @app (UntypedLogs.LogEntry val) (@getenv some_reg_t (@ContextEnv some_reg_t some_reg_t_finite) (fun _ : some_reg_t => list (UntypedLogs.LogEntry val)) action_log k)
                    (@getenv some_reg_t (@ContextEnv some_reg_t some_reg_t_finite) (fun _ : some_reg_t => list (UntypedLogs.LogEntry val)) sched_log k))) in
            In o (written_outputs state_op) -> 
              (
                @UntypedLogs.log_existsb val some_reg_t (@ContextEnv some_reg_t some_reg_t_finite) combined_log reg UntypedLogs.is_read1 = false
                /\
                @UntypedLogs.log_existsb val some_reg_t (@ContextEnv some_reg_t some_reg_t_finite) combined_log reg UntypedLogs.is_write0 = false
                /\
                @UntypedLogs.log_existsb val some_reg_t (@ContextEnv some_reg_t some_reg_t_finite) combined_log reg UntypedLogs.is_write1 = false
              )
            ) ->

        (* Precondition: Ensure all written outputs have values in Gamma *)
        (forall o, In o (written_outputs state_op) -> exists v, BitsToLists.list_assoc Gamma (_out_name tf_ctx o) = Some v) ->

        (* ---------------- *)
        let write_logs := log_after_act_write_output_vars hw_reg_state sched_log action_log (written_outputs state_op) Gamma in

        UntypedSemantics.interp_action hw_reg_state sigma Gamma sched_log action_log (_rule_write_output_vars tf_ctx state_op {{ pass }}) = 
        Some (write_logs, Bits [], Gamma).
    Proof.
      intros. unfold write_logs, log_after_act_write_output_vars, written_outputs in *.
      unfold ULog_ULog, ULog_Renv, ULog_reg_t, ULog_V in *.

      generalize dependent H.
      generalize dependent H0.
      
      unfold _rule_write_output_vars, spec_all_outputs, some_fs_output_elements, spec_outputs, spec_outputs_fin, tf_spec_outputs, tf_spec_outputs_fin in *.
      timeout 10 simpl in *.

      generalize finite_injective.
      generalize finite_surjective.
      intros H_inj H_surj.

      set (OutputList := finite_elements). 
      set (RegList := finite_elements).

      assert (NoDup OutputList) as H_nodup.
      { apply NoDup_map_inv with (f:=finite_index). apply finite_injective. }

      generalize dependent action_log.
      induction OutputList; intros.
      {
        timeout 10 simpl. 
        assert ((vect_to_list Ob) = []). { (* hammer. *) timeout 10 hauto lq: on. } rewrite H1.
        (* hammer. *) timeout 10 hauto lq: on.
      }
      {
        timeout 10 simpl.
        destruct (spec_no_output_dec tf_ctx a state_op).
        {
          apply IHOutputList. inversion H_nodup. exact H4.
          intros. apply H0. (* hammer. *) timeout 10 sauto. 
          intros. apply H. (* hammer. *) timeout 10 sauto.
        }
        {
          timeout 10 simpl.

          assert (exists v, BitsToLists.list_assoc Gamma (_out_name tf_ctx a) = Some v) as [v H1].
          { apply H0. (* hammer. *) timeout 10 sauto. } rewrite H1 in *. clear H1. timeout 10 simpl.
          set (any_read1s := UntypedLogs.log_existsb _ _ _).
          assert (any_read1s = false). { 
            apply (H a). rewrite filter_In. split.
            - apply in_eq. 
            - (* hammer. *) timeout 10 sauto.
          } rewrite H1. clear H1 any_read1s.
          set (any_write0s := UntypedLogs.log_existsb _ _ _).
          assert (any_write0s = false). { 
            apply (H a). rewrite filter_In. split.
            - apply in_eq. 
            - (* hammer. *) timeout 10 sauto.
          } rewrite H1. clear H1 any_write0s.
          set (any_write1s := UntypedLogs.log_existsb _ _ _).
          assert (any_write1s = false). { 
            apply (H a). rewrite filter_In. split.
            - apply in_eq. 
            - (* hammer. *) timeout 10 sauto.
          } rewrite H1. clear H1 any_write1s.
          timeout 10 simpl.

          rewrite IHOutputList. reflexivity.
          {
            inversion H_nodup. exact H4.
          } {
            intros. apply H0. (* hammer. *) timeout 10 hauto.
          } {
            clear IHOutputList.
            intros.
            assert (~ In a OutputList) as H_not_in.
            { inversion H_nodup. (* hammer. *) timeout 10 hauto lq: on. }

            destruct (eq_dec o a).
            { subst o. unfold not in H_not_in. apply filter_In in H1. (* hammer. *) timeout 10 hauto lq: on. }
            {
              assert (~ tf_op_no_output some_fs_states _ some_fs_inputs some_fs_outputs _ some_fs_states_size some_fs_outputs_size o state_op). {
                contradict H1. rewrite filter_In. (* hammer. *) timeout 10 hauto.
              }
              assert (In o (filter (fun o : some_fs_outputs => if spec_no_output_dec tf_ctx o state_op then false else true) (a :: OutputList))).
              {
                unfold spec_no_output_dec in *.
                apply filter_In. split.
                - apply filter_In in H1. destruct H1. (* hammer. *) timeout 10 hauto lq: on.
                - (* hammer. *) timeout 10 hauto.
              }
              specialize (H o H3).
              unfold UntypedLogs.log_existsb in *. unfold getenv in *. cbn -[_out_name] in *. rewrite !cassoc_ccreate in *.
              rewrite !cassoc_creplace_neq_k. all: (* hammer. *) timeout 10 hauto lq: on.
            }
          }
        }
      }
    Qed.

    Definition written_vars (state_op: tf_ops (spec_states tf_ctx) (spec_inputs tf_ctx) (spec_outputs tf_ctx)) := 
        List.filter (fun s => if (spec_var_not_written_dec tf_ctx s state_op) then false else true) some_fs_state_elements.

    Definition log_after_act_write_state_vars (hw_reg_state: hw_env_t) (sched_log: ULog_ULog) action_log state_list Gamma :=
      let val_for_state := fun s => match BitsToLists.list_assoc Gamma (_reg_name tf_ctx s) with
        | Some v => v
        | None => hw_reg_state.[tf_reg tf_ctx s] (* Default value if not found, should not happen due to precondition *)
        end
      in
        List.fold_left (fun (acc_log: UntypedLogs._ULog) s =>
          UntypedLogs.log_cons (REnv:=ULog_Renv) (tf_reg tf_ctx s) (UntypedLogs.LE Logs.LogWrite P1 (val_for_state s)) acc_log
        ) state_list action_log.

    (* TODO: this does no longer end in {{pass}} but instead in the rule_write_output_vars *)
    Lemma interp_act_write_state_vars {REnv : Env some_reg_t} : 
      forall (hw_reg_state: hw_env_t) (Gamma: list (string * val)) sched_log action_log state_op other,

      (* Precondition: Ensure all writes performed by the wrapper will succeed. *)
      (forall s, 
          let reg := tf_reg tf_ctx s in 
          let combined_log := 
              (@ccreate some_reg_t (fun _ : some_reg_t => list (UntypedLogs.LogEntry val)) (@finite_elements some_reg_t some_reg_t_finite) 
                (fun (k : some_reg_t) (_ : @member some_reg_t k (@finite_elements some_reg_t some_reg_t_finite)) =>
                  @app (UntypedLogs.LogEntry val) (@getenv some_reg_t (@ContextEnv some_reg_t some_reg_t_finite) (fun _ : some_reg_t => list (UntypedLogs.LogEntry val)) action_log k)
                  (@getenv some_reg_t (@ContextEnv some_reg_t some_reg_t_finite) (fun _ : some_reg_t => list (UntypedLogs.LogEntry val)) sched_log k))) in
          In s (written_vars state_op) -> @UntypedLogs.log_existsb val some_reg_t (@ContextEnv some_reg_t some_reg_t_finite) combined_log reg UntypedLogs.is_write1 = false) ->

      (* Precondition: Ensure all written vars have values in Gamma *)
      (forall s, In s (written_vars state_op) -> exists v, BitsToLists.list_assoc Gamma (_reg_name tf_ctx s) = Some v) ->

      (* ---------------- *)
      let write_logs := log_after_act_write_state_vars hw_reg_state sched_log action_log (written_vars state_op) Gamma in

      UntypedSemantics.interp_action hw_reg_state sigma Gamma sched_log action_log (_rule_write_state_vars tf_ctx state_op other) =
      UntypedSemantics.interp_action hw_reg_state sigma Gamma sched_log write_logs other.
    Proof.
      intros. unfold write_logs, log_after_act_write_state_vars, written_vars in *.
      unfold ULog_ULog, ULog_Renv, ULog_reg_t, ULog_V in *.
      
      generalize dependent H.
      generalize dependent H0.

      unfold _rule_write_state_vars, spec_all_states, some_fs_state_elements, spec_states, spec_states_fin, tf_spec_states, tf_spec_states_fin in *.
      timeout 10 simpl in *. 

      generalize finite_injective.
      generalize finite_surjective.
      intros H_inj H_surj.

      set (StateList := finite_elements). 
      set (RegList := finite_elements).

      assert (NoDup StateList) as H_nodup.
      { apply NoDup_map_inv with (f:=finite_index). apply finite_injective. }

      generalize dependent action_log.
      induction StateList; intros. reflexivity.
      {
        timeout 10 simpl.
        destruct (spec_var_not_written_dec tf_ctx a state_op).
        {
          apply IHStateList. inversion H_nodup. exact H4.
          intros. apply H0. timeout 10 sauto. intros. apply H. timeout 10 sauto.
        }
        {
          timeout 10 simpl.

          assert (exists v, BitsToLists.list_assoc Gamma (_reg_name tf_ctx a) = Some v) as [v H1].
          { apply H0. timeout 10 sauto. } rewrite H1 in *. clear H1. timeout 10 simpl.
          set (any_write1s := UntypedLogs.log_existsb _ _ _).
          assert (any_write1s = false). { 
            apply (H a). rewrite filter_In. split.
            - apply in_eq. 
            - timeout 10 sauto.
          }
          rewrite H1. clear H1 any_write1s.
          timeout 10 simpl.

          rewrite IHStateList. reflexivity.
          {
            inversion H_nodup. exact H4.
          } {
            intros. apply H0. timeout 10 sauto.
          } {
            clear IHStateList.
            intros.
            assert (~ In a StateList) as H_not_in.
            { inversion H_nodup. timeout 10 sauto. }

            destruct (eq_dec s a).
            { subst s. unfold not in H_not_in. apply filter_In in H1. timeout 10 sauto. }
            {
              assert (~ tf_op_var_not_written some_fs_states some_fs_states_fin some_fs_inputs some_fs_outputs some_fs_states_size some_fs_inputs_size s state_op). {
                contradict H1. rewrite filter_In. timeout 10 sauto.
              }
              assert (In s (filter (fun s : some_fs_states => if spec_var_not_written_dec tf_ctx s state_op then false else true) (a :: StateList))).
              {
                unfold spec_var_not_written_dec in *.
                apply filter_In. split.
                - apply filter_In in H1. destruct H1. timeout 10 sauto.
                - timeout 10 sauto.
              }
              specialize (H s H3).
              unfold UntypedLogs.log_existsb in *. unfold getenv in *. cbn -[_reg_name] in *. rewrite !cassoc_ccreate in *.
              rewrite !cassoc_creplace_neq_k. all: timeout 10 sauto.
            }
          }
        }
      }
    Qed.

    Lemma all_written_vars_after_read_vars_ok:
      forall hw_reg_state s,
      In s (written_vars (tf_nop some_fs_states some_fs_inputs some_fs_outputs)) ->
        exists v : val,
          BitsToLists.list_assoc
            (Gamma_after_act_read_state_vars hw_reg_state [] UntypedLogs.log_empty UntypedLogs.log_empty (spec_all_states tf_ctx)) (_reg_name tf_ctx s) = Some v.
    Proof.

    Qed.

  End ActionInterpretation.

  Section CmdGuard.
    
    Lemma interp_rule_wrong_cmd:
      forall (hw_reg_state: hw_env_t) log cmd,
      sigma (ext_in_cmd tf_ctx) val_true <> encoded_cmd cmd ->
      UntypedSemantics.interp_rule hw_reg_state sigma log (some_rules (rule_cmd tf_ctx cmd)) = None.
    Proof.
      intros.
      unfold some_rules, rules, _rule_cmd.
      unfold UntypedSemantics.interp_rule, UntypedSemantics.interp_action.

      cbn. unfold val_true.

      (* We know what in_cmd will give as a result so lets substitute it in our code *)
      set (sigma_val := sigma (ext_in_cmd tf_ctx) (Bits [true])) in *.
      assert (HSigmaValCmd: sigma_val <> encoded_cmd cmd).
      { unfold sigma_val. exact H. }
      destruct sigma_val eqn:H_sigma_val.
      1,2,4: (* hammer *) timeout 10 sfirstorder.
      remember (BitsToLists.get_field (Struct sig v) "valid") as valid_field_opt.
      destruct valid_field_opt eqn:H_cmd_valid. 2: (* hammer *) timeout 10 sfirstorder.
      cbn. destruct v0. 2-4: (* hammer *) timeout 10 sfirstorder.
      cbn. destruct v0. (* hammer *) timeout 10 sfirstorder.
      cbn. destruct v0. 2: (* hammer. *) timeout 10 sfirstorder.
      cbn. destruct b. 2: (* hammer. *) timeout 10 sfirstorder.
      cbn. remember (BitsToLists.get_field_struct _ _ _) as data_field_opt.
      destruct data_field_opt. 2: (* hammer. *) timeout 10 sfirstorder.
      cbn. destruct v0. 2,4: (* hammer. *) timeout 10 sfirstorder. 2: (* hammer. *) timeout 10 hauto.
      cbn. set (eqb_result := BitsToLists.list_eqb _ _ _) in *. assert (eqb_result = false).
      2: { rewrite H0. cbn. reflexivity. } subst eqb_result.
      rewrite <- Bool.not_true_iff_false. rewrite BitsToLists.list_eqb_correct.
      2: (* hammer. *) timeout 10 eauto using eqb_true_iff.
                      
      intro H_eq. subst.
      timeout 10 cbn in *. unfold not in *.
      unfold _fs_cmd_encoding in *. 
      unfold_all.
      apply HSigmaValCmd. clear HSigmaValCmd.
      generalize (sigma_ext_in_cmd_is_struct cmd (Bits [true])); intros.
      rewrite <- H_sigma_val in *. subst sigma_val. 

      destruct H0 as [valid' [cmd_encoding H_sigma_struct]].
      rewrite H_sigma_struct in *.
      repeat f_equal. all: (* hammer. *) timeout 10 hauto.
    Qed.

    Lemma interp_scheduler_no_cmd:
      forall (hw_reg_state: hw_env_t) cmd log (l: list some_fs_action) sched,
      sigma (ext_in_cmd tf_ctx) val_true = encoded_cmd cmd ->
      (~ In cmd l) ->
      UntypedSemantics.interp_scheduler' some_rules hw_reg_state sigma log 
        (fold_right (fun (t : some_fs_action) (acc : scheduler) => rule_cmd tf_ctx t |> acc) sched l)
        = UntypedSemantics.interp_scheduler' some_rules hw_reg_state sigma log sched.
    Proof.
      intros.

      induction l. reflexivity.
      assert (~ In cmd l) as H0S.
      { intros H_in. apply H0. (* hammer. *) timeout 10 hauto. }
      specialize (IHl H0S). 
      cbn. rewrite IHl. clear IHl.

      set (MT := UntypedSemantics.interp_rule _ _ _ _).
      assert (MT = None) as H_rule_none.
      {
        unfold not in H0S. destruct (eq_dec a cmd).
        - subst a. exfalso. apply H0S. (* hammer. *) timeout 10 sauto.
        - apply interp_rule_wrong_cmd. 
          unfold not. rewrite H. intros. apply (encoded_cmd_inj cmd a) in H1. (* hammer. *) timeout 10 sfirstorder.
      }
      rewrite H_rule_none. reflexivity.   
    Qed.

    Lemma interp_rule_right_cmd':
      forall (hw_reg_state: hw_env_t) log cmd,
      sigma (ext_in_cmd tf_ctx) val_true = encoded_cmd cmd ->
      UntypedSemantics.interp_rule hw_reg_state sigma log (some_rules (rule_cmd tf_ctx cmd)) = 
      UntypedSemantics.interp_rule hw_reg_state sigma log (_rule_cmd tf_ctx cmd).
    Proof.
      intros.
      unfold some_rules.
      unfold UntypedSemantics.interp_rule.
      unfold UntypedSemantics.interp_action.
      cbn -[_rule_cmd].

      set (sigma_val := sigma (ext_in_cmd tf_ctx) (Bits [true])) in *.
      assert (HSigmaValCmd: sigma_val = encoded_cmd cmd).
      { unfold sigma_val. exact H. } rewrite HSigmaValCmd in *. clear sigma_val HSigmaValCmd. clear H.
      cbn -[_rule_cmd].

      (* Help out unpacking the relevant spec_action_index info from tf_ctx *)
      unfold _fs_cmd_encoding, some_cmd_reg_size, spec_action_index, spec_action, spec_action_fin in *.
      assert (@finite_index some_fs_action some_fs_action_fin cmd = @finite_index (spec_action tf_ctx) (spec_action_fin tf_ctx) cmd).
      { unfold tf_ctx, tf_spec_action, tf_spec_action_fin in *. fold tf_ctx in *. reflexivity. } rewrite H in *; clear H.

      (* Help out with the comparison *)
      set (eq_true := BitsToLists.list_eqb _ _ _) in *.
      assert (eq_true = true).
      { unfold eq_true. apply BitsToLists.list_eqb_refl. (* hammer. *) timeout 10 sfirstorder using eqb_true_iff. } rewrite H in *; clear H. clear eq_true.

      unfold opt_bind.
      cbn.
      reflexivity.
    Qed.

    (* Definition log_after_rule_right_cmd :=
      None. *)

    Lemma interp_rule_right_cmd:
      forall (hw_reg_state: hw_env_t) cmd,
      sigma (ext_in_cmd tf_ctx) val_true = encoded_cmd cmd ->
      UntypedSemantics.interp_rule hw_reg_state sigma UntypedLogs.log_empty (some_rules (rule_cmd tf_ctx cmd)) = 
      match some_fs_action_ops cmd with
        | tf_nop _ _ _ => None
        | tf_neg _ _ _ x => None
        | tf_input _ _ _ x y => None
        | tf_output _ _ _ x y => None
      end (* TODO: put actual value here *)
      .
    Proof.
      intros.
      rewrite interp_rule_right_cmd' with (1:=H). unfold _rule_cmd.
      unfold UntypedSemantics.interp_rule. 
      rewrite (@interp_act_read_state_vars ContextEnv). 2: { intros. apply Common.log_existsb_empty. }
      cbn. unfold _rule_aux, op_to_uaction. 

      destruct (some_fs_action_ops cmd).
      { (* NOP *)
        rewrite (@interp_act_write_state_vars ContextEnv).
        2: {
          intros. subst reg. subst combined_log. unfold_all. unfold UntypedLogs.log_existsb in *.
          repeat (unfold getenv || rewrite !cassoc_ccreate || rewrite app_nil_l || rewrite app_nil_r); cbn.
          repeat (unfold getenv || rewrite !cassoc_ccreate || rewrite app_nil_l || rewrite app_nil_r); cbn.

          generalize (log_after_act_read_state_vars_no_state_read_writes hw_reg_state finite_elements s); intros.
          unfold UntypedLogs.log_existsb, getenv in *. cbn. (* hammer. *) timeout 10 hauto lq: on.
        }
        2: {
          intros. unfold written_vars in *. 
          econstructor. unfold Gamma_after_act_read_state_vars. inversion H. Unshelve. timeout 10 sauto. 


        }
      }

    Lemma log_after_rule_right_cmd:
      forall (hw_reg_state: hw_env_t) log cmd out,
      sigma (ext_in_cmd tf_ctx) val_true = encoded_cmd cmd ->
      UntypedSemantics.interp_rule hw_reg_state sigma UntypedLogs.log_empty (some_rules (rule_cmd tf_ctx cmd)) = Some log ->
        UntypedLogs.log_existsb log (tf_out_ack tf_ctx out) UntypedLogs.is_read0 = false
        /\ UntypedLogs.log_existsb log (tf_out_ack tf_ctx out) UntypedLogs.is_write0 = false
        /\ UntypedLogs.log_existsb log (tf_out_ack tf_ctx out) UntypedLogs.is_read1 = false
        /\ UntypedLogs.log_existsb log (tf_out_ack tf_ctx out) UntypedLogs.is_write1 = false
        /\ UntypedLogs.log_existsb log (tf_out tf_ctx out) UntypedLogs.is_write1 = false.
    Proof.
      intros.
      rewrite interp_rule_right_cmd with (1:=H) in H0. unfold _rule_cmd in H0.
      unfold UntypedSemantics.interp_rule in H0. 
      rewrite (@interp_act_read_state_vars ContextEnv) in H0. 2: { intros. apply Common.log_existsb_empty. }
      cbn in H0. unfold _rule_aux, op_to_uaction in H0. 

      destruct (some_fs_action_ops cmd).
      { (* NOP *)
        rewrite (@interp_act_write_state_vars ContextEnv) in H0.
        2: {
          intros. subst reg. subst combined_log. unfold_all. unfold UntypedLogs.log_existsb in *.
          repeat (unfold getenv || rewrite !cassoc_ccreate || rewrite app_nil_l || rewrite app_nil_r); cbn.
          repeat (unfold getenv || rewrite !cassoc_ccreate || rewrite app_nil_l || rewrite app_nil_r); cbn.

          generalize (log_after_act_read_state_vars_no_state_read_writes hw_reg_state finite_elements s); intros.
          unfold UntypedLogs.log_existsb, getenv in *. cbn in H2. (* hammer. *) timeout 10 hauto lq: on.
        }
        2: {
          intros. unfold written_vars in *. 
          econstructor. inversion H. Unshelve. timeout 10 sauto. 


        }
      }


    Definition interp_rule_out_result (hw_reg_state : hw_env_t)
        (log : @UntypedLogs._ULog val (reg_t tf_ctx) (@ContextEnv some_reg_t some_reg_t_finite)) (out : spec_outputs tf_ctx) := 
      let ack_result :=
        sigma (ext_output tf_ctx out)
          match
            list_find_opt UntypedLogs.log_latest_write0_fn
              (ccreate finite_elements (fun (k : reg_t tf_ctx) (_ : member k finite_elements) => 
                log.[k])).[tf_out tf_ctx out]
          with
          | Some v => v
          | None => hw_reg_state.[tf_out tf_ctx out]
          end
      in
        UntypedLogs.log_cons (REnv:=ULog_Renv) (tf_out_ack tf_ctx out) 
          {| UntypedLogs.kind := LogWrite; UntypedLogs.port := P1; UntypedLogs.val := ack_result |}
          (
            UntypedLogs.log_cons (tf_out tf_ctx out) 
              {| UntypedLogs.kind := LogRead; UntypedLogs.port := P1; UntypedLogs.val := Bits [] |}
              UntypedLogs.log_empty 
          ).

    Lemma interp_rule_out:
      forall (hw_reg_state: hw_env_t) log out,
      UntypedLogs.log_existsb log (tf_out tf_ctx out) UntypedLogs.is_write1 = false ->
      UntypedLogs.log_existsb log (tf_out_ack tf_ctx out) UntypedLogs.is_write1 = false ->
      UntypedSemantics.interp_rule hw_reg_state sigma log (some_rules (rule_out tf_ctx out)) = 
      Some(
        interp_rule_out_result hw_reg_state log out
      ). 
    Proof.
      intros.
      unfold interp_rule_out_result, some_rules, rules, _rule_cmd.
      unfold UntypedSemantics.interp_rule, UntypedSemantics.interp_action.

      squash. rewrite H. clear H. cbn.

      (* Have we written to out this out ack this cycle? *)
      set (has_w_ack := UntypedLogs.log_existsb _ _ _).
      assert (has_w_ack = false). {
        subst has_w_ack.
        unfold UntypedLogs.log_existsb in *.
        
        unfold getenv in *. cbn [ContextEnv] in *.
        rewrite !cassoc_ccreate. unfold UntypedLogs.RLog in *. rewrite Common.cassoc_put_neq. 
        rewrite !cassoc_ccreate. rewrite app_nil_l. exact H0.
        (* hammer. *) timeout 10 sfirstorder.
      } rewrite H. clear H has_w_ack. cbn. squash.
      unfold getenv in *. cbn [ContextEnv] in *. rewrite !cassoc_ccreate. rewrite app_nil_l. reflexivity.
    Qed.

    Definition log_after_rules_out (hw_reg_state: hw_env_t) log := 
      fold_right (fun (t : some_fs_outputs) (acc: env_t ContextEnv (fun _ : reg_t tf_ctx => UntypedLogs.RLog val)) => 
        UntypedLogs.log_app (interp_rule_out_result hw_reg_state acc t) acc
      ) log (rev finite_elements).
      
    Lemma interp_scheduler_outputs:
      forall other (hw_reg_state: hw_env_t) log,
        (forall o, In o finite_elements -> UntypedLogs.log_existsb log (tf_out tf_ctx o) UntypedLogs.is_write1 = false) ->
        (forall o, In o finite_elements -> UntypedLogs.log_existsb log (tf_out tf_ctx o) UntypedLogs.is_write0 = false) ->
        (forall o, In o finite_elements -> UntypedLogs.log_existsb log (tf_out_ack tf_ctx o) UntypedLogs.is_write1 = false) ->
        UntypedSemantics.interp_scheduler' (rules tf_ctx) hw_reg_state sigma log
          (fold_right (fun (t : some_fs_outputs) (acc : scheduler) => rule_out tf_ctx t |> acc) other finite_elements)
        =
        UntypedSemantics.interp_scheduler' (rules tf_ctx) hw_reg_state sigma (log_after_rules_out hw_reg_state log) other.
    Proof.
      intros. unfold log_after_rules_out.

      set (output_list := finite_elements) in *.
      assert (nodup: NoDup (output_list)).
      { apply NoDup_map_inv with (f:=finite_index). apply finite_injective. }

      generalize dependent log.
      induction output_list.
      { (* hammer. *) timeout 10 hauto lq: on. }
      intros.
      cbn -[rules UntypedLogs.log_app interp_rule_out_result hw_env_t] in *.

      unfold_clean. rewrite interp_rule_out.
      { rewrite !IHoutput_list.
        { f_equal. cbn. clean. rewrite fold_right_app. cbn. reflexivity. }
        all: inversion nodup; subst. exact H5. 
        - intros. specialize (H o). destruct H. (* hammer *) timeout 10 fcrush. unfold UntypedLogs.log_existsb. 
          cbn. unfold_clean. unfold getenv. cbn. 
          rewrite !cassoc_ccreate. unfold ULog_Renv. unfold_clean. 
          rewrite !Common.cassoc_put_neq. rewrite !cassoc_ccreate. rewrite app_nil_l. reflexivity.
          (* hammer. *) timeout 10 sauto. (* hammer. *) timeout 10 sauto.
        - intros. specialize (H0 o). destruct H0. (* hammer *) timeout 10 fcrush. unfold UntypedLogs.log_existsb. 
          cbn. unfold_clean. unfold getenv. cbn. 
          rewrite !cassoc_ccreate. unfold ULog_Renv. unfold_clean. 
          rewrite !Common.cassoc_put_neq. rewrite !cassoc_ccreate. rewrite app_nil_l. reflexivity.
          (* hammer. *) timeout 10 sauto. (* hammer. *) timeout 10 sauto.
        - intros. specialize (H1 o). destruct H1. (* hammer *) timeout 10 fcrush. unfold UntypedLogs.log_existsb. 
          cbn. unfold_clean. unfold getenv. cbn. 
          rewrite !cassoc_ccreate. unfold ULog_Renv. unfold_clean. 
          rewrite !Common.cassoc_put_neq. rewrite !cassoc_ccreate. rewrite app_nil_l. reflexivity.
          (* hammer. *) timeout 10 sauto. (* hammer. *) timeout 10 sauto. 
      }
      all: (* hammer *) timeout 10 hauto lq: on.
    Qed.

    Lemma log_after_rules_out_no_state_read_writes:
      forall hw_reg_state log act,
      UntypedLogs.log_existsb (log_after_rules_out hw_reg_state log) (tf_reg tf_ctx act) UntypedLogs.is_write0 =
      UntypedLogs.log_existsb log (tf_reg tf_ctx act) UntypedLogs.is_write0
      /\
      UntypedLogs.log_existsb (log_after_rules_out hw_reg_state log) (tf_reg tf_ctx act) UntypedLogs.is_write1 =
      UntypedLogs.log_existsb log (tf_reg tf_ctx act) UntypedLogs.is_write1
      /\
      UntypedLogs.log_existsb (log_after_rules_out hw_reg_state log) (tf_reg tf_ctx act) UntypedLogs.is_read0 =
      UntypedLogs.log_existsb log (tf_reg tf_ctx act) UntypedLogs.is_read0
      /\
      UntypedLogs.log_existsb (log_after_rules_out hw_reg_state log) (tf_reg tf_ctx act) UntypedLogs.is_read1 =
      UntypedLogs.log_existsb log (tf_reg tf_ctx act) UntypedLogs.is_read1.
    Proof.
      split. 2: split. 3: split.

      all: (
        intros;
        unfold log_after_rules_out;
        set (output_list := (rev finite_elements)) in *;
        induction output_list;
        try reflexivity;
        cbn -[interp_rule_out_result UntypedLogs.log_existsb env_t] in *;
        unfold interp_rule_out_result at 1;
        cbn -[interp_rule_out_result UntypedLogs.log_existsb env_t] in *;
        unfold UntypedLogs.log_existsb, getenv, ULog_Renv in *;
        unfold_clean; cbn -[interp_rule_out_result env_t] in *;
        repeat ( rewrite !Common.cassoc_put_neq || rewrite !cassoc_ccreate || rewrite !Common.cassoc_put_neq );
        try rewrite app_nil_l; try exact IHoutput_list;
        (* hammer. *) timeout 10 sfirstorder
      ).
    Qed.

    Lemma log_after_rules_out_no_output_read_writes:
      forall hw_reg_state log act,
      UntypedLogs.log_existsb (log_after_rules_out hw_reg_state log) (tf_out tf_ctx act) UntypedLogs.is_write0 =
      UntypedLogs.log_existsb log (tf_out tf_ctx act) UntypedLogs.is_write0
      /\
      UntypedLogs.log_existsb (log_after_rules_out hw_reg_state log) (tf_out tf_ctx act) UntypedLogs.is_write1 =
      UntypedLogs.log_existsb log (tf_out tf_ctx act) UntypedLogs.is_write1
      /\
      UntypedLogs.log_existsb (log_after_rules_out hw_reg_state log) (tf_out tf_ctx act) UntypedLogs.is_read0 =
      UntypedLogs.log_existsb log (tf_out tf_ctx act) UntypedLogs.is_read0.
    Proof.
      split. 2: split.

      (* Repeated 3x, how can I do "all: (_)." with a destruct?  *)
      intros.
        unfold log_after_rules_out.
        set (output_list := (rev finite_elements)) in *.
        induction output_list.
        try reflexivity.
        cbn -[interp_rule_out_result UntypedLogs.log_existsb env_t] in *.
        unfold interp_rule_out_result at 1.
        cbn -[interp_rule_out_result UntypedLogs.log_existsb env_t] in *.
        unfold UntypedLogs.log_existsb, getenv, ULog_Renv in *.
        unfold_clean. cbn -[interp_rule_out_result env_t] in *.
        destruct (eq_dec a act).
        {
          subst a.
          repeat ( rewrite !Common.cassoc_put_eq || rewrite !cassoc_ccreate || rewrite Common.cassoc_put_neq ).
          all: (* hammer. *) timeout 10 hauto lq: on.
        } {
          repeat ( rewrite !Common.cassoc_put_neq || rewrite !cassoc_ccreate ).
          try rewrite app_nil_l; try exact IHoutput_list.
          all: (* hammer. *) timeout 10 sfirstorder.
        }

      intros.
        unfold log_after_rules_out.
        set (output_list := (rev finite_elements)) in *.
        induction output_list.
        try reflexivity.
        cbn -[interp_rule_out_result UntypedLogs.log_existsb env_t] in *.
        unfold interp_rule_out_result at 1.
        cbn -[interp_rule_out_result UntypedLogs.log_existsb env_t] in *.
        unfold UntypedLogs.log_existsb, getenv, ULog_Renv in *.
        unfold_clean. cbn -[interp_rule_out_result env_t] in *.
        destruct (eq_dec a act).
        {
          subst a.
          repeat ( rewrite !Common.cassoc_put_eq || rewrite !cassoc_ccreate || rewrite Common.cassoc_put_neq ).
          all: (* hammer. *) timeout 10 hauto lq: on.
        } {
          repeat ( rewrite !Common.cassoc_put_neq || rewrite !cassoc_ccreate ).
          try rewrite app_nil_l; try exact IHoutput_list.
          all: (* hammer. *) timeout 10 sfirstorder.
        }
      
      intros.
        unfold log_after_rules_out.
        set (output_list := (rev finite_elements)) in *.
        induction output_list.
        try reflexivity.
        cbn -[interp_rule_out_result UntypedLogs.log_existsb env_t] in *.
        unfold interp_rule_out_result at 1.
        cbn -[interp_rule_out_result UntypedLogs.log_existsb env_t] in *.
        unfold UntypedLogs.log_existsb, getenv, ULog_Renv in *.
        unfold_clean. cbn -[interp_rule_out_result env_t] in *.
        destruct (eq_dec a act).
        {
          subst a.
          repeat ( rewrite !Common.cassoc_put_eq || rewrite !cassoc_ccreate || rewrite Common.cassoc_put_neq ).
          all: (* hammer. *) timeout 10 hauto lq: on.
        } {
          repeat ( rewrite !Common.cassoc_put_neq || rewrite !cassoc_ccreate ).
          try rewrite app_nil_l; try exact IHoutput_list.
          all: (* hammer. *) timeout 10 sfirstorder.
        }
    Qed.
    
    Lemma interp_scheduler_writes_state_only_cmd (hw_reg_state: hw_env_t) cmd reg:
      ((exists state_var, tf_reg tf_ctx state_var = reg) \/ (exists out_var, tf_out tf_ctx out_var = reg)) ->
      sigma (ext_in_cmd tf_ctx) val_true = encoded_cmd cmd ->
      UntypedLogs.latest_write (UntypedSemantics.interp_scheduler' some_rules hw_reg_state sigma UntypedLogs.log_empty some_system_schedule) reg =
      UntypedLogs.latest_write (UntypedSemantics.interp_scheduler' some_rules hw_reg_state sigma UntypedLogs.log_empty (rule_cmd tf_ctx cmd |> done)) reg.
    Proof.
      intros. unfold some_system_schedule, system_schedule, system_schedule_actions, system_schedule_outputs in *.

      set (action_list := (spec_all_actions tf_ctx)) in *.

      assert (H_nodup: NoDup (action_list)). {
        apply NoDup_map_inv with (f:=finite_index).
        apply finite_injective.
      }
      assert (H_in_l: In cmd action_list). {
        generalize (finite_surjective cmd). intros H1.
        apply nth_error_In with (finite_index cmd). exact H1.
      }

      unfold_all.

      induction (action_list). destruct H_in_l.
      
      destruct (eq_dec a cmd).
      {
        timeout 10 cbn -[rules UntypedLogs.log_empty].

        subst a. assert (H_not_in_l: ~ In cmd l). { inversion H_nodup. timeout 10 sauto. }
        
        assert ((~ Common.scheduler_has_rule (fold_right (fun (t : some_fs_action) (acc : scheduler) => rule_cmd tf_ctx t |> acc) (done) l) (rule_cmd tf_ctx cmd))).
        {
          unfold not. unfold Common.scheduler_has_rule. intros H_in.
          clear IHl. induction l.
          { timeout 10 sauto. }
          {
            destruct (eq_dec a cmd) as [H_eq | H_neq].
            { timeout 10 sauto. }
            { 
              timeout 10 cbn [fold_right Common.scheduler_has_rule] in H_in. 
              destruct (eq_dec (rule_cmd tf_ctx a) (rule_cmd tf_ctx cmd)) as [H_eq2 | H_neq2].
              apply cmd_rule_eq_dec_equal in H_eq2. subst a. contradiction.
              apply IHl.
              (* hammer. *) timeout 10 sauto lq:on.
              (* hammer. *) timeout 10 sauto lq: on drew: off.
              (* hammer. *) timeout 10 sauto lq:on.
              (* hammer. *) timeout 10 sfirstorder.
            }
          }
        }

        f_equal.
        rewrite !(interp_scheduler_no_cmd hw_reg_state cmd). 2: exact H0. 2: exact H_not_in_l.
        unfold some_reg_t, some_reg_t_finite.
        unfold UntypedLogs.log_empty, create, getenv. cbn -[rules].

        match goal with
        | [ |- cassoc _ match ?LHS with _ => _ end = cassoc _ match ?RHS with _ => _ end ] =>
          remember LHS as MATCH
        end.

        destruct MATCH.
        {
          rewrite !(interp_scheduler_no_cmd hw_reg_state cmd) with (1:=H0) (2:=H_not_in_l).
          rewrite interp_scheduler_outputs.

          (* TODO *)
          rewrite TODO.
          
        }
      }
      {
        timeout 10 cbn -[rules UntypedLogs.log_empty UntypedLogs.latest_write].
        rewrite interp_rule_wrong_cmd.
        {
          inversion H_in_l. congruence.
          inversion H_nodup. subst l0 x.
          destruct (eq_dec l []).   
          { subst l. contradiction. }

          rewrite IHl. all: (* hammer *) timeout 10 hauto lq: on.
        }
        {
          unfold not. intros. assert (encoded_cmd cmd = encoded_cmd a). { timeout 10 sauto. } 
          apply encoded_cmd_inj' in H1. contradiction. timeout 10 sauto.
        }
      }
    Qed.

    Lemma interp_scheduler_only_cmd:
      forall (hw_reg_state: hw_env_t) cmd state_var,
      sigma (ext_in_cmd tf_ctx) val_true = encoded_cmd cmd ->
      UntypedLogs.latest_write (UntypedSemantics.interp_scheduler' some_rules hw_reg_state sigma UntypedLogs.log_empty some_system_schedule) (tf_reg tf_ctx state_var) =
      UntypedLogs.latest_write (UntypedSemantics.interp_scheduler' some_rules hw_reg_state sigma (log_after_rules_out hw_reg_state (ContextEnv.(create) (fun _ => []))) ( rule_cmd tf_ctx cmd |> done )) (tf_reg tf_ctx state_var).
    Proof.
      intros.

      set (schedule := some_system_schedule) in *.
      unfold some_system_schedule, system_schedule, system_schedule_outputs, system_schedule_actions in *.
      unfold_all. cbn in schedule.

      set (action_order := finite_elements) in *.

      subst schedule.
      rewrite interp_scheduler_outputs. 2-4: ( intros; apply Common.log_existsb_empty ).
      rewrite (interp_scheduler_cmds_only_cmd hw_reg_state cmd). 
      squash.
      exact H. 
      {
        subst action_order.
        generalize (finite_surjective cmd). intros H1.
        apply nth_error_In with (finite_index cmd). exact H1.
      }
      {
        apply NoDup_map_inv with (f:=finite_index).
        apply finite_injective.
      }
    Qed. 

    Lemma interp_action_write_vars_unchanged_by_outputs:
      forall (hw_reg_state: hw_env_t) Gamma log log2 cmd,
      UntypedSemantics.interp_action hw_reg_state sigma Gamma (log_after_rules_out hw_reg_state log) log2
        (_rule_write_output_vars tf_ctx (some_fs_action_ops cmd) {{ pass }}) =
      UntypedSemantics.interp_action hw_reg_state sigma Gamma log log2
        (_rule_write_output_vars tf_ctx (some_fs_action_ops cmd) {{ pass }}).
    Proof.
      intros.

      unfold _rule_write_output_vars, spec_all_outputs, spec_outputs, spec_outputs_fin, tf_spec_outputs, tf_spec_outputs_fin in *.
      set (OutputList := finite_elements).

      generalize dependent Gamma.
      generalize dependent log2.
      induction OutputList; intros. (* hammer *) timeout 10 sfirstorder.
      destruct (spec_no_output_dec tf_ctx a (some_fs_action_ops cmd)) eqn:H_no_out_dec.
      {
        cbn -[UntypedLogs.log_empty _reg_name _out_name]. rewrite H_no_out_dec.
        apply IHOutputList.
      }
      {
        cbn -[UntypedLogs.log_empty _reg_name _out_name]. rewrite H_no_out_dec.
        cbn -[UntypedLogs.log_empty _reg_name _out_name UntypedLogs.log_existsb].
        f_equal.
        2: { extensionality t. destruct t. destruct p. apply IHOutputList. }
        f_equal. extensionality t. destruct t. destruct p.
        cbn in a.

        generalize (log_after_rules_out_no_output_read_writes hw_reg_state log a).
        intros H_log_no_out_rw. destruct H_log_no_out_rw as [H_w0 [H_w1 H_r1]].
        rewrite (Common.log_existsb_context_concat (log_after_rules_out hw_reg_state log) log). 2: exact H_w1.
        reflexivity.
      }
    Qed.

    (* Lemma interp_action_cmd_unchanged_by_outputs:
      forall (hw_reg_state: hw_env_t) Gamma log cmd,
      UntypedSemantics.interp_action hw_reg_state sigma Gamma (log_after_rules_out hw_reg_state log) UntypedLogs.log_empty
        (_rule_aux tf_ctx (some_fs_action_ops cmd) (_rule_write_state_vars tf_ctx (some_fs_action_ops cmd) (_rule_write_output_vars tf_ctx (some_fs_action_ops cmd) {{ pass }}))) =
      UntypedSemantics.interp_action hw_reg_state sigma Gamma log UntypedLogs.log_empty
        (_rule_aux tf_ctx (some_fs_action_ops cmd) (_rule_write_state_vars tf_ctx (some_fs_action_ops cmd) (_rule_write_output_vars tf_ctx (some_fs_action_ops cmd) {{ pass }}))).
    Proof.
      intros.

      destruct some_fs_action_ops eqn:H_fs_action_ops.
      { (* Nop *)
        timeout 10 cbn -[UntypedLogs.log_empty].

      }



    Lemma interp_rule_cmd_unchanged_by_outputs:
      forall (hw_reg_state: hw_env_t) log cmd,
      sigma (ext_in_cmd tf_ctx) val_true = encoded_cmd cmd ->
      UntypedSemantics.interp_rule hw_reg_state sigma (log_after_rules_out hw_reg_state log) (some_rules (rule_cmd tf_ctx cmd)) =
      UntypedSemantics.interp_rule hw_reg_state sigma log (some_rules (rule_cmd tf_ctx cmd)).
    Proof.
      intros.

      rewrite !interp_rule_right_cmd. 2-3: exact H.
      unfold some_rules, rules, _rule_cmd, UntypedSemantics.interp_rule.

      match goal with
      | [ |- match ?LHS with _ => _ end = match ?RHS with _ => _ end ] =>
        remember LHS as H_LHS; remember RHS as H_RHS
      end.
      assert (H_eq: H_LHS = H_RHS). 2: { rewrite H_eq. reflexivity. } subst.

      induction spec_all_states. {
        timeout 10 cbn -[UntypedLogs.log_empty]. f_equal. cbn.
      } *)
    
  End CmdGuard.

  

  (* Prove next HW cycle = next Spec cycle *)
    Definition _ur (x: some_reg_t) := val_of_value (some_r x).
    Definition initial_hw_state := 
        ContextEnv.(create) _ur.

    Definition next_hw_cycle (hw_reg_state: env_t ContextEnv (fun _ : some_reg_t => val)) := 
    UntypedSemantics.interp_cycle some_rules hw_reg_state sigma some_system_schedule.

    (* TODO: Update once we have operation lists as input *)
    Definition some_fs_step :=  tf_op_step_commit some_fs_states _ some_fs_inputs some_fs_outputs some_fs_states_size some_fs_inputs_size.
    Definition some_fs_op_step_writes :=  tf_op_step_writes some_fs_states _ some_fs_inputs some_fs_outputs some_fs_states_size some_fs_inputs_size.

    Definition StateR (hw_reg_state: env_t ContextEnv (fun _ : some_reg_t => val)) (fs_state: ContextEnv.(env_t) some_fs_states_t) :=
        forall x, hw_reg_state.[tf_reg tf_ctx x] = val_of_value (fs_state.[x]).
    
    Theorem InitState_correct :
        StateR initial_hw_state (ContextEnv.(create) some_fs_states_init).
    Proof.
        unfold initial_hw_state. intros x.
        rewrite getenv_create. rewrite getenv_create. (* hammer. *) timeout 10 hauto lq: on.
    Qed.

    Definition SigmaR (input: forall (x : some_fs_inputs), (type_denote (tf_inputs_type some_fs_inputs some_fs_inputs_size x))) :=
        forall x, sigma (ext_input tf_ctx x) val_true = val_of_value (input x).

    Lemma latest_write_eq_some_fs_op_step_writes:
      forall hw_reg_state fs_state fs_sigma cmd state_var,
      sigma (ext_in_cmd tf_ctx) val_true = encoded_cmd cmd ->
      StateR hw_reg_state fs_state ->
      SigmaR fs_sigma ->
      UntypedLogs.latest_write (UntypedSemantics.interp_scheduler some_rules hw_reg_state sigma some_system_schedule) (tf_reg tf_ctx state_var) 
      = match (some_fs_op_step_writes fs_state fs_sigma state_var (some_fs_action_ops cmd)) with
        | Some k => Some (val_of_value k)
        | None => None
      end.
    Proof.
        intros hw_reg_state fs_state fs_sigma cmd state_var H_sigma_eq_cmd H_state H_fs_sigma.
        unfold StateR in H_state.

        rewrite (interp_scheduler_only_cmd hw_reg_state cmd).
        { unfold UntypedSemantics.interp_scheduler, UntypedSemantics.interp_scheduler'.
          rewrite (interp_rule_right_cmd hw_reg_state).
          { 
            unfold _rule_cmd, UntypedSemantics.interp_rule.
            unfold UntypedLogs.latest_write, UntypedLogs.log_find.

            rewrite (@interp_act_read_state_vars ContextEnv).
            {
              simpl. unfold _rule_aux, spec_all_states. cbn -[_reg_name].  
              destruct (some_fs_action_ops cmd) eqn:H_ops.
              { (* nop *)
                cbn -[_reg_name]. 
                
                rewrite (@interp_act_write_state_vars ContextEnv).
                {
                  rewrite filter_written_vars_nop.
                  cbn -[_reg_name]. rewrite !Common.getenv_ccreate.
                  rewrite app_nil_r. 
                  set (RegList := finite_elements).
                  set (StateList := finite_elements).
                  
                  cbn -[_reg_name].
                  rewrite SemanticProperties.find_none_notb. reflexivity.
                  intros. unfold UntypedLogs.log_latest_write_fn.
                  destruct a. destruct kind. reflexivity.
                  exfalso. contradict H. subst RegList. unfold getenv; cbn -[_reg_name].
                  
                  rewrite <- fold_left_rev_right.
                  induction (rev StateList).
                  { 
                    cbn -[_reg_name].  rewrite cassoc_ccreate. timeout 10 sauto.
                  }
                  {
                    cbn -[_reg_name].  destruct ( eq_dec (tf_reg tf_ctx a) (tf_reg tf_ctx state_var) ).
                    { rewrite e. clear e. rewrite cassoc_creplace_eq. cbn -[_reg_name].  timeout 10 sauto. }
                    { rewrite cassoc_creplace_neq_k. timeout 10 sauto. timeout 10 sauto. } 
                  }
                }
                {
                  intros. subst combined_log. unfold UntypedLogs.log_existsb, getenv. timeout 10 cbn -[_reg_name]. rewrite !cassoc_ccreate.
                  rewrite !app_nil_r. 
                  set (RegList := finite_elements).
                  set (StateList := finite_elements).

                  rewrite <- fold_left_rev_right.

                  induction (rev StateList).
                  { timeout 10 simpl. rewrite !cassoc_ccreate. timeout 10 sauto. }
                  {
                    timeout 10 simpl.  destruct ( eq_dec (tf_reg tf_ctx a) reg ).
                    { rewrite e. clear e. rewrite cassoc_creplace_eq. cbn -[_reg_name]. apply IHl. }
                    { rewrite cassoc_creplace_neq_k. timeout 10 sauto. timeout 10 sauto. } 
                  }                
                }
                {
                  intros. econstructor. rewrite filter_written_vars_nop in *. inversion H. Unshelve. timeout 10 sauto.         
                }
              }
              { (* neg *)
              
                cbn -[_reg_name]. unfold opt_bind.
                rewrite app_nil_r.
              
                set (read_val := BitsToLists.list_assoc _ _). assert (H_read_val: read_val = Some (hw_reg_state.[tf_reg tf_ctx x])).
                {
                  subst read_val. set (RegList := finite_elements).  set (StateList := finite_elements).

                  assert (In x (rev StateList)) as H_in.
                  { 
                    subst StateList. generalize (@finite_surjective some_fs_states some_fs_states_fin x). intros H1. rewrite <- in_rev.
                    apply nth_error_In with (finite_index x). exact H1.
                  }
                  assert (NoDup (rev StateList)) as H_nodup.
                  {
                    subst StateList. apply NoDup_rev. apply NoDup_map_inv with (f:=finite_index).
                    apply finite_injective.
                  }

                  unfold UntypedLogs.latest_write0. unfold UntypedLogs.log_find. unfold getenv; cbn -[_reg_name].
                  (* Set Printing All.                   *)
                  set (f_nil := (fun _ _ => _)).
                  assert (f_nil = (fun _ _ => [])).
                  {
                    subst f_nil. extensionality k. extensionality m.
                    rewrite !cassoc_ccreate. timeout 10 sauto.
                  } rewrite H. clear H f_nil.

                  set (f_access := (fun _ => _)).
                  assert (f_access = (fun s => (_reg_name tf_ctx s, hw_reg_state.[tf_reg tf_ctx s]))).
                  {
                    subst f_access. extensionality s.
                    rewrite !cassoc_ccreate. timeout 10 sauto.
                  } rewrite H. clear H f_access.

                  induction (rev StateList).
                  { timeout 10 sauto. }

                  destruct (eq_dec a x).
                  { rewrite e. subst RegList StateList. timeout 10 cbn -[_reg_name]. destruct string_rec. { reflexivity. } contradict n. timeout 10 sauto. }

                  timeout 10 cbn -[_reg_name]. destruct string_rec. {
                    contradict e. unfold not. intros. apply reg_name_inj in H. timeout 10 sauto.
                  }

                  apply in_inv in H_in. destruct H_in. timeout 10 sauto.
                  inversion H_nodup. apply IHl. timeout 10 sauto. timeout 10 sauto.
                } rewrite H_read_val. clear H_read_val read_val.

                unfold UntypedSemantics.usigma1. 
                rewrite H_state. cbn -[_reg_name]. 

                rewrite (@interp_act_write_state_vars ContextEnv).
                {
                  rewrite filter_written_vars_neg in *.
                  rewrite !Common.getenv_ccreate.
                  rewrite <- !fold_left_rev_right.
                  rewrite !app_nil_r.

                  set (RegList := finite_elements).
                  set (StateList := finite_elements).
                  
                  unfold getenv; cbn -[_reg_name].  unfold putenv; cbn -[_reg_name].  
                  destruct (eq_dec x state_var).
                  { (* The var we are interested in is the one we just negated, we should get Some new value *)
                    rewrite e. clear e.
                    rewrite cassoc_creplace_eq. cbn -[_reg_name].
                    destruct string_rec. {
                      unfold when_vars_match.
                      destruct (@eq_dec some_fs_states (@EqDec_FiniteType some_fs_states some_fs_states_fin) state_var state_var).
                      { 
                        rewrite e0. f_equal. f_equal. 
                        
                        unfold Bits.neg, Bits.map.
                        rewrite vect_to_list_map.
                        reflexivity.
                      } contradict n. timeout 10 sauto.
                    } contradict n. timeout 10 sauto.
                  } { (* The var we are interested in is unchanged, we should get None *)
                    rewrite cassoc_creplace_neq_k.
                    {
                      unfold when_vars_match.
                      destruct (@eq_dec some_fs_states (@EqDec_FiniteType some_fs_states some_fs_states_fin) x state_var).
                      { contradict n. timeout 10 sauto. }

                      cbn -[_reg_name].
                      rewrite SemanticProperties.find_none_notb. reflexivity.
                      intros. unfold UntypedLogs.log_latest_write_fn.
                      destruct a. destruct kind. reflexivity.
                      exfalso. contradict H. subst RegList. unfold getenv; cbn -[_reg_name].
                      
                      induction (rev StateList).
                      { 
                        cbn -[_reg_name].  rewrite cassoc_ccreate. timeout 10 sauto.
                      }
                      {
                        cbn -[_reg_name].  destruct ( eq_dec (tf_reg tf_ctx a) (tf_reg tf_ctx state_var) ).
                        { rewrite e. clear e. rewrite cassoc_creplace_eq. cbn -[_reg_name].  timeout 10 sauto. }
                        { rewrite cassoc_creplace_neq_k. timeout 10 sauto. timeout 10 sauto. } 
                      }
                      
                    } timeout 10 sauto.
                  }
                }
                {
                  intros. subst combined_log. unfold UntypedLogs.log_existsb, getenv. timeout 10 cbn -[_reg_name]. rewrite !cassoc_ccreate.
                  rewrite !app_nil_r. 
                  set (RegList := finite_elements).
                  set (StateList := finite_elements).

                  rewrite <- fold_left_rev_right.

                  induction (rev StateList).
                  { timeout 10 simpl. rewrite !cassoc_ccreate. timeout 10 sauto. }
                  {
                    timeout 10 simpl.  destruct ( eq_dec (tf_reg tf_ctx a) reg ).
                    { rewrite e. clear e. rewrite cassoc_creplace_eq. cbn -[_reg_name]. apply IHl. }
                    { rewrite cassoc_creplace_neq_k. timeout 10 sauto. timeout 10 sauto. } 
                  }                
                }
                {
                  intros. econstructor. rewrite filter_written_vars_neg in *. assert (s = x) by (timeout 10 sauto). subst s. timeout 10 sauto.         
                }
              }
            }
            {
              unfold UntypedLogs.log_existsb. intros.
              unfold existsb, getenv. cbn -[_reg_name].  
              rewrite cassoc_ccreate.
              timeout 10 sauto.
            }
          } exact H_sigma_eq_cmd.
        } exact H_sigma_eq_cmd.
    Qed.
    
    Theorem NextState_correct:
        forall cmd fs_state hw_reg_state,
        sigma (ext_in_cmd tf_ctx) val_true = encoded_cmd cmd ->
        StateR hw_reg_state fs_state ->
        StateR (next_hw_cycle hw_reg_state) (some_fs_step fs_state (some_fs_action_ops cmd)).
    Proof.
        intros cmd fs_state hw_reg_state H_sigma_eq_cmd H_state.

        (* We consider each state var individually *)
        intros state_var.

        (* Create next state definitions & specialize state equivalence to the vars we consider *)
        set (some_fs_step fs_state (some_fs_action_ops cmd)) as fs_state'.
        unfold next_hw_cycle, StateR in *.
        unfold some_reg_t in *.

        (* Compute what the next functional state will be, then use the hypothesis to relate it to the previous hardware state *)
        unfold some_fs_step, tf_op_step_commit, tf_op_step_writes in fs_state'.
        destruct some_fs_action_ops eqn:H_ops.
        { (* nop *)
          subst fs_state'; rewrite getenv_create.
          rewrite <- H_state.

          unfold UntypedSemantics.interp_cycle, UntypedLogs.commit_update.
          rewrite getenv_create.

          rewrite (latest_write_eq_some_fs_op_step_writes hw_reg_state fs_state cmd).
          { rewrite H_ops. cbn. reflexivity. }
          { exact H_sigma_eq_cmd. }
          { exact H_state. }
        }
        { (* neg *)
          subst fs_state'; rewrite getenv_create.

          unfold UntypedSemantics.interp_cycle, UntypedLogs.commit_update.
          rewrite getenv_create.

          rewrite (latest_write_eq_some_fs_op_step_writes hw_reg_state fs_state cmd).
          { 
            rewrite H_ops. cbn -[val_of_value]. 
            unfold when_vars_match.
            destruct (eq_dec x state_var).
            {
              rewrite H_state. subst x. reflexivity.
            } {
              rewrite H_state. reflexivity.
            }
          }
          { exact H_sigma_eq_cmd. }
          { exact H_state. }
        }
    Qed.

End CompositionalCorrectness.
