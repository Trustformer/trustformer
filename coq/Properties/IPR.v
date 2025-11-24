Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.
Require Koika.Properties.SemanticProperties.
Require Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Synthesis.
Require Import Trustformer.Utils.
Require Trustformer.Properties.Common.
From Koika.Utils Require Import Tactics.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Streams.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Init.Tactics.
Require Import Coq.Program.Equality.

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Section CompositionalCorrectness.

  (* Opaque finite_elements. *)
  Arguments finite_elements : simpl never.

  Context {tf_ctx: TFSynthContext}.
  Context (sigma: (ext_fn_t tf_ctx) -> val -> val).
  Context (sigma_valid: forall f x, exists (f_t : retSig (Sigma tf_ctx f)), sigma f x = val_of_value f_t ).

  (* ====== Abbreviations ====== *)

  Local Notation spec_states := (tf_spec_states tf_ctx).
  Local Notation spec_states_fin := (tf_spec_states_fin tf_ctx).
  Local Notation spec_states_size := (tf_spec_states_size tf_ctx).
  Local Notation spec_states_t := (tf_states_type spec_states spec_states_size).
  Local Notation spec_states_init := (tf_spec_states_init tf_ctx).
  Local Notation spec_all_states := (@finite_elements spec_states spec_states_fin).
  Local Notation spec_state_index := (@finite_index spec_states spec_states_fin).
  Local Notation spec_state_num := (Datatypes.length spec_all_states).

  Local Notation spec_inputs := (tf_spec_inputs tf_ctx).
  Local Notation spec_inputs_fin := (tf_spec_inputs_fin tf_ctx).
  Local Notation spec_inputs_size := (tf_spec_inputs_size tf_ctx).
  Local Notation spec_inputs_t := (tf_inputs_type spec_inputs spec_inputs_size).
  Local Notation spec_all_inputs := (@finite_elements spec_inputs spec_inputs_fin).
  Local Notation spec_input_index := (@finite_index spec_inputs spec_inputs_fin).
  Local Notation spec_input_num := (Datatypes.length spec_all_inputs).

  Local Notation spec_outputs := (tf_spec_outputs tf_ctx).
  Local Notation spec_outputs_fin := (tf_spec_outputs_fin tf_ctx).
  Local Notation spec_outputs_size := (tf_spec_outputs_size tf_ctx).
  Local Notation spec_outputs_t := (tf_outputs_type spec_outputs spec_outputs_size).
  Local Notation spec_all_outputs := (@finite_elements spec_outputs spec_outputs_fin).
  Local Notation spec_output_index := (@finite_index spec_outputs spec_outputs_fin).
  Local Notation spec_output_num := (Datatypes.length spec_all_outputs).

  Local Notation spec_action := (tf_spec_action tf_ctx).
  Local Notation spec_action_fin := (tf_spec_action_fin tf_ctx).
  Local Notation spec_all_actions := (@finite_elements spec_action spec_action_fin).
  Local Notation spec_action_index := (@finite_index spec_action spec_action_fin).
  Local Notation spec_action_num := (Datatypes.length spec_all_actions).

  Local Notation spec_action_reg_size := (tf_spec_action_reg_size tf_ctx).
  Local Notation spec_action_encoding := (tf_spec_action_encoding tf_ctx).
  Local Notation spec_action_encoding_inj := (tf_spec_action_encoding_inj tf_ctx).

  Local Notation spec_action_ops := (tf_spec_action_ops tf_ctx).

  Local Notation spec_var_not_written_dec := (tf_op_var_not_written_dec spec_states spec_states_fin spec_inputs spec_outputs spec_states_size spec_inputs_size spec_outputs_size).
  Local Notation spec_no_output_dec := (tf_op_no_output_dec spec_states spec_states_fin spec_inputs spec_outputs spec_outputs_fin spec_states_size spec_inputs_size spec_outputs_size).

  (* Instances, they might require explicit unfolding *)

  Instance _eq_dec_states : EqDec spec_states := _eq_dec_states tf_ctx.
  Instance _eq_dec_outputs : EqDec spec_outputs := _eq_dec_outputs tf_ctx.
  Instance _eq_dec_actions : EqDec spec_action.
  Proof. pose spec_action_fin. apply EqDec_FiniteType. Defined.

  (* Obtain the various outputs of the synthesis *)
  Local Notation impl_R := (R tf_ctx).
  Local Notation impl_r := (r tf_ctx).
  Local Notation impl_rules := (rules tf_ctx).
  Local Notation system_schedule := (system_schedule tf_ctx).
  Local Notation impl_reg := (reg_t tf_ctx).
  Local Notation impl_cmd_reg_size := (tf_spec_action_reg_size tf_ctx).

  Local Notation impl_regs_finite := (_reg_t_finite tf_ctx).
  Local Notation impl_all_regs := (@finite_elements impl_reg impl_regs_finite).

  (* Other useful notations *)
  Local Notation val_true := (Bits ( [true] )).

  Local Notation RegCEnv := (@ContextEnv impl_reg impl_regs_finite).
  Local Notation hw_env_t := (env_t RegCEnv (fun _ : impl_reg => val)).
  Local Notation RegCEnvLog := (@UntypedLogs._ULog val impl_reg RegCEnv).

  (* Encoding of commands as bitvectors *)
  Definition _fs_cmd_encoding (a: spec_action) :=
    tf_spec_action_encoding tf_ctx a.
  Definition _encoded_cmd (a: spec_action) : type_denote (maybe (bits_t impl_cmd_reg_size)) :=
      (Ob~1, (_fs_cmd_encoding a, tt)).
  Definition encoded_cmd (a: spec_action) := val_of_value (_encoded_cmd a).

  (* Useful Tactics *)
  Ltac clean := 
    (* the list of all regs is verbose this should clean it up a bit *)
      try match goal with
      | [ all_regs := _ |- _ ] => subst all_regs
      | _ => idtac
      end;
      try set (all_regs := (map _ _ ++ map _ _  ++ map _ _)) in *;
      try match goal with
      | [ all_regs := _ |- _ ] => try (assert (all_regs = @finite_elements impl_reg impl_regs_finite) as _aux_H_all_regs by reflexivity; rewrite _aux_H_all_regs in *; clear _aux_H_all_regs; clear all_regs)
      | _ => idtac
      end
      .
  
  Ltac unfold_misc := unfold var_t in *.
  Ltac cbn2 := unfold_misc; timeout 10 cbn -[vect_to_list UntypedLogs.log_existsb UntypedLogs.log_empty _reg_name _out_name Nat.eq_dec] in *; unfold_misc.

  Ltac unfold_getenv := unfold getenv; cbn [ContextEnv].
  Ltac unfold_getenv_all := unfold getenv in *; cbn [ContextEnv] in *.

  (* ============ Helper Lemmas on the synthesis results ============= *)
  Lemma list_decidable_eq_spec_states : ListDec.decidable_eq spec_states.
  Proof.
    unfold ListDec.decidable_eq.
    intros. unfold Decidable.decidable.
    destruct (eq_dec x y). left; auto. right; auto.
  Qed.

  Lemma list_decidable_eq_spec_outputs : ListDec.decidable_eq spec_outputs.
  Proof.
    unfold ListDec.decidable_eq.
    intros. unfold Decidable.decidable.
    destruct (eq_dec x y). left; auto. right; auto.
  Qed.

  (* Properties about the encoding of commands *)
  Section Encoding.

    Lemma encoded_cmd_inj :
      forall (a1 a2 : spec_action),
      encoded_cmd a1 = encoded_cmd a2 -> a1 = a2.
    Proof.
      intros a1 a2 H_eq.
      unfold encoded_cmd, _encoded_cmd, _fs_cmd_encoding in H_eq.
      cbn in H_eq. injection H_eq as H_bits_eq. apply vect_to_list_inj in H_bits_eq.
      apply spec_action_encoding_inj. exact H_bits_eq.
    Qed.

    Lemma encoded_cmd_inj' :
      forall (a1 a2 : spec_action),
      a1 <> a2 -> encoded_cmd a1 <> encoded_cmd a2.
    Proof.
      intros a1 a2 H_neq. intros H_eq.
      apply encoded_cmd_inj in H_eq.
      contradiction.
    Qed.    

    Lemma sigma_ext_in_cmd_is_struct :
      forall (cmd : spec_action) vars,
      exists valid' cmd_encoding,
      sigma (ext_in_cmd tf_ctx) vars = Struct (Maybe (bits_t impl_cmd_reg_size)) [Bits [valid']; Bits cmd_encoding].
    Proof.
      intros cmd vars.
      specialize (sigma_valid (ext_in_cmd tf_ctx) vars) as H_valid.
      destruct H_valid as [[valid_bit [payload_val ?]] Heq].
      rewrite Heq.
      cbn [val_of_value type_denote] in *. eexists _, _.
      reflexivity.
    Qed.

    Lemma reg_name_inj :
      forall r1 r2,
        (_reg_name tf_ctx r1) = (_reg_name tf_ctx r2) -> r1 = r2.
    Proof.
      intros. unfold _reg_name in H.
      timeout 10 simpl in H. 
      injection H. intros.
      apply string_id_of_nat_inj in H0.
      apply finite_index_injective in H0.
      exact H0.
    Qed.

    Lemma reg_name_inj' :
      forall r1 r2,
        (_reg_name tf_ctx r1) <> (_reg_name tf_ctx r2) -> r1 <> r2.
    Proof.
      intros. unfold _reg_name in H.
      timeout 10 simpl in H.
      unfold not in *. intros. subst r2.
      apply H. reflexivity.
    Qed.

    Lemma out_name_inj :
      forall o1 o2,
        (_out_name tf_ctx o1) = (_out_name tf_ctx o2) -> o1 = o2.
    Proof.
      intros. unfold _out_name in H.
      timeout 10 simpl in H.
      injection H. intros.
      apply string_id_of_nat_inj in H0.
      apply finite_index_injective in H0.
      exact H0.
    Qed.

    Lemma out_name_inj' :
      forall o1 o2,
        (_out_name tf_ctx o1) <> (_out_name tf_ctx o2) -> o1 <> o2.
    Proof.
      intros. unfold _out_name in H.
      timeout 10 simpl in H. 
      unfold not in *. intros. subst o2.
      apply H. reflexivity.
    Qed.

  End Encoding. 

  
  Section ActionInterpretation.

    Definition Gamma_after_act_read_state_vars (hw_reg_state: hw_env_t) (Gamma: list (string * val)) sched_log action_log state_list :=
      let state_values := List.map (fun s =>
        let v := match UntypedLogs.latest_write0 (REnv:=RegCEnv) (UntypedLogs.log_app action_log sched_log) (tf_reg tf_ctx s) with
                | Some v => v
                | None => hw_reg_state.[(tf_reg tf_ctx s)]
                end
        in (_reg_name tf_ctx s, v)
      ) (List.rev state_list) in
      state_values ++ Gamma.
    
    Definition log_after_act_read_state_vars (hw_reg_state: hw_env_t) (sched_log: RegCEnvLog) action_log state_list :=
      List.fold_left (fun (acc_log: UntypedLogs._ULog) s =>
        UntypedLogs.log_cons (REnv:=RegCEnv) (tf_reg tf_ctx s) (UntypedLogs.LE Logs.LogRead P1 (Bits [])) acc_log
      ) state_list action_log.

    Lemma interp_act_read_state_vars : 
      forall (hw_reg_state: hw_env_t) (Gamma: list (string * val)) sched_log action_log code state_list,

      (* Precondition: Ensure all reads performed by the wrapper will succeed. *)
      (forall (reg: impl_reg), UntypedLogs.log_existsb sched_log reg UntypedLogs.is_write1 = false) ->

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
        (* All Writes succeed *)
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
      unfold UntypedLogs.log_existsb  in *.
      set (c_nil := UntypedLogs.log_empty). 
      assert (
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_read0 kind prt) (getenv RegCEnv c_nil (tf_reg tf_ctx act)) = false
        /\
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_write0 kind prt) (getenv RegCEnv c_nil (tf_reg tf_ctx act)) = false
        /\
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_write1 kind prt) (getenv RegCEnv c_nil (tf_reg tf_ctx act)) = false
      ).
      {
        subst c_nil. unfold UntypedLogs.log_empty. rewrite getenv_create. cbn [existsb]. repeat split.
      }

      generalize dependent c_nil.
      induction l; intros. exact H.
      unfold UntypedLogs.log_existsb in *. cbn in *.
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
        subst cons1. unfold UntypedLogs.log_cons. destruct (eq_dec (tf_reg tf_ctx act) (tf_reg tf_ctx a)).
        { rewrite e in *. rewrite Common.cassoc_put_eq. cbn [existsb UntypedLogs.is_read0 UntypedLogs.is_write0 UntypedLogs.is_write1]. cbn. exact H. }
        { rewrite Common.cassoc_put_neq. 2: { (* hammer. *) timeout 10 hauto lq: on. } exact H. }
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
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_read0 kind prt) (getenv RegCEnv c_nil (tf_out tf_ctx out)) = false
        /\
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_read1 kind prt) (getenv RegCEnv c_nil (tf_out tf_ctx out)) = false
        /\
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_write0 kind prt) (getenv RegCEnv c_nil (tf_out tf_ctx out)) = false
        /\
        existsb (fun '{| UntypedLogs.kind := kind; UntypedLogs.port := prt |} => UntypedLogs.is_write1 kind prt) (getenv RegCEnv c_nil (tf_out tf_ctx out)) = false
      ).
      {
        subst c_nil. unfold getenv. cbn. rewrite cassoc_ccreate. cbn. (* hammer *) timeout 10 sfirstorder.
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
        subst cons1. unfold UntypedLogs.log_cons. cbn.  rewrite Common.cassoc_put_neq. 2: { (* hammer. *) timeout 10 hauto lq: on. } exact H.
      }
      specialize (IHl H0). exact IHl.
    Qed.

    Lemma log_after_act_read_state_vars_no_find_last_write:
      forall hw_reg_state l act,
        list_find_opt UntypedLogs.log_latest_write_fn
          (cassoc (finite_member act)
            (log_after_act_read_state_vars hw_reg_state UntypedLogs.log_empty UntypedLogs.log_empty l)) = None.
    Proof.
      intros. unfold log_after_act_read_state_vars.
      rewrite <- fold_left_rev_right.
      induction (rev l); intros.
      { cbn. rewrite cassoc_ccreate. cbn. reflexivity. }
      {
        cbn. unfold UntypedLogs.log_cons. 
        destruct (eq_dec act (tf_reg tf_ctx a)).
        { rewrite e in *. rewrite Common.cassoc_put_eq. cbn. apply IHl0. }
        { rewrite Common.cassoc_put_neq. 2: { timeout 10 hauto. } apply IHl0. }
      }
    Qed.

    Definition written_outputs (state_op: tf_ops (spec_states) (spec_inputs) (spec_outputs)) := 
        List.filter (fun o => if (spec_no_output_dec o state_op) then false else true) spec_all_outputs.

    Definition log_after_act_write_output_vars (hw_reg_state: hw_env_t) (sched_log: RegCEnvLog) action_log output_list Gamma :=
      let val_for_output := fun o => match BitsToLists.list_assoc Gamma (_out_name tf_ctx o) with
        | Some v => v
        | None => Bits []  (* Default value if not found, should not happen due to precondition *)
        end
      in
        List.fold_left (fun (acc_log: UntypedLogs._ULog) o =>
          UntypedLogs.log_cons (REnv:=RegCEnv) (tf_out tf_ctx o) (UntypedLogs.LE Logs.LogWrite P0 (val_for_output o)) acc_log
        ) output_list action_log.

    Lemma interp_act_write_output_vars {REnv : Env impl_reg} : 
      forall (hw_reg_state: hw_env_t) (Gamma: list (string * val)) sched_log action_log state_op,

        (* Precondition: Ensure all writes performed by the wrapper will succeed. *)
        (forall o, 
            let reg := tf_out tf_ctx o in 
            let combined_log := 
                (@ccreate impl_reg (fun _ : impl_reg => list (UntypedLogs.LogEntry val)) (@finite_elements impl_reg impl_regs_finite) 
                  (fun (k : impl_reg) (_ : @member impl_reg k (@finite_elements impl_reg impl_regs_finite)) =>
                    @app (UntypedLogs.LogEntry val) (@getenv impl_reg (@ContextEnv impl_reg impl_regs_finite) (fun _ : impl_reg => list (UntypedLogs.LogEntry val)) action_log k)
                    (@getenv impl_reg (@ContextEnv impl_reg impl_regs_finite) (fun _ : impl_reg => list (UntypedLogs.LogEntry val)) sched_log k))) in
            In o (written_outputs state_op) -> 
              (
                @UntypedLogs.log_existsb val impl_reg (@ContextEnv impl_reg impl_regs_finite) combined_log reg UntypedLogs.is_read1 = false
                /\
                @UntypedLogs.log_existsb val impl_reg (@ContextEnv impl_reg impl_regs_finite) combined_log reg UntypedLogs.is_write0 = false
                /\
                @UntypedLogs.log_existsb val impl_reg (@ContextEnv impl_reg impl_regs_finite) combined_log reg UntypedLogs.is_write1 = false
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

      generalize dependent H. generalize dependent H0.
      
      unfold _rule_write_output_vars. timeout 10 simpl in *.

      set (OutputList := finite_elements). 
      set (RegList := finite_elements).

      assert (H_nodup: NoDup OutputList) by (exact finite_nodup).

      generalize dependent action_log.
      induction OutputList; intros.
      {
        timeout 10 simpl. 
        assert ((vect_to_list Ob) = []). { (* hammer. *) timeout 10 hauto lq: on. } rewrite H1.
        (* hammer. *) timeout 10 hauto lq: on.
      }
      {
        timeout 10 simpl.
        destruct (spec_no_output_dec a state_op).
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
              assert (~ tf_op_no_output spec_states spec_states_fin spec_inputs spec_outputs spec_outputs_fin spec_states_size spec_outputs_size o state_op). {
                contradict H1. rewrite filter_In. (* hammer. *) timeout 10 hauto.
              }
              assert (In o (filter (fun o : spec_outputs => if spec_no_output_dec o state_op then false else true) (a :: OutputList))).
              {
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

    Lemma log_after_act_write_output_vars_no_find_last_write_state:
      forall hw_reg_state act l Gamma other,
        list_find_opt UntypedLogs.log_latest_write_fn
          (cassoc (finite_member (tf_reg tf_ctx act))
            (log_after_act_write_output_vars hw_reg_state UntypedLogs.log_empty other l Gamma)) 
        =
        list_find_opt UntypedLogs.log_latest_write_fn
          (cassoc (finite_member (tf_reg tf_ctx act)) other).
    Proof.
      intros. unfold log_after_act_write_output_vars.
      rewrite <- fold_left_rev_right.
      induction (rev l); intros.
      { cbn. reflexivity. }
      {
        cbn -[_out_name _reg_name]. unfold UntypedLogs.log_cons. 
        rewrite Common.cassoc_put_neq. 2: { timeout 10 hauto. } apply IHl0.
      }
    Qed.

    Lemma log_after_act_write_output_vars_no_find_last_write_out:
      forall hw_reg_state act l Gamma other,
        ~ In act l -> 
        list_find_opt UntypedLogs.log_latest_write_fn
          (cassoc (finite_member (tf_out tf_ctx act))
            (log_after_act_write_output_vars hw_reg_state UntypedLogs.log_empty other l Gamma)) 
        =
        list_find_opt UntypedLogs.log_latest_write_fn
          (cassoc (finite_member (tf_out tf_ctx act)) other).
    Proof.
      intros. unfold log_after_act_write_output_vars.
      rewrite <- fold_left_rev_right.
      assert (~ In act (rev l)). { unfold not in *. intros. apply H. apply in_rev. exact H0. }
      generalize dependent H0. 
      induction (rev l); intros.
      { cbn. reflexivity. }
      {
        assert (~ In act l0). { unfold not in *. intros. apply H0. apply in_cons. exact H1. }
        specialize (IHl0 H1).
        cbn -[_out_name _reg_name]. unfold UntypedLogs.log_cons. 
        rewrite Common.cassoc_put_neq. 2: { timeout 10 hauto. } apply IHl0.
      }
    Qed.

    Lemma log_after_act_write_output_vars_find_last_write_out:
      forall hw_reg_state act l Gamma other,
        In act l -> 
        list_find_opt UntypedLogs.log_latest_write_fn
          (cassoc (finite_member (tf_out tf_ctx act))
            (log_after_act_write_output_vars hw_reg_state UntypedLogs.log_empty other l Gamma)) 
        =
        Some match BitsToLists.list_assoc Gamma (_out_name tf_ctx act) with
              | Some v => v
              | None => Bits []
              end.
    Proof.
      intros. unfold log_after_act_write_output_vars.
      rewrite <- fold_left_rev_right.
      assert (In act (rev l)). { intros. apply in_rev. rewrite rev_involutive. exact H. }
      generalize dependent H0. 
      induction (rev l); intros.
      { inversion H0. }
      {
        destruct (eq_dec act a).
        { 
          subst a. cbn -[_out_name _reg_name]. cbn -[_out_name _reg_name]. unfold UntypedLogs.log_cons. 
          rewrite Common.cassoc_put_eq. cbn -[_out_name _reg_name]. reflexivity. 
        }
        {
          assert (In act l0). { (* hammer. *) timeout 10 fcrush. }
          specialize (IHl0 H1). cbn -[_out_name _reg_name]. unfold UntypedLogs.log_cons. 
          rewrite Common.cassoc_put_neq. 2: { timeout 10 hauto. } apply IHl0.
        }
      }
    Qed.

    Definition written_vars (state_op: tf_ops (spec_states) (spec_inputs) (spec_outputs)) := 
        List.filter (fun s => if (spec_var_not_written_dec s state_op) then false else true) spec_all_states.

    Definition log_after_act_write_state_vars (hw_reg_state: hw_env_t) (sched_log: RegCEnvLog) action_log state_list Gamma :=
      let val_for_state := fun s => match BitsToLists.list_assoc Gamma (_reg_name tf_ctx s) with
        | Some v => v
        | None => hw_reg_state.[tf_reg tf_ctx s] (* Default value if not found, should not happen due to precondition *)
        end
      in
        List.fold_left (fun (acc_log: UntypedLogs._ULog) s =>
          UntypedLogs.log_cons (REnv:=RegCEnv) (tf_reg tf_ctx s) (UntypedLogs.LE Logs.LogWrite P1 (val_for_state s)) acc_log
        ) state_list action_log.

    Lemma interp_act_write_state_vars : 
      forall (hw_reg_state: hw_env_t) (Gamma: list (string * val)) sched_log action_log state_op other,

      (* Precondition: Ensure all writes performed by the wrapper will succeed. *)
      (forall s, 
          let reg := tf_reg tf_ctx s in 
          let combined_log := 
              (@ccreate impl_reg (fun _ : impl_reg => list (UntypedLogs.LogEntry val)) (@finite_elements impl_reg impl_regs_finite) 
                (fun (k : impl_reg) (_ : @member impl_reg k (@finite_elements impl_reg impl_regs_finite)) =>
                  @app (UntypedLogs.LogEntry val) (@getenv impl_reg (@ContextEnv impl_reg impl_regs_finite) (fun _ : impl_reg => list (UntypedLogs.LogEntry val)) action_log k)
                  (@getenv impl_reg (@ContextEnv impl_reg impl_regs_finite) (fun _ : impl_reg => list (UntypedLogs.LogEntry val)) sched_log k))) in
          In s (written_vars state_op) -> @UntypedLogs.log_existsb val impl_reg (@ContextEnv impl_reg impl_regs_finite) combined_log reg UntypedLogs.is_write1 = false) ->

      (* Precondition: Ensure all written vars have values in Gamma *)
      (forall s, In s (written_vars state_op) -> exists v, BitsToLists.list_assoc Gamma (_reg_name tf_ctx s) = Some v) ->

      (* ---------------- *)
      let write_logs := log_after_act_write_state_vars hw_reg_state sched_log action_log (written_vars state_op) Gamma in

      UntypedSemantics.interp_action hw_reg_state sigma Gamma sched_log action_log (_rule_write_state_vars tf_ctx state_op other) =
      UntypedSemantics.interp_action hw_reg_state sigma Gamma sched_log write_logs other.
    Proof.
      intros. unfold write_logs, log_after_act_write_state_vars, written_vars in *.
      
      generalize dependent H. generalize dependent H0.

      unfold _rule_write_state_vars in *.
      timeout 10 simpl in *. 

      set (StateList := finite_elements). 
      set (RegList := finite_elements).

      assert (H_nodup: NoDup StateList) by (exact finite_nodup).

      generalize dependent action_log.
      induction StateList; intros. reflexivity.
      {
        timeout 10 simpl.
        destruct (spec_var_not_written_dec a state_op).
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
              assert (~ tf_op_var_not_written spec_states spec_states_fin spec_inputs spec_outputs spec_states_size spec_inputs_size s state_op). {
                contradict H1. rewrite filter_In. timeout 10 sauto.
              }
              assert (In s (filter (fun s : spec_states => if spec_var_not_written_dec s state_op then false else true) (a :: StateList))).
              {
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

    Lemma log_after_act_write_state_vars_no_find_last_write_out:
      forall hw_reg_state act l Gamma other,
        list_find_opt UntypedLogs.log_latest_write_fn
          (cassoc (finite_member (tf_out tf_ctx act))
            (log_after_act_write_state_vars hw_reg_state UntypedLogs.log_empty other l Gamma)) 
        =
        list_find_opt UntypedLogs.log_latest_write_fn
          (cassoc (finite_member (tf_out tf_ctx act)) other).
    Proof.
      intros. unfold log_after_act_write_state_vars.
      rewrite <- fold_left_rev_right.
      induction (rev l); intros.
      { cbn. reflexivity. }
      {
        cbn -[_out_name _reg_name]. unfold UntypedLogs.log_cons. 
        rewrite Common.cassoc_put_neq. 2: { timeout 10 hauto. } apply IHl0.
      }
    Qed.

    Lemma log_after_act_write_state_vars_no_find_last_write_state:
      forall hw_reg_state act l Gamma other,
        ~ In act l -> 
        list_find_opt UntypedLogs.log_latest_write_fn
          (cassoc (finite_member (tf_reg tf_ctx act))
            (log_after_act_write_state_vars hw_reg_state UntypedLogs.log_empty other l Gamma)) 
        =
        list_find_opt UntypedLogs.log_latest_write_fn
          (cassoc (finite_member (tf_reg tf_ctx act)) other).
    Proof.
      intros. unfold log_after_act_write_state_vars.
      rewrite <- fold_left_rev_right.
      assert (~ In act (rev l)). { unfold not in *. intros. apply H. apply in_rev. exact H0. }
      generalize dependent H0. 
      induction (rev l); intros.
      { cbn. reflexivity. }
      {
        assert (~ In act l0). { unfold not in *. intros. apply H0. apply in_cons. exact H1. }
        specialize (IHl0 H1).
        cbn -[_out_name _reg_name]. unfold UntypedLogs.log_cons. 
        rewrite Common.cassoc_put_neq. 2: { timeout 10 hauto. } apply IHl0.
      }
    Qed.

    Lemma log_after_act_write_state_vars_find_last_write_state:
      forall hw_reg_state act l Gamma other,
        In act l -> 
        list_find_opt UntypedLogs.log_latest_write_fn
          (cassoc (finite_member (tf_reg tf_ctx act))
            (log_after_act_write_state_vars hw_reg_state UntypedLogs.log_empty other l Gamma)) 
        =
        Some match BitsToLists.list_assoc Gamma (_reg_name tf_ctx act) with
              | Some v => v
              | None => hw_reg_state.[tf_reg tf_ctx act]
              end.
    Proof.
      intros. unfold log_after_act_write_state_vars.
      rewrite <- fold_left_rev_right.
      assert (In act (rev l)). { intros. apply in_rev. rewrite rev_involutive. exact H. }
      generalize dependent H0. 
      induction (rev l); intros.
      { inversion H0. }
      {
        destruct (eq_dec act a).
        { 
          subst a. cbn -[_out_name _reg_name]. cbn -[_out_name _reg_name]. unfold UntypedLogs.log_cons. 
          rewrite Common.cassoc_put_eq. cbn -[_out_name _reg_name]. reflexivity. 
        }
        {
          assert (In act l0). { (* hammer. *) timeout 10 fcrush. }
          specialize (IHl0 H1). cbn -[_out_name _reg_name]. unfold UntypedLogs.log_cons. 
          rewrite Common.cassoc_put_neq. 2: { timeout 10 hauto. } apply IHl0.
        }
      }
    Qed.

    Lemma all_vars_after_read_vars_correct:
      forall hw_reg_state s,
      (* TODO: currently all states are read, but in the future this only holds for the read states *)
        BitsToLists.list_assoc
            (Gamma_after_act_read_state_vars hw_reg_state [] UntypedLogs.log_empty UntypedLogs.log_empty (spec_all_states)) (_reg_name tf_ctx s) = Some hw_reg_state.[tf_reg tf_ctx s].
    Proof.
      intros. unfold Gamma_after_act_read_state_vars. rewrite List.app_nil_r.

      set (spec_list := (rev _)).
      assert (In s spec_list) as H_in_spec_list.
      {
        unfold spec_list. generalize (finite_surjective s (FiniteType:=spec_states_fin)).
        intros H1. rewrite <- in_rev. apply nth_error_In with (finite_index s (FiniteType:=spec_states_fin)). exact H1.
      }

      generalize dependent H_in_spec_list.
      induction spec_list; intros.
      { (* hammer. *) timeout 10 sfirstorder. }
      cbn -[_reg_name] in *.
      destruct (string_rec _ _ _).
      { apply reg_name_inj in e. subst a.
        repeat (unfold getenv in * || rewrite !cassoc_ccreate || rewrite app_nil_l || rewrite app_nil_r); cbn in *.
        repeat (unfold getenv || rewrite !cassoc_ccreate || rewrite app_nil_l || rewrite app_nil_r); cbn.
         reflexivity.
      }
      {
        apply reg_name_inj' in n.
        destruct H_in_spec_list. congruence.
        (* hammer *) hauto lq: on.
      }
    Qed.

  End ActionInterpretation.

  Section Expressions.
    
    Definition bits_of_value_lossy (v: val) : list bool :=
      match v with
        | Bits bl => bl
        | _ => []
      end.

    Definition val_convert (out_var_size in_var_size : nat) (x : val) : val :=
      if Nat.eq_dec out_var_size in_var_size then
        x
      else 
        if Nat.leb in_var_size out_var_size then
          Bits (bits_of_value_lossy x ++ repeat false (out_var_size - in_var_size))
        else
          Bits (firstn (out_var_size) (bits_of_value_lossy x)).

    Lemma val_convert_same:
      forall s x, val_convert s s x = x.
    Proof.
      intros.
      unfold val_convert.
      destruct (Nat.eq_dec s s).
      - reflexivity.
      - exfalso. apply n. reflexivity.
    Qed.

    Lemma val_convert_more:
      forall s1 s2 x, 
        s1 > s2 ->
        val_convert s1 s2 x = Bits (bits_of_value_lossy x ++ repeat false (s1 - s2)).
    Proof.
      intros.
      unfold val_convert.
      destruct (Nat.eq_dec s1 s2).
      - lia.
      - destruct (Nat.leb s2 s1) eqn:Hleb.
        + reflexivity.
        + (* hammer. *) timeout 10 hauto b: on.
    Qed.

    Lemma val_convert_less:
      forall s1 s2 x, 
        s1 < s2 ->
        val_convert s1 s2 x = Bits (firstn (s1) (bits_of_value_lossy x)).
    Proof.
      intros.
      unfold val_convert.
      destruct (Nat.eq_dec s1 s2).
      - lia.
      - destruct (Nat.leb s2 s1) eqn:Hleb.
        + (* hammer. *) timeout 10 hauto b: on.
        + reflexivity.
    Qed.

    Lemma val_convert_of_bits_is_bits:
      forall s1 s2 bl1,
        ((Datatypes.length bl1) = s2) ->
        exists bl2, val_convert s1 s2 (Bits bl1) = Bits bl2 /\ Datatypes.length bl2 = s1.
    Proof.
      intros. subst. unfold val_convert. destruct (Nat.eq_dec _ _). 
      econstructor; split; try auto. unfold bits_of_value_lossy.
      destruct (Nat.leb _ _ ) eqn:Hleb.
      {
        rewrite Nat.leb_le in Hleb.
        econstructor; split; try reflexivity. 
        rewrite List.app_length, repeat_length. lia.
      }
      {
        rewrite Nat.leb_gt in Hleb.
        econstructor; split; try reflexivity. 
        rewrite firstn_length. lia.
      }
    Qed.

    Lemma synth_convert_is_val_convert:
      forall hw_reg_state Gamma Log code f_dst f_src bl, 
        (UntypedSemantics.interp_action hw_reg_state sigma Gamma UntypedLogs.log_empty Log code = Some (Log, Bits bl, Gamma) 
          /\ Datatypes.length bl = f_src) ->

        UntypedSemantics.interp_action (REnv:=RegCEnv) hw_reg_state sigma Gamma UntypedLogs.log_empty Log
          (synth_convert tf_ctx f_dst f_src code ) =
          Some (Log, val_convert f_dst f_src (Bits bl), Gamma).
    Proof.
      intros.
      destruct H as [Hcode Hlen].

      unfold synth_convert, val_convert.
      destruct (Nat.eq_dec f_dst f_src). exact Hcode.
      destruct (Nat.leb f_src f_dst) eqn:Hleb.
      { cbn2. rewrite Hcode, <- Hlen. cbn2.
        reflexivity.
      } {
        cbn2. rewrite Hcode. cbn2.
        rewrite Nat.leb_gt in Hleb.
        rewrite firstn_length.
        replace (Init.Nat.min f_dst (Datatypes.length _)) with f_dst by lia.
        rewrite Nat.sub_diag. cbn2.
        rewrite app_nil_r. reflexivity.
      }
    Qed.
        
    Fixpoint value_of_expr (expr: tf_expr spec_states) (hw_reg_state: hw_env_t) (target_size: nat) : val :=
      match expr with
        | tf_const _ value => 
            Bits (vect_to_list (Bits.of_nat (target_size) value))
        | tf_var _ v =>
            val_convert target_size (spec_states_size v) hw_reg_state.[tf_reg tf_ctx v]
        | tf_op1 _ op src =>
            match UntypedSemantics.usigma1 UNot (value_of_expr src hw_reg_state target_size) with
              | Some v => v
              | None => Bits []
            end
        | tf_op2 _ op src1 src2 =>
            let v1 := (bits_of_value_lossy (value_of_expr src1 hw_reg_state target_size)) in
            let v2 := (bits_of_value_lossy (value_of_expr src2 hw_reg_state target_size)) in
            match op with
              | tf_and => 
                  Bits (UntypedSemantics.ubits2_sigma UAnd v1 v2)
              | tf_or => 
                  Bits (UntypedSemantics.ubits2_sigma UOr v1 v2)
              | tf_xor => 
                  Bits (UntypedSemantics.ubits2_sigma UXor v1 v2)
              | tf_add => 
                  Bits (UntypedSemantics.ubits2_sigma UPlus v1 v2)
              | tf_sub => 
                  Bits (UntypedSemantics.ubits2_sigma UMinus v1 v2)
              | tf_mul => 
                  val_convert target_size (target_size + target_size) (Bits (UntypedSemantics.ubits2_sigma UMul v1 v2))
              | tf_cmp cop =>
                  match cop with
                    | tf_eq => val_convert target_size (1) 
                      (Bits [if BitsToLists.val_beq (value_of_expr src1 hw_reg_state target_size) (value_of_expr src2 hw_reg_state target_size) then true else false])
                    | tf_neq  => val_convert target_size (1) 
                      (Bits [if BitsToLists.val_beq (value_of_expr src1 hw_reg_state target_size) (value_of_expr src2 hw_reg_state target_size) then false else true])
                    | tf_lt  => val_convert target_size (1) (Bits (UntypedSemantics.ubits2_sigma (UCompare false cLt) v1 v2))
                    | tf_le  => val_convert target_size (1) (Bits (UntypedSemantics.ubits2_sigma (UCompare false cLe) v1 v2))
                    | tf_gt  => val_convert target_size (1) (Bits (UntypedSemantics.ubits2_sigma (UCompare false cGt) v1 v2))
                    | tf_ge  => val_convert target_size (1) (Bits (UntypedSemantics.ubits2_sigma (UCompare false cGe) v1 v2))
                  end
            end
        end. 

    Lemma value_of_expr_bits:
      forall expr hw_reg_state f_dst,
        (forall s, exists bl, hw_reg_state.[tf_reg tf_ctx s] = Bits bl /\ Datatypes.length bl = spec_states_size s) ->
        exists bl, value_of_expr expr hw_reg_state f_dst = Bits bl /\ Datatypes.length bl = f_dst.
    Proof.
      intros. induction expr.
      {
        econstructor. cbn2. split. reflexivity. rewrite vect_to_list_length. reflexivity.
      } {
        cbn2. unfold val_convert. destruct (Nat.eq_dec _ _). specialize (H v). (* hammer. *) timeout 10 sfirstorder.
        destruct (Nat.leb _ _ ) eqn:Hleb.
        { 
          econstructor. specialize (H v). destruct H as [bl [Hhw Hlen]].
          split. reflexivity. unfold bits_of_value_lossy.
          cbn2. rewrite Hhw. rewrite app_length, repeat_length. rewrite Hlen, Nat.add_comm. 
          rewrite Nat.leb_le in Hleb. rewrite (Nat.sub_add _ _ Hleb). reflexivity.
        }
        {
          econstructor. specialize (H v). destruct H as [bl [Hhw Hlen]].
          split. reflexivity. unfold bits_of_value_lossy.
          cbn2. rewrite Hhw. rewrite firstn_length. rewrite Hlen. 
          apply leb_complete_conv in Hleb. lia.
        }
      } {
        cbn2. unfold UntypedSemantics.usigma1. destruct IHexpr as [bl [Hval Hlen]].
        rewrite Hval. econstructor. split. reflexivity. unfold UntypedSemantics.usigma1'. rewrite map_length. exact Hlen. 
      } {
        cbn2. destruct IHexpr1 as [bl1 [Hval1 Hlen1]]. destruct IHexpr2 as [bl2 [Hval2 Hlen2]].
        rewrite Hval1. rewrite Hval2. destruct op.
        1-3: econstructor; split; try reflexivity; rewrite Common.datatypes_length_bitwise; unfold bits_of_value_lossy; rewrite Hlen1, Hlen2; lia.
        1-2: econstructor; split; try reflexivity; rewrite vect_to_list_length; unfold bits_of_value_lossy; lia.
        { apply val_convert_of_bits_is_bits. { rewrite vect_to_list_length. unfold bits_of_value_lossy. lia. } }
        { destr; subst. 1-2: apply val_convert_of_bits_is_bits; reflexivity. 
          all: apply val_convert_of_bits_is_bits; destr; simpl_eq; try reflexivity; (* hammer *) timeout 10 hauto lq: on.
        }
      }
    Qed.

    Ltac prove_expr_is_bits expr1 hw_reg_state f_dst H :=
      let H0 := fresh "H0" in
      let bl1 := fresh "bl1" in
      let Hval1 := fresh "Hval1" in
      let Hval2 := fresh "Hval2" in
      generalize (value_of_expr_bits expr1 hw_reg_state f_dst H); intros H0; 
      destruct H0 as [bl1 [Hval1 Hval2]];
      destruct value_of_expr; try congruence; inversion Hval1; subst bl1; clear Hval1.

    Lemma interp_act_expr_to_uaction:
      forall expr f_dst hw_reg_state,
        (forall s, exists bl, hw_reg_state.[tf_reg tf_ctx s] = Bits bl /\ Datatypes.length bl = spec_states_size s) ->
        (* TODO: generalize this for any logs that fulfill some conditions (reads succeed) *)
        UntypedSemantics.interp_action hw_reg_state sigma
          (Gamma_after_act_read_state_vars hw_reg_state [] UntypedLogs.log_empty UntypedLogs.log_empty spec_all_states)
          UntypedLogs.log_empty
          (log_after_act_read_state_vars hw_reg_state UntypedLogs.log_empty UntypedLogs.log_empty spec_all_states) 
          (expr_to_uaction tf_ctx expr f_dst) 
          = Some ( 
            (log_after_act_read_state_vars hw_reg_state UntypedLogs.log_empty UntypedLogs.log_empty spec_all_states, 
            (value_of_expr expr hw_reg_state f_dst), 
            Gamma_after_act_read_state_vars hw_reg_state [] UntypedLogs.log_empty UntypedLogs.log_empty spec_all_states)
          ).
    Proof.
      intros. (* repeat econstructor. *)

      generalize dependent f_dst.
      induction expr; intros.
      { (* tf_const *)
        unfold value_of_expr. cbn2; unfold synth_convert; cbn2. repeat f_equal.
      } { (* tf_var *)
        unfold value_of_expr. cbn2. 
        destruct hw_reg_state.[tf_reg tf_ctx v] eqn:Hval. 2-4: (* hammer. *) timeout 10 sauto.
        apply synth_convert_is_val_convert. cbn2. rewrite !all_vars_after_read_vars_correct. cbn2.
        (* hammer. *) timeout 10 hauto b: on.
      } { (* tf_op1 *)
        unfold value_of_expr. cbn2.
        rewrite IHexpr. cbn2. unfold opt_bind, UntypedSemantics.usigma1.
        prove_expr_is_bits expr hw_reg_state f_dst H. 
      } { (* tf_op2 *)
        cbn2.
        destruct op.
        {
          cbn2. rewrite IHexpr1. cbn2. rewrite IHexpr2. cbn2.
          prove_expr_is_bits expr1 hw_reg_state f_dst H. prove_expr_is_bits expr2 hw_reg_state f_dst H.
          cbn2. reflexivity.
        }
        {
          cbn2. rewrite IHexpr1. cbn2. rewrite IHexpr2. cbn2.
          prove_expr_is_bits expr1 hw_reg_state f_dst H. prove_expr_is_bits expr2 hw_reg_state f_dst H.
          cbn2. reflexivity.
        }
        {
          cbn2. rewrite IHexpr1. cbn2. rewrite IHexpr2. cbn2.
          prove_expr_is_bits expr1 hw_reg_state f_dst H. prove_expr_is_bits expr2 hw_reg_state f_dst H.
          cbn2. reflexivity.
        }
        {
          cbn2. rewrite IHexpr1. cbn2. rewrite IHexpr2. cbn2.
          prove_expr_is_bits expr1 hw_reg_state f_dst H. prove_expr_is_bits expr2 hw_reg_state f_dst H.
          cbn2. reflexivity.
        }
        {
          cbn2. rewrite IHexpr1. cbn2. rewrite IHexpr2. cbn2.
          prove_expr_is_bits expr1 hw_reg_state f_dst H. prove_expr_is_bits expr2 hw_reg_state f_dst H.
          cbn2. reflexivity.
        }
        { 
          apply synth_convert_is_val_convert. cbn2.
          rewrite IHexpr1. cbn2. rewrite IHexpr2. cbn2.
          prove_expr_is_bits expr1 hw_reg_state f_dst H. prove_expr_is_bits expr2 hw_reg_state f_dst H.
          cbn2. split; try reflexivity. subst.
          rewrite vect_to_list_length. lia.   
        }
        {
          destruct cmp_op. 
          all:
          ( 
            apply synth_convert_is_val_convert; cbn2;
            rewrite IHexpr1; cbn2; rewrite IHexpr2; cbn2;
            prove_expr_is_bits expr1 hw_reg_state f_dst H; prove_expr_is_bits expr2 hw_reg_state f_dst H;
            cbn2; split; try reflexivity; subst; destr; destruct Heqs; cbn2; reflexivity   
          ).
        }
      } 
    Qed.

    Lemma val_convert_correct:
      forall {szC} szA szB ( x : bits_t szC ),
        (szA = szC) ->
        val_convert szB szA (Bits (vect_to_list x)) = Bits (vect_to_list (convert (szA:=szC) (szB:=szB) x)).
    Proof.
      intros. unfold val_convert, bits_of_value_lossy, convert. cbn -[Nat.ltb].
      destruct (Nat.eq_dec szB szA).
      { destruct e. destruct Nat.eq_dec. 2: congruence. simpl. destruct e. reflexivity. }
      {
        destruct (Nat.leb szA szB) eqn:Hle.
        { (* szB < szA *) 
          apply Nat.leb_le in Hle. destr. destr. destruct (__convert_le szC szB l). simpl.
          unfold Bits.extend_end. destruct (vect_extend_end_cast szC szB). simpl.
          assert ((szC + (szB - szC) - szA) = (szB - szC)) by lia. rewrite H0. clear H0.
          rewrite vect_to_list_app. rewrite BitsToLists.repeat_bits_const. reflexivity.
        } {
          (* szA < szB *)
          apply leb_iff_conv in Hle. destruct Nat.eq_dec. congruence.
          destr. lia.
          unfold Bits.slice. rewrite BitsToLists.vect_extend_end_firstn. unfold Bits.extend_end.
          destruct (vect_extend_end_cast (Nat.min szB (szC - 0)) szB). simpl.
          assert ((szB - Nat.min szB (szC - 0)) = 0) by lia. rewrite H0. clear H0. cbn.
          rewrite vect_to_list_app. rewrite app_nil_r. rewrite vect_to_list_firstn. rewrite vect_to_list_skipn.
          rewrite skipn_O. reflexivity. 
        }
      }
    Qed.

    Lemma val_convert_correct2:
      forall szB bl,
        (Datatypes.length bl <= 1) -> 
        val_convert szB 1 (Bits bl) = 
        Bits (
          match bl with
          | [] => repeat false (szB - 1)
          | x :: xs => vect_to_list ( if x then Bits.of_positive szB 1 else Bits.zeroes szB )
          end
        ).
    Proof.
      intros. unfold val_convert, bits_of_value_lossy, convert. cbn2.
      destruct bl.
      {
        destr. rewrite Common.repeat_nil by lia; reflexivity.
        destr. rewrite app_nil_l. reflexivity.
        assert (szB = 0) by sauto. subst. reflexivity.
      }
      {
        assert (bl = []). {
          destruct bl; try reflexivity.
          simpl in H. lia.
        }
        subst. destr.
        - subst. f_equal. cbn2. destr; reflexivity.
        - destr; destruct szB; try congruence; destr. 
          + induction szB. congruence. unfold vect_to_list.
            cbn2. rewrite Common.vect_fold_left_of_zeros. rewrite app_nil_r. reflexivity.
          + induction szB. congruence. unfold vect_to_list.
            cbn2. rewrite Common.vect_fold_left_of_zeros. rewrite app_nil_r. reflexivity.
          + reflexivity.
          + reflexivity.
      }
    Qed.

    Lemma value_of_expr_correct:
      forall expr hw_reg_state fs_state state_var, 
        ( forall x : spec_states, hw_reg_state.[tf_reg tf_ctx x] = Bits (vect_to_list (fs_state.[x])) ) ->
      value_of_expr expr hw_reg_state (spec_states_size state_var) 
      = Bits (vect_to_list (n:=(spec_states_size state_var)) (tf_eval_expr spec_states spec_states_fin spec_states_size expr fs_state)).
    Proof.
      intros.

      induction expr. 
      { (* tf_const *)
        cbn2. reflexivity.
      } 
      { (* tf_var *)
        cbn2;  rewrite (H v). rewrite val_convert_correct; reflexivity. 
      }
      { (* tf_op1 *)
        cbn2;  rewrite IHexpr. cbn2. destruct op.
        unfold Bits.neg, Bits.map. rewrite vect_to_list_map. reflexivity.
      }
      {
        cbn2;  rewrite IHexpr1. rewrite IHexpr2. cbn2. destruct op.
        - f_equal. apply BitsToLists.and_correct'.
        - f_equal. apply BitsToLists.or_correct'.
        - f_equal. apply BitsToLists.xor_correct'.
        - f_equal. unfold Bits.plus. rewrite !Common.bits_of_list_vect_to_list. rewrite !Bits.to_N_rew. rewrite vect_to_list_length. reflexivity.
        - f_equal. unfold Bits.minus. rewrite !Common.bits_of_list_vect_to_list. rewrite !BitsToLists.bits_map_rew.  rewrite !Bits.to_N_rew. rewrite !vect_to_list_length. reflexivity.
        - rewrite val_convert_correct. 2: { rewrite !vect_to_list_length. reflexivity. }
          rewrite !Common.bits_of_list_vect_to_list. rewrite !Bits.to_N_rew. rewrite !vect_to_list_length. reflexivity.
        - destr.
          * rewrite val_convert_correct2. 2: { destr; unfold Datatypes.length. all: lia. } 
            repeat f_equal. destruct BitsToLists.list_eqb eqn:Heqb.
              {
                rewrite (BitsToLists.list_eqb_correct _ Bool.eqb_true_iff) in Heqb.
                unfold beq_dec. apply vect_to_list_inj in Heqb. destruct (eq_dec _ _); try congruence.
              }
              {
                rewrite <- Bool.not_true_iff_false, (BitsToLists.list_eqb_correct _ Bool.eqb_true_iff) in Heqb.
                unfold beq_dec. destruct (eq_dec _ _); try congruence.
              }
          * rewrite val_convert_correct2. 2: { destr; unfold Datatypes.length. all: lia. } 
            repeat f_equal. destruct BitsToLists.list_eqb eqn:Heqb.
              {
                rewrite (BitsToLists.list_eqb_correct _ Bool.eqb_true_iff) in Heqb.
                unfold beq_dec. apply vect_to_list_inj in Heqb. destruct (eq_dec _ _); try congruence.
              }
              {
                rewrite <- Bool.not_true_iff_false, (BitsToLists.list_eqb_correct _ Bool.eqb_true_iff) in Heqb.
                unfold beq_dec. destruct (eq_dec _ _); try congruence.
              }
          * rewrite val_convert_correct2. 2: { destr; unfold Datatypes.length. all: lia. } 
            repeat f_equal. destruct Nat.eq_dec. 
            + unfold Bits.unsigned_lt in *; unfold Bits.lift_comparison in *.
              rewrite !Koika.BitsToLists.vect_of_list_to_list, !Bits.to_N_rew.
              reflexivity.
            + rewrite !vect_to_list_length in n.
              unfold Bits.unsigned_lt in *; unfold Bits.lift_comparison in *.
              destr.
          * rewrite val_convert_correct2. 2: { destr; unfold Datatypes.length. all: lia. } 
            repeat f_equal. destruct Nat.eq_dec. 
            + unfold Bits.unsigned_le in *; unfold Bits.lift_comparison in *.
              rewrite !Koika.BitsToLists.vect_of_list_to_list, !Bits.to_N_rew.
              reflexivity.
            + rewrite !vect_to_list_length in n.
              unfold Bits.unsigned_le in *; unfold Bits.lift_comparison in *.
              destr.
          * rewrite val_convert_correct2. 2: { destr; unfold Datatypes.length. all: lia. } 
            repeat f_equal. destruct Nat.eq_dec. 
            + unfold Bits.unsigned_gt in *; unfold Bits.lift_comparison in *.
              rewrite !Koika.BitsToLists.vect_of_list_to_list, !Bits.to_N_rew.
              reflexivity.
            + rewrite !vect_to_list_length in n.
              unfold Bits.unsigned_gt in *; unfold Bits.lift_comparison in *.
              destr.
          * rewrite val_convert_correct2. 2: { destr; unfold Datatypes.length. all: lia. } 
            repeat f_equal. destruct Nat.eq_dec. 
            + unfold Bits.unsigned_ge in *; unfold Bits.lift_comparison in *.
              rewrite !Koika.BitsToLists.vect_of_list_to_list, !Bits.to_N_rew.
              reflexivity.
            + rewrite !vect_to_list_length in n.
              unfold Bits.unsigned_ge in *; unfold Bits.lift_comparison in *.
              destr.
      }
    Qed.

  End Expressions.

  Section CmdGuard.
    
    Lemma interp_rule_wrong_cmd:
      forall (hw_reg_state: hw_env_t) log cmd,
      sigma (ext_in_cmd tf_ctx) val_true <> encoded_cmd cmd ->
      UntypedSemantics.interp_rule hw_reg_state sigma log (impl_rules (rule_cmd tf_ctx cmd)) = None.
    Proof.
      intros.
      unfold impl_rules, rules, _rule_cmd.
      unfold UntypedSemantics.interp_rule, UntypedSemantics.interp_action.

      cbn.

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
      
      apply HSigmaValCmd. clear HSigmaValCmd.
      generalize (sigma_ext_in_cmd_is_struct cmd (Bits [true])); intros.
      rewrite <- H_sigma_val in *. subst sigma_val. 

      destruct H0 as [valid' [cmd_encoding H_sigma_struct]].
      rewrite H_sigma_struct in *.
      repeat f_equal. all: (* hammer. *) timeout 10 hauto.
    Qed.

    Lemma interp_scheduler_no_cmd:
      forall (hw_reg_state: hw_env_t) cmd log (l: list spec_action) sched,
      sigma (ext_in_cmd tf_ctx) val_true = encoded_cmd cmd ->
      (~ In cmd l) ->
      UntypedSemantics.interp_scheduler' impl_rules hw_reg_state sigma log 
        (fold_right (fun (t : spec_action) (acc : scheduler) => rule_cmd tf_ctx t |> acc) sched l)
        = UntypedSemantics.interp_scheduler' impl_rules hw_reg_state sigma log sched.
    Proof.
      intros.

      induction l. reflexivity.
      assert (~ In cmd l) as H0S.
      { intros H_in. apply H0. (* hammer. *) timeout 10 hauto. }
      specialize (IHl H0S). 
      cbn [fold_right UntypedSemantics.interp_scheduler'].
      rewrite IHl. clear IHl.

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
      UntypedSemantics.interp_rule hw_reg_state sigma log (impl_rules (rule_cmd tf_ctx cmd)) = 
      UntypedSemantics.interp_rule hw_reg_state sigma log (_rule_cmd tf_ctx cmd).
    Proof.
      intros.
      unfold impl_rules.
      unfold UntypedSemantics.interp_rule.
      unfold UntypedSemantics.interp_action.
      cbn -[_rule_cmd].

      set (sigma_val := sigma (ext_in_cmd tf_ctx) (Bits [true])) in *.
      assert (HSigmaValCmd: sigma_val = encoded_cmd cmd).
      { unfold sigma_val. exact H. } rewrite HSigmaValCmd in *. clear sigma_val HSigmaValCmd. clear H.
      cbn -[_rule_cmd].

      (* Help out with the comparison *)
      set (eq_true := BitsToLists.list_eqb _ _ _) in *.
      assert (eq_true = true).
      { unfold eq_true. apply BitsToLists.list_eqb_refl. (* hammer. *) timeout 10 sfirstorder using eqb_true_iff. } rewrite H in *; clear H. clear eq_true.

      unfold opt_bind.
      cbn.
      reflexivity.
    Qed.

    Definition assignments_added (hw_reg_state: hw_env_t) cmd :=
      match spec_action_ops cmd with
        | tf_nop _ _ _ => [ ]
        | tf_assign _ _ _ x expr => [ ( _reg_name tf_ctx x, value_of_expr expr hw_reg_state (spec_states_size x) ) ]
        | tf_input _ _ _ x y => [ (_reg_name tf_ctx x, val_convert (spec_states_size x) (spec_inputs_size y) (sigma (ext_input tf_ctx y) (Bits [true])) )]
        | tf_output _ _ _ x y => [ (_out_name tf_ctx x, val_convert (spec_outputs_size x) (spec_states_size y) hw_reg_state.[tf_reg tf_ctx y]) ]
      end.

    Definition log_after_rule_right_cmd (hw_reg_state: hw_env_t) cmd :=
      let Gamma' := assignments_added hw_reg_state cmd
                      ++ Gamma_after_act_read_state_vars hw_reg_state [] UntypedLogs.log_empty UntypedLogs.log_empty spec_all_states
      in
      Some
        (log_after_act_write_output_vars hw_reg_state UntypedLogs.log_empty
          (log_after_act_write_state_vars hw_reg_state UntypedLogs.log_empty
            (log_after_act_read_state_vars hw_reg_state UntypedLogs.log_empty UntypedLogs.log_empty spec_all_states) 
            (written_vars (spec_action_ops cmd))
            Gamma') 
          (written_outputs (spec_action_ops cmd))
          Gamma'
        ).

    Local Ltac tac_interp_rule_right_cmd_vars1 hw_reg_state reg combined_log s := 
          intros; subst reg; subst combined_log; unfold UntypedLogs.log_existsb in *;
          repeat (unfold getenv || rewrite !cassoc_ccreate || rewrite app_nil_l || rewrite app_nil_r); cbn;
          repeat (unfold getenv || rewrite !cassoc_ccreate || rewrite app_nil_l || rewrite app_nil_r); cbn;

          generalize (log_after_act_read_state_vars_no_state_read_writes hw_reg_state spec_all_states s); intros;
          unfold UntypedLogs.log_existsb, getenv in *; cbn; (* hammer. *) timeout 10 hauto lq: on.

    Local Ltac tac_interp_rule_right_cmd_vars2 hw_reg_state s := 
          intros; generalize (all_vars_after_read_vars_correct hw_reg_state s); intros Hvars_correct;
          cbn2; try (destruct (string_rec _ _ _ _); (* hammer. *) timeout 10 sauto);
          cbn2; rewrite Hvars_correct; (* hammer *) timeout 10 hauto lq: on.  

    Local Ltac tac_interp_rule_right_cmd_out1 := 
          intros o reg combined_log Hwritten; unfold written_outputs in Hwritten; cbn in Hwritten;
          apply filter_In in Hwritten; (* hammer. *) timeout 10 hauto lq: on.
    
    Local Ltac tac_interp_rule_right_cmd_out2 :=
          intros o Hwritten; unfold written_outputs in Hwritten; cbn in Hwritten;
          apply filter_In in Hwritten; (* hammer. *) timeout 10 hauto lq: on.
        
    Local Ltac tac_interp_rule_right_cmd_out3 hw_reg_state :=
          intros o reg combined_log Hwritten; subst reg; subst combined_log;
          unfold UntypedLogs.log_existsb in *;
          repeat (unfold getenv || rewrite !cassoc_ccreate || rewrite app_nil_l || rewrite app_nil_r); cbn -[_reg_name _out_name] in *;
          repeat (unfold getenv || rewrite !cassoc_ccreate || rewrite app_nil_l || rewrite app_nil_r); cbn -[_reg_name _out_name] in *;

          unfold log_after_act_write_state_vars in *;
          set (Hwritten_s := written_vars _);
          assert (H2: Hwritten_s = []) by (
            unfold Hwritten_s, written_vars; cbn;
            induction spec_all_states as [| s l IHl]; try reflexivity; cbn; exact IHl
          ); rewrite H2; clear H2;

          cbn -[_reg_name _out_name] in *;

          generalize (log_after_act_read_state_vars_no_output_read_writes hw_reg_state spec_all_states o); intros;
          unfold UntypedLogs.log_existsb, getenv in *; cbn in *; (* hammer; *) timeout 10 hauto lq: on.

    Local Ltac tac_interp_rule_right_cmd_out4 y :=
          intros o Hwritten;
            
          assert (y = o) by (
            unfold written_outputs in Hwritten; cbn -[spec_no_output_dec] in Hwritten; apply filter_written_outputs in Hwritten;
            unfold not in Hwritten; unfold tf_op_no_output in Hwritten; cbn in Hwritten;
            unfold when_outputs_match in Hwritten; destruct (eq_dec y o) as [e | n]; try (rewrite e; reflexivity);
            exfalso; apply Hwritten; intros; reflexivity
          ); subst y;
          
          cbn -[_reg_name _out_name] in *; destruct string_rec as [e | n]; try apply out_name_inj' in n; (* hammer. *) timeout 10 hauto lq: on. 

    Lemma interp_rule_right_cmd:
      forall (hw_reg_state: hw_env_t) cmd,
      sigma (ext_in_cmd tf_ctx) val_true = encoded_cmd cmd ->
      (forall s, exists bl, hw_reg_state.[tf_reg tf_ctx s] = Bits bl /\ Datatypes.length bl = spec_states_size s) ->
      UntypedSemantics.interp_rule hw_reg_state sigma UntypedLogs.log_empty (rules tf_ctx (rule_cmd tf_ctx cmd)) = 
        log_after_rule_right_cmd hw_reg_state cmd.
    Proof.
      intros.
      unfold log_after_rule_right_cmd, assignments_added, bits_of_value_lossy, val_convert.
      rewrite interp_rule_right_cmd' with (1:=H). unfold _rule_cmd.
      unfold UntypedSemantics.interp_rule. 
      rewrite interp_act_read_state_vars. 2: { intros. apply Common.log_existsb_empty. }
      cbn2. unfold _rule_aux, op_to_uaction. 

      destruct (spec_action_ops cmd).
      { (* NOP *)
        rewrite interp_act_write_state_vars.
        2: tac_interp_rule_right_cmd_vars1 hw_reg_state reg combined_log s.
        2: tac_interp_rule_right_cmd_vars2 hw_reg_state s.

        rewrite (interp_act_write_output_vars (REnv:=RegCEnv)). reflexivity.
        tac_interp_rule_right_cmd_out1.
        tac_interp_rule_right_cmd_out2.
      }
      { (* ASSIGN *)
        generalize (interp_act_expr_to_uaction expr (spec_states_size dst) hw_reg_state H0); intros Hinterp_expr.
        cbn2. 

        rewrite Hinterp_expr; clear Hinterp_expr; cbn2.
        
        rewrite interp_act_write_state_vars.
        2: tac_interp_rule_right_cmd_vars1 hw_reg_state reg combined_log s.
        2: tac_interp_rule_right_cmd_vars2 hw_reg_state s. 

        rewrite (interp_act_write_output_vars (REnv:=RegCEnv)). reflexivity.
        tac_interp_rule_right_cmd_out1.
        tac_interp_rule_right_cmd_out2.
      }
      { (* INPUT *)
        unfold synth_convert.
        cbn -[_reg_name _out_name Nat.ltb] in *. 
        destruct (Nat.eq_dec (spec_states_size dst) (spec_inputs_size src)).
        { (* Sizes match *)
          cbn -[_reg_name _out_name] in *.
          rewrite interp_act_write_state_vars.
          2: tac_interp_rule_right_cmd_vars1 hw_reg_state reg combined_log s.
          2: tac_interp_rule_right_cmd_vars2 hw_reg_state s.

          rewrite (interp_act_write_output_vars (REnv:=RegCEnv)). reflexivity.
          tac_interp_rule_right_cmd_out1.
          tac_interp_rule_right_cmd_out2.
        } { (* Size Conversion *)
          destruct (Nat.leb (spec_inputs_size src) (spec_states_size dst)) eqn:Hle.
          { (* Input smaller than state, zero-extend *)
            cbn -[_reg_name _out_name] in *.
            specialize (sigma_valid (ext_input tf_ctx src) (Bits [true])) as Hvalid. destruct Hvalid as [input Hinput].
            rewrite Hinput in *. cbn -[_reg_name _out_name] in *.
            rewrite interp_act_write_state_vars.
            2: tac_interp_rule_right_cmd_vars1 hw_reg_state reg combined_log s.
            2: tac_interp_rule_right_cmd_vars2 hw_reg_state s.

            rewrite (interp_act_write_output_vars (REnv:=RegCEnv)). cbn -[_reg_name _out_name] in *.
            rewrite vect_to_list_length. reflexivity.
            tac_interp_rule_right_cmd_out1.
            tac_interp_rule_right_cmd_out2.
          } { (* Input larger than state, truncate *)
            cbn -[_reg_name _out_name Nat.ltb] in *.
            specialize (sigma_valid (ext_input tf_ctx src) (Bits [true])) as Hvalid. destruct Hvalid as [input Hinput].
            rewrite Hinput in *. cbn -[_reg_name _out_name Nat.ltb] in *.
            rewrite interp_act_write_state_vars.
            2: tac_interp_rule_right_cmd_vars1 hw_reg_state reg combined_log s.
            2: tac_interp_rule_right_cmd_vars2 hw_reg_state s.

            rewrite (interp_act_write_output_vars (REnv:=RegCEnv)). cbn -[_reg_name _out_name Nat.ltb] in *.
            rewrite firstn_length. rewrite vect_to_list_length. rewrite Common.repeat_nil by ((* hammer *) timeout 10 hauto b: on).
            rewrite app_nil_r. reflexivity.
            tac_interp_rule_right_cmd_out1.
            tac_interp_rule_right_cmd_out2.
          }
        }
      }
      { (* OUTPUT *)
        unfold synth_convert.
        generalize (all_vars_after_read_vars_correct hw_reg_state). intros.
        cbn -[_reg_name _out_name Nat.ltb] in *. 

        destruct (Nat.eq_dec (spec_outputs_size dst) (spec_states_size src)).
        { (* Sizes match *)
          clear e. cbn -[_reg_name _out_name] in *.
          rewrite (H1 src). cbn -[_reg_name _out_name Nat.ltb] in *. destruct (H0 src) as [bl [Hbl Hblsize]].
          rewrite Hbl. cbn -[_reg_name _out_name Nat.ltb] in *. 

          rewrite interp_act_write_state_vars.
          2: tac_interp_rule_right_cmd_vars1 hw_reg_state reg combined_log s.
          2: tac_interp_rule_right_cmd_vars2 hw_reg_state s.

          clear H1.
          rewrite (interp_act_write_output_vars (REnv:=RegCEnv)). reflexivity.
          tac_interp_rule_right_cmd_out3 hw_reg_state.
          tac_interp_rule_right_cmd_out4 dst.
        } { (* Size Conversion *)
          clear n.
          destruct (Nat.leb (spec_states_size src) (spec_outputs_size dst)) eqn:Hle.
          (* Output smaller than state, truncate *)
          { 
            cbn -[_reg_name _out_name Nat.ltb] in *.
            rewrite (H1 src). cbn -[_reg_name _out_name Nat.ltb] in *. destruct (H0 src) as [bl [Hbl Hblsize]].
            rewrite Hbl. cbn -[_reg_name _out_name Nat.ltb] in *. 

            rewrite interp_act_write_state_vars.
            2: tac_interp_rule_right_cmd_vars1 hw_reg_state reg combined_log s.
            2: tac_interp_rule_right_cmd_vars2 hw_reg_state s.

            clear H1.
            rewrite (interp_act_write_output_vars (REnv:=RegCEnv)). cbn -[_reg_name _out_name Nat.ltb] in *. rewrite Hblsize. reflexivity.
            tac_interp_rule_right_cmd_out3 hw_reg_state.
            tac_interp_rule_right_cmd_out4 dst.
          } { (* Output larger than state, zero-extend *)
            cbn -[_reg_name _out_name Nat.ltb] in *.
            rewrite (H1 src). cbn -[_reg_name _out_name Nat.ltb] in *. destruct (H0 src) as [bl [Hbl Hblsize]].
            rewrite Hbl. cbn -[_reg_name _out_name Nat.ltb] in *. 

            rewrite interp_act_write_state_vars.
            2: tac_interp_rule_right_cmd_vars1 hw_reg_state reg combined_log s.
            2: tac_interp_rule_right_cmd_vars2 hw_reg_state s.

            clear H1.
            rewrite (interp_act_write_output_vars (REnv:=RegCEnv)). cbn -[_reg_name _out_name Nat.ltb] in *.
            repeat f_equal. rewrite firstn_length. rewrite Hblsize. rewrite Common.repeat_nil. 2: (* hammer *) hauto b: on.
            rewrite app_nil_r. reflexivity.
            tac_interp_rule_right_cmd_out3 hw_reg_state.
            tac_interp_rule_right_cmd_out4 dst.
          }
        }
      }
    Qed.

    Definition interp_rule_out_result (hw_reg_state : hw_env_t)
        (log : @UntypedLogs._ULog val (reg_t tf_ctx) (@ContextEnv impl_reg impl_regs_finite)) (out : spec_outputs) := 
      let ack_result :=
        sigma (ext_output tf_ctx out)
          match
            list_find_opt UntypedLogs.log_latest_write0_fn
              (ccreate impl_all_regs (fun (k : reg_t tf_ctx) (_ : member k impl_all_regs) => 
                log.[k])).[tf_out tf_ctx out]
          with
          | Some v => v
          | None => hw_reg_state.[tf_out tf_ctx out]
          end
      in
        UntypedLogs.log_cons (REnv:=RegCEnv) (tf_out_ack tf_ctx out) 
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
      UntypedSemantics.interp_rule hw_reg_state sigma log (impl_rules (rule_out tf_ctx out)) = 
      Some(
        interp_rule_out_result hw_reg_state log out
      ). 
    Proof.
      intros.
      unfold interp_rule_out_result, impl_rules, rules, _rule_cmd.
      unfold UntypedSemantics.interp_rule, UntypedSemantics.interp_action.

      cbn2. repeat f_equal. rewrite H. clear H. cbn.

      (* Have we written to out this out ack this cycle? *)
      set (has_w_ack := UntypedLogs.log_existsb _ _ _).
      assert (has_w_ack = false). {
        subst has_w_ack.
        unfold UntypedLogs.log_existsb in *.
        
        unfold getenv in *. cbn [ContextEnv] in *.
        rewrite !cassoc_ccreate. unfold UntypedLogs.RLog in *. rewrite Common.cassoc_put_neq. 
        rewrite !cassoc_ccreate. rewrite app_nil_l. exact H0.
        (* hammer. *) timeout 10 sfirstorder.
      } rewrite H. clear H has_w_ack. cbn. cbn2. repeat f_equal.
      unfold getenv in *. cbn [ContextEnv] in *. rewrite !cassoc_ccreate. rewrite app_nil_l. reflexivity.
    Qed.

    Definition log_after_rules_out (hw_reg_state: hw_env_t) log := 
      fold_right (fun (t : spec_outputs) (acc: env_t ContextEnv (fun _ : reg_t tf_ctx => UntypedLogs.RLog val)) => 
        UntypedLogs.log_app (interp_rule_out_result hw_reg_state acc t) acc
      ) log (rev spec_all_outputs).
      
    Lemma interp_scheduler_outputs:
      forall other (hw_reg_state: hw_env_t) log,
        (forall o, In o spec_all_outputs -> UntypedLogs.log_existsb log (tf_out tf_ctx o) UntypedLogs.is_write1 = false) ->
        (forall o, In o spec_all_outputs -> UntypedLogs.log_existsb log (tf_out_ack tf_ctx o) UntypedLogs.is_write1 = false) ->
        UntypedSemantics.interp_scheduler' (rules tf_ctx) hw_reg_state sigma log
          (fold_right (fun (t : spec_outputs) (acc : scheduler) => rule_out tf_ctx t |> acc) other spec_all_outputs)
        =
        UntypedSemantics.interp_scheduler' (rules tf_ctx) hw_reg_state sigma (log_after_rules_out hw_reg_state log) other.
    Proof.
      intros. unfold log_after_rules_out.

      set (output_list := finite_elements) in *.
      assert (nodup: NoDup (output_list)).
      { apply NoDup_map_inv with (f:=(finite_index (FiniteType:=spec_outputs_fin))). apply finite_injective. }

      generalize dependent log.
      induction output_list.
      { (* hammer. *) timeout 10 hauto lq: on. }
      intros.
      cbn -[rules UntypedLogs.log_app interp_rule_out_result hw_env_t] in *.

      clean. rewrite interp_rule_out.
      { rewrite !IHoutput_list.
        { f_equal. cbn. clean. rewrite fold_right_app. cbn. reflexivity. }
        all: inversion nodup; subst. exact H4. 
        - intros. specialize (H o). destruct H. (* hammer *) timeout 10 fcrush. unfold UntypedLogs.log_existsb. 
          cbn. clean. unfold getenv. cbn. 
          rewrite !cassoc_ccreate.  clean. 
          rewrite !Common.cassoc_put_neq. rewrite !cassoc_ccreate. rewrite app_nil_l. reflexivity.
          (* hammer. *) timeout 10 sauto. (* hammer. *) timeout 10 sauto.
        - intros. specialize (H0 o). destruct H0. (* hammer *) timeout 10 fcrush. unfold UntypedLogs.log_existsb. 
          cbn. clean. unfold getenv. cbn. 
          rewrite !cassoc_ccreate.  clean. 
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

      {
        intros.
        unfold log_after_rules_out.
        set (output_list := (rev spec_all_outputs)) in *.
        induction output_list.
        try reflexivity.
        cbn -[interp_rule_out_result UntypedLogs.log_existsb env_t] in *.
        unfold interp_rule_out_result at 1.
        cbn -[interp_rule_out_result UntypedLogs.log_existsb env_t] in *.
        unfold UntypedLogs.log_existsb, getenv in *.
        clean. cbn -[interp_rule_out_result env_t] in *.
        repeat ( rewrite !Common.cassoc_put_neq || rewrite !cassoc_ccreate || rewrite !Common.cassoc_put_neq ).
        try rewrite app_nil_l. try exact IHoutput_list.
        (* hammer. *) timeout 10 hauto lq: on .
        (* hammer. *) timeout 10 hauto lq: on .
        (* hammer. *) timeout 10 hauto lq: on .
      }

      {
        intros.
        unfold log_after_rules_out.
        set (output_list := (rev spec_all_outputs)) in *.
        induction output_list.
        try reflexivity.
        cbn -[interp_rule_out_result UntypedLogs.log_existsb env_t] in *.
        unfold interp_rule_out_result at 1.
        cbn -[interp_rule_out_result UntypedLogs.log_existsb env_t] in *.
        unfold UntypedLogs.log_existsb, getenv in *.
        clean. cbn -[interp_rule_out_result env_t] in *.
        repeat ( rewrite !Common.cassoc_put_neq || rewrite !cassoc_ccreate || rewrite !Common.cassoc_put_neq ).
        try rewrite app_nil_l. try exact IHoutput_list.
        (* hammer. *) timeout 10 hauto lq: on .
        (* hammer. *) timeout 10 hauto lq: on .
        (* hammer. *) timeout 10 hauto lq: on .
      }

      {
        intros.
        unfold log_after_rules_out.
        set (output_list := (rev spec_all_outputs)) in *.
        induction output_list.
        try reflexivity.
        cbn -[interp_rule_out_result UntypedLogs.log_existsb env_t] in *.
        unfold interp_rule_out_result at 1.
        cbn -[interp_rule_out_result UntypedLogs.log_existsb env_t] in *.
        unfold UntypedLogs.log_existsb, getenv in *.
        clean. cbn -[interp_rule_out_result env_t] in *.
        repeat ( rewrite !Common.cassoc_put_neq || rewrite !cassoc_ccreate || rewrite !Common.cassoc_put_neq ).
        try rewrite app_nil_l. try exact IHoutput_list.
        (* hammer. *) timeout 10 hauto lq: on .
        (* hammer. *) timeout 10 hauto lq: on .
        (* hammer. *) timeout 10 hauto lq: on .
      }

      {
        intros.
        unfold log_after_rules_out.
        set (output_list := (rev spec_all_outputs)) in *.
        induction output_list.
        try reflexivity.
        cbn -[interp_rule_out_result UntypedLogs.log_existsb env_t] in *.
        unfold interp_rule_out_result at 1.
        cbn -[interp_rule_out_result UntypedLogs.log_existsb env_t] in *.
        unfold UntypedLogs.log_existsb, getenv in *.
        clean. cbn -[interp_rule_out_result env_t] in *.
        repeat ( rewrite !Common.cassoc_put_neq || rewrite !cassoc_ccreate || rewrite !Common.cassoc_put_neq ).
        try rewrite app_nil_l. try exact IHoutput_list.
        (* hammer. *) timeout 10 hauto lq: on .
        (* hammer. *) timeout 10 hauto lq: on .
        (* hammer. *) timeout 10 hauto lq: on .
      }
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
        unfold UntypedLogs.log_existsb, getenv in *.
        clean. cbn -[interp_rule_out_result env_t] in *.
        destruct (eq_dec a act).
        {
          subst a.
          repeat ( rewrite !Common.cassoc_put_eq || rewrite !cassoc_ccreate || rewrite Common.cassoc_put_neq ).
          all: (* hammer. *) timeout 10 hauto lq: on.
        } {
          repeat ( rewrite !Common.cassoc_put_neq || rewrite !cassoc_ccreate ).
          try rewrite app_nil_l; try exact IHoutput_list.
          all: (* hammer. *) timeout 10 hauto lq: on.
        }

      intros.
        unfold log_after_rules_out.
        set (output_list := (rev finite_elements)) in *.
        induction output_list.
        try reflexivity.
        cbn -[interp_rule_out_result UntypedLogs.log_existsb env_t] in *.
        unfold interp_rule_out_result at 1.
        cbn -[interp_rule_out_result UntypedLogs.log_existsb env_t] in *.
        unfold UntypedLogs.log_existsb, getenv in *.
        clean. cbn -[interp_rule_out_result env_t] in *.
        destruct (eq_dec a act).
        {
          subst a.
          repeat ( rewrite !Common.cassoc_put_eq || rewrite !cassoc_ccreate || rewrite Common.cassoc_put_neq ).
          all: (* hammer. *) timeout 10 hauto lq: on.
        } {
          repeat ( rewrite !Common.cassoc_put_neq || rewrite !cassoc_ccreate ).
          try rewrite app_nil_l; try exact IHoutput_list.
          all: (* hammer. *) timeout 10 hauto lq: on.
        }
      
      intros.
        unfold log_after_rules_out.
        set (output_list := (rev finite_elements)) in *.
        induction output_list.
        try reflexivity.
        cbn -[interp_rule_out_result UntypedLogs.log_existsb env_t] in *.
        unfold interp_rule_out_result at 1.
        cbn -[interp_rule_out_result UntypedLogs.log_existsb env_t] in *.
        unfold UntypedLogs.log_existsb, getenv in *.
        clean. cbn -[interp_rule_out_result env_t] in *.
        destruct (eq_dec a act).
        {
          subst a.
          repeat ( rewrite !Common.cassoc_put_eq || rewrite !cassoc_ccreate || rewrite Common.cassoc_put_neq ).
          all: (* hammer. *) timeout 10 hauto lq: on.
        } {
          repeat ( rewrite !Common.cassoc_put_neq || rewrite !cassoc_ccreate ).
          try rewrite app_nil_l; try exact IHoutput_list.
          all: (* hammer. *) timeout 10 hauto lq: on.
        }
    Qed.
    
    Ltac tac_interp_scheduler_writes_state_only_cmd_nowrite1 reg_a reg_b IHl := 
            cbn2; set (log := fold_right _ _ _); assert (n2: reg_a <> reg_b) by ( (* hammer. *) timeout 10 sauto );
            rewrite (Common.cassoc_log_cons_neq log (reg_a) (reg_b) _ n2); subst log; cbn -[_reg_name _out_name];
            apply IHl.
          
    Lemma interp_scheduler_writes_state_only_cmd (hw_reg_state: hw_env_t) cmd reg:
      ((exists state_var, tf_reg tf_ctx state_var = reg) \/ (exists out_var, tf_out tf_ctx out_var = reg)) ->
      sigma (ext_in_cmd tf_ctx) val_true = encoded_cmd cmd ->
      (forall s, exists bl, hw_reg_state.[tf_reg tf_ctx s] = Bits bl /\ Datatypes.length bl = spec_states_size s) ->
      UntypedLogs.latest_write (UntypedSemantics.interp_scheduler' impl_rules hw_reg_state sigma UntypedLogs.log_empty system_schedule) reg =
      UntypedLogs.latest_write (UntypedSemantics.interp_scheduler' impl_rules hw_reg_state sigma UntypedLogs.log_empty (rule_cmd tf_ctx cmd |> done)) reg.
    Proof.
      intros. unfold system_schedule, system_schedule_actions, system_schedule_outputs in *.

      set (action_list := (spec_all_actions)) in *.

      assert (H_nodup: NoDup (action_list)). {
        apply NoDup_map_inv with (f:=finite_index (FiniteType:=spec_action_fin)).
        apply finite_injective.
      }
      assert (H_in_l: In cmd action_list). {
        generalize (finite_surjective (FiniteType:=spec_action_fin) cmd). intros H2.
        apply nth_error_In with (finite_index (FiniteType:=spec_action_fin) cmd). exact H2.
      }

      induction (action_list). destruct H_in_l.
      
      destruct (eq_dec a cmd).
      {
        cbn [fold_right UntypedSemantics.interp_scheduler'] in *. clear IHl.
        subst a. assert (H_not_in_l: ~ In cmd l). { inversion H_nodup. timeout 10 sauto. }
      
        rewrite !(interp_scheduler_no_cmd hw_reg_state cmd). 2: exact H0. 2: exact H_not_in_l.

        rewrite (interp_rule_right_cmd hw_reg_state cmd H0 H1). 
        
        cbn [log_after_rule_right_cmd].
        rewrite !(interp_scheduler_no_cmd hw_reg_state cmd). 2: exact H0. 2: exact H_not_in_l.

        rewrite interp_scheduler_outputs.
        2: {
          intros o H_in. unfold UntypedLogs.log_existsb.
          unfold log_after_act_write_output_vars, log_after_act_write_state_vars, log_after_act_read_state_vars.
          
          repeat (unfold_getenv || rewrite !cassoc_ccreate || rewrite app_nil_l || rewrite app_nil_r).
          cbn [UntypedLogs.log_app map2 create RegCEnv].
          repeat (unfold_getenv || rewrite !cassoc_ccreate || rewrite app_nil_l || rewrite app_nil_r).

          rewrite <- !fold_left_rev_right.

          set (l1 := rev _).
          set (l2 := rev _).
          set (l3 := rev _).

          induction (l3).
          2: { 
            cbn [fold_right] in *.  
            destruct (eq_dec a o).
            { 
              subst a. set (log := fold_right _ _ _).
              rewrite (Common.cassoc_log_cons_eq log (tf_out tf_ctx o)). subst log. cbn [fold_right].
              apply IHl0. 
            }
            tac_interp_scheduler_writes_state_only_cmd_nowrite1 (tf_out tf_ctx a) (tf_out tf_ctx o) IHl0.
          }
          cbn [fold_right] in *.

          induction (l2).
          2: tac_interp_scheduler_writes_state_only_cmd_nowrite1 (tf_reg tf_ctx a) (tf_out tf_ctx o) IHl0.
          cbn [fold_right] in *.
          induction (l1).
          2: tac_interp_scheduler_writes_state_only_cmd_nowrite1 (tf_reg tf_ctx a) (tf_out tf_ctx o) IHl0.

          cbn [fold_right UntypedLogs.log_empty create RegCEnv]. 
          repeat (unfold_getenv || rewrite !cassoc_ccreate || rewrite app_nil_l || rewrite app_nil_r).
          reflexivity.
        }
        2: {
          intros o H_in. unfold UntypedLogs.log_existsb.
          unfold log_after_act_write_output_vars, log_after_act_write_state_vars, log_after_act_read_state_vars.
          
          repeat (unfold_getenv || rewrite !cassoc_ccreate || rewrite app_nil_l || rewrite app_nil_r).
          cbn [UntypedLogs.log_app map2 create RegCEnv].
          repeat (unfold_getenv || rewrite !cassoc_ccreate || rewrite app_nil_l || rewrite app_nil_r).

          rewrite <- !fold_left_rev_right.

          set (l1 := rev _).
          set (l2 := rev _).
          set (l3 := rev _).

          induction (l3).
          2: tac_interp_scheduler_writes_state_only_cmd_nowrite1 (tf_out tf_ctx a) (tf_out_ack tf_ctx o) IHl0.
          cbn [fold_right] in *.

          induction (l2).
          2: tac_interp_scheduler_writes_state_only_cmd_nowrite1 (tf_reg tf_ctx a) (tf_out_ack tf_ctx o) IHl0.
          cbn [fold_right] in *.

          induction (l1).
          2: tac_interp_scheduler_writes_state_only_cmd_nowrite1 (tf_reg tf_ctx a) (tf_out_ack tf_ctx o) IHl0.

          cbn [fold_right UntypedLogs.log_empty create RegCEnv]. 
          repeat (unfold_getenv || rewrite !cassoc_ccreate || rewrite app_nil_l || rewrite app_nil_r).
          reflexivity.
        }

        unfold log_after_rules_out.
        induction (rev finite_elements).
        { reflexivity. }
        cbn [UntypedSemantics.interp_scheduler' fold_right] in *.

        repeat (unfold_getenv_all || rewrite !cassoc_ccreate in * || rewrite app_nil_l in * || rewrite app_nil_r in *).
        unfold UntypedLogs.latest_write, UntypedLogs.log_find, UntypedLogs.RLog in *. 
        repeat (unfold_getenv_all || rewrite !cassoc_ccreate  in * || rewrite app_nil_l  in * || rewrite app_nil_r in *).

        set (log1 := interp_rule_out_result _ _ _ ). set (log2 := fold_right _ _ _).
        rewrite (Common.cassoc_log_app log1 log2 reg). subst log1. subst log2.
        
        unfold interp_rule_out_result, UntypedLogs.log_cons.
        cbn [fold_right] in *.

        destruct reg.
        { (* state_var *)
          rewrite Common.cassoc_put_neq by ((* hammer *) timeout 10 sauto). rewrite Common.cassoc_put_neq by ((* hammer *) timeout 10 sauto).

          cbn [fold_right UntypedLogs.log_empty create RegCEnv]. 
          repeat (unfold_getenv || rewrite !cassoc_ccreate || rewrite app_nil_l || rewrite app_nil_r).
          unfold UntypedLogs.RLog. 
          apply IHl0.
        }
        { (* out_var *)
          rewrite Common.cassoc_put_neq by ((* hammer *) timeout 10 sauto).
          destruct (eq_dec x a).
          { 
            subst a. rewrite Common.cassoc_put_eq.

            cbn [fold_right UntypedLogs.log_empty create RegCEnv]. 
            repeat (unfold_getenv || rewrite !cassoc_ccreate || rewrite app_nil_l || rewrite app_nil_r).
            unfold UntypedLogs.RLog. 
            apply IHl0.
          }
          {
            rewrite Common.cassoc_put_neq by ((* hammer *) timeout 10 sauto).
            
            cbn [fold_right UntypedLogs.log_empty create RegCEnv]. 
            repeat (unfold_getenv || rewrite !cassoc_ccreate || rewrite app_nil_l || rewrite app_nil_r).
            unfold UntypedLogs.RLog. 
            apply IHl0.
          }
        }
        { (* impossible *)
          contradict H. clear IHl0. (* hammer. *) timeout 10 hauto.
        }
      }
      {
        cbn [fold_right UntypedSemantics.interp_scheduler'] in *.
        rewrite interp_rule_wrong_cmd.
        {
          inversion H_in_l. congruence.
          inversion H_nodup. subst l0 x.
          destruct (eq_dec l []).   
          { subst l. contradiction. }

          rewrite IHl. all: (* hammer *) timeout 10 hauto lq: on.
        }
        {
          unfold not. intros. assert (encoded_cmd cmd = encoded_cmd a). { rewrite <- H0. rewrite H2. reflexivity. } 
          apply encoded_cmd_inj' in H3. contradiction. auto.
        }
      }
    Qed.
    
  End CmdGuard.


  (* Prove next HW cycle = next Spec cycle *)

  Definition _ur (x: impl_reg) := val_of_value (impl_r x).
  Definition initial_hw_state := 
      RegCEnv.(create) _ur.
  Definition next_hw_cycle (hw_reg_state: hw_env_t) := 
    UntypedSemantics.interp_cycle impl_rules hw_reg_state sigma system_schedule.

  (* TODO: Update once we have operation lists as input *)
  Local Notation spec_step :=  (tf_op_step_commit spec_states spec_states_fin spec_inputs spec_outputs spec_states_size spec_inputs_size).
  Local Notation spec_op_step_writes :=  (tf_op_step_writes spec_states spec_states_fin spec_inputs spec_outputs spec_states_size spec_inputs_size).
  Local Notation spec_step_outputs := (tf_op_outputs spec_states spec_states_fin spec_inputs spec_outputs spec_outputs_fin spec_states_size spec_inputs_size spec_outputs_size).

  Local Notation spec_state_env_t := (ContextEnv (FT:=spec_states_fin).(env_t) spec_states_t).
  Local Notation spec_output_env_t := (ContextEnv (FT:=spec_outputs_fin).(env_t) spec_outputs_t).

  Definition StateR (hw_reg_state: hw_env_t) (fs_state: spec_state_env_t) :=
      forall x, hw_reg_state.[tf_reg tf_ctx x] = val_of_value (fs_state.[x]).

  Lemma StateR_means_state_bits:
    forall hw_reg_state fs_state,
    StateR hw_reg_state fs_state ->
    forall x,
      exists bl, hw_reg_state.[tf_reg tf_ctx x] = Bits bl /\ Datatypes.length bl = spec_states_size x.
  Proof.
      intros hw_reg_state fs_state H_state x.
      specialize (H_state x). unfold getenv in *. cbn in *.
      exists (vect_to_list (cassoc (finite_member x) fs_state)).
      split. (* hammer. *) timeout 10 sfirstorder.
      rewrite vect_to_list_length. reflexivity.
  Qed.

  Definition OutputR (hw_reg_state: hw_env_t) (fs_output: spec_output_env_t) :=
      forall x, hw_reg_state.[tf_out tf_ctx x] = val_of_value (fs_output.[x]).
  
  Definition InputR (fs_input: forall (x : spec_inputs), (type_denote (spec_inputs_t x))) :=
      forall x, val_of_value (fs_input x) = sigma (ext_input tf_ctx x) val_true.

  Theorem InitState_correct :
      StateR initial_hw_state (ContextEnv.(create) spec_states_init)
      /\ 
      OutputR initial_hw_state (ContextEnv.(create) (fun _ => Bits.zero)).
  Proof.
      split.
      {
        unfold initial_hw_state. intros x.
        rewrite getenv_create. rewrite getenv_create. (* hammer. *) timeout 10 hauto lq: on.
      } {
        unfold initial_hw_state. intros x.
        rewrite getenv_create. rewrite getenv_create. (* hammer. *) timeout 10 hauto lq: on.
      }
  Qed.
  
  Theorem NextState_correct:
      forall cmd fs_state hw_reg_state fs_input last_fs_output,
      sigma (ext_in_cmd tf_ctx) val_true = encoded_cmd cmd ->
      StateR hw_reg_state fs_state ->
      InputR fs_input ->
      OutputR hw_reg_state last_fs_output -> (
        StateR (next_hw_cycle hw_reg_state) (spec_step fs_state fs_input (spec_action_ops cmd))
        /\
        OutputR (next_hw_cycle hw_reg_state) (spec_step_outputs fs_state fs_input last_fs_output (spec_action_ops cmd))
      ).
  Proof.
      intros. rename H into H_sigma_eq_cmd. rename H0 into H_state. rename H1 into H_input. rename H2 into H_output.

      split.
      { (* States *)

        (* We consider each state var individually *)
        intros state_var.
        unfold next_hw_cycle, StateR, InputR, OutputR in *.

        unfold getenv in *. timeout 10 cbn in *. rewrite !cassoc_ccreate in *.
        unfold UntypedSemantics.interp_scheduler, tf_op_step_writes.

        rewrite (interp_scheduler_writes_state_only_cmd hw_reg_state cmd).
        2: (* hammer *) timeout 10 sfirstorder.
        2: apply H_sigma_eq_cmd.
        2: apply (StateR_means_state_bits hw_reg_state fs_state); exact H_state.

        cbn -[impl_rules]. 
        rewrite (interp_rule_right_cmd hw_reg_state).
        2: exact H_sigma_eq_cmd.
        2: apply (StateR_means_state_bits hw_reg_state fs_state); exact H_state.

         cbn -[UntypedLogs.log_empty]. unfold getenv in *. cbn -[UntypedLogs.log_empty] in *. rewrite !cassoc_ccreate in *.
        rewrite app_nil_r.

        (* Output wrapper did not write to state *)
        rewrite (log_after_act_write_output_vars_no_find_last_write_state hw_reg_state state_var).

        destruct (spec_action_ops cmd) eqn:H_ops.
        { (* Nop *)
          rewrite <- (H_state state_var).
          set (written_vars_list := (written_vars _)).
          
          destruct (ListDec.In_decidable list_decidable_eq_spec_states state_var written_vars_list).
          { contradict H. subst written_vars_list. unfold written_vars. cbn. unfold not ; intros. apply filter_In in H. (* hammer. *) timeout 10 sfirstorder. }

          rewrite (log_after_act_write_state_vars_no_find_last_write_state hw_reg_state state_var). 2: exact H.

          rewrite (log_after_act_read_state_vars_no_find_last_write hw_reg_state _ (tf_reg tf_ctx state_var)).
          reflexivity.
        } {
          (* Assign *)
          unfold when_vars_match.
          destruct (eq_dec dst state_var).
          { subst dst.
            set (written_vars_list := (written_vars _)).

            destruct (ListDec.In_decidable list_decidable_eq_spec_states state_var written_vars_list).
            2: { contradict H. subst written_vars_list. unfold written_vars.
                 apply filter_written_vars. unfold not.
                 unfold tf_op_var_not_written; intros.
                 specialize (H fs_state fs_input).
                 unfold tf_op_step_writes, when_vars_match in H.
                 rewrite eq_dec_refl in H. (* hammer. *) timeout 10 sfirstorder. 
                }

            rewrite (log_after_act_write_state_vars_find_last_write_state hw_reg_state state_var). 2: exact H.
            unfold assignments_added. rewrite H_ops. cbn -[_reg_name _out_name]. destruct string_rec.
            2: { contradict n. timeout 10 sauto. }

            apply (value_of_expr_correct expr hw_reg_state fs_state state_var H_state).
          }
          {
            set (written_vars_list := (written_vars _)).

            destruct (ListDec.In_decidable list_decidable_eq_spec_states state_var written_vars_list).
            { contradict H. subst written_vars_list. unfold written_vars.
              rewrite filter_written_vars. unfold not. intros. apply H. clear H.
              unfold tf_op_var_not_written; intros.
              unfold tf_op_step_writes, when_vars_match.
              (* hammer. *) hauto.
            }

            rewrite (log_after_act_write_state_vars_no_find_last_write_state hw_reg_state state_var). 2: exact H.
            rewrite (log_after_act_read_state_vars_no_find_last_write hw_reg_state _ (tf_reg tf_ctx state_var)).
            rewrite <- (H_state state_var). reflexivity.
          }
        } {
          (* Input *)
          unfold when_vars_match.
          destruct (eq_dec dst state_var).
          { subst dst.
            set (written_vars_list := (written_vars _)).

            destruct (ListDec.In_decidable list_decidable_eq_spec_states state_var written_vars_list).
            2: { contradict H. subst written_vars_list. unfold written_vars.
                 apply filter_written_vars. unfold not.
                 unfold tf_op_var_not_written; intros.
                 specialize (H fs_state fs_input).
                 unfold tf_op_step_writes, when_vars_match in H.
                 rewrite eq_dec_refl in H. (* hammer. *) timeout 10 sfirstorder. 
                }

            rewrite (log_after_act_write_state_vars_find_last_write_state hw_reg_state state_var). 2: exact H.
            unfold assignments_added. rewrite H_ops. cbn -[_reg_name _out_name]. destruct string_rec.
            2: { contradict n. timeout 10 sauto. }

            rewrite <- (H_input src).
            apply val_convert_correct.
            reflexivity.
          }
          {
            set (written_vars_list := (written_vars _)).

            destruct (ListDec.In_decidable list_decidable_eq_spec_states state_var written_vars_list).
            { contradict H. subst written_vars_list. unfold written_vars.
              rewrite filter_written_vars. unfold not. intros. apply H. clear H.
              unfold tf_op_var_not_written; intros.
              unfold tf_op_step_writes, when_vars_match.
              (* hammer. *) hauto.
            }

            rewrite (log_after_act_write_state_vars_no_find_last_write_state hw_reg_state state_var). 2: exact H.
            rewrite (log_after_act_read_state_vars_no_find_last_write hw_reg_state _ (tf_reg tf_ctx state_var)).
            rewrite <- (H_state state_var). reflexivity.
          }
        } {
          (* Output *)
          rewrite <- (H_state state_var).
          set (written_vars_list := (written_vars _)).
          
          destruct (ListDec.In_decidable list_decidable_eq_spec_states state_var written_vars_list).
          { contradict H. subst written_vars_list. unfold written_vars. cbn. unfold not ; intros. apply filter_In in H. (* hammer. *) timeout 10 sfirstorder. }

          rewrite (log_after_act_write_state_vars_no_find_last_write_state hw_reg_state state_var). 2: exact H.

          rewrite (log_after_act_read_state_vars_no_find_last_write hw_reg_state _ (tf_reg tf_ctx state_var)).
          reflexivity.
        }
      } {
        (* Outputs *)

        (* We consider each output individually *)
        intros out_var.
        unfold next_hw_cycle, StateR, InputR, OutputR in *.

        unfold getenv in *. timeout 10 cbn in *. rewrite !cassoc_ccreate in *.
        unfold UntypedSemantics.interp_scheduler, tf_op_step_outputs.

        rewrite (interp_scheduler_writes_state_only_cmd hw_reg_state cmd).
        2: (* hammer *) timeout 10 sfirstorder.
        2: apply H_sigma_eq_cmd.
        2: apply (StateR_means_state_bits hw_reg_state fs_state); exact H_state.

        cbn -[impl_rules]. 
        rewrite (interp_rule_right_cmd hw_reg_state).
        2: exact H_sigma_eq_cmd.
        2: apply (StateR_means_state_bits hw_reg_state fs_state); exact H_state.

         cbn -[UntypedLogs.log_empty]. unfold getenv in *. cbn -[UntypedLogs.log_empty] in *. rewrite !cassoc_ccreate in *.
        rewrite app_nil_r.

        destruct (spec_action_ops cmd) eqn:H_ops.
        all: try 
          (
            set (written_outputs_list := (written_outputs _));
            
            destruct (ListDec.In_decidable list_decidable_eq_spec_outputs out_var written_outputs_list);
            try ( contradict H; subst written_outputs_list; unfold written_outputs; cbn; unfold not ; intros; apply filter_In in H; (* hammer; *) timeout 10 sfirstorder );

            rewrite (log_after_act_write_output_vars_no_find_last_write_out hw_reg_state out_var); try exact H;
            rewrite (log_after_act_write_state_vars_no_find_last_write_out hw_reg_state out_var);
            rewrite (log_after_act_read_state_vars_no_find_last_write hw_reg_state _ (tf_out tf_ctx out_var));
            rewrite <- (H_output out_var); reflexivity
          ).
        (* Output *)
        unfold when_outputs_match.
        destruct (eq_dec dst out_var).
        { subst dst.
          set (written_outputs_list := (written_outputs _)).

          destruct (ListDec.In_decidable list_decidable_eq_spec_outputs out_var written_outputs_list).
          2: { contradict H. subst written_outputs_list. unfold written_outputs.
                apply filter_written_outputs. unfold not.
                unfold tf_op_no_output; intros.
                specialize (H fs_state).
                unfold tf_op_step_outputs, when_outputs_match in H.
                rewrite eq_dec_refl in H. (* hammer. *) timeout 10 sfirstorder. 
              }

          rewrite (log_after_act_write_output_vars_find_last_write_out hw_reg_state out_var). 2: exact H.
          unfold assignments_added. rewrite H_ops. cbn -[_reg_name _out_name]. destruct string_rec.
          2: { contradict n. timeout 10 sauto. }

          unfold getenv.  cbn. rewrite (H_state src).
          apply val_convert_correct.
          reflexivity.
        }
        {
          set (written_outputs_list := (written_outputs _)).

          destruct (ListDec.In_decidable list_decidable_eq_spec_outputs out_var written_outputs_list).
          { contradict H. subst written_outputs_list. unfold written_outputs.
            rewrite filter_written_outputs. unfold not. intros. apply H. clear H.
            unfold tf_op_no_output; intros.
            unfold tf_op_step_outputs, when_outputs_match.
            (* hammer. *) hauto.
          }

          rewrite (log_after_act_write_output_vars_no_find_last_write_out hw_reg_state out_var). 2: exact H.
          rewrite (log_after_act_write_state_vars_no_find_last_write_out hw_reg_state out_var).
          rewrite (log_after_act_read_state_vars_no_find_last_write hw_reg_state _ (tf_out tf_ctx out_var)).
          rewrite <- (H_output out_var). reflexivity.
        }
      }     
  Qed.

End CompositionalCorrectness.
