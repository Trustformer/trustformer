Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.
Require Koika.Properties.SemanticProperties.
Require Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.

Require Import Trustformer.v2.Syntax.
Require Import Trustformer.v2.Semantics.
Require Import Trustformer.v2.Synthesis.
Require Import Trustformer.v2.Utils.
Require Trustformer.v2.Properties.Common.
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


  (* Encoding of commands as bitvectors *)
  Definition _fs_cmd_encoding (a: some_fs_action) :=
    Bits.of_nat some_cmd_reg_size (@finite_index some_fs_action _ a).
  Definition _encoded_cmd (a: some_fs_action) : type_denote (maybe (bits_t some_cmd_reg_size)) :=
      (Ob~1, (_fs_cmd_encoding a, tt)).
  Definition encoded_cmd (a: some_fs_action) := val_of_value (_encoded_cmd a).

  Definition val_true := Bits ( [true] ).

  Ltac unfold_some_specs := 
    repeat (unfold some_fs_states_t in * || unfold some_R in * || unfold some_r in * || unfold some_rules in * || unfold some_system_schedule in * 
    || unfold some_reg_t in * || unfold some_cmd_reg_size in * || unfold some_reg_t_elements in * || unfold some_fs_state_elements in * 
    || unfold encoded_cmd in * || unfold _encoded_cmd in * || unfold _fs_cmd_encoding in * ).

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
      destruct valid_field_opt eqn:H_cmd_valid. 2: (* hammer *) sfirstorder.
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
      2: (* hammer. *) eauto using eqb_true_iff.
                      
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

    Lemma interp_rule_right_cmd:
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

    Definition interp_out_rule_result (hw_reg_state : hw_env_t) 
        (log : @UntypedLogs._ULog val (reg_t tf_ctx) (@ContextEnv some_reg_t some_reg_t_finite)) (out : spec_outputs tf_ctx) := 
      UntypedLogs.log_cons (REnv:=ULog_Renv) (tf_out_ack tf_ctx out) 
          {| UntypedLogs.kind := LogWrite; UntypedLogs.port := P1; UntypedLogs.val := sigma (ext_output tf_ctx out) hw_reg_state.[tf_out tf_ctx out] |}
          (
            UntypedLogs.log_cons (tf_out tf_ctx out) 
              {| UntypedLogs.kind := LogRead; UntypedLogs.port := P0; UntypedLogs.val := Bits [] |}
              UntypedLogs.log_empty 
          ).

    Lemma interp_out_rule:
      forall (hw_reg_state: hw_env_t) log out,
      UntypedLogs.log_existsb log (tf_out tf_ctx out) UntypedLogs.is_write1 = false ->
      UntypedLogs.log_existsb log (tf_out tf_ctx out) UntypedLogs.is_write0 = false ->
      UntypedLogs.log_existsb log (tf_out_ack tf_ctx out) UntypedLogs.is_write1 = false ->
      UntypedSemantics.interp_rule hw_reg_state sigma log (some_rules (rule_out tf_ctx out)) = 
      Some(
        interp_out_rule_result hw_reg_state log out
      ). 
    Proof.
      intros.
      unfold interp_out_rule_result, some_rules, rules, _rule_cmd.
      unfold UntypedSemantics.interp_rule, UntypedSemantics.interp_action.

      squash. rewrite H. rewrite H0. clear H H0. cbn.

      (* Have we written to out this out ack this cycle? *)
      set (has_w_ack := UntypedLogs.log_existsb _ _ _).
      assert (has_w_ack = false). {
        subst has_w_ack.
        unfold UntypedLogs.log_existsb in *.
        
        unfold getenv in *. cbn [ContextEnv] in *.
        rewrite !cassoc_ccreate. unfold UntypedLogs.RLog in *. rewrite Common.cassoc_put_neq. 
        rewrite !cassoc_ccreate. rewrite app_nil_l. exact H1.
        (* hammer. *) timeout 10 sfirstorder.
      } rewrite H. clear H has_w_ack. squash.
    Qed.

    Definition log_after_outputs (hw_reg_state: hw_env_t) log := 
      fold_right (fun (t : some_fs_outputs) (acc: env_t ContextEnv (fun _ : reg_t tf_ctx => UntypedLogs.RLog val)) => 
        UntypedLogs.log_app (interp_out_rule_result hw_reg_state acc t) acc
      ) log (rev finite_elements).
      
    Lemma interp_scheduler_only_outputs:
      forall other (hw_reg_state: hw_env_t) log,
        (forall o, In o finite_elements -> UntypedLogs.log_existsb log (tf_out tf_ctx o) UntypedLogs.is_write1 = false) ->
        (forall o, In o finite_elements -> UntypedLogs.log_existsb log (tf_out tf_ctx o) UntypedLogs.is_write0 = false) ->
        (forall o, In o finite_elements -> UntypedLogs.log_existsb log (tf_out_ack tf_ctx o) UntypedLogs.is_write1 = false) ->
        UntypedSemantics.interp_scheduler' (rules tf_ctx) hw_reg_state sigma log
          (fold_right (fun (t : some_fs_outputs) (acc : scheduler) => rule_out tf_ctx t |> acc) other finite_elements)
        =
        UntypedSemantics.interp_scheduler' (rules tf_ctx) hw_reg_state sigma (log_after_outputs hw_reg_state log) other.
    Proof.
      intros. unfold log_after_outputs.

      set (output_list := finite_elements) in *.
      assert (nodup: NoDup (output_list)).
      { apply NoDup_map_inv with (f:=finite_index). apply finite_injective. }

      generalize dependent log.
      induction output_list.
      { (* hammer. *) timeout 10 hauto lq: on. }
      intros.
      cbn -[rules UntypedLogs.log_app interp_out_rule_result hw_env_t] in *.

      unfold_clean. rewrite interp_out_rule.
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
      all: (* hammer *) hauto lq: on.
    Qed.

    Lemma log_after_outputs_no_state_read_writes:
      forall hw_reg_state log act,
      UntypedLogs.log_existsb (log_after_outputs hw_reg_state log) (tf_reg tf_ctx act) UntypedLogs.is_write0 =
      UntypedLogs.log_existsb log (tf_reg tf_ctx act) UntypedLogs.is_write0
      /\
      UntypedLogs.log_existsb (log_after_outputs hw_reg_state log) (tf_reg tf_ctx act) UntypedLogs.is_write1 =
      UntypedLogs.log_existsb log (tf_reg tf_ctx act) UntypedLogs.is_write1
      /\
      UntypedLogs.log_existsb (log_after_outputs hw_reg_state log) (tf_reg tf_ctx act) UntypedLogs.is_read0 =
      UntypedLogs.log_existsb log (tf_reg tf_ctx act) UntypedLogs.is_read0
      /\
      UntypedLogs.log_existsb (log_after_outputs hw_reg_state log) (tf_reg tf_ctx act) UntypedLogs.is_read1 =
      UntypedLogs.log_existsb log (tf_reg tf_ctx act) UntypedLogs.is_read1.
    Proof.
      split. 2: split. 3: split.

      all: (
        intros;
        unfold log_after_outputs;
        set (output_list := (rev finite_elements)) in *;
        induction output_list;
        try reflexivity;
        cbn -[interp_out_rule_result UntypedLogs.log_existsb env_t] in *;
        unfold interp_out_rule_result at 1;
        cbn -[interp_out_rule_result UntypedLogs.log_existsb env_t] in *;
        unfold UntypedLogs.log_existsb, getenv, ULog_Renv in *;
        unfold_clean; cbn -[interp_out_rule_result env_t] in *;
        repeat ( rewrite !Common.cassoc_put_neq || rewrite !cassoc_ccreate || rewrite !Common.cassoc_put_neq );
        try rewrite app_nil_l; try exact IHoutput_list;
        (* hammer. *) timeout 10 sfirstorder
      ).
    Qed.

    Lemma log_after_outputs_no_output_read_writes:
      forall hw_reg_state log act,
      UntypedLogs.log_existsb (log_after_outputs hw_reg_state log) (tf_reg tf_ctx act) UntypedLogs.is_write0 =
      UntypedLogs.log_existsb log (tf_reg tf_ctx act) UntypedLogs.is_write0
      /\
      UntypedLogs.log_existsb (log_after_outputs hw_reg_state log) (tf_reg tf_ctx act) UntypedLogs.is_write1 =
      UntypedLogs.log_existsb log (tf_reg tf_ctx act) UntypedLogs.is_write1
      /\
      UntypedLogs.log_existsb (log_after_outputs hw_reg_state log) (tf_reg tf_ctx act) UntypedLogs.is_read0 =
      UntypedLogs.log_existsb log (tf_reg tf_ctx act) UntypedLogs.is_read0
      /\
      UntypedLogs.log_existsb (log_after_outputs hw_reg_state log) (tf_reg tf_ctx act) UntypedLogs.is_read1 =
      UntypedLogs.log_existsb log (tf_reg tf_ctx act) UntypedLogs.is_read1.
    Proof.
      split. 2: split. 3: split.

      all: (
        intros;
        unfold log_after_outputs;
        set (output_list := (rev finite_elements)) in *;
        induction output_list;
        try reflexivity;
        cbn -[interp_out_rule_result UntypedLogs.log_existsb env_t] in *;
        unfold interp_out_rule_result at 1;
        cbn -[interp_out_rule_result UntypedLogs.log_existsb env_t] in *;
        unfold UntypedLogs.log_existsb, getenv, ULog_Renv in *;
        unfold_clean; cbn -[interp_out_rule_result env_t] in *;
        repeat ( rewrite !Common.cassoc_put_neq || rewrite !cassoc_ccreate || rewrite !Common.cassoc_put_neq );
        try rewrite app_nil_l; try exact IHoutput_list;
        (* hammer. *) timeout 10 sfirstorder
      ).
    Qed.

    (* --- TODO: Update below --- *)

    Lemma interp_scheduler_only_cmd:
      forall (hw_reg_state: hw_env_t) cmd state_var,
      sigma (ext_in_cmd tf_ctx) val_true = encoded_cmd cmd ->
      UntypedLogs.latest_write (UntypedSemantics.interp_scheduler some_rules hw_reg_state sigma some_system_schedule) (tf_reg tf_ctx state_var) =
      UntypedLogs.latest_write (UntypedSemantics.interp_scheduler some_rules hw_reg_state sigma ( rule_cmd tf_ctx cmd |> done )) (tf_reg tf_ctx state_var).
    Proof.
      intros.
      unfold UntypedSemantics.interp_scheduler.

      set (schedule := some_system_schedule) in *.
      unfold some_system_schedule, system_schedule, system_schedule_outputs, system_schedule_actions in *.
      unfold_all. cbn in schedule.

      set (action_order := finite_elements) in *.

      assert (NoDup (action_order)).
      {
        apply NoDup_map_inv with (f:=finite_index).
        apply finite_injective.
      }
      assert (action_order_some : action_order <> []).
      { 
        intros H_empty.
        subst action_order.
        generalize (finite_surjective cmd). intros H1.
        rewrite H_empty in H1.
        rewrite nth_error_nil in H1. inversion H1.
      }
      assert (action_order_has_cmd : In cmd action_order).
      { 
        subst action_order.
        generalize (finite_surjective cmd). intros H1.
        apply nth_error_In with (finite_index cmd). exact H1.
      }

      subst schedule.
      induction (action_order).
      { destruct action_order_some. reflexivity. }
      
      timeout 10 cbn -[some_rules UntypedLogs.log_empty].

      destruct (eq_dec a cmd).
      {
        subst a. assert (H_not_in_l: ~ In cmd l). { inversion H0. timeout 10 sauto. }
        
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
              (* hammer. *) timeout 10 hauto lq:on.
              (* hammer. *) timeout 10 sfirstorder.
              (* hammer. *) timeout 10 sauto lq:on.
              (* hammer. *) timeout 10 sfirstorder.
              exact H_in.                
            }
          }
        }

        case_eq (@UntypedSemantics.interp_rule pos_t var_t fn_name_t EqDec_string (reg_t tf_ctx) (ext_fn_t tf_ctx) (@ContextEnv some_reg_t some_reg_t_finite) hw_reg_state sigma (@UntypedLogs.log_empty val (reg_t tf_ctx) (@ContextEnv some_reg_t some_reg_t_finite)) (some_rules (rule_cmd tf_ctx cmd))).
        {
          intros. rewrite (interp_scheduler_no_cmd hw_reg_state cmd). reflexivity. exact H. exact H1.
        }
        {
          intros. rewrite (interp_scheduler_no_cmd hw_reg_state cmd). reflexivity. exact H. exact H1.
        }
      }
      {
        rewrite interp_rule_wrong_cmd.
        {
          inversion action_order_has_cmd. congruence.
          inversion H0. subst l0 x.
          destruct (eq_dec l []).
          { subst l. contradiction. }
          {
            apply IHl.
            timeout 10 sauto.
            timeout 10 sauto.
            timeout 10 sauto.
          }
        }
        {
          unfold not. intros. assert (encoded_cmd cmd = encoded_cmd a). { timeout 10 sauto. } apply encoded_cmd_inj' in H2. contradiction. timeout 10 sauto.
        }
      }
      
    Qed. 
    
    

  End CmdGuard.

  Section ActionInterpretation.

    Lemma interp_act_read_state_vars {REnv : Env some_reg_t} : 
      forall (hw_reg_state: hw_env_t) (Gamma: list (string * val)) sched_log action_log code state_list,
      (* Precondition: Ensure all reads performed by the wrapper will succeed. *)
      (forall (reg: some_reg_t), UntypedLogs.log_existsb sched_log reg UntypedLogs.is_write1 = false) ->

      UntypedSemantics.interp_action hw_reg_state sigma Gamma sched_log action_log (_rule_read_state_vars_rec tf_ctx state_list code) =
      
      (* 1. Pre-calculate the values of all state registers that would be read. *)
      let state_values := List.map (fun s =>
        let v := match UntypedLogs.latest_write0 (UntypedLogs.log_app action_log sched_log) (tf_reg tf_ctx s) with
                | Some v => v
                | None => hw_reg_state.[(tf_reg tf_ctx s)]
                end
        in (_reg_name tf_ctx s, v)
      ) (List.rev state_list) in

      (* 2. Pre-calculate the log entries that would be generated by these reads. *)
      let read_logs := List.fold_left (fun (acc_log: UntypedLogs._ULog) s =>
        UntypedLogs.log_cons (tf_reg tf_ctx s) (UntypedLogs.LE Logs.LogRead P1 (Bits [])) acc_log
      ) state_list action_log in

      (* 3. The result is equivalent to interpreting [code] with the pre-calculated
            context and log, then packaging the result. The final Gamma is unchanged
            because UBind cleans up after itself. *)
      match UntypedSemantics.interp_action hw_reg_state sigma (state_values ++ Gamma) sched_log read_logs code with
      | Some (final_log, v, Gamma') => Some (final_log, v, skipn (List.length state_list) Gamma')
      | None => None
      end.
    Proof.
      intros.

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

    Lemma interp_act_write_state_vars {REnv : Env some_reg_t} : 
      forall (hw_reg_state: hw_env_t) (Gamma: list (string * val)) sched_log action_log state_op,
      (* Precondition: Ensure all writes performed by the wrapper will succeed. *)
      (* (forall (reg: some_reg_t), UntypedLogs.log_existsb sched_log reg UntypedLogs.is_write0 = false) -> *)

      (* (forall (reg: some_reg_t), let combined_log := (@ccreate some_reg_t (fun _ : some_reg_t => list (UntypedLogs.LogEntry val)) (@finite_elements some_reg_t some_reg_t_finite)
              (fun (k : some_reg_t) (_ : @member some_reg_t k (@finite_elements some_reg_t some_reg_t_finite)) =>
              @app (UntypedLogs.LogEntry val) (@getenv some_reg_t (@ContextEnv some_reg_t some_reg_t_finite) (fun _ : some_reg_t => list (UntypedLogs.LogEntry val)) action_log k)
              (@getenv some_reg_t (@ContextEnv some_reg_t some_reg_t_finite) (fun _ : some_reg_t => list (UntypedLogs.LogEntry val)) sched_log k))) in
          (@UntypedLogs.log_existsb val some_reg_t (@ContextEnv some_reg_t some_reg_t_finite) combined_log reg UntypedLogs.is_read1 = false
          /\ @UntypedLogs.log_existsb val some_reg_t (@ContextEnv some_reg_t some_reg_t_finite) combined_log reg UntypedLogs.is_write1 = false
          /\ @UntypedLogs.log_existsb val some_reg_t (@ContextEnv some_reg_t some_reg_t_finite) combined_log reg UntypedLogs.is_write0 = false)) -> *)

      let written_vars := List.filter (fun s => if (tf_op_var_not_written_dec some_fs_states some_fs_states_fin some_fs_states_size s state_op) then false else true) some_fs_state_elements in

      (* Precondition: Ensure all writes performed by the wrapper will succeed. *)
      (* (forall (reg: some_reg_t), UntypedLogs.log_existsb sched_log reg UntypedLogs.is_write0 = false) -> *)

      (forall s, let reg := tf_reg tf_ctx s in let combined_log := (@ccreate some_reg_t (fun _ : some_reg_t => list (UntypedLogs.LogEntry val)) (@finite_elements some_reg_t some_reg_t_finite)
              (fun (k : some_reg_t) (_ : @member some_reg_t k (@finite_elements some_reg_t some_reg_t_finite)) =>
              @app (UntypedLogs.LogEntry val) (@getenv some_reg_t (@ContextEnv some_reg_t some_reg_t_finite) (fun _ : some_reg_t => list (UntypedLogs.LogEntry val)) action_log k)
              (@getenv some_reg_t (@ContextEnv some_reg_t some_reg_t_finite) (fun _ : some_reg_t => list (UntypedLogs.LogEntry val)) sched_log k))) in
          In s written_vars -> @UntypedLogs.log_existsb val some_reg_t (@ContextEnv some_reg_t some_reg_t_finite) combined_log reg UntypedLogs.is_write1 = false) ->

      (* Precondition: Ensure all written vars have values in Gamma *)
      (forall s, In s written_vars -> exists v, BitsToLists.list_assoc Gamma (_reg_name tf_ctx s) = Some v) ->

      let val_for_state := fun s => match BitsToLists.list_assoc Gamma (_reg_name tf_ctx s) with
      | Some v => v
      | None => hw_reg_state.[tf_reg tf_ctx s]
      end
      in

      let write_logs := List.fold_left (fun (acc_log: UntypedLogs._ULog) s =>
        UntypedLogs.log_cons (tf_reg tf_ctx s) (UntypedLogs.LE Logs.LogWrite P1 (val_for_state s)) acc_log
      ) written_vars action_log in 

      UntypedSemantics.interp_action hw_reg_state sigma Gamma sched_log action_log (_rule_write_state_vars tf_ctx state_op {{ pass }}) =
      Some (write_logs, Bits [], Gamma).
    Proof.
      intros.
      
      generalize dependent H.
      generalize dependent H0.

      unfold _rule_write_state_vars, spec_all_states, some_fs_state_elements, spec_states, spec_states_fin, tf_spec_states, tf_spec_states_fin in *.
      timeout 10 simpl. 

      generalize finite_injective.
      generalize finite_surjective.
      intros H_inj H_surj.

      subst written_vars.
      subst val_for_state.
      subst write_logs.
      set (StateList := finite_elements). 
      set (RegList := finite_elements).

      assert (NoDup StateList) as H_nodup.
      { apply NoDup_map_inv with (f:=finite_index). apply finite_injective. }

      generalize dependent action_log.
      induction StateList; intros.
      {
        timeout 10 simpl. 
        assert ((vect_to_list Ob) = []). { timeout 10 sauto. } rewrite H1.
        timeout 10 sauto.
      }
      {
        timeout 10 simpl.
        destruct (tf_op_var_not_written_dec some_fs_states some_fs_states_fin some_fs_states_size a state_op).
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
              (* generalize (@finite_surjective some_fs_states some_fs_states_fin a). intros Hxx. apply nth_error_In with (finite_index a). exact Hxx. *)
            - timeout 10 sauto.
          }
          rewrite H1. clear H1 any_write1s.
          timeout 10 simpl.

          rewrite IHStateList.
          {
            timeout 10 sauto.
          } {
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
              assert (~ tf_op_var_not_written some_fs_states some_fs_states_fin some_fs_states_size s state_op). {
                contradict H1. rewrite filter_In. timeout 10 sauto.
              }
              assert (In s (filter (fun s : some_fs_states => if tf_op_var_not_written_dec some_fs_states some_fs_states_fin some_fs_states_size s state_op then false else true) (a :: StateList))).
              {
                apply filter_In. split.
                - apply filter_In in H1. destruct H1. timeout 10 sauto.
                - timeout 10 sauto.
              }
              specialize (H s H3).
              unfold UntypedLogs.log_existsb in *. unfold getenv in *. cbn -[_reg_name] in *. rewrite !cassoc_ccreate in *.
              rewrite !cassoc_creplace_neq_k. timeout 10 sauto. timeout 10 sauto.
            }
          }
        }
      }
    Qed.

  End ActionInterpretation.

  (* Prove next HW cycle = next Spec cycle *)
    Definition _ur (x: some_reg_t) := val_of_value (some_r x).
    Definition initial_hw_state := 
        ContextEnv.(create) _ur.

    Definition next_hw_cycle (hw_reg_state: env_t ContextEnv (fun _ : some_reg_t => val)) := 
    UntypedSemantics.interp_cycle some_rules hw_reg_state sigma some_system_schedule.

    (* TODO: Update once we have operation lists as input *)
    Definition some_fs_step :=  tf_op_step_commit some_fs_states _ some_fs_states_size.
    Definition some_fs_op_step_writes :=  tf_op_step_writes some_fs_states _ some_fs_states_size.

    Definition StateR (hw_reg_state: env_t ContextEnv (fun _ : some_reg_t => val)) (fs_state: ContextEnv.(env_t) some_fs_states_t) :=
        forall x, hw_reg_state.[tf_reg tf_ctx x] = val_of_value (fs_state.[x]).
    
    Theorem InitState_correct :
        StateR initial_hw_state (ContextEnv.(create) some_fs_states_init).
    Proof.
        unfold initial_hw_state. intros x.
        rewrite getenv_create. rewrite getenv_create. (* hammer. *)  hauto lq: on.
    Qed.

    Lemma latest_write_eq_some_fs_op_step_writes:
      forall hw_reg_state fs_state cmd state_var,
      sigma (ext_in_cmd tf_ctx) val_true = encoded_cmd cmd ->
      StateR hw_reg_state fs_state ->
      UntypedLogs.latest_write (UntypedSemantics.interp_scheduler some_rules hw_reg_state sigma some_system_schedule) (tf_reg tf_ctx state_var) 
      = match (some_fs_op_step_writes fs_state state_var (some_fs_action_ops cmd)) with
        | Some k => Some (val_of_value k)
        | None => None
      end.
    Proof.
        intros hw_reg_state fs_state cmd state_var H_sigma_eq_cmd H_state.
        unfold StateR in H_state.

        (* assert (H_hwstate_is_bits: forall (s: some_fs_states), exists x, hw_reg_state.[tf_reg tf_ctx s] = Bits x).
        { 
          unfold StateR in H_state. unfold some_fs_states_t in *. unfold tf_states_type in *.
          intros. rewrite H_state. unfold val_of_value. timeout 10 eauto.
        } *)

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
