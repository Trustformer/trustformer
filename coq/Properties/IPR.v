Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.
Require Koika.Properties.SemanticProperties.
Require Import Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Synthesis.
Require Import Trustformer.Utils.
Require Trustformer.Properties.Common.
From Koika.Utils Require Import Tactics.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Streams.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Init.Tactics.
Require Import Coq.Program.Equality.

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Section CompositionalCorrectness.

  (* Opaque finite_elements. *)
  Arguments finite_elements : simpl never.
  Arguments _reg_name : simpl never.
  Arguments _out_name : simpl never.

  Context {tf_ctx: TFSynthContext}.
  Context (sigma: (ext_fn_t tf_ctx) -> val -> val).
  Context (sigma_valid: forall f x, exists (f_t : retSig (Sigma tf_ctx f)), sigma f x = val_of_value f_t ).

  (* ====== Abbreviations ====== *)

  Local Notation spec_states := (tf_spec_states tf_ctx).
  Local Notation spec_states_fin := (tf_spec_states_fin tf_ctx).
  Local Notation spec_states_size := (tf_spec_states_size tf_ctx).
  Local Notation spec_states_t := (tf_states_type spec_states_size).
  Local Notation spec_states_init := (tf_spec_states_init tf_ctx).
  Local Notation spec_all_states := (@finite_elements spec_states spec_states_fin).
  Local Notation spec_state_index := (@finite_index spec_states spec_states_fin).
  Local Notation spec_state_num := (Datatypes.length spec_all_states).

  Local Notation spec_inputs := (tf_spec_inputs tf_ctx).
  Local Notation spec_inputs_fin := (tf_spec_inputs_fin tf_ctx).
  Local Notation spec_inputs_size := (tf_spec_inputs_size tf_ctx).
  Local Notation spec_inputs_t := (tf_inputs_type spec_inputs_size).
  Local Notation spec_all_inputs := (@finite_elements spec_inputs spec_inputs_fin).
  Local Notation spec_input_index := (@finite_index spec_inputs spec_inputs_fin).
  Local Notation spec_input_num := (Datatypes.length spec_all_inputs).

  Local Notation spec_outputs := (tf_spec_outputs tf_ctx).
  Local Notation spec_outputs_fin := (tf_spec_outputs_fin tf_ctx).
  Local Notation spec_outputs_size := (tf_spec_outputs_size tf_ctx).
  Local Notation spec_outputs_t := (tf_outputs_type spec_outputs_size).
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

  Local Notation spec_var_written := (tf_ops_var_written (states_var_fin:=spec_states_fin) spec_states_size spec_inputs_size spec_outputs_size).
  Local Notation spec_out_written := (tf_ops_out_written (states_var_fin:=spec_states_fin) spec_states_size spec_inputs_size spec_outputs_size).
  Local Notation spec_var_written_dec := (tf_ops_var_written_dec spec_states_size spec_inputs_size spec_outputs_size).
  Local Notation spec_out_written_dec := (tf_ops_out_written_dec spec_states_size spec_inputs_size spec_outputs_size).
  Local Notation spec_eval_expr := (tf_eval_expr spec_states_size spec_inputs_size).

  Local Notation sem_var_not_written_means_ops_run_unchanged := (tf_ops_var_not_written_means_ops_run_unchanged spec_states_size spec_inputs_size spec_outputs_size).
  Local Notation sem_out_not_written_means_ops_run_unchanged := (tf_ops_out_not_written_means_ops_run_unchanged spec_states_size spec_inputs_size spec_outputs_size).

  Local Notation sem_op_step_updates := (tf_op_step_updates spec_states_size spec_inputs_size spec_outputs_size).
  Local Notation sem_op_step_commit_state := (tf_op_step_commit_state spec_states_size spec_outputs_size).
  Local Notation sem_op_step_commit_output := (tf_op_step_commit_output spec_states_size spec_outputs_size).
  Local Notation sem_op_step_commit := (tf_op_step_commit spec_states_size spec_outputs_size).
  Local Notation sem_update := (tf_update spec_states_size spec_outputs_size).

  Local Notation sem_ops_updates := (tf_ops_updates spec_states_size spec_inputs_size spec_outputs_size).
  Local Notation sem_ops_updates_correct2 := (tf_ops_updates_correct2 spec_states_size spec_inputs_size spec_outputs_size).
  Local Notation sem_ops_run := (tf_ops_run spec_states_size spec_inputs_size spec_outputs_size).

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

  Local Notation spec_state_env_t := (ContextEnv (FT:=spec_states_fin).(env_t) spec_states_t).
  Local Notation spec_output_env_t := (ContextEnv (FT:=spec_outputs_fin).(env_t) spec_outputs_t).

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
  Ltac cbn2 := unfold_misc; timeout 10 cbn -[vect_to_list UntypedLogs.log_existsb UntypedLogs.log_empty _reg_name _out_name Nat.eq_dec eq_dec may_read] in *; unfold_misc.

  Ltac unfold_getenv := unfold getenv; cbn [ContextEnv].
  Ltac unfold_getenv_all := unfold getenv in *; cbn [ContextEnv] in *.

  
  Ltac assert_nested_match_equal :=
      match goal with
      | [ |-
            match
                match ?X1 with
                | _ => _
                end
            with
            | _ => _
            end = match ?X2 with
            | _ => _
            end ] =>
          assert (X1 = X2)
      end.

  (* ============ Helper Lemmas on the synthesis results ============= *)

  Lemma list_decidable_eq_string : ListDec.decidable_eq string.
  Proof.
    unfold ListDec.decidable_eq.
    intros. unfold Decidable.decidable.
    destruct (String.string_dec x y). left; auto. right; auto.
  Qed.

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

  Section HelperStructures.

    Lemma spec_all_states_complete:
      forall s: spec_states,
      In s spec_all_states.
    Proof.
      intros. generalize (finite_surjective s (FiniteType:=spec_states_fin)).
      intros H1. apply nth_error_In with (finite_index s (FiniteType:=spec_states_fin)). exact H1.
    Qed.

    Lemma spec_all_outputs_complete:
      forall o: spec_outputs,
      In o spec_all_outputs.
    Proof.
      intros. generalize (finite_surjective o (FiniteType:=spec_outputs_fin)).
      intros H1. apply nth_error_In with (finite_index o (FiniteType:=spec_outputs_fin)). exact H1.
    Qed.

    Definition isStateReg (r: impl_reg) :=
      exists s, r = tf_reg tf_ctx s.

    Definition isOutputReg (r: impl_reg) :=
      exists o, r = tf_out tf_ctx o.

    (* ======== Read/Write ======== *)
    Definition may_read_all sched_log port regs :=
      forallb (may_read (REnv:=RegCEnv) (V:=val) sched_log port) regs.

    Definition may_write_all sched_log action_log port regs :=
      forallb (may_write (REnv:=RegCEnv) (V:=val) sched_log action_log port) regs. 

    Lemma may_write_log_cons_neq :
      forall sched_log action_log kind v port1 port2 reg1 reg2,
        reg1 <> reg2 ->
        may_write (REnv:=RegCEnv) (V:=val) sched_log (log_cons reg2 {| kind := kind; port := port1; UntypedLogs.val := v |} action_log) port2 reg1 =
        may_write (REnv:=RegCEnv) (V:=val) sched_log action_log port2 reg1.
    Proof.
      intros. unfold may_write.
      cbn. unfold_getenv_all.
      rewrite !cassoc_ccreate. cbn2. 
      (* Set Printing All. *)
      assert (reg2 <> reg1) by (* hammer *) timeout 10 hauto lq: on.
      rewrite (Common.cassoc_log_cons_neq action_log (reg2) (reg1) _ H0).
      reflexivity.
    Qed.

    Lemma may_write_all_log_cons_neq :
      forall sched_log action_log reg kind v port regs,
        ~ In reg regs ->
        may_write_all sched_log (log_cons reg {| kind := kind; port := port; UntypedLogs.val := v |} action_log) port regs =
        may_write_all sched_log action_log port regs.
    Proof.
      intros. unfold may_write_all.
      induction regs; cbn.
      { reflexivity. }
      {
        destruct (eq_dec a reg).
        { contradict H. rewrite e. left. reflexivity. }
        {
          apply List.not_in_cons in H; destruct H as [H1 H2].
          rewrite !(IHregs H2); clear IHregs.
          destruct (forallb (may_write sched_log action_log port) regs); rewrite ?andb_false_r, ?andb_true_r.
          2: reflexivity.
          apply (may_write_log_cons_neq _ _ _ _ _ _ _ _ n).
        }
      }
    Qed.

    (* ======== Variables & Gamma ======== *)
    Definition val_unreachable := Bits [].
    Arguments val_unreachable : simpl never.

    Definition has_var (Gamma: list (string * val)) var_name :=
      exists v, BitsToLists.list_assoc (V:=val) Gamma var_name = Some v.

    Lemma has_var_ignore_left:
      forall Gamma1 Gamma2 var_name,
        has_var Gamma1 var_name ->
        has_var (Gamma2 ++ Gamma1) var_name.
    Proof.
      intros Gamma1 Gamma2 var_name H_has.
      unfold has_var in *.
      destruct H_has as [v H_lookup].
      apply Common.bits_to_list_assoc_fallback_app with (a:=Gamma2) in H_lookup.
      destruct (BitsToLists.list_assoc (Gamma2 ++ Gamma1) var_name); try congruence.
      econstructor; reflexivity.
    Qed.

    Lemma has_var_ignore_right:
      forall Gamma1 Gamma2 var_name,
        has_var Gamma2 var_name ->
        has_var (Gamma2 ++ Gamma1) var_name.
    Proof.
      intros Gamma1 Gamma2 var_name H_has.
      unfold has_var in *.
      destruct H_has as [v H_lookup].
      apply Common.bits_to_list_assoc_app with (a:=Gamma1) in H_lookup.
      destruct (BitsToLists.list_assoc (Gamma2 ++ Gamma1) var_name); try congruence.
      econstructor; reflexivity.
    Qed.

    Lemma has_var_ignore_middle:
      forall Gamma1 Gamma2 Gamma3 var_name,
        has_var (Gamma1 ++ Gamma3) var_name ->
        has_var (Gamma1 ++ Gamma2 ++ Gamma3) var_name.
    Proof.
      intros Gamma1 Gamma2 Gamma3 var_name H_has.
      unfold has_var in *.
      destruct H_has as [v H_lookup].
      destruct (BitsToLists.list_assoc (Gamma1) var_name) eqn:H_lookup_l.
      - apply has_var_ignore_right with (Gamma1:=(Gamma2 ++ Gamma3)). econstructor. rewrite H_lookup_l. reflexivity.
      - destruct (BitsToLists.list_assoc (Gamma3) var_name) eqn:H_lookup_r.
        + rewrite app_assoc. apply has_var_ignore_left with (Gamma2:=Gamma1 ++ Gamma2). econstructor. rewrite H_lookup_r. reflexivity.
        + rewrite Common.bits_to_list_assoc_app_both_none in H_lookup; congruence.
    Qed.

    Definition has_var_all (Gamma: list (string * val)) var_names :=
      Forall (has_var Gamma) var_names.

    Lemma has_var_all_ignore_left:
      forall Gamma1 Gamma2 var_names,
        has_var_all Gamma1 var_names ->
        has_var_all (Gamma2 ++ Gamma1) var_names.
    Proof.
      intros Gamma1 Gamma2 var_names H_all.
      unfold has_var_all in *.
      rewrite Forall_forall in *.
      intros var_name H_in.
      apply has_var_ignore_left with (Gamma2:=Gamma2).
      apply (H_all var_name H_in).
    Qed.

    Lemma has_var_all_ignore_right:
      forall Gamma1 Gamma2 var_names,
        has_var_all Gamma2 var_names ->
        has_var_all (Gamma2 ++ Gamma1) var_names.
    Proof.
      intros Gamma1 Gamma2 var_names H_all.
      unfold has_var_all in *.
      rewrite Forall_forall in *.
      intros var_name H_in.
      apply has_var_ignore_right with (Gamma2:=Gamma2).
      apply (H_all var_name H_in).
    Qed.

    Lemma has_var_all_ignore_middle:
      forall Gamma1 Gamma2 Gamma3 var_names,
        has_var_all (Gamma1 ++ Gamma3) var_names ->
        has_var_all (Gamma1 ++ Gamma2 ++ Gamma3) var_names.
    Proof.
      intros Gamma1 Gamma2 Gamma3 var_names H_all.
      unfold has_var_all in *.
      rewrite Forall_forall in *.
      intros var_name H_in.
      apply has_var_ignore_middle with (Gamma1:=Gamma1) (Gamma3:=Gamma3).
      apply (H_all var_name H_in).
    Qed.

    Lemma has_var_all_correct:
      forall Gamma var_name var_names,
        In var_name var_names ->
        has_var_all Gamma var_names ->
        has_var Gamma var_name.
    Proof.
      intros Gamma var_name var_names H_in H_all.
      unfold has_var_all, has_var in *.
      rewrite Forall_forall in H_all.
      apply (H_all var_name H_in).
    Qed.

    Lemma has_var_all_subset:
      forall Gamma var_names1 var_names2,
        (forall v, In v var_names1 -> In v var_names2) ->
        has_var_all Gamma var_names2 ->
        has_var_all Gamma var_names1.
    Proof.
      intros Gamma var_names1 var_names2 H_subset H_all.
      unfold has_var_all in *.
      rewrite Forall_forall in *.
      intros var_name H_in1.
      apply (H_all var_name).
      apply H_subset. exact H_in1.
    Qed.

    Definition has_sized_bits (value : val) (sz: nat):=
      exists bl : list bool, value = Bits bl /\ Datatypes.length bl = sz.

    Definition value_of_option_lossy (v: option val) : val :=
      match v with
        | Some v' => v'
        | None => val_unreachable
      end.

    Definition bits_of_value_lossy (v: val) : list bool :=
      match v with
        | Bits bl => bl
        | _ => []
      end.

    Definition lookup (Gamma: list (string * val)) (var_name: string) : val :=
      (value_of_option_lossy (BitsToLists.list_assoc (V:=val) Gamma var_name)).
    Arguments lookup : simpl never.

    Lemma lookup_cons_eq:
      forall Gamma var_name1 var_name2 v,
        var_name1 = var_name2 ->
        lookup ((var_name1, v) :: Gamma) var_name2 = v.
    Proof.
      intros. unfold lookup.
      cbn -[eq_dec]. destr. reflexivity.
    Qed.

    Lemma lookup_cons_neq:
      forall Gamma var_name1 var_name2 v,
        var_name1 <> var_name2 ->
        lookup ((var_name2, v) :: Gamma) var_name1 = lookup Gamma var_name1.
    Proof.
      intros. unfold lookup.
      cbn -[eq_dec]. destr.
    Qed.

    Definition lookup_s (Gamma: list (string * val)) (v: spec_states) : val :=
      lookup Gamma (_reg_name tf_ctx v).

    Definition lookup_o (Gamma: list (string * val)) (o: spec_outputs) : val :=
      lookup Gamma (_out_name tf_ctx o).

    Definition Gamma_ok_state (Gamma: list (string * val)) :=
      (forall s, has_sized_bits (lookup_s Gamma s) (spec_states_size s)).

    Lemma Gamma_ok_state_app:
      forall Gamma1 Gamma2,
        Gamma_ok_state Gamma1 ->
        (forall s v, In ((_reg_name tf_ctx s), v) Gamma2 -> has_sized_bits v (spec_states_size s)) ->
        Gamma_ok_state (Gamma2 ++ Gamma1).
    Proof.
      intros Gamma1 Gamma2 H_G1 H_G2. unfold Gamma_ok_state in *.
      intros s. unfold lookup_s, lookup. 
      induction Gamma2.
      - cbn. apply H_G1. 
      - cbn -[eq_dec]. destruct a as [var_name v].
        destruct (eq_dec (_reg_name tf_ctx s) var_name).
        + subst var_name. apply H_G2. left. reflexivity.
        + apply IHGamma2. clear IHGamma2. intros. apply H_G2. right. exact H.
    Qed.

    Definition Gamma_ok_output (Gamma: list (string * val)) :=
      (forall o, has_sized_bits (lookup_o Gamma o) (spec_outputs_size o)).

    Lemma Gamma_ok_output_app:
      forall Gamma1 Gamma2,
        Gamma_ok_output Gamma1 ->
        (forall o v, In ((_out_name tf_ctx o), v) Gamma2 -> has_sized_bits v (spec_outputs_size o)) ->
        Gamma_ok_output (Gamma2 ++ Gamma1).
    Proof.
      intros Gamma1 Gamma2 H_G1 H_G2. unfold Gamma_ok_output in *.
      intros o. unfold lookup_o, lookup. 
      induction Gamma2.
      - cbn. apply H_G1. 
      - cbn -[eq_dec]. destruct a as [var_name v].
        destruct (eq_dec (_out_name tf_ctx o) var_name).
        + subst var_name. apply H_G2. left. reflexivity.
        + apply IHGamma2. clear IHGamma2. intros. apply H_G2. right. exact H.
    Qed.

    (* ======== State Relation ======== *)
    Definition StateR (hw_reg_state: hw_env_t) (fs_state: spec_state_env_t) :=
        forall x, hw_reg_state.[tf_reg tf_ctx x] = val_of_value (fs_state.[x]).

    Lemma StateR_means_sized_bits:
      forall hw_reg_state fs_state,
        StateR hw_reg_state fs_state ->
        forall x, has_sized_bits (hw_reg_state.[tf_reg tf_ctx x]) (spec_states_size x).
    Proof.
        intros hw_reg_state fs_state H_state x.
        specialize (H_state x). unfold getenv in *. cbn in *.
        exists (vect_to_list (cassoc (finite_member x) fs_state)).
        split. (* hammer. *) timeout 10 sfirstorder.
        rewrite vect_to_list_length. reflexivity.
    Qed.

    Definition OutputR (hw_reg_state: hw_env_t) (fs_output: spec_output_env_t) :=
        forall x, hw_reg_state.[tf_out tf_ctx x] = val_of_value (fs_output.[x]).

    Lemma OutputR_means_sized_bits:
      forall hw_reg_state fs_output,
        OutputR hw_reg_state fs_output -> 
        forall x, has_sized_bits (hw_reg_state.[tf_out tf_ctx x]) (spec_outputs_size x).
    Proof.
        intros hw_reg_state fs_output H_output x.
        specialize (H_output x). unfold getenv in *. cbn in *.
        exists (vect_to_list (cassoc (finite_member x) fs_output)).
        split. (* hammer. *) timeout 10 sfirstorder.
        rewrite vect_to_list_length. reflexivity.
    Qed.
    
    Definition InputR (fs_input: forall (x : spec_inputs), (type_denote (spec_inputs_t x))) :=
        forall x, val_of_value (fs_input x) = sigma (ext_input tf_ctx x) val_true.

    (* ======== Inverse Mapping ======== *)

    Lemma _val_to_bits_cast1:
      forall v sz, has_sized_bits v sz -> (Datatypes.length (bits_of_value_lossy v)) = sz.
    Proof.
      intros v sz H_has.
      destruct H_has as [bl [H_v_eq H_sz]].
      subst v. cbn. rewrite H_sz. reflexivity.
    Qed.

    Definition val_to_bits (sz: nat) (v: val) (PSz: has_sized_bits v sz) : bits sz :=
      let Heq := _val_to_bits_cast1 v sz PSz in
      rew [Bits.bits] Heq in (vect_of_list (bits_of_value_lossy v)).

    Lemma val_of_val_to_bits_correct:
      forall sz v (PSz: has_sized_bits v sz),
        let tau := (bits_t sz) in
        val_of_value (tau:=tau) (val_to_bits sz v PSz) = v.
    Proof.
      intros sz v PSz tau.
      unfold val_to_bits.
      destruct PSz as [bl [H_v_eq H_sz]].
      subst v. cbn. simpl_eq.
      rewrite BitsToLists.vect_to_list_of_list.
      reflexivity.
    Qed.

    Lemma val_to_bits_equiv:
      forall sz v1 v2 H1 H2,
        v1 = v2 ->
        val_to_bits sz v1 H1 = val_to_bits sz v2 H2.
    Proof.
      intros sz v1 v2 H1 H2 H_eq.
      subst v2. unfold val_to_bits.
      vect_to_list_t.
      reflexivity.
    Qed.

    Lemma val_to_bits_of_sized_val_correct:
      forall sz v H,
        val_to_bits sz (val_of_value (tau:=bits_t sz) v) H = v.
    Proof.
      intros sz v H. clear sigma_valid. unfold val_to_bits, bits_of_value_lossy, val_of_value in *.
      rewrite BitsToLists.vect_of_list_to_list. vect_to_list_t. reflexivity.
    Qed.

    Definition SpecStateEnvExt (fs_state: spec_state_env_t) (Gamma: list (string * val)) (PGokS: Gamma_ok_state Gamma) : spec_state_env_t :=
      ContextEnv (FT:=spec_states_fin).(create) (fun s => 
        val_to_bits (spec_states_size s) (lookup_s Gamma s) (PGokS s)
        (* match BitsToLists.list_assoc (V:=val) Gamma (_reg_name tf_ctx s) return spec_states_t s with
        | Some v => val_to_bits (spec_states_size s) (lookup_s Gamma s) (PGokS s)
        | None => fs_state.[s]
        end *)
        ).

    Definition SpecOutputEnvExt (fs_output: spec_output_env_t) (Gamma: list (string * val)) (PGokS: Gamma_ok_output Gamma) : spec_output_env_t :=
      ContextEnv (FT:=spec_outputs_fin).(create) (fun o => 
        val_to_bits (spec_outputs_size o) (lookup_o Gamma o) (PGokS o)
        (* match BitsToLists.list_assoc (V:=val) Gamma (_out_name tf_ctx o) return spec_outputs_t o with
        | Some v => val_to_bits (spec_outputs_size o) (lookup_o Gamma o) (PGokS o)
        | None => fs_output.[o]
        end *)
        ).

  End HelperStructures.
  
  Ltac extract_var H := 
    let v := fresh "v" in
    let Hvar := fresh "Hvar" in
    cbn in H; destruct H as [v Hvar]; unfold lookup in *; rewrite ?Hvar in *; try cbn [value_of_option_lossy] in *.

  Ltac extract_var_cons H := 
    let Hvar := fresh "Hvar" in
    cbn in H; apply Forall_inv in H as Hvar; extract_var Hvar; apply Forall_inv_tail in H.

  Ltac extract_bits H := 
    let bl := fresh "bl" in
    let Hbits := fresh "Hbits" in
    cbn in H; destruct H as [bl Hbits]; rewrite ?Hbits in *.

  Ltac extract_sized_bits H := 
    let bl := fresh "bl" in
    let Hbits := fresh "Hbits" in
    let Hsz := fresh "Hsz" in
    cbn in H; destruct H as [bl [Hbits Hsz]]; rewrite ?Hbits, ?Hsz in *.

  Ltac extract_lookup H :=
    let Hlu := fresh "Hlu" in
    pose proof (H) as Hlu; unfold lookup_s, lookup_s, lookup in Hlu; rewrite ?Hlu in *.

  (* ========================= *)

  Section ActionInterpretation.

    Definition Gamma_after_read_vars0 (hw_reg_state: hw_env_t) (Gamma: list (string * val)) regs var_map :=
      map (fun reg => (var_map reg, hw_reg_state.[(reg)])) (rev regs) ++ Gamma.

    Definition ActionLog_after_read_vars0 action_log regs :=
      fold_right (fun 'reg (acc_log: _ULog) =>
        log_cons (REnv:=RegCEnv) (reg) (LE Logs.LogRead P0 (Bits [])) acc_log
      ) action_log (rev regs).

    Lemma interp_act_read_vars0 :
      forall (hw_reg_state: hw_env_t) (Gamma: list (string * val)) sched_log action_log code regs var_map,

        may_read_all sched_log P0 regs = true ->

        interp_action hw_reg_state sigma Gamma sched_log action_log (_rule_read_vars0 tf_ctx var_map regs code) =

          let Gamma' := Gamma_after_read_vars0 hw_reg_state Gamma regs var_map in
          let action_log' := ActionLog_after_read_vars0 action_log regs in

          match interp_action hw_reg_state sigma Gamma' sched_log action_log' code with
          | Some (final_log, v, Gamma'') => Some (final_log, v, skipn (length regs) Gamma'')
          | None => None
          end.
    Proof.
      intros. unfold _rule_read_vars0.
      
      generalize dependent Gamma.
      generalize dependent action_log.
      induction regs; intros. 
      {
        unfold Gamma_after_read_vars0, ActionLog_after_read_vars0 in *.
        timeout 10 simpl. destr. 
        - destruct p as [ [final_log v] Gamma']. reflexivity.
        - reflexivity.
      }
      {
        rename a into reg. cbn -[may_read]. cbn -[may_read] in H.
        apply andb_true_iff in H. destruct H as [H_read H_read_rest].
        rewrite H_read. cbn. specialize (IHregs H_read_rest).
        rewrite IHregs. clear IHregs. 
        unfold Gamma_after_read_vars0, ActionLog_after_read_vars0. cbn.
        unfold opt_bind.

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
          rewrite HeqLMM. rewrite HeqRM. clear HeqLMM. clear HeqRM.
          f_equal.
          { rewrite map_app. cbn. rewrite <- app_assoc. reflexivity. }
          { rewrite fold_right_app. reflexivity. }
        } 
        rewrite Heq. clear Heq. clear HeqLMM. clear HeqRM.

        case_eq RM.
        {
          intros. destruct p as [p0 Gamma']. destruct p0 as [final_log v].
          repeat f_equal. clear H. generalize dependent (Datatypes.length regs).
          induction Gamma'; intros.
          { cbn. rewrite skipn_nil. reflexivity. }
          { cbn. destruct n. reflexivity. cbn. apply IHGamma'. } 
        }
        {
          intros. reflexivity.
        }
      }
    Qed. 

    Lemma latest_write_of_ActionLog_after_read_vars0 :
      forall action_log regs reg,
        latest_write (ActionLog_after_read_vars0 action_log regs) reg
        = latest_write action_log reg.
    Proof.
      intros. unfold ActionLog_after_read_vars0.
      induction (rev regs); cbn.
      { reflexivity. }
      { 
        unfold_getenv_all. destruct (eq_dec reg a).
        { subst. cbn. rewrite Common.cassoc_log_cons_eq. cbn. exact IHl. }
        { rewrite Common.cassoc_log_cons_neq. 2: congruence. exact IHl. }
      }
    Qed.

    Definition ActionLog_after_write_vars0 Gamma action_log regs var_map :=
      fold_right (fun reg (acc_log: _ULog) =>
        log_cons (REnv:=RegCEnv) (reg) (LE Logs.LogWrite P0 (lookup Gamma (var_map reg))) acc_log
      ) action_log (rev regs).

    Lemma interp_act_write_vars0 :
      forall (hw_reg_state: hw_env_t) (Gamma: list (string * val)) sched_log action_log code regs var_map,

        may_write_all sched_log action_log P0 regs = true ->

        has_var_all Gamma (map var_map regs) ->

        NoDup regs ->

        interp_action hw_reg_state sigma Gamma sched_log action_log (_rule_write_vars0 tf_ctx var_map regs code) =

          let action_log' := ActionLog_after_write_vars0 Gamma action_log regs var_map in
          interp_action hw_reg_state sigma Gamma sched_log action_log' code.
    Proof.
      intros. unfold _rule_write_vars0.

      generalize dependent action_log.
      induction regs; intros. 
      { reflexivity. }

      rename a into reg. cbn -[may_write]. 

      extract_var_cons H0. cbn -[may_write].
      specialize (IHregs H0).
      
      cbn -[may_write] in H.
      apply andb_true_iff in H. destruct H as [H_write H_write_rest].
      rewrite H_write. cbn. 

      rewrite IHregs; clear IHregs. 
      {
        unfold ActionLog_after_write_vars0. f_equal.
        unfold log_cons.
        rewrite fold_right_app. cbn. repeat f_equal.
        rewrite Hvar0. reflexivity.
      }
      {
        inversion H1. exact H4.
      }
      {
        rewrite may_write_all_log_cons_neq. 2: { cbn in H1. inversion H1. exact H3. }
        exact H_write_rest.
      }
    Qed. 

    Lemma latest_write_of_ActionLog_after_write_vars0_in:
      forall Gamma action_log regs var_map reg,
        In reg regs -> 
        latest_write (ActionLog_after_write_vars0 Gamma action_log regs var_map) reg
        = Some (lookup Gamma (var_map reg)).
    Proof.
      intros. unfold ActionLog_after_write_vars0.
      apply In_rev in H. generalize dependent H.
      induction (rev regs); intros.
      { contradiction. }
      {
        destruct (eq_dec a reg).
        {
          subst. cbn. unfold_getenv_all. rewrite Common.cassoc_log_cons_eq. reflexivity.
        }
        {
          inversion H; try congruence.
          cbn. unfold_getenv_all. rewrite Common.cassoc_log_cons_neq by exact n.
          apply IHl. exact H0.
        }
      }
    Qed.
      
    Lemma latest_write_of_ActionLog_after_write_vars0_not_in:
      forall Gamma action_log regs var_map reg,
        ~ In reg regs -> 
        latest_write (ActionLog_after_write_vars0 Gamma action_log regs var_map) reg
        = latest_write action_log reg.
    Proof.
      intros. unfold ActionLog_after_write_vars0.
      assert (H_in: ~ In reg (rev regs)).
      { intros Hc. apply H. apply In_rev. exact Hc. }
      clear H. rename H_in into H. generalize dependent H.
      induction (rev regs); intros.
      { reflexivity. }
      {
        destruct (eq_dec a reg).
        {
          subst. contradict H. left. reflexivity.
        }
        {
          cbn. unfold_getenv_all. rewrite Common.cassoc_log_cons_neq by exact n.
          apply IHl. intros H_in. apply H. right. exact H_in.
        }
      }
    Qed.

    Lemma Gamma_after_intro_ok_state:
      forall hw_reg_state,
        (forall x, has_sized_bits (hw_reg_state.[tf_reg tf_ctx x]) (spec_states_size x)) ->
        Gamma_ok_state (Gamma_after_read_vars0 hw_reg_state (Gamma_after_read_vars0 hw_reg_state [] (map (tf_reg tf_ctx) spec_all_states) (_register_var_name tf_ctx))
            (map (tf_out tf_ctx) spec_all_outputs) (_register_var_name tf_ctx)).
    Proof.
      intros. unfold Gamma_after_read_vars0, Gamma_ok_state.
      intros. specialize (H s). extract_sized_bits H.
      econstructor. split.
      {
        unfold lookup_s, lookup. rewrite <- !map_rev. induction (rev spec_all_outputs).
        2: { cbn2. destr. inversion e. }
        cbn2.

        assert (In s (rev spec_all_states)) as H_in.
        { 
          generalize (finite_surjective s (FiniteType:=spec_states_fin)).
          intros H1. rewrite <- in_rev. apply nth_error_In with (finite_index s (FiniteType:=spec_states_fin)). exact H1.
        }
        generalize dependent H_in.
        induction (rev spec_all_states); intros. inversion H_in.

        destruct (eq_dec s a).
        { subst a. cbn2. destr. cbn. rewrite Hbits. reflexivity. }
        {
          inversion H_in. congruence.
          cbn2. destr. 
          { contradict n; apply reg_name_inj; exact e. }
          
          specialize (IHl H). exact IHl.
        }
      }
      { exact Hsz. }
    Qed.

    Lemma Gamma_after_intro_ok_output:
      forall hw_reg_state,
        (forall x, has_sized_bits (hw_reg_state.[tf_out tf_ctx x]) (spec_outputs_size x)) ->
        Gamma_ok_output (Gamma_after_read_vars0 hw_reg_state (Gamma_after_read_vars0 hw_reg_state [] (map (tf_reg tf_ctx) spec_all_states) (_register_var_name tf_ctx))
          (map (tf_out tf_ctx) spec_all_outputs) (_register_var_name tf_ctx)).
    Proof.
      intros. unfold Gamma_after_read_vars0, Gamma_ok_output.
      intros. specialize (H o). extract_sized_bits H.
      econstructor. split.  
      {
        unfold lookup_o, lookup. rewrite <- !map_rev.
        
        assert (In o (rev spec_all_outputs)) as H_in.
        { 
          generalize (finite_surjective o (FiniteType:=spec_outputs_fin)).
          intros H1. rewrite <- in_rev. apply nth_error_In with (finite_index o (FiniteType:=spec_outputs_fin)). exact H1.
        }
        generalize dependent H_in.
        induction (rev spec_all_outputs); intros. inversion H_in.
        
        destruct (eq_dec o a).
        { subst a. cbn2. destr. cbn. rewrite Hbits. reflexivity. }
        {
          inversion H_in. congruence.
          cbn2. destr. 
          { contradict n; apply out_name_inj; exact e. }
          
          specialize (IHl H). exact IHl.
        }
      }
      { exact Hsz. }
    Qed.

    Lemma Gamma_after_intro_has_state_vars:
      forall hw_reg_state,
        has_var_all 
          (Gamma_after_read_vars0 hw_reg_state (Gamma_after_read_vars0 hw_reg_state [] (map (tf_reg tf_ctx) spec_all_states) (_register_var_name tf_ctx))
            (map (tf_out tf_ctx) spec_all_outputs) (_register_var_name tf_ctx)) 
          (map (_register_var_name tf_ctx) (map (tf_reg tf_ctx) spec_all_states)).
    Proof.
      intros. unfold Gamma_after_read_vars0, Gamma_ok_output.
      induction (spec_all_states); intros.
      { cbn. constructor. }
      {
        cbn. constructor. 
        2: { rewrite !map_app. rewrite app_nil_r in *. rewrite app_assoc at 1. apply has_var_all_ignore_right. exact IHl. }
        rewrite !map_app. rewrite app_nil_r in *. rewrite app_assoc at 1. apply has_var_ignore_left. cbn.
        unfold has_var, lookup. cbn -[eq_dec _reg_name]. destr. econstructor; reflexivity.
      }
    Qed.

    Lemma Gamma_after_intro_is_hw_state:
      forall hw_reg_state s,
        BitsToLists.list_assoc
          (Gamma_after_read_vars0 hw_reg_state (Gamma_after_read_vars0 hw_reg_state [] (map (tf_reg tf_ctx) spec_all_states) (_register_var_name tf_ctx))
            (map (tf_out tf_ctx) spec_all_outputs) (_register_var_name tf_ctx)) 
          (_reg_name tf_ctx s) = Some( hw_reg_state.[(tf_reg tf_ctx s)] ) .
    Proof.
      intros. unfold Gamma_after_read_vars0, Gamma_ok_output.
      assert (NoDup spec_all_states) as H_nodup by (apply finite_nodup).
      pose proof (spec_all_states_complete s) as H_in.
      generalize dependent H_in.
      generalize dependent H_nodup.
      induction (spec_all_states); intros.
      { inversion H_in. }
      cbn [map rev]. rewrite app_nil_r in *. rewrite map_app. cbn [map]. inv H_nodup; inv H_in.
      {
        apply Common.bits_to_list_assoc_app_not_in.
        { rewrite map_map. cbn. rewrite in_map_iff. intro. destruct H as [x [Heq Hin]].
          unfold _register_var_name in Heq. destruct x. 
          {
            rewrite <- in_rev in Hin. apply in_map_iff in Hin. destruct Hin as [s0 [Heq' Hin']]. congruence.
          }
          all: contradict Heq; timeout 10 fcrush.
        }

        apply Common.bits_to_list_assoc_app_not_in.
        { rewrite map_map. cbn. rewrite in_map_iff. intro. destruct H as [x [Heq Hin]].
          unfold _register_var_name in Heq. destruct x. 
          {
            rewrite <- in_rev in Hin. apply in_map_iff in Hin. destruct Hin as [s0 [Heq' Hin']].
            assert (s0 = x) by congruence. subst s0. apply reg_name_inj in Heq. try congruence.
          }
          all: contradict Heq; timeout 10 fcrush.
        }

        cbn -[eq_dec]. destr.
      }
      {
        rewrite app_assoc. rewrite Common.bits_to_list_assoc_app with (x:=hw_reg_state.[tf_reg tf_ctx s]); try reflexivity.
        exact (IHl H2 H).
      }
    Qed.

    Lemma Gamma_after_intro_has_output_vars:
      forall hw_reg_state,
        has_var_all 
          (Gamma_after_read_vars0 hw_reg_state (Gamma_after_read_vars0 hw_reg_state [] (map (tf_reg tf_ctx) spec_all_states) (_register_var_name tf_ctx))
            (map (tf_out tf_ctx) spec_all_outputs) (_register_var_name tf_ctx)) 
          (map (_register_var_name tf_ctx) (map (tf_out tf_ctx) spec_all_outputs)).
    Proof.
      intros. unfold Gamma_after_read_vars0, Gamma_ok_output.
      induction (spec_all_outputs); intros.
      { cbn. constructor. }
      {
        cbn. constructor. 
        2: { rewrite !map_app. rewrite app_nil_r in *. rewrite <- app_assoc. apply has_var_all_ignore_middle. exact IHl. }
        rewrite !map_app. rewrite app_nil_r in *. rewrite <- app_assoc. apply has_var_ignore_left. apply has_var_ignore_right. cbn.
        unfold has_var, lookup. cbn -[eq_dec _out_name]. destr. econstructor; reflexivity.
      }
    Qed.

    Lemma Gamma_after_intro_is_hw_output:
      forall hw_reg_state o,
        BitsToLists.list_assoc
          (Gamma_after_read_vars0 hw_reg_state (Gamma_after_read_vars0 hw_reg_state [] (map (tf_reg tf_ctx) spec_all_states) (_register_var_name tf_ctx))
            (map (tf_out tf_ctx) spec_all_outputs) (_register_var_name tf_ctx)) 
          (_out_name tf_ctx o) = Some( hw_reg_state.[(tf_out tf_ctx o)] ).
    Proof.
      intros. unfold Gamma_after_read_vars0, Gamma_ok_output.
      apply Common.bits_to_list_assoc_app.

      assert (NoDup spec_all_outputs) as H_nodup by (apply finite_nodup).
      pose proof (spec_all_outputs_complete o) as H_in.
      generalize dependent H_in.
      generalize dependent H_nodup.
      induction (spec_all_outputs); intros.
      { inversion H_in. }
      cbn [map rev]. rewrite map_app. cbn [map]. inv H_nodup; inv H_in.
      {
        apply Common.bits_to_list_assoc_app_not_in.
        { rewrite map_map. cbn. rewrite in_map_iff. intro. destruct H as [x [Heq Hin]].
          unfold _register_var_name in Heq. destruct x. 
          { contradict Heq; timeout 10 fcrush. }
          {
            rewrite <- in_rev in Hin. apply in_map_iff in Hin. destruct Hin as [o0 [Heq' Hin']].
            assert (o0 = x) by congruence. subst o0. apply out_name_inj in Heq. try congruence.
          }
          { contradict Heq; timeout 10 fcrush. }
        }

        cbn -[eq_dec]. destr.
      }
      {
        apply Common.bits_to_list_assoc_app. exact (IHl H2 H).
      }
    Qed.

    Lemma ActionLog_after_intro_may_write_all:
      forall l,          
        may_write_all log_empty 
          (ActionLog_after_read_vars0 
            (ActionLog_after_read_vars0 log_empty (map (tf_reg tf_ctx) spec_all_states)) 
            (map (tf_out tf_ctx) spec_all_outputs)) P0 l = true.
    Proof.
      intros. unfold ActionLog_after_read_vars0, may_write_all.
      rewrite forallb_forall. intros. unfold may_write.
      induction (rev (map (tf_reg tf_ctx) spec_all_states)); induction (rev (map (tf_out tf_ctx) spec_all_outputs)).
      {
        cbn. unfold_getenv_all. rewrite !cassoc_ccreate. reflexivity.
      }
      {
        cbn in *. unfold_getenv_all. rewrite !cassoc_ccreate in *. rewrite !app_nil_r in *.
        unfold log_cons in *. destruct (eq_dec a x).
        { subst. rewrite Common.cassoc_put_eq. unfold_getenv_all. cbn. exact IHl0. }
        { rewrite Common.cassoc_put_neq by exact n. exact IHl0. }
      }
      {
        cbn in *. unfold_getenv_all. rewrite !cassoc_ccreate in *. rewrite !app_nil_r in *.
        unfold log_cons in *. destruct (eq_dec a x).
        { subst. rewrite Common.cassoc_put_eq. unfold_getenv_all. cbn. exact IHl0. }
        { rewrite Common.cassoc_put_neq by exact n. exact IHl0. }
      }
      {
        cbn in *. unfold_getenv_all. rewrite !cassoc_ccreate in *. rewrite !app_nil_r in *.
        unfold log_cons in *. destruct (eq_dec a0 x).
        { subst. rewrite Common.cassoc_put_eq in *. unfold_getenv_all. cbn in *. apply IHl1. exact IHl0. }
        { rewrite Common.cassoc_put_neq in * by exact n. apply IHl1. exact IHl0. }
      }
    Qed.

    Lemma may_write_all_of_ActionLog_after_write_vars:
      forall Gamma action_log regs var_map port l,
        (forall reg, In reg l -> ~ In reg regs) ->
        may_write_all log_empty (ActionLog_after_write_vars0 Gamma action_log regs var_map) port l
        =
        may_write_all log_empty action_log port l.
    Proof.
      intros. unfold may_write_all, ActionLog_after_write_vars0.
      induction l; intros. reflexivity.

      assert (Ha : ~ In a regs). { apply H. left. reflexivity. }
      assert (Hl : forall reg, In reg l -> ~ In reg regs). { intros r Hr. apply H. right. apply Hr. }
      clear H. specialize (IHl Hl). change (a :: l) with ([a] ++ l).
      rewrite !forallb_app. rewrite IHl; clear IHl. destruct (forallb (may_write log_empty action_log port) l). 
      2: { rewrite !andb_false_r. reflexivity. }
      rewrite !andb_true_r. cbn. rewrite !andb_true_r.
      assert (~ In a (rev regs)) as Hn. { intro. rewrite <- in_rev in H. congruence. }
      generalize dependent Hn.
      induction (rev regs); intros. reflexivity.
      
      cbn in *. destruct (eq_dec a a0).
      { subst a0. destruct Hn. left. reflexivity. }
      { rewrite (may_write_log_cons_neq _ _ _ _ _ _ _ _ n). apply IHl0. timeout 10 fcrush. }
    
    Qed.

  End ActionInterpretation.

  Section Expressions.

    Lemma sigma_input_sized_bits:
      forall i,
        has_sized_bits (sigma (ext_input tf_ctx i) val_true) (spec_inputs_size i).
    Proof.
      intros.
      specialize (sigma_valid (ext_input tf_ctx i) val_true) as H_valid.
      destruct H_valid as [input_val Heq]. rewrite Heq.
      cbn in *. eexists _; split.
      reflexivity. rewrite vect_to_list_length. reflexivity.
    Qed.

    Definition val_convert (out_var_size in_var_size : nat) (x : val) : val :=
      if Nat.eq_dec out_var_size in_var_size then
        x
      else 
        if Nat.leb in_var_size out_var_size then
          Bits (bits_of_value_lossy x ++ repeat false (out_var_size - in_var_size))
        else
          Bits (firstn (out_var_size) (bits_of_value_lossy x)).

    Lemma val_convert_sz_correct:
      forall val1 sz1 sz2,
        has_sized_bits val1 sz1 ->
        has_sized_bits (val_convert sz2 sz1 val1) sz2.
    Proof.
      intros. subst. unfold val_convert. destruct (Nat.eq_dec _ _). 
      { rewrite e; exact H. }
      unfold bits_of_value_lossy. destruct (Nat.leb _ _ ) eqn:Hleb.
      {
        extract_sized_bits H. rewrite Nat.leb_le in Hleb.
        econstructor; split; try reflexivity. 
        rewrite List.app_length, repeat_length. lia.
      }
      {
        extract_sized_bits H. rewrite Nat.leb_gt in Hleb.
        econstructor; split; try reflexivity. 
        rewrite firstn_length. lia.
      }
    Qed.

    Lemma synth_convert_is_val_convert:
      forall (hw_reg_state: hw_env_t) (Gamma: list (string * val)) sched_log action_log action_log' code f_dst f_src ret_val, 
        (interp_action hw_reg_state sigma Gamma sched_log action_log code = Some (action_log', ret_val, Gamma) 
          /\ has_sized_bits ret_val f_src) ->
        interp_action hw_reg_state sigma Gamma sched_log action_log
          (synth_convert tf_ctx f_dst f_src code ) =
          Some (action_log', val_convert f_dst f_src ret_val, Gamma).
    Proof.
      intros.
      destruct H as [Hcode H]. extract_sized_bits H.

      unfold synth_convert, val_convert.
      destruct (Nat.eq_dec f_dst f_src). exact Hcode.
      destruct (Nat.leb f_src f_dst) eqn:Hleb.
      { cbn2. rewrite Hcode, <- Hsz. cbn2.
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
        
    Fixpoint value_of_expr (expr: tf_expr) (Gamma: list (string * val)) (target_size: nat) : val :=
      match expr with
        | tf_const value => 
            Bits (vect_to_list (Bits.of_nat (target_size) value))
        | tf_var v =>
            val_convert target_size (spec_states_size v) (lookup_s Gamma v)
        | tf_input v =>
            val_convert target_size (spec_inputs_size v) (sigma (ext_input tf_ctx v) val_true)
        | tf_op1 op src =>
            value_of_option_lossy (UntypedSemantics.usigma1 UNot (value_of_expr src Gamma target_size))
        | tf_op2 op src1 src2 =>
            let v1 := (bits_of_value_lossy (value_of_expr src1 Gamma target_size)) in
            let v2 := (bits_of_value_lossy (value_of_expr src2 Gamma target_size)) in
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
              | tf_cmp sz cop =>
                  let v1 := (bits_of_value_lossy (value_of_expr src1 Gamma sz)) in
                  let v2 := (bits_of_value_lossy (value_of_expr src2 Gamma sz)) in
                  match cop with
                    | tf_eq => val_convert target_size (1) 
                      (Bits [if BitsToLists.val_beq (value_of_expr src1 Gamma sz) (value_of_expr src2 Gamma sz) then true else false])
                    | tf_neq  => val_convert target_size (1) 
                      (Bits [if BitsToLists.val_beq (value_of_expr src1 Gamma sz) (value_of_expr src2 Gamma sz) then false else true])
                    | tf_lt  => val_convert target_size 1 (Bits (UntypedSemantics.ubits2_sigma (UCompare false cLt) v1 v2))
                    | tf_le  => val_convert target_size 1 (Bits (UntypedSemantics.ubits2_sigma (UCompare false cLe) v1 v2))
                    | tf_gt  => val_convert target_size 1 (Bits (UntypedSemantics.ubits2_sigma (UCompare false cGt) v1 v2))
                    | tf_ge  => val_convert target_size 1 (Bits (UntypedSemantics.ubits2_sigma (UCompare false cGe) v1 v2))
                  end
            end
        end. 

    Lemma value_of_expr_bits:
      forall expr Gamma f_dst,
        (forall s, has_sized_bits (lookup_s Gamma s) (spec_states_size s)) ->
        has_sized_bits (value_of_expr expr Gamma f_dst) f_dst.
    Proof.
      intros. 
      generalize dependent f_dst.
      induction expr; intros.
      {
        econstructor. cbn2. split. reflexivity. rewrite vect_to_list_length. reflexivity.
      } {
        cbn2. specialize (H v). apply val_convert_sz_correct. exact H.
      } {
        cbn2. generalize sigma_input_sized_bits; intros. specialize (H0 v). apply val_convert_sz_correct. exact H0.
      } {
        specialize (IHexpr f_dst).
        cbn2. unfold UntypedSemantics.usigma1.
        extract_sized_bits IHexpr. cbn. econstructor. 
        split. reflexivity. rewrite map_length. exact Hsz.
      } {
        cbn2. destruct (IHexpr1 f_dst) as [bl1 [Hval1 Hlen1]]. destruct (IHexpr2 f_dst) as [bl2 [Hval2 Hlen2]].
        rewrite Hval1. rewrite Hval2. destruct op.
        1-3: econstructor; split; try reflexivity; rewrite Common.datatypes_length_bitwise; unfold bits_of_value_lossy; rewrite Hlen1, Hlen2; lia.
        1-2: econstructor; split; try reflexivity; rewrite vect_to_list_length; unfold bits_of_value_lossy; lia.
        { apply val_convert_sz_correct. econstructor; split; try reflexivity; rewrite vect_to_list_length; unfold bits_of_value_lossy; lia. }
        { destr; subst. 
          1-2: apply val_convert_sz_correct; econstructor; split; try reflexivity; rewrite vect_to_list_length; unfold bits_of_value_lossy; lia.
          all: (
            apply val_convert_sz_correct; econstructor; split; try reflexivity; destr; try reflexivity;
            clear Heqs; contradict n; destruct (IHexpr1 cmp_sz) as [? [HE1 HlenE1]]; destruct (IHexpr2 cmp_sz) as [? [HE2 HlenE2]];
            rewrite HE1, HE2; cbn; lia
          ).
        }
      }
    Qed.

    Lemma interp_act_expr_to_uaction:
      forall (hw_reg_state: hw_env_t) (Gamma: list (string * val)) sched_log action_log expr f_dst,
      
        (forall s, has_var Gamma (_reg_name tf_ctx s)) ->

        (forall s, has_sized_bits (lookup_s Gamma s) (spec_states_size s)) ->

        UntypedSemantics.interp_action hw_reg_state sigma Gamma sched_log action_log (expr_to_uaction tf_ctx expr f_dst) 
          = Some ( (action_log, value_of_expr expr Gamma f_dst, Gamma) ).
    Proof.
      intros. rename H into HVar. rename H0 into HBits.

      generalize dependent f_dst.
      induction expr; intros.
      { (* tf_const *)
        reflexivity.
      } { (* tf_var *)
        cbn2. apply synth_convert_is_val_convert. cbn2. split.
        { specialize (HVar v). unfold lookup_s, lookup. extract_var HVar. reflexivity. }
        { specialize (HBits v). exact HBits. }
      } { (* tf_var *)
        cbn2. apply synth_convert_is_val_convert. cbn2. split.
        { reflexivity. }
        { exact (sigma_input_sized_bits v). }
      } { (* tf_op1 *)
        cbn2. rewrite IHexpr. cbn2. 
        generalize (value_of_expr_bits expr Gamma f_dst HBits); intros H0.
        extract_sized_bits H0. cbn. reflexivity.
      } { (* tf_op2 *)
        cbn -[eq_dec].
        destruct op.
        1-5: (
          cbn2; rewrite IHexpr1; cbn2; rewrite IHexpr2; cbn2;
          generalize (value_of_expr_bits expr1 Gamma f_dst HBits); intros H0; extract_sized_bits H0; 
          generalize (value_of_expr_bits expr2 Gamma f_dst HBits); intros H1; extract_sized_bits H1; 
          cbn; reflexivity
        ).
        { 
          apply synth_convert_is_val_convert. cbn2.
          rewrite IHexpr1. cbn2. rewrite IHexpr2. cbn2.
          generalize (value_of_expr_bits expr1 Gamma f_dst HBits); intros H0; extract_sized_bits H0; 
          generalize (value_of_expr_bits expr2 Gamma f_dst HBits); intros H1; extract_sized_bits H1; 
          cbn. split; try reflexivity. econstructor; split; try reflexivity.
          rewrite Common.datatypes_length_vect_fold_left_of_bits. lia.
        }
        {
          destruct cmp_op. 
          1-2: (
            apply synth_convert_is_val_convert; cbn2;
            rewrite IHexpr1; cbn2; rewrite IHexpr2; cbn2;
            generalize (value_of_expr_bits expr1 Gamma f_dst HBits); intros H0; extract_sized_bits H0; 
            generalize (value_of_expr_bits expr2 Gamma f_dst HBits); intros H1; extract_sized_bits H1; 
            cbn; split; try reflexivity; econstructor; split; try reflexivity
          ).
          all: (
            apply synth_convert_is_val_convert; cbn2;
            rewrite IHexpr1; cbn2; rewrite IHexpr2; cbn2;
            generalize (value_of_expr_bits expr1 Gamma cmp_sz HBits); intros H0; extract_sized_bits H0; 
            generalize (value_of_expr_bits expr2 Gamma cmp_sz HBits); intros H1; extract_sized_bits H1; 
            cbn2; split; try reflexivity; subst; destr; econstructor; split; try reflexivity
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
      forall expr hw_reg_state Gamma fs_state n input PGokS,
        StateR hw_reg_state fs_state ->
        InputR input ->  
        (forall s, has_var Gamma (_reg_name tf_ctx s)) ->
        value_of_expr expr Gamma n
        = Bits (vect_to_list (n:=n) (spec_eval_expr expr (SpecStateEnvExt fs_state Gamma PGokS) input)).
    Proof.
      intros.

      generalize dependent n.
      induction expr; intros. 
      { (* tf_const *)
        cbn2. reflexivity.
      } 
      { (* tf_var *)
        cbn2. rewrite <- (val_convert_correct (spec_states_size v)). 2: { reflexivity. }
        rewrite Common.getenv_ccreate. specialize (H1 v). extract_var H1.
        cbn2. generalize (val_of_val_to_bits_correct). intros Hval. cbn in Hval.
        rewrite Hval. reflexivity.
      }
      { (* tf_op1 *)
        cbn2. specialize (H0 v). cbn2. 
        rewrite <- (val_convert_correct (spec_inputs_size v)). 2: { reflexivity. }
        rewrite H0. reflexivity. 
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
        - destr; rewrite IHexpr1; rewrite IHexpr2.
          * rewrite val_convert_correct2. 2: { destr; unfold Datatypes.length. all: lia. } 
            repeat f_equal. unfold BitsToLists.val_beq. destruct BitsToLists.list_eqb eqn:Heqb.
              {
                rewrite (BitsToLists.list_eqb_correct _ Bool.eqb_true_iff) in Heqb.
                unfold beq_dec. apply vect_to_list_inj in Heqb. destruct (eq_dec _ _); try congruence.
              }
              {
                rewrite <- Bool.not_true_iff_false, (BitsToLists.list_eqb_correct _ Bool.eqb_true_iff) in Heqb.
                unfold beq_dec. destruct (eq_dec _ _); try congruence.
              }
          * rewrite val_convert_correct2. 2: { destr; unfold Datatypes.length. all: lia. } 
            repeat f_equal. unfold BitsToLists.val_beq. destruct BitsToLists.list_eqb eqn:Heqb.
              {
                rewrite (BitsToLists.list_eqb_correct _ Bool.eqb_true_iff) in Heqb.
                unfold beq_dec. apply vect_to_list_inj in Heqb. destruct (eq_dec _ _); try congruence.
              }
              {
                rewrite <- Bool.not_true_iff_false, (BitsToLists.list_eqb_correct _ Bool.eqb_true_iff) in Heqb.
                unfold beq_dec. destruct (eq_dec _ _); try congruence.
              }
          * rewrite val_convert_correct2. 2: { destr; unfold Datatypes.length. all: lia. } 
            repeat f_equal. destruct eq_dec. 
            + unfold Bits.unsigned_lt in *; unfold Bits.lift_comparison in *. simpl_eq.
              rewrite !Koika.BitsToLists.vect_of_list_to_list, !Bits.to_N_rew.
              reflexivity.
            + cbn in n0. rewrite !vect_to_list_length in n0.
              unfold Bits.unsigned_lt in *; unfold Bits.lift_comparison in *.
              destr.
          * rewrite val_convert_correct2. 2: { destr; unfold Datatypes.length. all: lia. } 
            repeat f_equal. destruct eq_dec. 
            + unfold Bits.unsigned_le in *; unfold Bits.lift_comparison in *. simpl_eq.
              rewrite !Koika.BitsToLists.vect_of_list_to_list, !Bits.to_N_rew.
              reflexivity.
            + cbn in n0. rewrite !vect_to_list_length in n0.
              unfold Bits.unsigned_le in *; unfold Bits.lift_comparison in *.
              destr.
          * rewrite val_convert_correct2. 2: { destr; unfold Datatypes.length. all: lia. } 
            repeat f_equal. destruct eq_dec. 
            + unfold Bits.unsigned_gt in *; unfold Bits.lift_comparison in *. simpl_eq.
              rewrite !Koika.BitsToLists.vect_of_list_to_list, !Bits.to_N_rew.
              reflexivity.
            + cbn in n0. rewrite !vect_to_list_length in n0.
              unfold Bits.unsigned_gt in *; unfold Bits.lift_comparison in *.
              destr.
          * rewrite val_convert_correct2. 2: { destr; unfold Datatypes.length. all: lia. } 
            repeat f_equal. destruct eq_dec. 
            + unfold Bits.unsigned_ge in *; unfold Bits.lift_comparison in *. simpl_eq.
              rewrite !Koika.BitsToLists.vect_of_list_to_list, !Bits.to_N_rew.
              reflexivity.
            + cbn in n0. rewrite !vect_to_list_length in n0.
              unfold Bits.unsigned_ge in *; unfold Bits.lift_comparison in *.
              destr.
      }
    Qed.

  End Expressions.

  Section CmdGuard.
    
    Lemma interp_rule_wrong_cmd:
      forall (hw_reg_state: hw_env_t) log cmd,
      sigma (ext_in_cmd tf_ctx) val_true <> encoded_cmd cmd ->
      interp_rule hw_reg_state sigma log (impl_rules (rule_cmd tf_ctx cmd)) = None.
    Proof.
      intros.
      Set Printing All. (* <- IDK why this is needed currently? *)
      unfold rules, _rule_cmd.
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
      Unset Printing All.
    Qed.

    Lemma interp_scheduler_no_cmd:
      forall (hw_reg_state: hw_env_t) cmd log (l: list spec_action) sched,
      sigma (ext_in_cmd tf_ctx) val_true = encoded_cmd cmd ->
      (~ In cmd l) ->
      UntypedSemantics.interp_scheduler' impl_rules hw_reg_state sigma log 
        (fold_right (fun (t : spec_action) acc => rule_cmd tf_ctx t |> acc) sched l)
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

    Lemma interp_rule_out:
      forall (hw_reg_state: hw_env_t) log out,
        may_read log P1 (tf_out tf_ctx out) = true ->
        may_write log log_empty P1 (tf_out_ack tf_ctx out) = true ->
        interp_rule hw_reg_state sigma log (impl_rules (rule_out tf_ctx out)) = 
        Some (log_cons (tf_out_ack tf_ctx out)
          {| kind := LogWrite; port := P1;  UntypedLogs.val := sigma (ext_output tf_ctx out)
              match latest_write0 (log_app log_empty log) (tf_out tf_ctx out) with
              | Some v => v
              | None => hw_reg_state.[tf_out tf_ctx out]
              end
          |} (log_cons (tf_out tf_ctx out) {| kind := LogRead; port := P1; UntypedLogs.val := Bits [] |} log_empty)).
    Proof.
      intros.
      unfold impl_rules, interp_rule, interp_action.
      rewrite H. cbn -[may_write log_cons log_empty latest_write0 log_app].
      rewrite may_write_log_cons_neq. 2: congruence.
      rewrite H0. reflexivity.
    Qed.

    Lemma interp_rule_out_fail:
      forall (hw_reg_state: hw_env_t) log out,
        may_read log P1 (tf_out tf_ctx out) = false \/ may_write log log_empty P1 (tf_out_ack tf_ctx out) = false ->
        interp_rule hw_reg_state sigma log (impl_rules (rule_out tf_ctx out)) = None.
    Proof.
      intros.
      unfold impl_rules, interp_rule, interp_action.
      destruct (may_read log P1 (tf_out tf_ctx out)). 2: reflexivity.
      cbn -[may_write log_empty]. rewrite may_write_log_cons_neq. 2: congruence.
      destruct (may_write log log_empty P1 (tf_out_ack tf_ctx out)). 2: reflexivity.
      lia.
    Qed.

    Lemma interp_scheduler_out_no_writes:
      forall (hw_reg_state: hw_env_t) reg log,
        isStateReg reg \/ isOutputReg reg ->
        latest_write (interp_scheduler' impl_rules hw_reg_state sigma log (system_schedule_outputs tf_ctx)) reg = latest_write log reg.
    Proof.
      intros. unfold system_schedule_outputs.

      assert (NoDup (spec_all_outputs)).
      { apply NoDup_map_inv with (f:=(finite_index (FiniteType:=spec_outputs_fin))). apply finite_injective. }

      generalize dependent H0. generalize dependent log.
      induction (spec_all_outputs); intros. reflexivity.
      inversion H0; subst.
      cbn [interp_scheduler' fold_right]. destruct (may_read log P1 (tf_out tf_ctx a)) eqn:H_read; destruct (may_write log log_empty P1 (tf_out_ack tf_ctx a)) eqn:H_write.
      2-4: rewrite interp_rule_out_fail; try apply (IHl _ H4); (* hammer *) hauto lq:on. 
      
      rewrite interp_rule_out.
      2: exact H_read. 2: exact H_write. set (new_log := (log_app _ log)).

      specialize (IHl new_log H4). clear H4.
      rewrite IHl. clear IHl.

      subst new_log. cbn. unfold_getenv_all. rewrite !cassoc_ccreate.
      rewrite Common.cassoc_put_neq.
      {
        destruct (eq_dec (tf_out tf_ctx a) reg).
        - rewrite e. rewrite Common.cassoc_put_eq. reflexivity.
        - rewrite !Common.cassoc_put_neq; try congruence. rewrite !cassoc_ccreate. rewrite app_nil_l. reflexivity.
      }
      destruct H; unfold isStateReg, isOutputReg in H; destruct H; congruence.
    Qed.   

    Lemma writes_of_interp_scheduler_wrong_cmds_only:
      forall (hw_reg_state: hw_env_t) cmd reg log l,
        isStateReg reg \/ isOutputReg reg ->
        sigma (ext_in_cmd tf_ctx) val_true = encoded_cmd cmd ->
        ~ In cmd l ->
        latest_write (interp_scheduler' impl_rules hw_reg_state sigma log
          (fold_right (fun (t : spec_action) (acc : Frontend.scheduler) => rule_cmd tf_ctx t |> acc)
            (fold_right (fun (t : spec_outputs) (acc : Frontend.scheduler) => rule_out tf_ctx t |> acc) (done) spec_all_outputs) l)) reg =
        latest_write log reg.
    Proof.
      intros.
      rewrite (interp_scheduler_no_cmd _ cmd); try exact H0; try exact H1.
      rewrite interp_scheduler_out_no_writes; try exact H; try reflexivity.
    Qed.

    Lemma writes_of_interp_scheduler_only_cmd:
      forall (hw_reg_state: hw_env_t) cmd reg,
        isStateReg reg \/ isOutputReg reg ->
        sigma (ext_in_cmd tf_ctx) val_true = encoded_cmd cmd ->
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

      cbn [fold_right system_schedule_actions system_schedule_outputs interp_scheduler'].
      destruct (eq_dec a cmd).
      {
        subst. clear IHl.
        assert (~ In cmd l). { inversion H_nodup; subst. exact H3. }
        destr.
        all: rewrite (writes_of_interp_scheduler_wrong_cmds_only _ cmd); try exact H; try exact H0; try exact H1; reflexivity.
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
          unfold not. intros. assert (encoded_cmd cmd = encoded_cmd a). { rewrite <- H0. rewrite H1. reflexivity. } 
          apply encoded_cmd_inj' in H2. contradiction. congruence.
        }
      }
    Qed.
    
  End CmdGuard.

  Section RegUpdates.

    Definition var_from_reg (r: reg_t tf_ctx) : string :=
      match r with
      | tf_reg _ x => _reg_name tf_ctx x
      | tf_out _ x => _out_name tf_ctx x
      | tf_out_ack _ x => "undefined"
      end.

    Definition make_hw_state (hw_reg_state: hw_env_t) (Gamma: list (string * val)) :=
      RegCEnv.(create) (fun r => 
        match BitsToLists.list_assoc (V:=val) Gamma (var_from_reg r) with
          | Some v => v
          | None => hw_reg_state.[r]
        end
      ).

    Definition sem_updates_to_Gamma_ext (updates: list sem_update) : list (string * val) :=
      flat_map (fun update =>
        match update with
          | tf_no_update _ _ => [ ("_unused", val_unreachable ) ]
          | tf_st_update _ _ dst value => [ (_reg_name tf_ctx dst, val_of_value value) ]
          | tf_out_update _ _ dst value => [ (_out_name tf_ctx dst, val_of_value value) ]
        end) (rev updates).

    Definition sem_updates_to_Gamma_ext_app:
      forall updates1 updates2,
        sem_updates_to_Gamma_ext (updates1 ++ updates2) =
        sem_updates_to_Gamma_ext updates2 ++ sem_updates_to_Gamma_ext updates1.
    Proof.
      unfold sem_updates_to_Gamma_ext.
      intros. rewrite rev_app_distr. rewrite flat_map_app. reflexivity.
    Qed.

    Lemma sem_updates_to_Gamma_ext_keeps_state_ok:
      forall updates Gamma,
        Gamma_ok_state Gamma ->
        Gamma_ok_state (sem_updates_to_Gamma_ext updates ++ Gamma).
    Proof.
      intros. apply Gamma_ok_state_app with (1:=H).
      intros s v. induction updates; intros.
      { inversion H0. }
      {
        cbn in H0. rewrite flat_map_app in H0. cbn in H0.
        apply in_app_or in H0. destruct H0.
        { apply IHupdates. exact H0. }
        destruct a; cbn in *.
        - destruct H0; timeout 10 fcrush.
        - assert (v = (Bits (vect_to_list value))) by (* hammer *) timeout 10 sfirstorder. rewrite H1. clear H1.
          assert (_reg_name tf_ctx var = _reg_name tf_ctx s) by (* hammer *) timeout 10 sfirstorder. apply reg_name_inj in H1. subst s.
          unfold has_sized_bits. econstructor. split; try reflexivity. rewrite vect_to_list_length. reflexivity.
        - destruct H0; timeout 10 fcrush.
      }
    Qed.

    Lemma sem_updates_to_Gamma_ext_keeps_output_ok:
      forall updates Gamma,
        Gamma_ok_output Gamma ->
        Gamma_ok_output (sem_updates_to_Gamma_ext updates ++ Gamma).
    Proof.
      intros. apply Gamma_ok_output_app with (1:=H).
      intros s v. induction updates; intros.
      { inversion H0. }
      {
        cbn in H0. rewrite flat_map_app in H0. cbn in H0.
        apply in_app_or in H0. destruct H0.
        { apply IHupdates. exact H0. }
        destruct a; cbn in *.
        - destruct H0; timeout 10 fcrush.
        - destruct H0; timeout 10 fcrush.
        - assert (v = (Bits (vect_to_list value))) by (* hammer *) timeout 10 sfirstorder. rewrite H1. clear H1.
          assert (_out_name tf_ctx var = _out_name tf_ctx s) by (* hammer *) timeout 10 sfirstorder. apply out_name_inj in H1. subst s.
          unfold has_sized_bits. econstructor. split; try reflexivity. rewrite vect_to_list_length. reflexivity.
      }
    Qed.
      

    Lemma sem_updates_to_Gamma_ext_correct:
      forall updates rule_ops fs_state fs_input fs_output Gamma GokS GokO GokS'' GokO'',
        updates = fst (sem_ops_updates rule_ops (SpecStateEnvExt fs_state Gamma GokS, SpecOutputEnvExt fs_output Gamma GokO) fs_input) ->
        snd (sem_ops_updates rule_ops (SpecStateEnvExt fs_state Gamma GokS, SpecOutputEnvExt fs_output Gamma GokO) fs_input) =
        (SpecStateEnvExt fs_state (sem_updates_to_Gamma_ext updates ++ Gamma) GokS'', SpecOutputEnvExt fs_output (sem_updates_to_Gamma_ext updates ++ Gamma) GokO'').
    Proof.
      intros. 
      generalize dependent Gamma.
      generalize dependent updates.

      induction rule_ops; intros.
      {
        apply Common.pair_inj'; cbn [fst snd]; apply equiv_eq; unfold equiv; intros; unfold_getenv_all.
        {
          cbn. unfold sem_ops_updates, sem_op_step_commit_state, sem_updates_to_Gamma_ext in *. cbn in H. 
          set (fun1 := fun _ _ => _) in *. set (fun2 := fun update : sem_update => _) in *.
          destr; rewrite ?cassoc_ccreate.
          {
            generalize dependent (GokS'' k). generalize dependent (GokS k).
            rewrite H. subst fun1; cbn -[eq_dec].
            destruct (eq_dec (_reg_name tf_ctx k) "_unused"). { unfold _reg_name in e. contradict e. timeout 10 fcrush. }
            intros. generalize dependent h. unfold lookup_s.  
            rewrite (lookup_cons_neq _ (_reg_name tf_ctx k) "_unused"). 2: { unfold _reg_name in *. timeout 10 fcrush. }
            intros. unfold val_to_bits. vect_to_list_t. reflexivity.
          }
          {
            generalize dependent (GokS'' k). generalize dependent (GokS k).
            rewrite H. subst fun1; cbn -[eq_dec].
            destruct (eq_dec (_reg_name tf_ctx k) (_reg_name tf_ctx var)); intros. 
            {
              apply reg_name_inj in e. subst k. rewrite Common.cassoc_put_eq. cbn. unfold val_to_bits. vect_to_list_t.
              generalize dependent h. unfold lookup_s. rewrite lookup_cons_eq. 2: { reflexivity. }
              unfold bits_of_value_lossy. rewrite Common.bits_of_list_vect_to_list. intros.
              vect_to_list_t. reflexivity.
            }
            {
              apply reg_name_inj' in n as Hn. rewrite Common.cassoc_put_neq. 2: hauto. rewrite !cassoc_ccreate.
              generalize (GokS k). unfold lookup_s in *. cbn -[eq_dec].
              cbn. intros. generalize dependent h.
              rewrite (lookup_cons_neq _ (_reg_name tf_ctx k) (_reg_name tf_ctx var)). 2: { exact n. }
              intros. unfold val_to_bits. vect_to_list_t. reflexivity. 
            }
          }
          {
            generalize dependent (GokS'' k). generalize dependent (GokS k).
            rewrite H. subst fun1; cbn -[eq_dec].
            destruct (eq_dec (_reg_name tf_ctx k) (_out_name tf_ctx var)). { unfold _reg_name in e. contradict e. timeout 10 fcrush. }
            intros. generalize dependent h. unfold lookup_s.  
            rewrite (lookup_cons_neq _ (_reg_name tf_ctx k) (_out_name tf_ctx var)). 2: { unfold _reg_name in *. timeout 10 fcrush. }
            intros. unfold val_to_bits. vect_to_list_t. reflexivity.
          }
        }
        {
          cbn. unfold sem_ops_updates, sem_op_step_commit_output, sem_updates_to_Gamma_ext in *. cbn in H. 
          set (fun1 := fun _ _ => _) in *. set (fun2 := fun update : sem_update => _) in *.
          destr; rewrite ?cassoc_ccreate.
          {
            generalize dependent (GokO'' k). generalize dependent (GokO k).
            rewrite H. subst fun1; cbn -[eq_dec].
            destruct (eq_dec (_out_name tf_ctx k) "_unused"). { unfold _out_name in e. contradict e. timeout 10 fcrush. }
            intros. generalize dependent h0. unfold lookup_o.  
            rewrite (lookup_cons_neq _ (_out_name tf_ctx k) "_unused"). 2: { unfold _out_name in *. timeout 10 fcrush. }
            intros. unfold val_to_bits. vect_to_list_t. reflexivity.
          }
          {
            generalize dependent (GokO'' k). generalize dependent (GokO k).
            rewrite H. subst fun1; cbn -[eq_dec].
            destruct (eq_dec (_out_name tf_ctx k) (_reg_name tf_ctx var)). { unfold _out_name in e. contradict e. timeout 10 fcrush. }
            intros. generalize dependent h0. unfold lookup_o.  
            rewrite (lookup_cons_neq _ (_out_name tf_ctx k) (_reg_name tf_ctx var)). 2: { unfold _out_name in *. timeout 10 fcrush. }
            intros. unfold val_to_bits. vect_to_list_t. reflexivity.    
          }
          {
            generalize dependent (GokO'' k). generalize dependent (GokO k).
            rewrite H. subst fun1; cbn -[eq_dec].
            destruct (eq_dec (_out_name tf_ctx k) (_out_name tf_ctx var)); intros. 
            {
              apply out_name_inj in e. subst k. rewrite Common.cassoc_put_eq. cbn. unfold val_to_bits. vect_to_list_t.
              generalize dependent h. unfold lookup_o. rewrite lookup_cons_eq. 2: { reflexivity. }
              unfold bits_of_value_lossy. rewrite Common.bits_of_list_vect_to_list. intros.
              vect_to_list_t. reflexivity.
            }
            {
              apply out_name_inj' in n as Hn. rewrite Common.cassoc_put_neq. 2: hauto. rewrite !cassoc_ccreate.
              generalize (GokO k). unfold lookup_o in *. cbn -[eq_dec].
              cbn. intros. generalize dependent h.
              rewrite (lookup_cons_neq _ (_out_name tf_ctx k) (_out_name tf_ctx var)). 2: { exact n. }
              intros. unfold val_to_bits. vect_to_list_t. reflexivity. 
            }
          }
        }
      }
      {
        apply Common.pair_inj'; cbn [fst snd]; apply equiv_eq; unfold equiv; intros; unfold_getenv_all.
        {
          cbn -[SpecStateEnvExt SpecOutputEnvExt]. 
          destruct (sem_ops_updates rule_ops1 _ _ ) as [updates1 state_output1] eqn:H_ops1.
          pose proof (f_equal fst H_ops1) as H_upd1; pose proof (f_equal snd H_ops1) as H_st1. cbn [fst snd] in H_upd1, H_st1; symmetry in H_upd1, H_st1.
          clear H_ops1. rewrite H_upd1 in *. clear H_upd1. rewrite H_st1 in *. clear H_st1.

          destruct (sem_ops_updates rule_ops2 _ _ ) as [updates2 state_output2] eqn:H_ops2.
          pose proof (f_equal fst H_ops2) as H_upd2; pose proof (f_equal snd H_ops2) as H_st2. cbn [fst snd] in H_upd2, H_st2; symmetry in H_upd2, H_st2.
          clear H_ops2. rewrite H_upd2 in *. clear H_upd2. rewrite H_st2 in *. clear H_st2.
          cbn -[SpecStateEnvExt SpecOutputEnvExt].
          
          clear updates1 updates2 state_output1 state_output2.
          set (updates1 := fst (sem_ops_updates rule_ops1 (SpecStateEnvExt fs_state Gamma GokS, SpecOutputEnvExt fs_output Gamma GokO) fs_input)).
          set (updates2 := fst (sem_ops_updates rule_ops2 (SpecStateEnvExt fs_state (sem_updates_to_Gamma_ext updates1 ++ Gamma) (sem_updates_to_Gamma_ext_keeps_state_ok updates1 Gamma GokS), 
                                                          SpecOutputEnvExt fs_output (sem_updates_to_Gamma_ext updates1 ++ Gamma) (sem_updates_to_Gamma_ext_keeps_output_ok updates1 Gamma GokO)) fs_input)).
          erewrite IHrule_ops1 with (updates:=updates1). 2: { reflexivity. }
          erewrite IHrule_ops2 with (updates:=updates2). 2: { reflexivity. }

          cbn. rewrite ?cassoc_ccreate. apply val_to_bits_equiv.
          rewrite app_assoc. rewrite <- sem_updates_to_Gamma_ext_app. f_equal. f_equal. f_equal. 

          subst updates updates1 updates2. cbn -[SpecStateEnvExt SpecOutputEnvExt].  
          destruct (sem_ops_updates rule_ops1 _ _ ) as [updatesA1 state_outputA1] eqn:H_ops1.
          pose proof (f_equal fst H_ops1) as H_upd1; pose proof (f_equal snd H_ops1) as H_st1. cbn [fst snd] in H_upd1, H_st1; symmetry in H_upd1, H_st1.
          clear H_ops1. rewrite H_upd1 in *. rewrite H_st1 in *. 
          cbn -[SpecStateEnvExt SpecOutputEnvExt]. 

          set (updates2a := sem_ops_updates rule_ops2 _ _). set (updates2b := sem_ops_updates rule_ops2 _ _).
          assert (updates2a = updates2b). 
          2: { rewrite H. clear H. destruct (updates2b) as [updates2 state_output2] eqn:H_ops2. reflexivity. }
          
          subst. subst updates2a. subst updates2b. f_equal.
          set (updates1 := fst (sem_ops_updates rule_ops1 (SpecStateEnvExt fs_state Gamma GokS, SpecOutputEnvExt fs_output Gamma GokO) fs_input)).
          erewrite IHrule_ops1 with (updates:=updates1). 2: { reflexivity. } reflexivity.
        }
        {
          cbn -[SpecStateEnvExt SpecOutputEnvExt]. 
          destruct (sem_ops_updates rule_ops1 _ _ ) as [updates1 state_output1] eqn:H_ops1.
          pose proof (f_equal fst H_ops1) as H_upd1; pose proof (f_equal snd H_ops1) as H_st1. cbn [fst snd] in H_upd1, H_st1; symmetry in H_upd1, H_st1.
          clear H_ops1. rewrite H_upd1 in *. clear H_upd1. rewrite H_st1 in *. clear H_st1.

          destruct (sem_ops_updates rule_ops2 _ _ ) as [updates2 state_output2] eqn:H_ops2.
          pose proof (f_equal fst H_ops2) as H_upd2; pose proof (f_equal snd H_ops2) as H_st2. cbn [fst snd] in H_upd2, H_st2; symmetry in H_upd2, H_st2.
          clear H_ops2. rewrite H_upd2 in *. clear H_upd2. rewrite H_st2 in *. clear H_st2.
          cbn -[SpecStateEnvExt SpecOutputEnvExt].
          
          clear updates1 updates2 state_output1 state_output2.
          set (updates1 := fst (sem_ops_updates rule_ops1 (SpecStateEnvExt fs_state Gamma GokS, SpecOutputEnvExt fs_output Gamma GokO) fs_input)).
          set (updates2 := fst (sem_ops_updates rule_ops2 (SpecStateEnvExt fs_state (sem_updates_to_Gamma_ext updates1 ++ Gamma) (sem_updates_to_Gamma_ext_keeps_state_ok updates1 Gamma GokS), 
                                                          SpecOutputEnvExt fs_output (sem_updates_to_Gamma_ext updates1 ++ Gamma) (sem_updates_to_Gamma_ext_keeps_output_ok updates1 Gamma GokO)) fs_input)).
          erewrite IHrule_ops1 with (updates:=updates1). 2: { reflexivity. }
          erewrite IHrule_ops2 with (updates:=updates2). 2: { reflexivity. }

          cbn. rewrite ?cassoc_ccreate. apply val_to_bits_equiv.
          rewrite app_assoc. rewrite <- sem_updates_to_Gamma_ext_app. f_equal. f_equal. f_equal.

          subst updates updates1 updates2. cbn -[SpecStateEnvExt SpecOutputEnvExt].  
          destruct (sem_ops_updates rule_ops1 _ _ ) as [updatesA1 state_outputA1] eqn:H_ops1.
          pose proof (f_equal fst H_ops1) as H_upd1; pose proof (f_equal snd H_ops1) as H_st1. cbn [fst snd] in H_upd1, H_st1; symmetry in H_upd1, H_st1.
          clear H_ops1. rewrite H_upd1 in *. rewrite H_st1 in *. 
          cbn -[SpecStateEnvExt SpecOutputEnvExt].

          set (updates2a := sem_ops_updates rule_ops2 _ _). set (updates2b := sem_ops_updates rule_ops2 _ _).
          assert (updates2a = updates2b). 
          2: { rewrite H. clear H. destruct (updates2b) as [updates2 state_output2] eqn:H_ops2. reflexivity. }  

          subst. subst updates2a. subst updates2b. f_equal.
          set (updates1 := fst (sem_ops_updates rule_ops1 (SpecStateEnvExt fs_state Gamma GokS, SpecOutputEnvExt fs_output Gamma GokO) fs_input)).
          erewrite IHrule_ops1 with (updates:=updates1). 2: { reflexivity. } reflexivity.
        }
        Unshelve.
        all: 
          (
            try (apply sem_updates_to_Gamma_ext_keeps_state_ok with (1:=GokS));
            try (apply sem_updates_to_Gamma_ext_keeps_output_ok with (1:=GokO));
            try (rewrite app_assoc; rewrite <- sem_updates_to_Gamma_ext_app; apply sem_updates_to_Gamma_ext_keeps_state_ok with (1:=GokS));
            try (rewrite app_assoc; rewrite <- sem_updates_to_Gamma_ext_app; apply sem_updates_to_Gamma_ext_keeps_output_ok with (1:=GokO))
          ).
      }
      {
        apply Common.pair_inj'; cbn [fst snd]; apply equiv_eq; unfold equiv; intros; unfold_getenv_all.
        {
          cbn -[SpecStateEnvExt SpecOutputEnvExt]. destr; cbn -[SpecStateEnvExt SpecOutputEnvExt].
          {
            erewrite IHrule_ops2.
            { reflexivity. }
            rewrite H. f_equal. cbn -[SpecStateEnvExt SpecOutputEnvExt]. destr.
          }
          {
            erewrite IHrule_ops1.
            { reflexivity. }
            rewrite H. f_equal. cbn -[SpecStateEnvExt SpecOutputEnvExt]. destr.
          }
        }
        {
          cbn -[SpecStateEnvExt SpecOutputEnvExt]. destr; cbn -[SpecStateEnvExt SpecOutputEnvExt].
          {
            erewrite IHrule_ops2.
            { reflexivity. }
            rewrite H. f_equal. cbn -[SpecStateEnvExt SpecOutputEnvExt]. destr.
          }
          {
            erewrite IHrule_ops1.
            { reflexivity. }
            rewrite H. f_equal. cbn -[SpecStateEnvExt SpecOutputEnvExt]. destr.
          }
        }
        Unshelve.
        all: 
          (
            try (apply sem_updates_to_Gamma_ext_keeps_state_ok with (1:=GokS));
            try (apply sem_updates_to_Gamma_ext_keeps_output_ok with (1:=GokO));
            try (rewrite app_assoc; rewrite <- sem_updates_to_Gamma_ext_app; apply sem_updates_to_Gamma_ext_keeps_state_ok with (1:=GokS));
            try (rewrite app_assoc; rewrite <- sem_updates_to_Gamma_ext_app; apply sem_updates_to_Gamma_ext_keeps_output_ok with (1:=GokO))
          ).
      }
    Qed.

    Ltac assert_match_terms_equal :=
      let LM := fresh "LM" in
      let RM := fresh "RM" in
      match goal with
      | [ |- match ?E1 with _ => _ end = match ?E2 with _ => _ end ] =>
        remember E1 as LM; remember E2 as RM;
        assert (LM = RM)
      end.

    Lemma interp_op_to_uaction:
      forall hw_reg_state fs_state fs_input fs_output Gamma sched_log action_log op code GokS GokO,
      StateR hw_reg_state fs_state ->
      InputR fs_input ->
      OutputR hw_reg_state fs_output ->
      has_var_all Gamma (map (_register_var_name tf_ctx) (map (tf_reg tf_ctx) spec_all_states)) ->
        let fs_state' := SpecStateEnvExt fs_state Gamma GokS in
        let fs_output' := SpecOutputEnvExt fs_output Gamma GokO in
        let (updates, fs_state'') := sem_ops_updates (tf_ops_base op) (fs_state', fs_output') fs_input in
        let Gamma' := (sem_updates_to_Gamma_ext updates) ++ Gamma in
          interp_action hw_reg_state sigma Gamma sched_log action_log (op_to_uaction tf_ctx op code) =
          let/opt3 l, v, G := interp_action hw_reg_state sigma Gamma' sched_log action_log code in Some (l, v, tl G).
    Proof.
      intros; rename H into H_state; rename H0 into H_input; rename H1 into H_output. rename H2 into H_hasvar.

      assert (H_hasvar': forall s : spec_states, has_var Gamma (_reg_name tf_ctx s)). {
        intros. apply has_var_all_correct with (var_names:=(map (_register_var_name tf_ctx) (map (tf_reg tf_ctx) spec_all_states))).
        2: exact H_hasvar. rewrite map_map. apply in_map_iff. exists s. split; try reflexivity. 
        exact (spec_all_states_complete s).
      }

      destruct op; cbn [op_to_uaction interp_action sem_ops_updates].
      {
        (* NOP *)
        reflexivity.
      }
      {
        (* ASSIGN *)
        rewrite (interp_act_expr_to_uaction); try exact GokS; try exact H_hasvar'.
        
        rewrite (value_of_expr_correct expr hw_reg_state Gamma fs_state (spec_states_size dst) fs_input GokS); 
        try exact H_state; try exact H_input; try exact H_hasvar'.

        unfold opt_bind.
        assert_match_terms_equal. 2: { rewrite H. reflexivity. } subst.

        reflexivity.
      }
      {
        (* OUTPUT *)
        rewrite (interp_act_expr_to_uaction); try exact GokS; try exact H_hasvar'.
        
        rewrite (value_of_expr_correct expr hw_reg_state Gamma fs_state (spec_outputs_size dst) fs_input GokS); 
        try exact H_state; try exact H_input; try exact H_hasvar'.

        unfold opt_bind.
        assert_match_terms_equal. 2: { rewrite H. reflexivity. } subst.
        
        reflexivity.
      }
    Qed. 

    Lemma interp_aux_state:
      forall Gamma GokS GokO hw_reg_state fs_state fs_input fs_output sched_log action_log rule_ops code,
      StateR hw_reg_state fs_state ->
      InputR fs_input ->
      OutputR hw_reg_state fs_output ->
      has_var_all Gamma (map (_register_var_name tf_ctx) (map (tf_reg tf_ctx) spec_all_states)) ->
        let fs_state' := SpecStateEnvExt fs_state Gamma GokS in
        let fs_output' := SpecOutputEnvExt fs_output Gamma GokO in
        let updates := fst (sem_ops_updates rule_ops (fs_state', fs_output') fs_input) in
        let Gamma' := (sem_updates_to_Gamma_ext updates) ++ Gamma in
          interp_action hw_reg_state sigma Gamma sched_log action_log (_rule_aux tf_ctx rule_ops code) =
          match interp_action hw_reg_state sigma Gamma' sched_log action_log code with
            | Some (l, v, G) => Some (l, v, skipn (length updates) G)
            | None => None
          end.
    Proof.
      intros; rename H into H_state; rename H0 into H_input; rename H1 into H_output; rename H2 into H_hasvar.

      generalize dependent H_output. generalize dependent H_input. generalize dependent H_state.
      generalize dependent code. generalize dependent action_log. generalize dependent sched_log.
      generalize dependent Gamma.
      
      induction rule_ops; intros.
      {
        cbn [sem_ops_updates _rule_aux interp_action].
        rewrite (interp_op_to_uaction _ _ _ _ _ _ _ _ _ GokS GokO H_state H_input H_output H_hasvar).
        unfold opt_bind. cbn [Datatypes.length]. reflexivity.
      } 
      {
        cbn [sem_ops_updates _rule_aux interp_action] in *.
        destruct (sem_ops_updates rule_ops1 (fs_state', fs_output') fs_input) as [updates1 state1] eqn:Heq1.
        destruct (sem_ops_updates rule_ops2 state1 fs_input) as [updates2 state2] eqn:Heq2.
        subst fs_state' fs_output'. 

        specialize (IHrule_ops1 Gamma GokS GokO H_hasvar sched_log action_log (_rule_aux tf_ctx rule_ops2 code) H_state H_input H_output).
        rewrite Heq1 in IHrule_ops1. rewrite IHrule_ops1; clear IHrule_ops1.
        
        set (Gamma'' := (sem_updates_to_Gamma_ext updates1) ++ Gamma).
        assert (Gamma_ok_state Gamma'') as GokS''.
        { apply sem_updates_to_Gamma_ext_keeps_state_ok. exact GokS. }
        assert (Gamma_ok_output Gamma'') as GokO''.
        { apply sem_updates_to_Gamma_ext_keeps_output_ok. exact GokO. }
        assert (has_var_all Gamma'' (map (_register_var_name tf_ctx) (map (tf_reg tf_ctx) spec_all_states))) as H_hasvar''. {
          subst Gamma''. apply has_var_all_ignore_left. exact H_hasvar.
        }

        specialize (IHrule_ops2 Gamma'' GokS'' GokO'' H_hasvar'').
        replace (SpecStateEnvExt fs_state Gamma'' GokS'', SpecOutputEnvExt fs_output Gamma'' GokO'') with state1 in IHrule_ops2.
        2: {
          clear IHrule_ops2. 
          pose proof (f_equal fst Heq1) as H_upd; pose proof (f_equal snd Heq1) as H_st; cbn [fst snd] in H_upd, H_st; symmetry in H_upd, H_st.
          subst Gamma''. rewrite H_st. generalize dependent H_upd.
          apply sem_updates_to_Gamma_ext_correct.
        } 
        rewrite Heq2 in IHrule_ops2; clear Heq2.

        rewrite IHrule_ops2; clear IHrule_ops2; try exact H_state; try exact H_input; try exact H_output.
        subst Gamma'' Gamma' updates. cbn [fst]. rewrite (sem_updates_to_Gamma_ext_app updates1 updates2).
        apply Common.tf_h_match_skipn_app.
        - rewrite app_length. lia.
        - rewrite app_assoc. reflexivity.
      }
      {
        assert (H_hasvar': forall s : spec_states, has_var Gamma (_reg_name tf_ctx s)). {
          intros. apply has_var_all_correct with (var_names:=(map (_register_var_name tf_ctx) (map (tf_reg tf_ctx) spec_all_states))).
          2: exact H_hasvar. rewrite map_map. apply in_map_iff. exists s. split; try reflexivity. 
          exact (spec_all_states_complete s).
        }

        cbn [sem_ops_updates _rule_aux interp_action] in *.
        rewrite (interp_act_expr_to_uaction); try exact GokS; try exact H_hasvar'.

        rewrite (value_of_expr_correct cond hw_reg_state Gamma fs_state 1 fs_input GokS); try exact H_state; try exact H_input; try exact H_hasvar'.

        subst Gamma' updates fs_state'. cbn -[SpecStateEnvExt]. 
        rewrite Common.bits_single_is_neg_beq_dec.
        destr; cbn [negb].
        {
          rewrite (IHrule_ops1 Gamma GokS GokO); clear IHrule_ops1; clear IHrule_ops2; 
          try exact H_state; try exact H_input; try exact H_output; try exact GokS; try exact GokO; try exact H_hasvar.
          apply Common.tf_h_match_skipn. reflexivity. reflexivity.
        }
        {
          rewrite (IHrule_ops2 Gamma GokS GokO); clear IHrule_ops1; clear IHrule_ops2; 
          try exact H_state; try exact H_input; try exact H_output; try exact GokS; try exact GokO; try exact H_hasvar.
          apply Common.tf_h_match_skipn. reflexivity. reflexivity.
        }
      }
    Qed. 

    Lemma interp_scheduler_correct:
      forall cmd fs_state hw_reg_state fs_input last_fs_output reg,
      sigma (ext_in_cmd tf_ctx) val_true = encoded_cmd cmd ->
      StateR hw_reg_state fs_state ->
      InputR fs_input ->
      OutputR hw_reg_state last_fs_output -> 
      isStateReg reg \/ isOutputReg reg ->
        latest_write (interp_scheduler' impl_rules hw_reg_state sigma log_empty system_schedule) reg
        = 
          let out_wrapper := (fun o : spec_outputs => (tf_out tf_ctx o, _out_name tf_ctx o)) in
          let st_wrapper := (fun s : spec_states => (tf_reg tf_ctx s, _reg_name tf_ctx s)) in
          let Gamma' := Gamma_after_read_vars0 hw_reg_state 
                    (Gamma_after_read_vars0 hw_reg_state [] (map (tf_reg tf_ctx) spec_all_states) (_register_var_name tf_ctx))
                    (map (tf_out tf_ctx) spec_all_outputs) (_register_var_name tf_ctx) in
          latest_write (log_app
              (ActionLog_after_write_vars0
                (sem_updates_to_Gamma_ext (fst (sem_ops_updates (spec_action_ops cmd) (fs_state, last_fs_output) fs_input)) ++ Gamma')
                (ActionLog_after_write_vars0
                  (sem_updates_to_Gamma_ext (fst (sem_ops_updates (spec_action_ops cmd) (fs_state, last_fs_output) fs_input)) ++ Gamma')
                  (ActionLog_after_read_vars0 (ActionLog_after_read_vars0 log_empty (map (tf_reg tf_ctx) spec_all_states)) (map (tf_out tf_ctx) spec_all_outputs))
                  (map (tf_reg tf_ctx) (_written_states tf_ctx (spec_action_ops cmd)))
                  (_register_var_name tf_ctx)
                  )
                (map (tf_out tf_ctx) (_written_outputs tf_ctx (spec_action_ops cmd)))
                (_register_var_name tf_ctx)
                ) log_empty) reg.
    Proof.
      intros. rename H into H_sigma_eq_cmd. rename H0 into H_state. rename H1 into H_input. rename H2 into H_output. rename H3 into H_isReg.

      (* Focus only on the rule of the command in question *)
      rewrite (writes_of_interp_scheduler_only_cmd hw_reg_state cmd); try exact H_sigma_eq_cmd; try exact H_isReg.

      (* Focus on Rule Body *)
      cbn [interp_scheduler'].
      rewrite interp_rule_right_cmd'; try exact H_sigma_eq_cmd.
      unfold _rule_cmd. unfold interp_rule.

      (* Read all state registers into vars *)
      rewrite interp_act_read_vars0.
      2: { 
        induction spec_all_states; try reflexivity. cbn -[may_read log_empty]. 
        rewrite andb_true_iff. split.
        - cbn. rewrite !Common.getenv_ccreate. reflexivity.
        - apply IHl.
      }

      (* Read all output registers into vars *)
      cbn [interp_action]. rewrite interp_act_read_vars0.
      2: {
        induction spec_all_outputs; try reflexivity. cbn -[may_read log_empty]. 
        rewrite andb_true_iff. split.
        - cbn. rewrite !Common.getenv_ccreate. reflexivity.
        - apply IHl.
      }

      pose proof (Gamma_after_intro_ok_state hw_reg_state (StateR_means_sized_bits hw_reg_state fs_state H_state)) as GokS.
      pose proof (Gamma_after_intro_ok_output hw_reg_state (OutputR_means_sized_bits hw_reg_state last_fs_output H_output)) as GokO.
      pose proof (Gamma_after_intro_has_state_vars hw_reg_state) as H_hasvar.

      (* Main Body _rule_aux *)
      cbn [interp_action]. 
      rewrite (interp_aux_state _ GokS GokO hw_reg_state fs_state fs_input last_fs_output ); try exact H_state; try exact H_input; try exact H_output; try exact H_hasvar.
      
      
      (* Write back updated state vars *)
      rewrite interp_act_write_vars0.
      2: { exact (ActionLog_after_intro_may_write_all _). }
      2: { 
        apply has_var_all_ignore_left. apply has_var_all_subset with (var_names2:=(map (_register_var_name tf_ctx) (map (tf_reg tf_ctx) spec_all_states))); try exact H_hasvar.
        intros x H_in. apply in_map_iff in H_in. destruct H_in as [s [H_eq H_in]].
        subst x. apply in_map_iff. exists s. split; try reflexivity. apply in_map_iff in H_in. destruct H_in as [s' [H_eq H_in]]. 
        apply in_map_iff. exists s'. split; try congruence. apply (spec_all_states_complete s'). 
      }
      2: { 
        unfold _written_states. apply FinFun.Injective_map_NoDup.
        { unfold FinFun.Injective. intros. inversion H. reflexivity. }
        { apply NoDup_filter. apply NoDup_map_inv with (f:=(finite_index (FiniteType:=spec_states_fin))). apply finite_injective. }      
      }

      (* Write back updated output vars *)
      rewrite interp_act_write_vars0.
      2: { 
        (* may_write_all_of_ActionLog_after_write_vars *)
        rewrite may_write_all_of_ActionLog_after_write_vars. exact (ActionLog_after_intro_may_write_all _).
        intros. intro. rewrite in_map_iff in *. destruct H as [o [H_eqo H_ino]]. destruct H0 as [s [H_eqs H_ins]]. subst. congruence.
      }
      2: { 
        apply has_var_all_ignore_left. apply has_var_all_subset with 
          (var_names2:=(map (_register_var_name tf_ctx) (map (tf_out tf_ctx) spec_all_outputs))); try exact (Gamma_after_intro_has_output_vars hw_reg_state).
        intros x H_in. apply in_map_iff in H_in. destruct H_in as [s [H_eq H_in]].
        subst x. apply in_map_iff. exists s. split; try reflexivity. apply in_map_iff in H_in. destruct H_in as [s' [H_eq H_in]]. 
        apply in_map_iff. exists s'. split; try congruence. apply (spec_all_outputs_complete s'). 
      }
      2: { 
        unfold _written_states. apply FinFun.Injective_map_NoDup.
        { unfold FinFun.Injective. intros. inversion H. reflexivity. }
        { apply NoDup_filter. apply NoDup_map_inv with (f:=(finite_index (FiniteType:=spec_outputs_fin))). apply finite_injective. }      
      }

      cbn [interp_action]. repeat f_equal. 
      {
        apply equiv_eq. unfold equiv; intros. 
        unfold SpecStateEnvExt. rewrite getenv_create. unfold Gamma_ok_state, lookup_s, lookup in *.
        generalize (GokS k). rewrite Gamma_after_intro_is_hw_state. cbn.
        rewrite H_state; intros. apply val_to_bits_of_sized_val_correct.
      }
      {
        apply equiv_eq. unfold equiv; intros. 
        unfold SpecOutputEnvExt. rewrite getenv_create. unfold Gamma_ok_output, lookup_o, lookup in *.
        generalize (GokO k). rewrite Gamma_after_intro_is_hw_output. cbn.
        rewrite H_output; intros. apply val_to_bits_of_sized_val_correct.
      }
      {
        apply equiv_eq. unfold equiv; intros. 
        unfold SpecStateEnvExt. rewrite getenv_create. unfold Gamma_ok_state, lookup_s, lookup in *.
        generalize (GokS k). rewrite Gamma_after_intro_is_hw_state. cbn.
        rewrite H_state; intros. apply val_to_bits_of_sized_val_correct.
      }
      {
        apply equiv_eq. unfold equiv; intros. 
        unfold SpecOutputEnvExt. rewrite getenv_create. unfold Gamma_ok_output, lookup_o, lookup in *.
        generalize (GokO k). rewrite Gamma_after_intro_is_hw_output. cbn.
        rewrite H_output; intros. apply val_to_bits_of_sized_val_correct.
      }
    Qed.

    Lemma sem_updates_state_correct:
      forall cmd fs_state hw_reg_state fs_input last_fs_output state_var,
      StateR hw_reg_state fs_state ->
      InputR fs_input ->
      OutputR hw_reg_state last_fs_output -> 
      lookup
        (sem_updates_to_Gamma_ext (fst (sem_ops_updates (spec_action_ops cmd) (fs_state, last_fs_output) fs_input)) ++
          Gamma_after_read_vars0 hw_reg_state (Gamma_after_read_vars0 hw_reg_state [] (map (tf_reg tf_ctx) spec_all_states) (_register_var_name tf_ctx))
          (map (tf_out tf_ctx) spec_all_outputs) (_register_var_name tf_ctx)) (_register_var_name tf_ctx (tf_reg tf_ctx state_var)) 
      = val_of_value (fst (sem_ops_run (spec_action_ops cmd) (fs_state, last_fs_output) fs_input)).[state_var].
    Proof.
      intros. rename H into H_state. rename H0 into H_input. rename H1 into H_output.
      unfold lookup, sem_ops_run, sem_op_step_commit, sem_updates_to_Gamma_ext. 
      rewrite (sem_ops_updates_correct2 (spec_action_ops cmd) (fs_state, last_fs_output) fs_input).
      set(updates := (fst (sem_ops_updates _ _ _))) in *. rewrite <- fold_left_rev_right.
      set (sem_update_fun := fun _ => _). set (sem_commit_fun := fun _ _ => _).
      induction (rev updates). 
      { cbn. rewrite Gamma_after_intro_is_hw_state. cbn. rewrite H_state. reflexivity. }
      {
        destruct a; cbn -[eq_dec].
        { destr; try exact IHl. unfold _reg_name in e. timeout 10 fcrush. }
        {
          destruct (eq_dec (_reg_name tf_ctx state_var) (_reg_name tf_ctx var)).
          { apply reg_name_inj in e. subst var. rewrite get_put_eq. reflexivity. }
          { apply reg_name_inj' in n. rewrite get_put_neq; try timeout 10 hauto. }
        }
        {
          destruct (eq_dec (_reg_name tf_ctx state_var) (_out_name tf_ctx var)).
          { unfold _reg_name in e. unfold _out_name in e. timeout 10 fcrush. }
          { exact IHl. }
        }
      }
    Qed.

    Lemma sem_updates_output_correct:
      forall cmd fs_state hw_reg_state fs_input last_fs_output output_var,
      StateR hw_reg_state fs_state ->
      InputR fs_input ->
      OutputR hw_reg_state last_fs_output -> 
      lookup
        (sem_updates_to_Gamma_ext (fst (sem_ops_updates (spec_action_ops cmd) (fs_state, last_fs_output) fs_input)) ++
          Gamma_after_read_vars0 hw_reg_state (Gamma_after_read_vars0 hw_reg_state [] (map (tf_reg tf_ctx) spec_all_states) (_register_var_name tf_ctx))
          (map (tf_out tf_ctx) spec_all_outputs) (_register_var_name tf_ctx)) (_register_var_name tf_ctx (tf_out tf_ctx output_var)) 
      = val_of_value (snd (sem_ops_run (spec_action_ops cmd) (fs_state, last_fs_output) fs_input)).[output_var].
    Proof.
      intros. rename H into H_state. rename H0 into H_input. rename H1 into H_output.
      unfold lookup, sem_ops_run, sem_op_step_commit, sem_updates_to_Gamma_ext.
      rewrite (sem_ops_updates_correct2 (spec_action_ops cmd) (fs_state, last_fs_output) fs_input).
      set(updates := fst (sem_ops_updates _ _ _)) in *. rewrite <- fold_left_rev_right.
      set (sem_update_fun := fun _ => _). set (sem_commit_fun := fun _ _ => _).
      induction (rev updates). 
      { cbn. rewrite Gamma_after_intro_is_hw_output. cbn. rewrite H_output. reflexivity. }
      {
        destruct a; cbn -[eq_dec].
        { destr; try exact IHl. unfold _reg_name in e. unfold _out_name in e. timeout 10 fcrush. }
        {
          destruct (eq_dec (_out_name tf_ctx output_var) (_reg_name tf_ctx var)).
          { unfold _reg_name in e. unfold _out_name in e. timeout 10 fcrush. }
          { exact IHl. }
        }
        {
          destruct (eq_dec (_out_name tf_ctx output_var) (_out_name tf_ctx var)).
          { apply out_name_inj in e. subst var. rewrite get_put_eq. reflexivity. }
          { apply out_name_inj' in n. rewrite get_put_neq; try timeout 10 hauto. }
        }
      }
    Qed.
      
  End RegUpdates.


  (* Prove next HW cycle = next Spec cycle *)

  Definition initial_hw_state := 
    RegCEnv.(create) (fun x => val_of_value (impl_r x)).
  Definition next_hw_cycle (hw_reg_state: hw_env_t) := 
    UntypedSemantics.interp_cycle impl_rules hw_reg_state sigma system_schedule.

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
      OutputR hw_reg_state last_fs_output -> 
      let (fs_state', fs_output') := sem_ops_run (spec_action_ops cmd) (fs_state, last_fs_output) fs_input in
      (
        StateR (next_hw_cycle hw_reg_state) fs_state'
        /\
        OutputR (next_hw_cycle hw_reg_state) fs_output'
      ).
  Proof.
      intros. rename H into H_sigma_eq_cmd. rename H0 into H_state. rename H1 into H_input. rename H2 into H_output.
      destruct sem_ops_run as [fs_state' fs_output'] eqn:H_semantics.

      split. 
      { 
        (* 1. Prepare the Spec step *)
        pose proof (f_equal fst H_semantics) as H_sem_state; cbn [fst] in H_sem_state. rewrite <- H_sem_state.
        clear H_sem_state H_semantics. 
        
        (* 2. Focus on one state at a time *)
        intros state_var. unfold next_hw_cycle, interp_cycle, interp_scheduler, commit_update.
        rewrite getenv_create.

        (* 3. Focus only on the result of the passed command -> relates the result to the Spec step *)
        rewrite (interp_scheduler_correct cmd fs_state hw_reg_state fs_input last_fs_output); 
        try exact H_sigma_eq_cmd; try exact H_state; try exact H_input; try exact H_output.
        2: { unfold isStateReg. left. exists state_var. reflexivity. }

        (* 4. Ignore the writes to the output regs *)
        cbn [latest_write]. rewrite Common.log_app_empty_r. cbn -[type_denote env_t]. 
        rewrite (latest_write_of_ActionLog_after_write_vars0_not_in).
        2: { induction _written_outputs. auto. cbn. unfold not; intros. destruct H; try congruence. }

        (* 5. Determine whether the state was written to or not *)
        destruct (ListDec.In_decidable list_decidable_eq_spec_states state_var (_written_states tf_ctx (spec_action_ops cmd))).
        2: {
          (* 6a.1 If the state was not written show the HW step becomes a NOP *)
          rewrite (latest_write_of_ActionLog_after_write_vars0_not_in).
          2: { intro. apply H; clear H. apply in_map_iff in H0. destruct H0 as [s [H_eq H_in]]. assert (s = state_var) by congruence. subst. exact H_in. }
          rewrite !latest_write_of_ActionLog_after_read_vars0.
          unfold latest_write, log_find. unfold getenv at 1; cbn [ContextEnv]. rewrite cassoc_ccreate. cbn [list_find_opt].

          (* 6a.2 Show the Spec step also becomes a NOP *)
          assert (~ spec_var_written state_var (spec_action_ops cmd)). {
            unfold not; intros. unfold _written_states in H.
            pose proof (spec_all_states_complete state_var) as H1.
            apply H; clear H. rewrite filter_In. split. exact H1. destr.
          }
          Set Printing All.
          rewrite (sem_var_not_written_means_ops_run_unchanged); try exact H0.
      
          (* 6a.3 Conclude both sides are equal *)
          rewrite H_state; reflexivity.
        }

        (* Var is written *)
        rewrite (latest_write_of_ActionLog_after_write_vars0_in).
        2: { apply in_map. exact H. }

        rewrite sem_updates_state_correct; try exact H_state; try exact H_input; try exact H_output. reflexivity.
      }
      {
        (* 1. Prepare the Spec step *)
        pose proof (f_equal snd H_semantics) as H_sem_output; cbn [snd] in H_sem_output. rewrite <- H_sem_output.
        clear H_sem_output H_semantics.

        (* 2. Focus on one output at a time *)
        intros output_var. unfold next_hw_cycle, interp_cycle, interp_scheduler, commit_update.
        rewrite getenv_create.
        
        (* 3. Focus only on the result of the passed command -> relates the result to the Spec step *)
        rewrite (interp_scheduler_correct cmd fs_state hw_reg_state fs_input last_fs_output); 
        try exact H_sigma_eq_cmd; try exact H_state; try exact H_input; try exact H_output.
        2: { unfold isOutputReg. right. exists output_var. reflexivity. }

        (* 4. Determine whether the output was written to or not *)
        cbn [latest_write]. rewrite Common.log_app_empty_r. cbn -[type_denote env_t]. 
        destruct (ListDec.In_decidable list_decidable_eq_spec_outputs output_var (_written_outputs tf_ctx (spec_action_ops cmd))).
        2: {
          (* 5a.1 If the output was not written show the HW step becomes a NOP *)
          rewrite (latest_write_of_ActionLog_after_write_vars0_not_in).
          2: { intro. apply H; clear H. apply in_map_iff in H0. destruct H0 as [s [H_eq H_in]]. assert (s = output_var) by congruence. subst. exact H_in. }
          rewrite (latest_write_of_ActionLog_after_write_vars0_not_in).
          2: { induction _written_states. auto. cbn. unfold not; intros. destruct H0; try congruence. }
          rewrite !latest_write_of_ActionLog_after_read_vars0.
          unfold latest_write, log_find. unfold getenv at 1; cbn [ContextEnv]. rewrite cassoc_ccreate. cbn [list_find_opt].

          (* 5a.2 Show the Spec step also becomes a NOP *)
          assert (~ spec_out_written output_var (spec_action_ops cmd)). {
            unfold not; intros. unfold _written_outputs in H.
            pose proof (spec_all_outputs_complete output_var) as H1.
            apply H; clear H. rewrite filter_In. split. exact H1. destr.
          }
          rewrite (sem_out_not_written_means_ops_run_unchanged); try exact H0.
          (* 5a.3 Conclude both sides are equal *)
          rewrite H_output; reflexivity.
        }

        (* Out is written *)
        rewrite (latest_write_of_ActionLog_after_write_vars0_in).
        2: { apply in_map. exact H. }

        rewrite sem_updates_output_correct; try exact H_state; try exact H_input; try exact H_output. reflexivity.
      }
  Qed.

End CompositionalCorrectness.
