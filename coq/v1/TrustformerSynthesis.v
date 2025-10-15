Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.
Require Koika.Properties.SemanticProperties.
Require Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.

Require Import Trustformer.v1.TrustformerSyntax.
Require Import Trustformer.v1.TrustformerSemantics.
Require Import Trustformer.v1.Utils.
Require Trustformer.v1.UntypedProperties.CommonProperties.
From Koika.Utils Require Import Tactics.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Streams.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Init.Tactics.

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Record TFSynthContext := {
  tf_spec_states : Type;
  tf_spec_states_fin : FiniteType tf_spec_states;
  tf_spec_states_names : Show tf_spec_states;
  tf_spec_states_size : tf_spec_states -> nat;
  tf_spec_states_init : forall x: tf_spec_states, tf_states_type tf_spec_states tf_spec_states_size x;
  tf_spec_action : Type;
  tf_spec_action_fin : FiniteType tf_spec_action;
  tf_spec_action_names : Show tf_spec_action;
  tf_spec_action_ops : tf_spec_action -> tf_ops tf_spec_states (* TODO: more than just a single op *)
}.

Section TrustformerSynthesis.

    Context (tf_synth_ctx: TFSynthContext).

    Definition spec_states := tf_spec_states tf_synth_ctx.
    Definition spec_states_fin : FiniteType spec_states := tf_spec_states_fin tf_synth_ctx.
    Definition spec_states_size := tf_spec_states_size tf_synth_ctx.
    Definition spec_states_t := tf_states_type spec_states spec_states_size.
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

    Instance eq_dec_states : EqDec spec_states.
    Proof.
      pose spec_states_fin.  
      apply EqDec_FiniteType.
    Qed.

    Definition _reg_name (x: spec_states) : string :=
      "tf_st_" ++ string_id_of_nat (state_index x).
    (* maybe create own string to nat function that just adds something idk *)

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

    Definition cmd_reg_size := @CommonProperties.finite_bits_needed spec_action spec_action_fin. (* TODO: determine size depending on length of list *)

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
    
    Definition op_to_uaction (op: tf_ops spec_states) (code: uaction reg_t ext_fn_t) : uaction reg_t ext_fn_t :=
      match op with
      | tf_nop _ => code 
      | tf_neg _ x => UBind (_reg_name x) (UUnop (UBits1 UNot) (UVar (_reg_name x))) code
      end.

    Definition _rule_aux
      (state_op: tf_ops spec_states)
      (code: uaction reg_t ext_fn_t)
      : uaction reg_t ext_fn_t :=
        op_to_uaction state_op code.

    (* Helper function that reads all state registers into variables *)
    (* TODO: a final version should only read the needed variables, to minimize dependencies *)
    (* Definition _rule_read_state_vars (code: uaction reg_t ext_fn_t) : uaction reg_t ext_fn_t  := 
      List.fold_right (fun x acc => 
        UBind (_reg_name x) {{ read1(tf_reg x) }} acc
      ) code all_spec_states. *)
    Fixpoint _rule_read_state_vars_rec (states_to_read : list (spec_states)) (code: uaction reg_t ext_fn_t): uaction reg_t ext_fn_t :=
      match states_to_read with
      | [] => code
      | x :: rest =>
        UBind (_reg_name x) 
          {{ read1(tf_reg x) }} 
          (_rule_read_state_vars_rec rest code)
      end.

    (* Helper function that writes back all modified state variables *)
    Definition _rule_write_state_vars (op: tf_ops spec_states) (code: uaction reg_t ext_fn_t) : uaction reg_t ext_fn_t  := 
      List.fold_right (fun x acc => 
        if tf_op_var_not_written_dec spec_states spec_states_fin spec_states_size x op then
          acc
        else
          USeq {{ write0(tf_reg x, `UVar (_reg_name x)`) }} acc
      ) code all_spec_states.

    Definition _rule_cmd cmd : uaction reg_t ext_fn_t :=
      let state_ops := spec_action_ops cmd in
      _rule_read_state_vars_rec all_spec_states (
        _rule_aux state_ops (
          _rule_write_state_vars state_ops {{ pass }})).

    Definition rules :=
        (fun rl =>  match rl with
          | rule_cmd cmd => 
            let cmd_enc := Bits.of_nat cmd_reg_size (action_index cmd) in
            {{
                  (* No let is better --> no sideeffects, but requires reproving some stuff  *)
                  guard(get(extcall ext_in_cmd(Ob~1), valid));
                  guard(get(extcall ext_in_cmd(Ob~1), data) == #cmd_enc);
                  `_rule_cmd cmd`
            }}
          end).
    
    Section Properties.


    End Properties.

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


Section CompositionalCorrectness.

    (* Generalize over any input to the synthesis *)
    Context (some_fs_states: Type).
    Context (some_fs_states_fin : FiniteType some_fs_states).
    Context (some_fs_states_names : Show some_fs_states).
    Context (some_fs_states_size : some_fs_states -> nat).
    Context (some_fs_states_init : forall x: some_fs_states, tf_states_type some_fs_states some_fs_states_size x).
    Context (some_fs_action : Type).
    Context (some_fs_action_fin : FiniteType some_fs_action).
    Context (some_fs_action_names : Show some_fs_action).
    Context (some_fs_action_ops : some_fs_action -> tf_ops some_fs_states).

    (* We craft the tx_context here as it leads to cleaner proofs than generalizing over it*)
    Definition tf_ctx := {|
      tf_spec_states := some_fs_states;
      tf_spec_states_fin := some_fs_states_fin;
      tf_spec_states_names := some_fs_states_names;
      tf_spec_states_size := some_fs_states_size;
      tf_spec_states_init := some_fs_states_init;
      tf_spec_action := some_fs_action;
      tf_spec_action_fin := some_fs_action_fin;
      tf_spec_action_names := some_fs_action_names;
      tf_spec_action_ops := some_fs_action_ops
    |}.
    Definition some_fs_states_t := tf_states_type some_fs_states some_fs_states_size.

    Context (sigma: ext_fn_t -> val -> val).
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

    Instance some_reg_t_finite : FiniteType (some_reg_t) := reg_t_finite tf_ctx.
    Definition some_reg_t_elements := @finite_elements some_reg_t some_reg_t_finite.
    Definition some_fs_state_elements := @finite_elements some_fs_states some_fs_states_fin.


    (* Encoding of commands as bitvectors *)
    Definition _fs_cmd_encoding (a: some_fs_action) :=
      Bits.of_nat some_cmd_reg_size (@finite_index some_fs_action _ a).
    Definition _encoded_cmd (a: some_fs_action) : type_denote (maybe (bits_t some_cmd_reg_size)) :=
        (Ob~1, (_fs_cmd_encoding a, tt)).
    Definition encoded_cmd (a: some_fs_action) := val_of_value (_encoded_cmd a).

    Definition val_true := Bits ( [true] ).
    Eval compute in val_true.

  (* Properties about the encoding of commands *)
  Section Encoding.

    Example val_of_value_for_cmd_is_struct :
    forall (a : some_fs_action),
      let sig := Maybe (bits_t some_cmd_reg_size) in
      encoded_cmd a
      =
      Struct sig [val_true; Bits (vect_to_list (_fs_cmd_encoding a))].
    Proof.
      intros. unfold encoded_cmd, _encoded_cmd. reflexivity.
    Qed.

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
      - rewrite pow2_correct. unfold some_cmd_reg_size, cmd_reg_size. apply CommonProperties.finite_bits_needed_correct.
      - rewrite pow2_correct. unfold some_cmd_reg_size, cmd_reg_size. apply CommonProperties.finite_bits_needed_correct.
    Qed.

    Lemma encoded_cmd_inj' :
      forall (a1 a2 : some_fs_action),
      a1 <> a2 ->
      encoded_cmd a1 <> encoded_cmd a2.
    Proof.
      intros a1 a2 H_neq. intros H_eq.
      apply encoded_cmd_inj in H_eq.
      contradiction.
    Qed.    

    Lemma sigma_ext_in_cmd_is_struct :
      forall (cmd : some_fs_action) vars,
      exists valid' cmd_encoding,
      sigma ext_in_cmd vars = Struct (Maybe (bits_t some_cmd_reg_size)) [Bits [valid']; Bits cmd_encoding].
    Proof.
      intros.
      specialize (sigma_valid ext_in_cmd vars).
      unfold retSig, Sigma, val_of_value, some_cmd_reg_size in *.
      destruct sigma_valid as [f_t Heq].
      destruct f_t as [b v_and_unit].
      destruct v_and_unit as [v H_unit].
      rewrite Heq.
      eexists _,_.
      simpl.
      reflexivity.
    Qed.   

    Lemma cmd_rule_eq_dec_equal:
      forall (cmd1 cmd2: some_fs_action),
        (rule_cmd tf_ctx cmd1) = (rule_cmd tf_ctx cmd2) <-> cmd1 = cmd2.
    Proof.
        intros. split.
        - intros H_eq. inversion H_eq. reflexivity.
        - intros H_eq. rewrite H_eq. reflexivity.
    Qed.

    Lemma cmd_rule_eq_dec_if:
      forall (cmd1 cmd2: some_fs_action) a b,
        (if eq_dec (rule_cmd tf_ctx cmd1) (rule_cmd tf_ctx cmd2)
        then a
        else b) ->
        ((cmd1 = cmd2 -> a) /\ (cmd1 <> cmd2 -> b)).
    Proof.
        intros. destruct (eq_dec (rule_cmd tf_ctx cmd1) (rule_cmd tf_ctx cmd2)) as [H_eq | H_neq].
        - assert (cmd1 = cmd2) as H_cmd_eq.
          { apply cmd_rule_eq_dec_equal. exact H_eq. }
          timeout 10 sauto.
        - timeout 10 sauto.
    Qed.

    Lemma reg_name_injective :
      forall r1 r2,
        (_reg_name tf_ctx r1) = (_reg_name tf_ctx r2) -> r1 = r2.
    Proof.
      intros. unfold _reg_name in H.
      timeout 10 simpl in H. unfold state_index in H.
      injection H. intros.
      apply finite_index_injective.
      apply string_id_of_nat_inj in H0.
      timeout 10 sauto.
    Qed.

  End Encoding. 

    (* Other helpful definitions *)
  Definition hw_env_t := env_t ContextEnv (fun _ : some_reg_t => val).

  Section CmdGuard.
    
    Lemma interp_rule_wrong_cmd:
      forall (hw_reg_state: hw_env_t) log cmd,
      sigma ext_in_cmd val_true <> encoded_cmd cmd ->
      UntypedSemantics.interp_rule hw_reg_state sigma log (some_rules (rule_cmd tf_ctx cmd)) = None.
    Proof.
      intros.
      unfold some_rules, rules, _rule_cmd.
      unfold UntypedSemantics.interp_rule, UntypedSemantics.interp_action.

      cbn. unfold val_true.

      (* We know what in_cmd will give as a result so lets substitute it in our code *)
      set (sigma_val := sigma ext_in_cmd (Bits [true])) in *.
      assert (HSigmaValCmd: sigma_val <> encoded_cmd cmd).
      { unfold sigma_val. exact H. }
      destruct sigma_val eqn:H_sigma_val.
      cbn. timeout 10 sauto. cbn. timeout 10 sauto.
      { remember (BitsToLists.get_field (Struct sig v) "valid") as valid_field_opt.
        destruct valid_field_opt eqn:H_cmd_valid.
        { cbn. destruct v0.
          { cbn. destruct v0.
            cbn. timeout 10 sauto. cbn. destruct v0.
            { cbn. destruct b.
              {
                cbn. remember (BitsToLists.get_field_struct (struct_fields sig) v "data") as data_field_opt.
                destruct data_field_opt.
                { cbn. destruct v0.
                  { cbn. 
                    assert (BitsToLists.list_eqb Bool.eqb v0 (vect_to_list (Bits.of_nat (cmd_reg_size tf_ctx) (action_index tf_ctx cmd))) = false).
                    { 
                      rewrite <- Bool.not_true_iff_false.
                      rewrite BitsToLists.list_eqb_correct.
                      {
                        intro H_eq. subst v0. subst sigma_val. clear valid_field_opt H_cmd_valid.
                        timeout 10 cbn in *. unfold not in *.
                        unfold _fs_cmd_encoding, some_cmd_reg_size, action_index, spec_action, spec_action_fin in *.
                        unfold tf_ctx, tf_spec_action, tf_spec_action_fin in *. fold tf_ctx in *.
                        apply HSigmaValCmd.
                        generalize (sigma_ext_in_cmd_is_struct cmd (Bits [true])); intros.
                        rewrite H_sigma_val in *. 

                        destruct H0 as [valid' [cmd_encoding H_sigma_struct]].
                        f_equal. timeout 10 sauto.
                        injection H_sigma_struct as Heqv.
                        rewrite Heqv in *. clear Heqv. rewrite H0 in *. clear H0.

                        unfold BitsToLists.get_field_struct in *.
                        f_equal. f_equal.
                        { timeout 10 sauto. }
                        { timeout 10 sauto. }
                    
                      } intros. split. intros. destruct a, b. timeout 10 sauto. timeout 10 sauto. timeout 10 sauto. timeout 10 sauto. 
                        intros. rewrite H0. destruct b. timeout 10 sauto. timeout 10 sauto.
                    } rewrite H0. cbn. timeout 10 sauto.
                  } cbn. timeout 10 sauto. cbn. timeout 10 sauto. cbn. timeout 10 sauto.
                } cbn. timeout 10 sauto.
              } cbn. timeout 10 sauto.                         
            } cbn. timeout 10 sauto.
          } cbn. timeout 10 sauto. cbn. timeout 10 sauto. cbn. timeout 10 sauto.            
        } cbn. timeout 10 sauto.  
       } cbn. timeout 10 sauto.
    Qed.

    Lemma interp_scheduler_no_cmd:
      forall (hw_reg_state: hw_env_t) cmd schedule log,
      sigma ext_in_cmd val_true = encoded_cmd cmd ->
      (~ CommonProperties.scheduler_has_rule schedule (rule_cmd tf_ctx cmd)) ->
      UntypedSemantics.interp_scheduler' some_rules hw_reg_state sigma log schedule = log.
    Proof.
      intros. unfold UntypedSemantics.interp_scheduler, UntypedSemantics.interp_scheduler'.

      induction schedule. reflexivity.
      {
        rewrite IHschedule. clear IHschedule.
        {
          unfold not, CommonProperties.scheduler_has_rule in H0.
          destruct r0. destruct (eq_dec cmd0 cmd).
          - subst cmd0. destruct (eq_dec (rule_cmd tf_ctx cmd) (rule_cmd tf_ctx cmd)).
            + exfalso. apply H0. sauto.
            + exfalso. unfold not in n. generalize (cmd_rule_eq_dec_equal cmd cmd). intros. inversion H1. timeout 10 sauto.
          - rewrite interp_rule_wrong_cmd.
            + timeout 10 sauto.
            + generalize (encoded_cmd_inj' cmd0 cmd). intros. timeout 10 sauto.
        }
        {
          generalize (CommonProperties.scheduler_has_not_rule_inductive (r0 |> schedule) (rule_cmd tf_ctx cmd) ).
          intros.
          pose proof (H1 H0) as H_derived.
          destruct (eq_dec r0 (rule_cmd tf_ctx cmd)) as [H_eq | H_neq].
          - exfalso. contradiction.
          - exact H_derived.
        }
      }
      {
        rewrite IHschedule2. clear IHschedule2.
        {
          unfold not, CommonProperties.scheduler_has_rule in H0.
          destruct r0. destruct (eq_dec cmd0 cmd).
          - subst cmd0. destruct (eq_dec (rule_cmd tf_ctx cmd) (rule_cmd tf_ctx cmd)).
            + exfalso. apply H0. sauto.
            + exfalso. unfold not in n. generalize (cmd_rule_eq_dec_equal cmd cmd). intros. inversion H1. timeout 10 sauto.
          - rewrite interp_rule_wrong_cmd.
            + timeout 10 sauto.
            + generalize (encoded_cmd_inj' cmd0 cmd). intros. timeout 10 sauto.

        }
        {
          generalize (CommonProperties.scheduler_has_not_rule_inductive (Try r0 schedule1 schedule2) (rule_cmd tf_ctx cmd) ).
          intros.
          pose proof (H1 H0) as H_derived.
          destruct (eq_dec r0 (rule_cmd tf_ctx cmd)) as [H_eq | H_neq].
          - exfalso. contradiction.
          - timeout 10 sauto.
        }
      }
      {
        rewrite IHschedule. clear IHschedule.
        timeout 10 sauto.
        {
          generalize (CommonProperties.scheduler_has_not_rule_inductive (SPos p schedule) (rule_cmd tf_ctx cmd) ).
          intros.
          pose proof (H1 H0) as H_derived.
          timeout 10 sauto.
        }
      }
    Qed.

    Lemma interp_scheduler_only_cmd:
      forall (hw_reg_state: hw_env_t) cmd,
      sigma ext_in_cmd val_true = encoded_cmd cmd ->
      UntypedSemantics.interp_scheduler some_rules hw_reg_state sigma some_system_schedule = 
      UntypedSemantics.interp_scheduler some_rules hw_reg_state sigma ( rule_cmd tf_ctx cmd |> done ).
    Proof.
      intros.
      unfold UntypedSemantics.interp_scheduler.
      (* unfold UntypedSemantics.interp_scheduler'. *)

      set (schedule := some_system_schedule) in *.
      unfold some_system_schedule, system_schedule, system_schedule_actions in *.
      unfold all_spec_actions in *.

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
        generalize (@finite_surjective (spec_action tf_ctx) (spec_action_fin tf_ctx) cmd). intros H1.
        rewrite H_empty in H1.
        rewrite nth_error_nil in H1. inversion H1.
      }
      assert (action_order_has_cmd : In cmd action_order).
      { 
        subst action_order.
        generalize (@finite_surjective (spec_action tf_ctx) (spec_action_fin tf_ctx) cmd). intros H1.
        apply nth_error_In with (finite_index cmd). exact H1.
      }

      induction (action_order).
      { destruct action_order_some. reflexivity. }
      {
        timeout 10 cbn -[some_rules UntypedLogs.log_empty].

        destruct (eq_dec a cmd).
        {
          subst a. assert (H_not_in_l: ~ In cmd l). { inversion H0. timeout 10 sauto. }
          
          assert ((~ CommonProperties.scheduler_has_rule (fold_right (fun (t : some_fs_action) (acc : scheduler) => rule_cmd tf_ctx t |> acc) (done) l) (rule_cmd tf_ctx cmd))).
          {
            unfold not. unfold CommonProperties.scheduler_has_rule. intros H_in.
            clear IHl. induction l.
            { timeout 10 sauto. }
            {
              destruct (eq_dec a cmd) as [H_eq | H_neq].
              { timeout 10 sauto. }
              { 
                timeout 10 cbn [fold_right CommonProperties.scheduler_has_rule] in H_in. 
                destruct (eq_dec (rule_cmd tf_ctx a) (rule_cmd tf_ctx cmd)) as [H_eq2 | H_neq2].
                apply cmd_rule_eq_dec_equal in H_eq2. subst a. contradiction.
                apply IHl. timeout 10 sauto. timeout 10 sauto. timeout 10 sauto. timeout 10 sauto.
                exact H_in.                
              }
            }
          }

          case_eq (@UntypedSemantics.interp_rule pos_t var_t fn_name_t EqDec_string (reg_t tf_ctx) ext_fn_t (@ContextEnv some_reg_t some_reg_t_finite) hw_reg_state sigma (@UntypedLogs.log_empty val (reg_t tf_ctx) (@ContextEnv some_reg_t some_reg_t_finite)) (some_rules (rule_cmd tf_ctx cmd))).
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
      }
    Qed. 
    
    Lemma interp_rule_right_cmd:
      forall (hw_reg_state: hw_env_t) log cmd,
      sigma ext_in_cmd val_true = encoded_cmd cmd ->
      UntypedSemantics.interp_rule hw_reg_state sigma log (some_rules (rule_cmd tf_ctx cmd)) = 
      UntypedSemantics.interp_rule hw_reg_state sigma log (_rule_cmd tf_ctx cmd).
    Proof.
      intros.
      unfold some_rules.
      unfold UntypedSemantics.interp_rule.
      unfold UntypedSemantics.interp_action.
      cbn -[_rule_cmd].

      set (sigma_val := sigma ext_in_cmd (Bits [true])) in *.
      assert (HSigmaValCmd: sigma_val = encoded_cmd cmd).
      { unfold sigma_val. exact H. } rewrite HSigmaValCmd in *. clear sigma_val HSigmaValCmd. clear H.
      cbn -[_rule_cmd].

      (* Help out unpacking the relevant action_index info from tf_ctx *)
      unfold _fs_cmd_encoding, some_cmd_reg_size, action_index, spec_action, spec_action_fin in *.
      assert (@finite_index some_fs_action some_fs_action_fin cmd = @finite_index (spec_action tf_ctx) (spec_action_fin tf_ctx) cmd).
      { unfold tf_ctx, tf_spec_action, tf_spec_action_fin in *. fold tf_ctx in *. reflexivity. } rewrite H in *; clear H.

      (* Help out with the comparison *)
      set (eq_true := BitsToLists.list_eqb _ _ _) in *.
      assert (eq_true = true).
      { unfold eq_true. apply BitsToLists.list_eqb_refl. intros. destruct a. timeout 10 sauto. timeout 10 sauto. } rewrite H in *; clear H. clear eq_true.

      unfold opt_bind.
      cbn.
      reflexivity.
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
      (forall (reg: some_reg_t), UntypedLogs.log_existsb sched_log reg UntypedLogs.is_write0 = false) ->

      let written_vars := List.filter (fun s => if (tf_op_var_not_written_dec some_fs_states some_fs_states_fin some_fs_states_size s state_op) then false else true) some_fs_state_elements in
      (* Precondition: Ensure all written vars have values in Gamma *)
      (forall s, In s written_vars -> exists v, BitsToLists.list_assoc Gamma (_reg_name tf_ctx s) = Some v) ->

      let val_for_state := fun s => match BitsToLists.list_assoc Gamma (_reg_name tf_ctx s) with
      | Some v => v
      | None => hw_reg_state.[tf_reg tf_ctx s]
      end
      in

      let write_logs := List.fold_left (fun (acc_log: UntypedLogs._ULog) s =>
        UntypedLogs.log_cons (tf_reg tf_ctx s) (UntypedLogs.LE Logs.LogWrite P0 (val_for_state s)) acc_log
      ) written_vars action_log in 

      UntypedSemantics.interp_action hw_reg_state sigma Gamma sched_log action_log (_rule_write_state_vars tf_ctx state_op {{ pass }}) =
      Some (write_logs, Bits [], Gamma).
    Proof.
    Admitted.

  End ActionInterpretation.

  (* Prove next HW cycle = next Spec cycle *)
    Definition _ur (x: some_reg_t) := val_of_value (some_r x).
    Definition initial_hw_state := 
        ContextEnv.(create) _ur.
    Check initial_hw_state.

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
      sigma ext_in_cmd val_true = encoded_cmd cmd ->
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
              simpl. unfold _rule_aux, all_spec_states. cbn -[_reg_name].  
              destruct (some_fs_action_ops cmd) eqn:H_ops.
              { (* nop *)
                cbn -[_reg_name]. 
                
                rewrite (@interp_act_write_state_vars ContextEnv).
                {
                  rewrite filter_written_vars_nop.
                  cbn -[_reg_name]. rewrite !CommonProperties.getenv_ccreate.
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
                  intros. cbn -[_reg_name].  unfold UntypedLogs.log_existsb. rewrite !CommonProperties.getenv_ccreate. timeout 10 sauto.
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
                    contradict e. unfold not. intros. apply reg_name_injective in H. timeout 10 sauto.
                  }

                  apply in_inv in H_in. destruct H_in. timeout 10 sauto.
                  inversion H_nodup. apply IHl. timeout 10 sauto. timeout 10 sauto.
                } rewrite H_read_val. clear H_read_val read_val.

                unfold UntypedSemantics.usigma1. 
                rewrite H_state. cbn -[_reg_name]. 

                rewrite (@interp_act_write_state_vars ContextEnv).
                {
                  rewrite filter_written_vars_neg in *.
                  rewrite !CommonProperties.getenv_ccreate.
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
                  intros. cbn -[_reg_name].  unfold UntypedLogs.log_existsb. rewrite !CommonProperties.getenv_ccreate. timeout 10 sauto.
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
        sigma ext_in_cmd val_true = encoded_cmd cmd ->
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
           

