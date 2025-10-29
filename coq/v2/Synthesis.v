Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.
Require Koika.Properties.SemanticProperties.
Require Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.

Require Import Trustformer.v2.Syntax.
Require Import Trustformer.v2.Semantics.
Require Import Trustformer.v2.Utils.
Require Trustformer.v2.Properties.Common.
From Koika.Utils Require Import Tactics.

Require Import Streams.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Init.Tactics.
Require Import Coq.Setoids.Setoid.

Require Import Hammer.Plugin.Hammer.
Set Hammer ATPLimit 5.
Set Hammer GSMode 63.

Record TFSynthContext := {
  tf_spec_states : Type;
  tf_spec_states_fin : FiniteType tf_spec_states;
  tf_spec_states_names : Show tf_spec_states;
  tf_spec_states_size : tf_spec_states -> nat;
  tf_spec_states_init : forall x: tf_spec_states, tf_states_type tf_spec_states tf_spec_states_size x;

  tf_spec_inputs : Type;
  tf_spec_inputs_fin : FiniteType tf_spec_inputs;
  tf_spec_inputs_names : Show tf_spec_inputs;
  tf_spec_inputs_size : tf_spec_inputs -> nat;

  tf_spec_outputs : Type;
  tf_spec_outputs_fin : FiniteType tf_spec_outputs;
  tf_spec_outputs_names : Show tf_spec_outputs;
  tf_spec_outputs_size : tf_spec_outputs -> nat;

  tf_spec_action : Type;
  tf_spec_action_fin : FiniteType tf_spec_action;
  tf_spec_action_names : Show tf_spec_action;
  tf_spec_action_ops : tf_spec_action -> tf_ops tf_spec_states tf_spec_inputs tf_spec_outputs (* TODO: more than just a single op *)
}.

Ltac unfold_tfctx := repeat (
  unfold tf_spec_states in * || unfold tf_spec_states_fin in * || unfold tf_spec_states_names in * || unfold tf_spec_states_size in * 
  || unfold tf_spec_states_init in * 
  
  || unfold tf_spec_inputs in * || unfold tf_spec_inputs_fin in * || unfold tf_spec_inputs_names in * || unfold tf_spec_inputs_size in * 
  
  || unfold tf_spec_outputs in * || unfold tf_spec_outputs_fin in * || unfold tf_spec_outputs_names in * || unfold tf_spec_outputs_size in * 
  
  || unfold tf_spec_action in * || unfold tf_spec_action_fin in * || unfold tf_spec_action_names in * 
  
  || unfold tf_spec_action_ops in *).

Section TrustformerSynthesis.

    Context (tf_synth_ctx: TFSynthContext).

    (* ====== Abbreviations ====== *)

    Definition spec_states := tf_spec_states tf_synth_ctx.
    Definition spec_states_fin : FiniteType spec_states := tf_spec_states_fin tf_synth_ctx.
    Definition spec_states_size := tf_spec_states_size tf_synth_ctx.
    Definition spec_states_t := tf_states_type spec_states spec_states_size.
    Definition spec_states_init := tf_spec_states_init tf_synth_ctx.
    Definition spec_all_states := @finite_elements spec_states spec_states_fin.
    Definition spec_state_index := @finite_index spec_states spec_states_fin.
    Definition spec_state_num := List.length spec_all_states.

    Definition spec_inputs := tf_spec_inputs tf_synth_ctx.
    Definition spec_inputs_fin : FiniteType spec_inputs := tf_spec_inputs_fin tf_synth_ctx.
    Definition spec_inputs_size := tf_spec_inputs_size tf_synth_ctx.
    Definition spec_inputs_t := tf_inputs_type spec_inputs spec_inputs_size.
    Definition spec_all_inputs := @finite_elements spec_inputs spec_inputs_fin.
    Definition spec_input_index := @finite_index spec_inputs spec_inputs_fin.
    Definition spec_input_num := List.length spec_all_inputs.

    Definition spec_outputs := tf_spec_outputs tf_synth_ctx.
    Definition spec_outputs_fin : FiniteType spec_outputs := tf_spec_outputs_fin tf_synth_ctx.
    Definition spec_outputs_size := tf_spec_outputs_size tf_synth_ctx.
    Definition spec_outputs_t := tf_outputs_type spec_outputs spec_outputs_size.
    Definition spec_all_outputs := @finite_elements spec_outputs spec_outputs_fin.
    Definition spec_output_index := @finite_index spec_outputs spec_outputs_fin.
    Definition spec_output_num := List.length spec_all_outputs.

    Definition spec_action := tf_spec_action tf_synth_ctx.
    Definition spec_action_fin := tf_spec_action_fin tf_synth_ctx.
    Definition spec_all_actions := @finite_elements spec_action spec_action_fin.
    Definition spec_action_index := @finite_index spec_action spec_action_fin.
    Definition spec_action_num := List.length spec_all_actions.

    Definition spec_action_ops := tf_spec_action_ops tf_synth_ctx.


    Instance show_spec_states : Show spec_states := tf_spec_states_names tf_synth_ctx.
    Instance show_spec_inputs : Show spec_inputs := tf_spec_inputs_names tf_synth_ctx.
    Instance show_spec_outputs : Show spec_outputs := tf_spec_outputs_names tf_synth_ctx.
    Instance show_spec_action : Show spec_action := tf_spec_action_names tf_synth_ctx.

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

    Definition spec_var_not_written_dec := tf_op_var_not_written_dec spec_states spec_states_fin spec_inputs spec_outputs spec_states_size spec_inputs_size spec_outputs_size.
    Definition spec_no_output_dec := tf_op_no_output_dec spec_states spec_states_fin spec_inputs spec_outputs spec_outputs_fin spec_states_size spec_inputs_size spec_outputs_size.

    (* ====== Registers ====== *)

    Inductive reg_t := 
    | tf_reg (x : spec_states)
    | tf_out (x : spec_outputs)
    | tf_out_ack (x : spec_outputs)
    .

    Instance _reg_t_finite : FiniteType reg_t.
    Proof.
      econstructor.
      instantiate (1 := fun x => 
        match x with
        |  tf_reg y => spec_state_index y
        |  tf_out y => spec_state_num + spec_output_index y
        |  tf_out_ack y => spec_state_num + spec_output_num + spec_output_index y
        end).
      instantiate (1 := 
        map (fun x => tf_reg x) spec_all_states
        ++ map (fun x => tf_out x) spec_all_outputs
        ++ map (fun x => tf_out_ack x) spec_all_outputs).
      {
        intros. unfold_specs. destruct a. 
        {
          rewrite nth_error_app1. rewrite nth_error_map. rewrite (@finite_surjective spec_states spec_states_fin _). 
          (* hammer. *) sfirstorder.
          rewrite <- nth_error_Some. rewrite nth_error_map. rewrite (@finite_surjective spec_states spec_states_fin _).
          (* hammer. *) sfirstorder.
        }
        {
          rewrite nth_error_app2. rewrite nth_error_app1.
          rewrite Nat.add_comm. rewrite map_length. rewrite Nat.add_sub.
          rewrite nth_error_map. rewrite (@finite_surjective spec_outputs spec_outputs_fin _). 
          (* hammer. *) sfirstorder.
          rewrite !map_length. rewrite Nat.add_comm. rewrite Nat.add_sub. 
          generalize (@finite_surjective spec_outputs spec_outputs_fin x). intros.
          apply nth_error_Some.
          (* hammer. *) scongruence use: @finite_surjective unfold: spec_outputs, tf_spec_outputs.
          rewrite !map_length. 
          (* hammer. *) sfirstorder.
        }
        {
          rewrite nth_error_app2. rewrite nth_error_app2.
          rewrite Nat.add_comm. rewrite Nat.add_comm. rewrite !map_length.
          rewrite Nat.add_comm. rewrite Nat.add_assoc. rewrite Nat.add_comm. rewrite Nat.add_assoc.
          rewrite Nat.add_sub. rewrite Nat.add_comm. rewrite Nat.add_sub.
          rewrite nth_error_map. rewrite (@finite_surjective spec_outputs spec_outputs_fin _). 
          (* hammer. *) sfirstorder.
          rewrite !map_length. rewrite Nat.add_comm. rewrite Nat.add_comm. rewrite Nat.add_comm. rewrite Nat.add_assoc.
          rewrite Nat.add_comm. rewrite Nat.add_assoc. rewrite Nat.add_sub. lia.
          rewrite !map_length. lia.
        }
      }
      {
        rewrite map_app. rewrite !map_map. apply NoDup_app. 
        assert ((fun x : spec_states => spec_state_index x) = spec_state_index) by reflexivity. rewrite H. clear H.
        apply (@finite_injective spec_states spec_states_fin).
        rewrite map_app. rewrite !map_map. apply NoDup_app.
        {
          apply FinFun.Injective_carac. apply Common.finite_elements_is_finfun_listing.
          unfold FinFun.Injective. apply Common.finite_index_plus_constant_l_inj.
        } {
          apply FinFun.Injective_map_NoDup. unfold FinFun.Injective.
          apply Common.finite_index_plus_constant_l_inj. apply Common.finite_elements_is_finfun_listing.
        } {
          intros. rewrite in_map_iff in H. rewrite in_map_iff in H0.
          destruct H as [s1 [Hs1_in Hs1_eq]]. destruct H0 as [s2 [Hs2_in Hs2_eq]]. subst x.
          rewrite <- Nat.add_assoc in Hs2_in. apply Nat.add_cancel_l in Hs2_in.
          assert (spec_output_num > spec_output_index s1). {
            apply Common.finite_index_in_range.
          }
          lia.
        } {
          intros. rewrite in_map_iff in H. rewrite in_map_iff in H0.
          destruct H as [s1 [Hs1_in Hs1_eq]]. destruct H0 as [s2 [Hs2_in Hs2_eq]]. subst x.
          destruct s2.
          {
            apply in_app_or in Hs2_eq. destruct Hs2_eq as [Hs2_eq | Hs2_eq].
            apply in_map_iff in Hs2_eq. destruct Hs2_eq as [s2' [Hs2'_in Hs2'_eq]]. subst.
            congruence.
            apply in_map_iff in Hs2_eq. destruct Hs2_eq as [s2' [Hs2'_in Hs2'_eq]]. subst.
            congruence.
          } {
            assert (spec_state_num > spec_state_index s1). {
              apply Common.finite_index_in_range.
            }
            lia.
          } {
            assert (spec_state_num > spec_state_index s1). {
              apply Common.finite_index_in_range.
            }
            lia.
          }
        }
      }
    Defined.

    Instance eq_dec_states : EqDec spec_states.
    Proof.
      pose spec_states_fin.  
      apply EqDec_FiniteType.
    Defined.

    Instance eq_dec_outputs : EqDec spec_outputs.
    Proof.
      pose spec_outputs_fin.  
      apply EqDec_FiniteType.
    Defined.

    Definition _reg_name (x: spec_states) : string :=
      "tf_st_" ++ string_id_of_nat (spec_state_index x).

    Definition _out_name (x: spec_outputs) : string :=
      "tf_out_" ++ string_id_of_nat (spec_output_index x).

    Instance reg_names : Show reg_t :=
      { show := fun r => match r with
          | tf_reg x => String.append "reg_" (show x)
          | tf_out x => String.append "out_" (show x)
          | tf_out_ack x => String.append "out_ack_" (show x)
          end
      }.

    (* ====== Register Types ====== *)

    Definition R (r: reg_t) :=
    match r with
    | tf_reg x => spec_states_t x
    | tf_out x => spec_outputs_t x
    | tf_out_ack x => bits_t 1
    end.

    Definition r (reg: reg_t) : R reg :=
      match reg with
      | tf_reg x => spec_states_init x
      | tf_out x => Bits.zero
      | tf_out_ack x => Bits.zero
      end.

    (* ====== External Functions ====== *)

    Inductive ext_fn_t := 
    | ext_in_cmd
    | ext_input (x : spec_inputs)
    | ext_output (x : spec_outputs)
    .

    Definition cmd_reg_size := @Common.finite_bits_needed spec_action spec_action_fin.

    Definition Sigma (fn: ext_fn_t) : ExternalSignature :=
      match fn with
      | ext_in_cmd => {$ bits_t 1 ~> maybe (bits_t cmd_reg_size) $}
      | ext_input x => {$ bits_t 1 ~> spec_inputs_t x $}
      | ext_output x => {$ spec_outputs_t x ~> bits_t 1 $}
      end.

    Definition ext_fn_specs (fn : ext_fn_t) := 
      match fn with
      | ext_in_cmd => {| efr_name := "in_cmd"; 
                        efr_internal := false |}
      | ext_input x => {| efr_name := String.append "in_param_" (show x); 
                          efr_internal := false |}
      | ext_output x => {| efr_name := String.append "out_param_" (show x); 
                           efr_internal := false |}
      end.

    Instance ext_fn_names : Show ext_fn_t :=
      { show := fun r => match r with
          | ext_in_cmd => "in_cmd"
          | ext_input x => String.append "in_param_" (show x)
          | ext_output x => String.append "out_param_" (show x)
          end
      }.
    
    (* ====== Rules ====== *)

    Inductive rule_name_t :=
    | rule_cmd (cmd: spec_action)
    | rule_out (out: spec_outputs)
    .

    Instance rule_names : Show rule_name_t :=
      { show := fun r => match r with
          | rule_cmd cmd => String.append "rule_cmd_" (show cmd)
          | rule_out out => String.append "rule_out_" (show out)
          end
      }.

    Definition system_schedule_actions : scheduler  :=
      List.fold_right (fun t acc => rule_cmd t |> acc) Done spec_all_actions.

    Definition system_schedule_outputs : scheduler := 
      List.fold_right (fun t acc => rule_out t |> acc) system_schedule_actions spec_all_outputs.

    Definition system_schedule := system_schedule_outputs.
    
    Definition op_to_uaction (op: tf_ops spec_states spec_inputs spec_outputs) (code: uaction reg_t ext_fn_t) : uaction reg_t ext_fn_t :=
      match op with
      | tf_nop _ _ _ => code 
      | tf_neg _ _ _ x => UBind (_reg_name x) (UUnop (UBits1 UNot) (UVar (_reg_name x))) code
      | tf_input _ _ _ x y => UBind (_reg_name x) (UExternalCall (ext_input y) {{Ob~1}}) code
      | tf_output _ _ _ x y => UBind (_out_name y) (UVar (_reg_name x)) code
      end.

    Definition _rule_aux
      (state_op: tf_ops spec_states spec_inputs spec_outputs)
      (code: uaction reg_t ext_fn_t)
      : uaction reg_t ext_fn_t :=
        op_to_uaction state_op code.

    (* Helper function that reads all state registers into variables *)
    Fixpoint _rule_read_state_vars_rec (states_to_read : list (spec_states)) (code: uaction reg_t ext_fn_t): uaction reg_t ext_fn_t :=
      match states_to_read with
      | [] => code
      | x :: rest =>
        UBind (_reg_name x) 
          {{ read1(tf_reg x) }} 
          (_rule_read_state_vars_rec rest code)
      end.

    (* Helper function that writes back all modified state variables *)
    Definition _rule_write_state_vars (op: tf_ops spec_states spec_inputs spec_outputs) (code: uaction reg_t ext_fn_t) : uaction reg_t ext_fn_t  := 
      List.fold_right (fun x acc => 
        if spec_var_not_written_dec x op then
          acc
        else
          USeq {{ write1(tf_reg x, `UVar (_reg_name x)`) }} acc
      ) code spec_all_states.
    
    (* Helper function that writes back all modified output variables *)
    Definition _rule_write_output_vars (op: tf_ops spec_states spec_inputs spec_outputs) (code: uaction reg_t ext_fn_t) : uaction reg_t ext_fn_t  := 
      List.fold_right (fun x acc => 
        if spec_no_output_dec x op then
          acc
        else
          USeq {{ write1(tf_out x, `UVar (_out_name x)`) }} acc
      ) code spec_all_outputs.

    Definition _rule_cmd cmd : uaction reg_t ext_fn_t :=
      let state_ops := spec_action_ops cmd in
      _rule_read_state_vars_rec spec_all_states (
        _rule_aux state_ops (
          _rule_write_state_vars state_ops (
            _rule_write_output_vars state_ops
              {{ pass }}))).

    Definition rules :=
        (fun rl =>  match rl with
          | rule_cmd cmd => 
            let cmd_enc := Bits.of_nat cmd_reg_size (spec_action_index cmd) in
            {{
                  guard(get(extcall ext_in_cmd(Ob~1), valid));
                  guard(get(extcall ext_in_cmd(Ob~1), data) == #cmd_enc);
                  `_rule_cmd cmd`
            }}
          | rule_out out =>
            UWrite P1 (tf_out_ack out) (UExternalCall (ext_output out) ({{ read0(tf_out out) }} ))
          end).

End TrustformerSynthesis.

(* 
  We need to override the type checking tactic, since by default it expects rules to have no parameters.
  Specifically, we need to match the three components of a rule (name, tf_ctx, param) and destruct the param
  so that there are no opaque values for the type checker.
*)

Ltac _tc_rules R Sigma uactions :=
    let rule_name_t := _arg_type uactions in
    let res := constr:(fun r: rule_name_t =>
                        ltac:(destruct r eqn:? ;
                                lazymatch goal with
                                | [ H: _ = ?r1 ?r2 ?r3 |- _ ] =>
                                    destruct r3 eqn:?;
                                    lazymatch goal with
                                    | [ H: _ = ?rr2 |- _ ] =>
                                        let ua := constr:(uactions rr2) in
                                        let ua := (eval hnf in ua) in
                                        (_tc_action R Sigma (@List.nil (var_t * type)) constr:(unit_t) ua)
                                    end
                                | [ H: _ = ?rr |- _ ] =>
                                    let ua := constr:(uactions rr) in
                                    let ua := (eval hnf in ua) in
                                    _tc_action R Sigma (@List.nil (var_t * type)) constr:(unit_t) ua
                                end)) in
    exact res.

Notation tc_rules R Sigma actions :=
    (ltac:(_tc_rules R Sigma actions)) (only parsing).

