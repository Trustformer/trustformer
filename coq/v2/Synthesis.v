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

    (* ====== Registers ====== *)

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

    Instance reg_names : Show reg_t :=
      { show := fun r => match r with
          | tf_reg x => String.append "reg_" (show x)
          end
      }.

    (* ====== Register Types ====== *)

    Definition R (r: reg_t) :=
    match r with
    | tf_reg x => spec_states_t x
    end.

    Definition r (reg: reg_t) : R reg :=
      match reg with
      | tf_reg x => spec_states_init x
      end.

    (* ====== External Functions ====== *)

    Inductive ext_fn_t := 
    | ext_in_cmd.

    Definition cmd_reg_size := @Common.finite_bits_needed spec_action spec_action_fin.

    Definition Sigma (fn: ext_fn_t) : ExternalSignature :=
      match fn with
      | ext_in_cmd => {$ bits_t 1 ~> maybe (bits_t cmd_reg_size) $}
      end.

    Definition ext_fn_specs (fn : ext_fn_t) := 
      match fn with
      | ext_in_cmd => {| efr_name := "in_cmd"; 
                        efr_internal := false |}
      end.
    
    (* ====== Rules ====== *)

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
          USeq {{ write1(tf_reg x, `UVar (_reg_name x)`) }} acc
      ) code all_spec_states.

    Definition _rule_cmd cmd : uaction reg_t ext_fn_t :=
      let state_ops := spec_action_ops cmd in
      (* TODO: a final version should only read the needed variables, for a more optimized result *)
      _rule_read_state_vars_rec all_spec_states (
        _rule_aux state_ops (
          _rule_write_state_vars state_ops {{ pass }})).

    Definition rules :=
        (fun rl =>  match rl with
          | rule_cmd cmd => 
            let cmd_enc := Bits.of_nat cmd_reg_size (action_index cmd) in
            {{
                  guard(get(extcall ext_in_cmd(Ob~1), valid));
                  guard(get(extcall ext_in_cmd(Ob~1), data) == #cmd_enc);
                  `_rule_cmd cmd`
            }}
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

