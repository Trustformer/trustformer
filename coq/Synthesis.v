Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.
Require Koika.Properties.SemanticProperties.
Require Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Utils.
Require Import Trustformer.Scheduler.Scheduler.
Require Trustformer.Properties.Common.
From Koika.Utils Require Import Tactics.

Require Import Streams.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Init.Tactics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.micromega.Lia.

Require Import Hammer.Plugin.Hammer.
Set Hammer ATPLimit 5.
Set Hammer GSMode 63.

Record TFSynthContext := {
  tf_spec_states : Type;
  tf_spec_states_fin : FiniteType tf_spec_states;
  tf_spec_states_names : Show tf_spec_states;
  tf_spec_states_size : tf_spec_states -> nat;
  tf_spec_states_init : forall x: tf_spec_states, tf_states_type tf_spec_states_size x;

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
  tf_spec_action_reg_size : nat;
  tf_spec_action_encoding : tf_spec_action -> bits_t tf_spec_action_reg_size;
  tf_spec_action_encoding_inj : forall a1 a2, tf_spec_action_encoding a1 = tf_spec_action_encoding a2 -> a1 = a2;
  tf_spec_action_ops : tf_spec_action -> @tf_ops tf_spec_states tf_spec_inputs tf_spec_outputs
}.

Section TrustformerSynthesis.

    Context (tf_ctx: TFSynthContext).

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

    (* ====== Instances ====== *)

    Hint Extern 0 (FiniteType spec_states) => exact (tf_spec_states_fin tf_ctx) : typeclass_instances.
    Hint Extern 0 (FiniteType spec_inputs) => exact (tf_spec_inputs_fin tf_ctx) : typeclass_instances.
    Hint Extern 0 (FiniteType spec_outputs) => exact (tf_spec_outputs_fin tf_ctx) : typeclass_instances.
    Hint Extern 0 (FiniteType spec_action) => exact (tf_spec_action_fin tf_ctx) : typeclass_instances.

    Hint Extern 0 (Show spec_states) => exact (tf_spec_states_names tf_ctx) : typeclass_instances.
    Hint Extern 0 (Show spec_inputs) => exact (tf_spec_inputs_names tf_ctx) : typeclass_instances.
    Hint Extern 0 (Show spec_outputs) => exact (tf_spec_outputs_names tf_ctx) : typeclass_instances.
    Hint Extern 0 (Show spec_action) => exact (tf_spec_action_names tf_ctx) : typeclass_instances.

    Instance _eq_dec_states : EqDec spec_states.
    Proof. pose spec_states_fin. apply EqDec_FiniteType. Defined.

    Instance _eq_dec_outputs : EqDec spec_outputs.
    Proof. pose spec_outputs_fin. apply EqDec_FiniteType. Defined.

    (* ====== Scheduler ====== *)

    Definition tfs_ctx : TFSchedContext := {|
      tfs_spec_states := spec_states;
      tfs_spec_states_fin := _;
      tfs_spec_states_size := spec_states_size;
      tfs_spec_states_init := spec_states_init;

      tfs_spec_inputs := spec_inputs;
      tfs_spec_inputs_fin := _;
      tfs_spec_inputs_size := spec_inputs_size;

      tfs_spec_outputs := spec_outputs;
      tfs_spec_outputs_fin := _;
      tfs_spec_outputs_size := spec_outputs_size;

      tfs_spec_action := spec_action;
      tfs_spec_action_fin := _;
      tfs_spec_action_ops := spec_action_ops
    |}.

    Hint Extern 0 (FiniteType (tfs_states tfs_ctx)) => exact (tfs_states_fin tfs_ctx) : typeclass_instances.
    Hint Extern 0 (Show (tfs_states tfs_ctx)) => exact (show_tfs_states tfs_ctx) : typeclass_instances.

    Local Notation tfs_states_index := (@finite_index (tfs_states tfs_ctx) _).
    Local Notation tfs_all_states := (@finite_elements (tfs_states tfs_ctx) _).
    Local Notation tfs_states_size := (tfs_states_size tfs_ctx).
    Local Notation tfs_states_t := (tf_states_type tfs_states_size).
    Local Notation tfs_states_init := (tfs_states_init tfs_ctx).
    Local Notation tfs_schedule := (tfs_schedule tfs_ctx).

    Local Notation spec_var_written_dec := (tf_ops_var_written_dec tfs_states_size spec_inputs_size spec_outputs_size).
    Local Notation spec_out_written_dec := (tf_ops_out_written_dec tfs_states_size spec_inputs_size spec_outputs_size).

    (* ====== Registers ====== *)

    Inductive reg_t := 
    | tf_cmd
    | tf_cmd_ack
    | tf_stage
    | tf_reg (x : tfs_states tfs_ctx)
    | tf_out_pub (x : spec_outputs)
    | tf_out (x : spec_outputs)
    | tf_out_ack (x : spec_outputs)
    .

    Local Ltac solve_lookup_in_app := 
      rewrite !map_length; (* hammer. *) hauto use: @Common.finite_index_bounded, vect_skipn_plus_cast unfold: finite_elements, tf_spec_states, tf_spec_outputs.    

    Local Ltac solve_bounded_lia H H0 s1 s2 t1 t2 :=
      rewrite in_map_iff in *; 
      destruct H as [s1 [Hs1_in Hs1_eq]]; destruct H0 as [s2 [Hs2_in Hs2_eq]]; subst;
      generalize (Common.finite_index_bounded s1 (fin_t := t1));
      generalize (Common.finite_index_bounded s2 (fin_t := t2));
      lia.

    Instance _reg_t_finite : FiniteType reg_t.
    Proof. Admitted.
      (* econstructor.
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
        intros. destruct a. 
        {
          rewrite nth_error_app1 by solve_lookup_in_app.
          rewrite nth_error_map. 
          rewrite (@finite_surjective spec_states spec_states_fin _). (* hammer. *) sfirstorder.
        }
        {
          rewrite nth_error_app2 by solve_lookup_in_app.
          rewrite nth_error_app1 by solve_lookup_in_app.

          rewrite !map_length. replace (_ + _ - _) with (spec_output_index x) by lia. rewrite nth_error_map.
          rewrite (@finite_surjective spec_outputs spec_outputs_fin x). (* hammer. *) sfirstorder.
        }
        {
          rewrite nth_error_app2 by solve_lookup_in_app.
          rewrite nth_error_app2 by solve_lookup_in_app.

          rewrite !map_length. replace (_ + _ + _ - _ - _) with (spec_output_index x) by lia. rewrite nth_error_map.
          rewrite (@finite_surjective spec_outputs spec_outputs_fin x). (* hammer. *) sfirstorder.
        }
      }
      {
        rewrite !map_app, !map_map. apply NoDup_app. 2: apply NoDup_app.
        - apply (finite_injective (FiniteType := spec_states_fin)).
        - apply FinFun.Injective_map_NoDup. 2: apply finite_nodup. unfold FinFun.Injective. apply Common.finite_index_plus_constant_l_inj.
        - apply FinFun.Injective_map_NoDup. 2: apply finite_nodup. unfold FinFun.Injective. apply Common.finite_index_plus_constant_l_inj.
        - intros. 
          solve_bounded_lia H H0 s1 s2 @spec_outputs_fin @spec_outputs_fin.
        - intros. apply in_app_or in H0. destruct H0. 
          * solve_bounded_lia H H0 s1 s2 @spec_states_fin @spec_outputs_fin.
          * solve_bounded_lia H H0 s1 s2 @spec_states_fin @spec_outputs_fin.
      }
    Defined. *)

    Definition _reg_name (x: tfs_states tfs_ctx) : string :=
      "tf_st_" ++ string_id_of_nat (tfs_states_index x).

    Definition _out_name (x: spec_outputs) : string :=
      "tf_out_" ++ string_id_of_nat (spec_output_index x).

    Instance reg_names : Show reg_t :=
      { show := fun r => match r with
          | tf_cmd => "cmd"
          | tf_cmd_ack => "cmd_ack"
          | tf_stage => "stage"
          | tf_reg x => String.append "st_" (show x)
          | tf_out x => String.append "out_" (show x)
          | tf_out_pub x => String.append "out_buf_" (show x)
          | tf_out_ack x => String.append "out_ack_" (show x)
          end
      }.

    (* ====== Register Types ====== *)

    Definition max_stage : nat :=
      List.fold_right (fun act acc => Nat.max acc (Datatypes.length (tfs_schedule act))) 0 spec_all_actions.

    Local Notation tf_stage_reg_size := (Nat.log2_up max_stage).

    Definition R (r: reg_t) :=
    match r with
    | tf_cmd => bits_t spec_action_reg_size
    | tf_cmd_ack => bits_t 1
    | tf_stage => bits_t tf_stage_reg_size
    | tf_reg x => tfs_states_t x
    | tf_out x => spec_outputs_t x
    | tf_out_pub x => spec_outputs_t x
    | tf_out_ack x => bits_t 1
    end.

    Definition r (reg: reg_t) : R reg :=
      match reg with
      | tf_cmd => Bits.zero
      | tf_cmd_ack => Bits.zero
      | tf_stage => Bits.zero
      | tf_reg x => tfs_states_init x
      | tf_out x => Bits.zero
      | tf_out_pub x => Bits.zero
      | tf_out_ack x => Bits.zero
      end.

    (* ====== External Functions ====== *)

    Inductive ext_fn_t := 
    | ext_in_cmd
    | ext_input (x : spec_inputs)
    | ext_output (x : spec_outputs)
    .

    Definition Sigma (fn: ext_fn_t) : ExternalSignature :=
      match fn with
      | ext_in_cmd => {$ bits_t 1 ~> maybe (bits_t spec_action_reg_size) $}
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
    | rule_cmd (cmd: spec_action) (stage: Vect.index (List.length (tfs_schedule cmd)))
    | rule_out (out: spec_outputs)
    | rule_busy
    .

    Instance rule_names : Show rule_name_t :=
      { show := fun r => match r with
          | rule_cmd cmd stage => String.append "rule_cmd_" (String.append (String.append (string_id_of_nat (Vect.index_to_nat stage)) "_") (show cmd))
          | rule_out out => String.append "rule_out_" (show out)
          | rule_busy => "rule_busy"
          end
      }.

    Definition system_schedule_outputs : scheduler := 
      List.fold_right (fun t acc => rule_out t |> acc) Done spec_all_outputs.

    Definition system_schedule_stages (cmd: spec_action) (other: scheduler) : scheduler :=
      List.fold_right (fun t acc => rule_cmd cmd t |> acc) other (@finite_elements (Vect.index (List.length (tfs_schedule cmd))) _).

    Definition system_schedule_actions : scheduler  :=
      List.fold_right system_schedule_stages system_schedule_outputs spec_all_actions.

    Definition system_schedule := rule_busy |> system_schedule_actions.
    
    Definition synth_convert (out_var_size in_var_size : nat) code : uaction reg_t ext_fn_t :=
      if Nat.eq_dec out_var_size in_var_size then
        code
      else if Nat.leb in_var_size out_var_size then
        (UUnop (UBits1 (UZExtL out_var_size)) code)
      else
        (UUnop (UBits1 (USlice 0 out_var_size)) code).

    Fixpoint expr_to_uaction (e: tf_expr) (target_size: nat) : uaction reg_t ext_fn_t :=
      match e with
        | tf_const value =>
            let val := Bits.of_nat target_size value in {{#val}}
        | tf_var v =>
            synth_convert target_size (tfs_states_size v) (UVar (_reg_name v))
        | tf_input v =>
            synth_convert target_size (spec_inputs_size v) (UExternalCall (ext_input v) {{Ob~1}})
        | tf_op1 op src =>
            (UUnop (UBits1 UNot) (expr_to_uaction src target_size))
        | tf_op2 op src1 src2 =>
            match op with
            | tf_and => (UBinop (UBits2 UAnd) (expr_to_uaction src1 target_size) (expr_to_uaction src2 target_size))
            | tf_or => (UBinop (UBits2 UOr) (expr_to_uaction src1 target_size) (expr_to_uaction src2 target_size))
            | tf_xor => (UBinop (UBits2 UXor) (expr_to_uaction src1 target_size) (expr_to_uaction src2 target_size))
            | tf_add => (UBinop (UBits2 UPlus) (expr_to_uaction src1 target_size) (expr_to_uaction src2 target_size))
            | tf_sub => (UBinop (UBits2 UMinus) (expr_to_uaction src1 target_size) (expr_to_uaction src2 target_size))
            | tf_mul => synth_convert target_size (target_size+target_size) (UBinop (UBits2 UMul) (expr_to_uaction src1 target_size) (expr_to_uaction src2 target_size))
            | tf_cmp cmp_sz cmp_op =>
                let op_f := match cmp_op with
                  | tf_eq => (UEq false)
                  | tf_neq => (UEq true)
                  | tf_lt => (UBits2 (UCompare false cLt))
                  | tf_le => (UBits2 (UCompare false cLe))
                  | tf_gt => (UBits2 (UCompare false cGt))
                  | tf_ge => (UBits2 (UCompare false cGe))
                  end in
                synth_convert target_size 1 (UBinop (op_f) (expr_to_uaction src1 cmp_sz) (expr_to_uaction src2 cmp_sz))
            end
        end.

    Definition op_to_uaction (op: tf_op) (code: uaction reg_t ext_fn_t) : uaction reg_t ext_fn_t :=
      match op with
      | tf_nop => UBind "_unused" {{ #Ob }} code 
      | tf_assign x expr => UBind (_reg_name x) (expr_to_uaction expr (tfs_states_size x)) code
      | tf_output x expr => UBind (_out_name x) (expr_to_uaction expr (spec_outputs_size x)) code
      end.

    Fixpoint _rule_aux
      (rule_ops: tf_ops)
      (code: uaction reg_t ext_fn_t)
      : uaction reg_t ext_fn_t :=
      match rule_ops with
      | tf_ops_base op => op_to_uaction op code
      | tf_ops_cons ops1 ops2 => _rule_aux ops1 (_rule_aux ops2 code)
      | tf_ops_if cond then_ops else_ops =>
          UIf (expr_to_uaction cond 1)
            (_rule_aux then_ops code)
            (_rule_aux else_ops code)
      end.      

    Definition _rule_read_var0 (var_map: reg_t -> string) (reg : reg_t) (code: uaction reg_t ext_fn_t): uaction reg_t ext_fn_t :=
        UBind (var_map reg) {{ read0(reg) }} code.

    Definition _rule_read_vars0 (var_map: reg_t -> string) (regs : list reg_t) (code: uaction reg_t ext_fn_t): uaction reg_t ext_fn_t :=
      List.fold_right (_rule_read_var0 var_map) code regs.

    Definition _rule_write_var0 (var_map: reg_t -> string) (reg : reg_t) (code: uaction reg_t ext_fn_t): uaction reg_t ext_fn_t :=
        USeq {{ write0(reg, `UVar (var_map reg)`) }} code.

    Definition _rule_write_vars0 (var_map: reg_t -> string) (regs : list reg_t) (code: uaction reg_t ext_fn_t): uaction reg_t ext_fn_t :=
      List.fold_right (_rule_write_var0 var_map) code regs.

    Definition _written_outputs (state_ops: tf_ops) := 
        List.filter (fun o => if (spec_out_written_dec o state_ops) then true else false) spec_all_outputs.

    Definition _written_states (state_ops: tf_ops) := 
        List.filter (fun s => if (spec_var_written_dec s state_ops) then true else false) tfs_all_states.

    Definition _register_var_name (r: reg_t) : string :=
      match r with
      | tf_cmd => "__unused"
      | tf_cmd_ack => "__unused"
      | tf_stage => "__unused"
      | tf_reg x => _reg_name x
      | tf_out x => _out_name x
      | tf_out_pub x => "__unused"
      | tf_out_ack x => "__unused"
      end.

    Definition _rule_cmd cmd stage : uaction reg_t ext_fn_t :=
      let cmd_schedule := vect_of_list (tfs_schedule cmd) in
      let rule_ops := vect_nth cmd_schedule stage in
      _rule_read_vars0 _register_var_name (map tf_reg tfs_all_states) (
        _rule_read_vars0 _register_var_name (map tf_out spec_all_outputs) (

          _rule_aux rule_ops (
          
            _rule_write_vars0 _register_var_name (map tf_reg (_written_states rule_ops)) (
              _rule_write_vars0 _register_var_name (map tf_out (_written_outputs rule_ops)) (
                {{ pass }} ))))).

    Definition _rule_cmd_guard cmd stage : uaction reg_t ext_fn_t :=
      let stage_idx := index_to_nat (sz:=(List.length (tfs_schedule cmd))) stage in
      let stage_idx_enc := Bits.of_nat tf_stage_reg_size stage_idx in
      let stage_max := Datatypes.length (tfs_schedule cmd) - 1 in
      let stage_idx_inc := if Nat.eq_dec stage_idx stage_max then
        Bits.zero
      else
        Bits.of_nat tf_stage_reg_size (stage_idx + 1) in
      let cmd_enc := spec_action_encoding cmd in
      
      if Nat.eq_dec stage_idx 0 then
        {{
          guard(get(extcall ext_in_cmd(Ob~1), valid));
          guard(get(extcall ext_in_cmd(Ob~1), data) == #cmd_enc);
          guard(read0(tf_stage) == #stage_idx_enc);
          write0(tf_cmd, #cmd_enc);
          write0(tf_stage, #stage_idx_inc)
        }}
      else
        {{
          guard(read0(tf_cmd) == #cmd_enc);
          guard(read0(tf_stage) == #stage_idx_enc);
          write0(tf_stage, #stage_idx_inc)
        }}.

    Definition rules :=
        (fun rl =>  match rl with
          | rule_busy =>
            let ready_stage := Bits.zero (sz:=tf_stage_reg_size) in
            {{
              guard(read0(tf_stage) != #ready_stage);
              write0(tf_cmd_ack, get(extcall ext_in_cmd(Ob~0), valid))
            }}
          | rule_cmd cmd stage => 
            {{
                  (`_rule_cmd_guard cmd stage`);
                  `_rule_cmd cmd stage`
            }}
          | rule_out out =>
            UWrite P1 (tf_out_ack out) (UExternalCall (ext_output out) ({{ read1(tf_out out) }} ))
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

