Require Import Koika.Frontend.
Require Import Koika.Std.
Require Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Synthesis.

Require Import Coq.Logic.EqdepFacts.

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

(*
    An example specification and synthesis of a simple negator module.
    The hardware module has a single internal state register (32 bits) and supports four actions (nop, neg, read, write).
    Actions are triggered through a command register, where the first 1 bit indicates if the command is valid,
    and the remaining bits indicate the action to perform.

 *)

Section FunctionalSpecification.

    Definition sz := 32.
    Definition bits_false := Bits.of_nat sz 0.
    Definition bits_true := Bits.neg (bits_false).

    Inductive fs_action :=
    | fs_act_nop
    | fs_act_neg
    | fs_act_read
    | fs_act_write
    .

    Inductive fs_states :=
    | fs_st_val
    .

    Inductive fs_inputs :=
    | fs_in_val
    .

    Inductive fs_outputs :=
    | fs_out_val
    .

    Definition fs_states_size (x: fs_states) : nat :=
    match x with
    | fs_st_val => sz
    end.

    Definition fs_inputs_size (x: fs_inputs) : nat := 
    match x with
    | fs_in_val => sz
    end.

    Definition fs_outputs_size (x: fs_outputs) : nat := 
    match x with
    | fs_out_val => sz
    end.

    Definition fs_states_t := tf_states_type fs_states fs_states_size. 

    Definition fs_states_init (x: fs_states) : (fs_states_t x) :=
    match x with
    | fs_st_val => Bits.zero
    end.

    Definition fs_transitions
        (act: fs_action)
        :
        (tf_ops fs_states fs_inputs fs_outputs)
        :=
        match act with
        | fs_act_nop => tf_nop _ _ _ 
        | fs_act_neg => tf_neg _ _ _ fs_st_val
        | fs_act_read => tf_output _ _ _ fs_st_val fs_out_val
        | fs_act_write => tf_input _ _ _ fs_st_val fs_in_val
        end.

    Definition fs_step := tf_op_step_commit fs_states _ fs_inputs fs_outputs fs_states_size fs_inputs_size.
    Definition fs_output := tf_op_outputs fs_states _ fs_inputs fs_outputs _ fs_states_size fs_inputs_size fs_outputs_size.
    
    Section Examples.
        Definition bits_10 := Bits.of_nat sz 10.
        Definition bits_neg10 := Bits.neg (Bits.of_nat sz 10).

        Definition s_init := ContextEnv.(create) fs_states_init.
        Example s_example : ContextEnv.(getenv) s_init fs_st_val = bits_false.
        Proof. reflexivity. Qed.

        Definition s1_trans := fs_transitions fs_act_nop.
        Definition s1_state := fs_step s_init (fun _ => Bits.zero) s1_trans.
        Definition s1_output := fs_output s_init (fun _ => Bits.zero) (ContextEnv.(create) (fun _ => Bits.zero)) s1_trans.
        Example s1_example_state : ContextEnv.(getenv) s1_state fs_st_val = bits_false.
        Proof. ssimpl. Qed.
        Example s1_example_output : ContextEnv.(getenv) s1_output fs_out_val = bits_false.
        Proof. ssimpl. Qed.

        Definition s2_trans := fs_transitions fs_act_write.
        Definition s2_state := fs_step s_init (fun x => match x with fs_in_val => bits_10 end) s2_trans.
        Definition s2_output := fs_output s_init (fun x => match x with fs_in_val => bits_10 end) (ContextEnv.(create) (fun _ => Bits.zero)) s2_trans.
        Example s2_example : ContextEnv.(getenv) s2_state fs_st_val = bits_10.
        Proof. 
            cbn -[vect_to_list]. sauto.
        Qed.
        Example s2_example_output : ContextEnv.(getenv) s2_output fs_out_val = bits_false.
        Proof. ssimpl. Qed.
        
        Definition s3_trans := fs_transitions fs_act_neg.
        Definition s3_state := fs_step s2_state (fun _ => Bits.zero) s3_trans.
        Definition s3_output := fs_output s2_state (fun _ => Bits.zero) (ContextEnv.(create) (fun _ => Bits.zero)) s3_trans.
        Example s3_example : ContextEnv.(getenv) s3_state fs_st_val = bits_neg10.
        Proof. 
            cbn -[vect_to_list Bits.neg]. sauto.
        Qed.
        Example s3_example_output : ContextEnv.(getenv) s3_output fs_out_val = bits_false.
        Proof. ssimpl. Qed.

        Definition s4_trans := fs_transitions fs_act_read.
        Definition s4_state := fs_step s3_state (fun _ => Bits.zero) s4_trans.
        Definition s4_output := fs_output s3_state (fun _ => Bits.zero) (ContextEnv.(create) (fun _ => Bits.zero)) s4_trans.
        Example s4_example : ContextEnv.(getenv) s4_state fs_st_val = bits_neg10.
        Proof. 
            cbn -[vect_to_list]. sauto.
        Qed.
        Example s4_example_output : ContextEnv.(getenv) s4_output fs_out_val = bits_neg10.
        Proof.
            cbn -[vect_to_list Bits.neg]. sauto.
        Qed.

    End Examples.

End FunctionalSpecification.


Section Synthesis.

    Definition tf_ctx : TFSynthContext := {|
        tf_spec_states := fs_states;
        tf_spec_states_fin := _; 
        tf_spec_states_size := fs_states_size;
        tf_spec_states_init := fs_states_init;

        tf_spec_inputs := fs_inputs;
        tf_spec_inputs_fin := _;
        tf_spec_inputs_size := fs_inputs_size;

        tf_spec_outputs := fs_outputs;
        tf_spec_outputs_fin := _;
        tf_spec_outputs_size := fs_outputs_size;

        tf_spec_action := fs_action;
        tf_spec_action_fin := _; 
        tf_spec_action_ops := fs_transitions
    |}.

    Definition R := Synthesis.R tf_ctx.

    Definition r := Synthesis.r tf_ctx.

    Definition Sigma := Synthesis.Sigma tf_ctx.

    Definition rules := Synthesis.rules tf_ctx.

    Definition system_schedule := Synthesis.system_schedule tf_ctx.
    
    Definition ext_fn_specs := Synthesis.ext_fn_specs tf_ctx.

    Instance ext_fn_names : Show (ext_fn_t tf_ctx) := Synthesis.ext_fn_names tf_ctx.

    Definition checked_rules := tc_rules R Sigma rules.

    Definition package :=
      {| ip_koika := {| koika_reg_types := R;
                        koika_reg_names := Synthesis.reg_names tf_ctx;
                        koika_reg_init := r;
                        koika_ext_fn_types := Sigma;
                        koika_rules := checked_rules;
                        koika_rule_names := Synthesis.rule_names tf_ctx;
                        koika_rule_external := (fun _ => false);
                        koika_scheduler := system_schedule;
                        koika_module_name := "Example_Negator" |};

      ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn; efs_method := false |};
                  sp_prelude := None |};

      ip_verilog := {| vp_ext_fn_specs := ext_fn_specs |} |}.
    

End Synthesis.

(* Extraction *)

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Example_Negator.ml" prog.

