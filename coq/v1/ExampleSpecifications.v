Require Import Koika.Frontend.
Require Import Koika.Std.
Require Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.

Require Import Trustformer.v1.TrustformerSyntax.
Require Import Trustformer.v1.TrustformerSemantics.
Require Import Trustformer.v1.TrustformerSynthesis.

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Section FunctionalSpecification.

    Definition sz := 32.
    Definition bits_false := Bits.of_nat sz 0.
    Definition bits_true := Bits.neg (bits_false).

    Inductive fs_action :=
    | fs_act_nop
    | fs_act_neg
    .

    Inductive fs_states :=
    | fs_st_val
    .

    Definition fs_states_size (x: fs_states) : nat :=
    match x with
    | fs_st_val => sz
    end.

    Definition fs_states_t := tf_states_type fs_states fs_states_size. 

    Definition fs_states_init (x: fs_states) : (fs_states_t x) :=
    match x with
    | fs_st_val => Bits.zero
    end.

    Definition fs_transitions
        (act: fs_action)
        :
        (tf_ops fs_states)
        :=
        match act with
        | fs_act_nop => tf_nop fs_states
        | fs_act_neg => tf_neg fs_states fs_st_val
        end.

    Definition fs_step := tf_op_step_commit fs_states _ fs_states_size. 
    
    Section Examples.

        Definition s_init := ContextEnv.(create) fs_states_init.
        Example s_example : ContextEnv.(getenv) s_init fs_st_val = bits_false.
        Proof. reflexivity. Qed.

        Definition s1_trans := fs_transitions fs_act_nop.
        Definition s1_state := fs_step s_init s1_trans.
        Example s1_example : ContextEnv.(getenv) s1_state fs_st_val = bits_false.
        Proof. ssimpl. Qed.
        
        Definition s2_trans := fs_transitions fs_act_neg.
        Definition s2_state := fs_step s_init s2_trans.
        Example s2_example : ContextEnv.(getenv) s2_state fs_st_val = bits_true.
        Proof. 
            unfold s2_state, s2_trans, fs_transitions.
            rewrite tf_op_step_commit_neg_same_var.
            unfold s_init. rewrite getenv_create.   
            reflexivity.    
        Qed.

    End Examples.

End FunctionalSpecification.


Section Synthesis.

    Definition tf_ctx : TFSynthContext := {|
        tf_spec_states := fs_states;
        tf_spec_states_fin := _; 
        tf_spec_states_t := fs_states_t;
        tf_spec_states_init := fs_states_init;
        tf_spec_action := fs_action;
        tf_spec_action_fin := _; 
        tf_spec_action_ops := fs_transitions
    |}.

    Definition R := TrustformerSynthesis.R tf_ctx.
    Check R.
    Definition r := TrustformerSynthesis.r tf_ctx.
    Check r.
    Definition Sigma := TrustformerSynthesis.Sigma.
    Check Sigma.

    Definition rules := TrustformerSynthesis.rules tf_ctx.
    Check rules.
    Definition system_schedule := TrustformerSynthesis.system_schedule tf_ctx.
    Check system_schedule.

    Definition checked_rules := tc_rules R Sigma rules.

    Definition package :=
      {| ip_koika := {| koika_reg_types := R;
                        koika_reg_names := TrustformerSynthesis.reg_names tf_ctx;
                        koika_reg_init := r;
                        koika_ext_fn_types := Sigma;
                        koika_rules := checked_rules;
                        koika_rule_names := TrustformerSynthesis.rule_names tf_ctx;
                        koika_rule_external := (fun _ => false);
                        koika_scheduler := system_schedule;
                        koika_module_name := "TestDesign2" |};

      ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn; efs_method := false |};
                  sp_prelude := None |};

      ip_verilog := {| vp_ext_fn_specs := ext_fn_specs |} |}.

End Synthesis.

(* Extraction *)

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "ExampleTrustformerV1.ml" prog.

