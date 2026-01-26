Require Import Koika.Frontend.
Require Import Koika.Std.
Require Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.TypedSynthesis.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.

Require Import Coq.Logic.EqdepFacts.

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

(*
    An example specification and synthesis of a simple lockbox.
    The hardware module has a single internal state register (32 bits) and supports two actions (set, test).
    Actions are triggered through a command register, where the first 1 bit indicates if the command is valid,
    and the remaining bits indicate the action to perform.

 *)

Section FunctionalSpecification.

    Definition sz := 32.
    Definition bits_false := Bits.of_nat sz 0.
    Definition bits_true := Bits.neg (bits_false).

    Inductive fs_action :=
    | fs_act_set
    | fs_act_test
    .

    Definition fs_action_encoding (a: fs_action) : bits_t 16 :=
    match a with
    | fs_act_set => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | fs_act_test => Ob~0~0~0~0~0~0~0~0~0~0~0~0~1~0~1~0
    end.

    Lemma fs_action_encoding_inj :
        forall a1 a2,
        fs_action_encoding a1 = fs_action_encoding a2 ->
        a1 = a2.
    Proof.
        intros. unfold fs_action_encoding in H.
        destruct a1; destruct a2; try reflexivity; try discriminate.
    Qed.

    Inductive fs_states :=
    | fs_st_pin
    | fs_st_secret
    .

    Inductive fs_inputs :=
    | fs_in_pin
    | fs_in_secret
    .

    Inductive fs_outputs :=
    | fs_out_status
    | fs_out_secret
    .

    Definition fs_states_size (x: fs_states) : nat :=
    match x with
    | fs_st_pin => sz
    | fs_st_secret => sz
    end.

    Definition fs_inputs_size (x: fs_inputs) : nat := 
    match x with
    | fs_in_pin => sz
    | fs_in_secret => sz
    end.

    Definition fs_outputs_size (x: fs_outputs) : nat := 
    match x with
    | fs_out_status => sz
    | fs_out_secret => sz
    end.

    Definition fs_states_t := tf_states_type fs_states_size. 

    Definition fs_states_init (x: fs_states) : (fs_states_t x) :=
    match x with
    | fs_st_pin => Bits.zero
    | fs_st_secret => Bits.zero
    end.

    Definition fs_transitions
        (act: fs_action)
        :
        (@tf_ops fs_states fs_inputs fs_outputs)
        :=
        match act with
        | fs_act_set => 
            tf_ops_cons
                (tf_ops_base (tf_assign fs_st_pin (tf_ivar fs_in_pin)))
                (tf_ops_base (tf_assign fs_st_secret (tf_ivar fs_in_secret)))
        | fs_act_test => tf_ops_if 
            (tf_op2 (tf_cmp sz tf_eq) (tf_svar fs_st_pin) (tf_ivar fs_in_pin)) 
                (tf_ops_cons 
                    (tf_ops_base (tf_output fs_out_secret (tf_svar fs_st_secret))) 
                    (tf_ops_base (tf_output fs_out_status (tf_const 1))))
                (tf_ops_base (tf_output fs_out_status (tf_const 0)))
        end.


    Definition fs_step := tf_ops_run fs_states_size fs_inputs_size fs_outputs_size.
    
    Section Examples.
        Definition bits_10 := Bits.of_nat sz 10.
        Definition bits_42 := Bits.of_nat sz 42.

        Definition s_init := ContextEnv.(create) fs_states_init.
        Example s_example : ContextEnv.(getenv) s_init fs_st_pin = bits_false.
        Proof. reflexivity. Qed.
        Example s_example2 : ContextEnv.(getenv) s_init fs_st_secret = bits_false.
        Proof. reflexivity. Qed.

        Definition s1_trans := fs_transitions fs_act_set.
        Definition s1_trans_r := (fs_step s1_trans (s_init, ContextEnv.(create) (fun _ => Bits.zero)) 
            (fun x => match x with 
                | fs_in_pin => bits_10 
                | fs_in_secret => bits_42
                end)).
        Definition s1_state := fst s1_trans_r.
        Definition s1_output := snd s1_trans_r.
        Example s1_example_pin : ContextEnv.(getenv) s1_state fs_st_pin = bits_10.
        Proof. 
            cbn -[vect_to_list]. sauto.
        Qed.
        Example s1_example_secret : ContextEnv.(getenv) s1_state fs_st_secret = bits_42.
        Proof. 
            cbn -[vect_to_list]. sauto.
        Qed.
        Example s1_example_output : ContextEnv.(getenv) s1_output fs_out_status = bits_false.
        Proof. ssimpl. Qed.

        Definition s2_trans := fs_transitions fs_act_test.
        Definition s2_trans_r := (fs_step s2_trans s1_trans_r (fun _ => Bits.zero)).
        Definition s2_state := fst s2_trans_r.
        Definition s2_output := snd s2_trans_r.
        Example s2_example_pin : ContextEnv.(getenv) s2_state fs_st_pin = bits_10.
        Proof. 
            cbn -[vect_to_list]. sauto.
        Qed.
        Example s2_example_secret : ContextEnv.(getenv) s2_state fs_st_secret = bits_42.
        Proof. 
            cbn -[vect_to_list]. sauto.
        Qed.
        Example s2_example_output : ContextEnv.(getenv) s2_output fs_out_status = Bits.of_nat sz 0.
        Proof. ssimpl. Qed.
        Example s2_example_output_secret : ContextEnv.(getenv) s2_output fs_out_secret = Bits.zero.
        Proof. ssimpl. Qed.

        Definition s3_trans := fs_transitions fs_act_test.
        Definition s3_trans_r := (fs_step s3_trans s2_trans_r (fun x => match x with 
            | fs_in_pin => bits_10 
            | fs_in_secret => Bits.zero
            end)).
        Definition s3_state := fst s3_trans_r.
        Definition s3_output := snd s3_trans_r.
        Example s3_example_pin : ContextEnv.(getenv) s3_state fs_st_pin = bits_10.
        Proof. 
            cbn -[vect_to_list Bits.neg]. sauto.
        Qed.
        Example s3_example_secret : ContextEnv.(getenv) s3_state fs_st_secret = bits_42.
        Proof. 
            cbn -[vect_to_list Bits.neg]. sauto.
        Qed.
        Example s3_example_output : ContextEnv.(getenv) s3_output fs_out_status = Bits.of_nat sz 1.
        Proof. ssimpl. Qed.
        Example s3_example_output_secret : ContextEnv.(getenv) s3_output fs_out_secret = bits_42.
        Proof. ssimpl. Qed.

    End Examples.

End FunctionalSpecification.


Section TypedSynthesis.

    Definition tfs_ctx : TFSchedContext := {|
        tfs_spec_states := fs_states;
        tfs_spec_states_fin := _;
        tfs_spec_states_size := fs_states_size;
        tfs_spec_states_init := fs_states_init;

        tfs_spec_inputs := fs_inputs;
        tfs_spec_inputs_fin := _;
        tfs_spec_inputs_size := fs_inputs_size;

        tfs_spec_outputs := fs_outputs;
        tfs_spec_outputs_fin := _;
        tfs_spec_outputs_size := fs_outputs_size;

        tfs_spec_action := fs_action;
        tfs_spec_action_fin := _;
        tfs_spec_action_ops := fs_transitions
    |}.

    Definition tf_schedule := tfs_schedule tfs_ctx 10.

    Definition tf_ctx : TFSynthContext := {|
        tf_sched_ctx := tf_schedule;

        tf_action_encoding := fs_action_encoding;
        tf_action_encoding_inj := fs_action_encoding_inj;
    |}.

    Definition R := TypedSynthesis.R tf_ctx.

    Definition r := TypedSynthesis.r tf_ctx.

    Definition Sigma := TypedSynthesis.Sigma tf_ctx.

    Definition system_schedule := TypedSynthesis.system_schedule tf_ctx.
    
    Definition ext_fn_specs := TypedSynthesis.ext_fn_specs tf_ctx.

    Instance ext_fn_names : Show _ := TypedSynthesis.ext_fn_names tf_ctx.

    Definition package :=
      {| ip_koika := {| koika_reg_types := R;
                        koika_reg_names := TypedSynthesis.reg_names tf_ctx;
                        koika_reg_init := r;
                        koika_reg_finite := TypedSynthesis._reg_t_finite tf_ctx;
                        koika_ext_fn_types := Sigma;
                        koika_rules := TypedSynthesis.rules tf_ctx;
                        koika_rule_names := TypedSynthesis.rule_names tf_ctx;
                        koika_rule_external := (fun _ => false);
                        koika_scheduler := system_schedule;
                        koika_module_name := "Example_Lockbox" |};

      ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn; efs_method := false |};
                  sp_prelude := None |};

      ip_verilog := {| vp_ext_fn_specs := ext_fn_specs |} |}.
    

End TypedSynthesis.

(* Extraction *)

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Example_Lockbox.ml" prog.

