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

    Inductive fs_action :=
    | fs_act
    .

    Definition fs_action_encoding (a: fs_action) : bits_t 16 :=
    match a with
    | fs_act => Bits.of_nat 16 10
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
    | x
    | y
    .

    Inductive fs_inputs :=
    | in_A
    .

    Inductive fs_outputs :=
    | out_A
    .

    Definition fs_states_size (x: fs_states) : nat :=
    sz.

    Definition fs_inputs_size (x: fs_inputs) : nat := 
    sz.

    Definition fs_outputs_size (x: fs_outputs) : nat := 
    sz.

    Definition fs_states_t := tf_states_type fs_states_size. 

    Definition fs_states_init (x: fs_states) : (fs_states_t x) :=
        match x with
        | x => Bits.zero
        | y => Bits.zero
        end.

    Definition fs_transitions
        (act: fs_action)
        :
        (@tf_ops fs_states fs_inputs fs_outputs)
        :=
        match act with
        | fs_act => 
            {[
                let $x := $x * $x;
                (if $in_A then
                    let $y := $x * $y;
                    let $x := $x + #1
                else
                    pass
                );
                let $out_A := $y 
            ]}
        end.

    Definition fs_step := tf_ops_run fs_states_size fs_inputs_size fs_outputs_size.
    
    Section Examples.
        

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
        tfs_spec_action_ops := fs_transitions;
        tfs_spec_decls := []
    |}.

    Definition tf_schedule := tfs_schedule tfs_ctx 5.

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
                        koika_module_name := "Example_Sched" |};

      ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn; efs_method := false |};
                  sp_prelude := None |};

      ip_verilog := {| vp_ext_fn_specs := ext_fn_specs |} |}.
    

End TypedSynthesis.

(* Extraction *)

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Example_Sched.ml" prog.

