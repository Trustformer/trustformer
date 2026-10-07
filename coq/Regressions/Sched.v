Require Import Koika.Frontend.
Require Import Koika.Std.
Require Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Backend.Lowering.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.

Require Import Coq.Logic.EqdepFacts.

(* A scheduling demo: one action over two 32-bit registers whose multiplies and
   conditional spread across several stages at cost limit 5. *)

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
        (@tf_ops fs_states fs_inputs fs_outputs Empty_set)
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

    Definition fs_step := tf_ops_run fs_states_size fs_inputs_size fs_outputs_size no_ips.
    
    Section Examples.
        

    End Examples.

End FunctionalSpecification.


Section Instance.

    Definition tfs_ctx : TFSchedContext := {|
        tfs_spec_states := fs_states;
        tfs_spec_states_fin := _;
        tfs_spec_states_size := fs_states_size;
        tfs_spec_states_init := fs_states_init;

        tfs_spec_inputs := fs_inputs;
        tfs_spec_inputs_fin := _;
        tfs_spec_inputs_size := fs_inputs_size;
        tfs_spec_inputs_class := fun _ => Public;
        tfs_spec_outputs := fs_outputs;
        tfs_spec_outputs_fin := _;
        tfs_spec_outputs_size := fs_outputs_size;
        tfs_spec_outputs_class := fun _ => Public;
        tfs_spec_action := fs_action;
        tfs_spec_action_fin := _;
        tfs_spec_action_ops := fs_transitions;
        (* no attached IP: no call names a response port here *)
        (* no IP drives any port here, so nothing can conflict with one *)
        tfs_spec_ips := Empty_set;
        tfs_spec_ip := no_ips;
        tfs_spec_decls := []
    |}.

    Definition tf_schedule := tfs_schedule tfs_ctx 5.

    Definition tf_ctx : TFSynthContext := {|
        tf_sched_ctx := tf_schedule;

        tf_action_encoding := fs_action_encoding;
        tf_action_encoding_inj := fs_action_encoding_inj;
    |}.

  Definition package := Lowering.package tf_ctx "Regression_Sched".
    

End Instance.

(* Extraction *)

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Regression_Sched.ml" prog.

