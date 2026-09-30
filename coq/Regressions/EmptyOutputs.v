Require Import Koika.Frontend.
Require Import Koika.Std.
Require Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.TypedSynthesis.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

(* A negator with an EMPTY output type: one 32-bit state register, two actions
   (nop, neg), triggered through a command register whose first bit marks it
   valid.  The empty [fs_outputs] is what this example pins. *)

Section FunctionalSpecification.

    Definition sz := 32.
    Definition bits_false := Bits.of_nat sz 0.
    Definition bits_true := Bits.neg (bits_false).

    Inductive fs_action :=
    | fs_act_nop
    | fs_act_neg
    .

    Definition fs_action_encoding (a: fs_action) : bits_t 16 :=
    match a with
    | fs_act_nop => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | fs_act_neg => Ob~0~0~0~0~0~0~0~0~0~0~0~0~1~0~1~0
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
    | fs_st_val
    .

    Inductive fs_inputs :=
    .

    Inductive fs_outputs :=
    .

    Definition fs_states_size (x: fs_states) : nat :=
    match x with
    | fs_st_val => sz
    end.

    Definition fs_inputs_size (x: fs_inputs) : nat := 
    match x with
    end.

    Definition fs_outputs_size (x: fs_outputs) : nat := 
    match x with
    end.

    Definition fs_states_t := tf_states_type fs_states_size. 

    Definition fs_states_init (x: fs_states) : (fs_states_t x) :=
    match x with
    | fs_st_val => Bits.zero
    end.

    Definition fs_transitions
        (act: fs_action)
        :
        (@tf_ops fs_states fs_inputs fs_outputs Empty_set)
        :=
        match act with
        | fs_act_nop => tf_ops_base (tf_nop) 
        | fs_act_neg => tf_ops_base (tf_assign fs_st_val (tf_op1 (tf_not) (tf_svar fs_st_val)))
        end.

    Definition fs_step := tf_ops_run fs_states_size fs_inputs_size fs_outputs_size no_ips.
    
    Section Examples.

        Definition s_init := ContextEnv.(create) fs_states_init.
        Example s_example : ContextEnv.(getenv) s_init fs_st_val = bits_false.
        Proof. reflexivity. Qed.

        Definition s1_trans := fs_transitions fs_act_nop.
        Definition s1_state := fst (fs_step s1_trans (s_init, ContextEnv.(create) (fun _ => Bits.zero)) (fun _ => Bits.zero)).
        Example s1_example : ContextEnv.(getenv) s1_state fs_st_val = bits_false.
        Proof. ssimpl. Qed.
        
        Definition s2_trans := fs_transitions fs_act_neg.
        Definition s2_state := fst (fs_step s2_trans (s_init, ContextEnv.(create) (fun _ => Bits.zero)) (fun _ => Bits.zero)).
        Example s2_example : ContextEnv.(getenv) s2_state fs_st_val = bits_true.
        Proof. 
            cbn -[vect_to_list]. sauto.
        Qed.

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

    Definition tf_schedule := tfs_schedule tfs_ctx 10.

    Definition tf_ctx : TFSynthContext := {|
        tf_sched_ctx := tf_schedule;

        tf_action_encoding := fs_action_encoding;
        tf_action_encoding_inj := fs_action_encoding_inj;
    |}.

  Definition package := TypedSynthesis.package tf_ctx "Example_InternalNegator".
    

End TypedSynthesis.

(* Extraction *)

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Example_InternalNegator.ml" prog.

