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

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

(* A lockbox: a pin and a secret in state, set from inputs; [test] publishes
   the secret and a status when the pin matches. *)

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
        (@tf_ops fs_states fs_inputs fs_outputs Empty_set)
        :=
        match act with
        | fs_act_set => 
            {[
                let $fs_st_pin := $fs_in_pin;
                let $fs_st_secret := $fs_in_secret
            ]}
        | fs_act_test => 
            {[
                if ($fs_st_pin ==[sz] $fs_in_pin) then 
                    let $fs_out_secret := $fs_st_secret;
                    let $fs_out_status := #1
                else 
                    let $fs_out_status := #0
            ]}
        end.


    Definition fs_step := tf_ops_run fs_states_size fs_inputs_size fs_outputs_size no_ips.
    
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


Section Lowering.

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

  Definition package := Lowering.package tf_ctx "Example_Lockbox".
    

End Lowering.

(* Extraction *)

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Example_Lockbox.ml" prog.

