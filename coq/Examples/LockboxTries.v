Require Import Koika.Frontend.
Require Import Koika.Std.
Require Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.TypedSynthesis.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.

(*
    The paper's running example: the 'lockbox' with a retry counter
    (paper/sections/05_design/01_functional_spec.tex, fig:example-spec),
    reproduced verbatim.

    This is the module behind fig:dfg1, fig:dfgA5 and fig:dfgB5, and the first
    example in the tree that uses arithmetic ([tf_sub]).
 *)

Section FunctionalSpecification.

    Definition sz := 32.
    (* [tries] counts down from 3, so two bits suffice -- this is the [2] in the
       paper's [$tries !=[2] #0]. *)
    Definition tsz := 2.
    Definition tries_reset := 3.

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
    | fs_st_tries
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
    | fs_st_tries => tsz
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
    | fs_st_tries => Bits.zero
    end.

    Definition fs_transitions
        (act: fs_action)
        :
        (@tf_ops fs_states fs_inputs fs_outputs)
        :=
        match act with
        | fs_act_set =>
            {[
                let $fs_st_pin := $fs_in_pin;
                let $fs_st_secret := $fs_in_secret;
                let $fs_st_tries := #tries_reset
            ]}
        | fs_act_test =>
            {[
                if ($fs_st_tries !=[tsz] #0) then
                    (if ($fs_st_pin ==[sz] $fs_in_pin) then
                        let $fs_out_secret := $fs_st_secret;
                        let $fs_out_status := #1;
                        let $fs_st_tries := #tries_reset
                    else
                        let $fs_out_status := #0;
                        let $fs_st_tries := $fs_st_tries - #1)
                else
                    let $fs_out_status := #0
            ]}
        end.

    Definition fs_step := tf_ops_run fs_states_size fs_inputs_size fs_outputs_size.

End FunctionalSpecification.

Section Examples.

    Definition bits_10 := Bits.of_nat sz 10.
    Definition bits_42 := Bits.of_nat sz 42.
    Definition bits_7 := Bits.of_nat sz 7.
    Definition tries (n: nat) := Bits.of_nat tsz n.
    Definition status (n: nat) := Bits.of_nat sz n.

    Definition pin_input (p: bits_t sz) (x: fs_inputs) : bits_t (fs_inputs_size x) :=
        match x with
        | fs_in_pin => p
        | fs_in_secret => Bits.zero
        end.

    Definition fs_outputs_t := tf_outputs_type fs_outputs_size.

    Definition initial
        : ContextEnv.(env_t) fs_states_t * ContextEnv.(env_t) fs_outputs_t :=
        (ContextEnv.(create) fs_states_init,
         ContextEnv.(create) (fun _ => Bits.zero)).

    Definition run (act: fs_action) input st := fs_step (fs_transitions act) st input.

    Definition st_set :=
        run fs_act_set (fun x => match x with
                                 | fs_in_pin => bits_10
                                 | fs_in_secret => bits_42
                                 end) initial.

    Example set_stores_pin :
        ContextEnv.(getenv) (fst st_set) fs_st_pin = bits_10.
    Proof. vm_compute. reflexivity. Qed.

    Example set_stores_secret :
        ContextEnv.(getenv) (fst st_set) fs_st_secret = bits_42.
    Proof. vm_compute. reflexivity. Qed.

    Example set_resets_tries :
        ContextEnv.(getenv) (fst st_set) fs_st_tries = tries 3.
    Proof. vm_compute. reflexivity. Qed.

    (* A wrong pin costs one try and reveals nothing. *)
    Definition st_wrong1 := run fs_act_test (pin_input bits_7) st_set.

    Example wrong_decrements_tries :
        ContextEnv.(getenv) (fst st_wrong1) fs_st_tries = tries 2.
    Proof. vm_compute. reflexivity. Qed.

    Example wrong_reports_failure :
        ContextEnv.(getenv) (snd st_wrong1) fs_out_status = status 0.
    Proof. vm_compute. reflexivity. Qed.

    Example wrong_keeps_secret :
        ContextEnv.(getenv) (snd st_wrong1) fs_out_secret = Bits.zero.
    Proof. vm_compute. reflexivity. Qed.

    (* The right pin releases the secret and refills the counter. *)
    Definition st_right := run fs_act_test (pin_input bits_10) st_wrong1.

    Example right_releases_secret :
        ContextEnv.(getenv) (snd st_right) fs_out_secret = bits_42.
    Proof. vm_compute. reflexivity. Qed.

    Example right_reports_success :
        ContextEnv.(getenv) (snd st_right) fs_out_status = status 1.
    Proof. vm_compute. reflexivity. Qed.

    Example right_refills_tries :
        ContextEnv.(getenv) (fst st_right) fs_st_tries = tries 3.
    Proof. vm_compute. reflexivity. Qed.

    (* Three wrong pins exhaust the counter... *)
    Definition st_wrong2 := run fs_act_test (pin_input bits_7) st_wrong1.
    Definition st_wrong3 := run fs_act_test (pin_input bits_7) st_wrong2.

    Example three_wrong_exhausts_tries :
        ContextEnv.(getenv) (fst st_wrong3) fs_st_tries = tries 0.
    Proof. vm_compute. reflexivity. Qed.

    (* ...and then even the right pin is refused, without touching the counter. *)
    Definition st_locked := run fs_act_test (pin_input bits_10) st_wrong3.

    Example locked_out_keeps_secret :
        ContextEnv.(getenv) (snd st_locked) fs_out_secret = Bits.zero.
    Proof. vm_compute. reflexivity. Qed.

    Example locked_out_reports_failure :
        ContextEnv.(getenv) (snd st_locked) fs_out_status = status 0.
    Proof. vm_compute. reflexivity. Qed.

    Example locked_out_does_not_wrap :
        ContextEnv.(getenv) (fst st_locked) fs_st_tries = tries 0.
    Proof. vm_compute. reflexivity. Qed.

End Examples.

Section TypedSynthesis.

    (* Blackbox: no declassification rules, so every phi on a secret is
       critical.  The whitebox variants live in LockboxTriesTaint.v. *)
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
                        koika_module_name := "Example_LockboxTries" |};

      ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn; efs_method := false |};
                  sp_prelude := None |};

      ip_verilog := {| vp_ext_fn_specs := ext_fn_specs |} |}.

End TypedSynthesis.

(* Extraction *)

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Example_LockboxTries.ml" prog.

