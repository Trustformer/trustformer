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

(*
    Calling a TRUSTED EXTERNAL FUNCTION from the DSL.

    The module keeps a 32-bit secret and, on request, publishes a tag computed by an
    attached module [fs_mix] over the secret combined with the caller's input. The
    attached module is reached through its own I/O wires, which the generated Verilog
    exposes with an "ext_" prefix (see TypedSynthesis.ext_fn_specs) and which the
    attacker is assumed not to observe.

    This example is the L = 0 (combinational) case: the declared latency is 0, so the
    attached module must answer in the same cycle. Phase B of the campaign adds
    declared latencies > 0.

    NOTE: exactly ONE call site per external function. Kôika gives each [ext_fn_t]
    element a single port pair and emits one `assign` per `ExternalCall` site, so a
    second call site — even in a different action — produces two conflicting drivers
    on `ext_<f>_arg`. See A8 in agents/extern-calls-mvp/PLAN.md.
 *)

Section FunctionalSpecification.

    Definition sz := 32.

    Inductive fs_action :=
    | fs_act_store
    | fs_act_tag
    .

    Definition fs_action_encoding (a: fs_action) : bits_t 16 :=
    match a with
    | fs_act_store => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | fs_act_tag   => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1
    end.

    Lemma fs_action_encoding_inj :
        forall a1 a2,
        fs_action_encoding a1 = fs_action_encoding a2 ->
        a1 = a2.
    Proof.
        intros. unfold fs_action_encoding in H.
        destruct a1; destruct a2; try reflexivity; try discriminate.
    Qed.

    Inductive fs_states  := fs_st_secret.
    Inductive fs_inputs  := fs_in_val.
    Inductive fs_outputs := fs_out_tag.

    (* The trusted external functions this module may call. *)
    Inductive fs_externs := fs_mix.

    Definition fs_states_size  (x: fs_states)  : nat := match x with fs_st_secret => sz end.
    Definition fs_inputs_size  (x: fs_inputs)  : nat := match x with fs_in_val    => sz end.
    Definition fs_outputs_size (x: fs_outputs) : nat := match x with fs_out_tag   => sz end.

    Definition fs_states_t := tf_states_type fs_states_size.

    Definition fs_states_init (x: fs_states) : (fs_states_t x) :=
    match x with
    | fs_st_secret => Bits.zero
    end.

    (* What the attached module is assumed to compute. Only its *type* reaches the
       generated hardware; this definition is the specification the attached module
       has to meet, and is what [externs_match] pins [sigma] to in synthesis_correct. *)
    Definition fs_mix_denote (x: bits_t sz) : bits_t sz :=
      Bits.xor (Bits.neg x) (Bits.of_nat sz 165).

    Definition fs_externs_sig : tf_externs fs_externs :=
      {| tfe_arg_size := fun f => match f with fs_mix => sz end;
         tfe_res_size := fun f => match f with fs_mix => sz end;
         (* combinational: the attached module answers in the same cycle *)
         tfe_latency  := fun f => match f with fs_mix => 0 end;
         tfe_denote   := fun f => match f with fs_mix => fs_mix_denote end |}.

    Definition fs_transitions
        (act: fs_action)
        : (@tf_ops fs_states fs_inputs fs_outputs fs_externs)
        :=
        match act with
        | fs_act_store =>
            tf_ops_base (tf_assign fs_st_secret (tf_ivar fs_in_val))
        | fs_act_tag =>
            (* the call's argument depends on the secret, so its result stays tainted *)
            tf_ops_base (tf_output fs_out_tag
              (tf_ext fs_mix (tf_op2 tf_xor (tf_svar fs_st_secret) (tf_ivar fs_in_val))))
        end.

    Definition fs_step :=
      tf_ops_run (externs := fs_externs_sig) fs_states_size fs_inputs_size fs_outputs_size.

    Section Examples.
        Definition bits_10 := Bits.of_nat sz 10.

        Definition s_init := ContextEnv.(create) fs_states_init.
        Definition o_init : ContextEnv.(env_t) (tf_outputs_type fs_outputs_size) :=
          ContextEnv.(create) (fun _ => Bits.zero).

        (* store the input into the secret *)
        Definition s1 := fs_step (fs_transitions fs_act_store) (s_init, o_init)
                           (fun x => match x with fs_in_val => bits_10 end).
        Example s1_state :
          ContextEnv.(getenv) (fst s1) fs_st_secret = bits_10.
        Proof. reflexivity. Qed.

        (* tag with input 0: the call sees the stored secret itself *)
        Definition s2 := fs_step (fs_transitions fs_act_tag) s1 (fun _ => Bits.zero).
        Example s2_output :
          ContextEnv.(getenv) (snd s2) fs_out_tag = fs_mix_denote bits_10.
        Proof. reflexivity. Qed.
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

        tfs_spec_externs := fs_externs;
        tfs_spec_externs_fin := _;
        tfs_spec_externs_sig := fs_externs_sig;

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
                        koika_module_name := "Example_ExternMix" |};

      ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn; efs_method := false |};
                  sp_prelude := None |};

      ip_verilog := {| vp_ext_fn_specs := ext_fn_specs |} |}.

End TypedSynthesis.

(* Extraction *)

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Example_ExternMix.ml" prog.
