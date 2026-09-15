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
    SPIKE (2026-09-10): [tf_concat] end to end, in the shape MARS actually needs.

    CryptSnapshot (TCG MARS Library Spec v1r14 section 5.6.9) hashes
        regSelect(4 bytes, big endian) || REG# || ... || ctx
    so the message is built by concatenating fields of DIFFERENT widths in a
    fixed order.  That is the whole reason tf_concat exists: [tf_const] carries a
    unary [nat] and cannot express a 2^256 shift, so the "a * 2^m + b" identity
    is unusable at these widths (measured: N.of_nat is linear in the value,
    2.19 s at 2^24).

    This module builds exactly that prefix -- a 32-bit selector concatenated
    with a 256-bit register, giving 288 bits -- and carries it to Verilog.
 *)

Section FunctionalSpecification.

    Inductive fs_action := | fs_act_snap.

    Definition fs_action_encoding (a: fs_action) : bits_t 16 :=
      match a with fs_act_snap => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0 end.

    Lemma fs_action_encoding_inj :
      forall a1 a2, fs_action_encoding a1 = fs_action_encoding a2 -> a1 = a2.
    Proof. intros. destruct a1; destruct a2; reflexivity. Qed.

    Inductive fs_states := | fs_st_pcr.
    Inductive fs_inputs := | fs_in_regsel.
    Inductive fs_outputs := | fs_out_msg.

    Definition fs_states_size (x: fs_states) : nat :=
      match x with fs_st_pcr => 256 end.
    Definition fs_inputs_size (x: fs_inputs) : nat :=
      match x with fs_in_regsel => 32 end.
    (* 32 + 256: the snapshot prefix *)
    Definition fs_outputs_size (x: fs_outputs) : nat :=
      match x with fs_out_msg => 288 end.

    Definition fs_states_t := tf_states_type fs_states_size.
    Definition fs_states_init (x: fs_states) : (fs_states_t x) :=
      match x with fs_st_pcr => Bits.zero end.

    (* regSelect in the HIGH bits, PCR in the low bits -- the order the spec's
       concatenation demands, pinned by [concat_hi_first] in WideDeepProbe.v. *)
    Definition fs_transitions (act: fs_action)
        : (@tf_ops fs_states fs_inputs fs_outputs Empty_set) :=
      match act with
      | fs_act_snap =>
          tf_ops_base (tf_output fs_out_msg
            (tf_op2 (tf_concat 32 256) (tf_ivar fs_in_regsel) (tf_svar fs_st_pcr)))
      end.

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
        tfs_spec_ip_resp_secret := ltac:(intros []);
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
                        koika_module_name := "Example_ConcatSpike" |};

      ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn; efs_method := false |};
                  sp_prelude := None |};

      ip_verilog := {| vp_ext_fn_specs := ext_fn_specs |} |}.

End TypedSynthesis.

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Example_ConcatSpike.ml" prog.
