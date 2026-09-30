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

(* The cheapest module that is both WIDE (256-bit datapath) and DEEP (a low cost
   limit splits the operator chain across many buffered stages), exercising the
   buffering machinery -- [valid_settled_run], [buffers_settled_run] -- at MARS
   scale.  Every literal is small on purpose: [tf_const] carries a unary [nat]
   through [N.of_nat], 2.2 s at 2^24, which is why [tf_concat] exists. *)

Section FunctionalSpecification.

    Definition wsz := 256.

    Inductive fs_action :=
    | fs_act_mix
    .

    Definition fs_action_encoding (a: fs_action) : bits_t 16 :=
    match a with
    | fs_act_mix => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    end.

    Lemma fs_action_encoding_inj :
        forall a1 a2,
        fs_action_encoding a1 = fs_action_encoding a2 ->
        a1 = a2.
    Proof.
        intros. destruct a1; destruct a2; reflexivity.
    Qed.

    Inductive fs_states := | fs_st_acc.
    Inductive fs_inputs := | fs_in_x.
    Inductive fs_outputs := | fs_out_y.

    Definition fs_states_size (x: fs_states) : nat :=
      match x with fs_st_acc => wsz end.
    Definition fs_inputs_size (x: fs_inputs) : nat :=
      match x with fs_in_x => wsz end.
    Definition fs_outputs_size (x: fs_outputs) : nat :=
      match x with fs_out_y => wsz end.

    Definition fs_states_t := tf_states_type fs_states_size.

    Definition fs_states_init (x: fs_states) : (fs_states_t x) :=
      match x with fs_st_acc => Bits.zero end.

    (* A chain of ten 256-bit operators.  With cost_limit = 2 and
       cost_fn(xor) = 1, cost_fn(add) = 2, the backward cost of the chain is far
       above the limit, so [calc_target_cycle] must split it into many stages and
       [require_buffer] must allocate a 256-bit buffer at every boundary. *)
    Definition mix_chain : @tf_expr fs_states fs_inputs fs_outputs :=
      let x0 := tf_op2 tf_xor (tf_ivar fs_in_x) (tf_svar fs_st_acc) in
      let x1 := tf_op2 tf_add x0 (tf_const 1) in
      let x2 := tf_op2 tf_xor x1 (tf_const 255) in
      let x3 := tf_op2 tf_add x2 (tf_const 7) in
      let x4 := tf_op2 tf_xor x3 (tf_const 4095) in
      let x5 := tf_op2 tf_add x4 (tf_const 3) in
      let x6 := tf_op2 tf_xor x5 (tf_const 65535) in
      let x7 := tf_op2 tf_add x6 (tf_const 9) in
      let x8 := tf_op2 tf_xor x7 (tf_const 31) in
      tf_op2 tf_add x8 (tf_const 5).

    Definition fs_transitions (act: fs_action)
        : (@tf_ops fs_states fs_inputs fs_outputs Empty_set) :=
      match act with
      | fs_act_mix =>
          tf_ops_cons
            (tf_ops_base (tf_assign fs_st_acc mix_chain))
            (tf_ops_base (tf_output fs_out_y mix_chain))
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
        tfs_spec_decls := []
    |}.

    (* Low on purpose: this is what forces pipeline depth. *)
    Definition tf_schedule := tfs_schedule tfs_ctx 2.

    Definition tf_ctx : TFSynthContext := {|
        tf_sched_ctx := tf_schedule;
        tf_action_encoding := fs_action_encoding;
        tf_action_encoding_inj := fs_action_encoding_inj;
    |}.

  Definition package := TypedSynthesis.package tf_ctx "Example_WideDeepSpike".

End TypedSynthesis.

(* Extraction *)

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Example_WideDeepSpike.ml" prog.
