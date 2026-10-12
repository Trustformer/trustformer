Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Coq.NArith.NArith.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Backend.Lowering.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Macros.

(* The shifts, signed compare and slices, each in a range that is easy to get
   wrong: shifts by 32 or more, the sign boundary, and slices past the end. *)

Section FunctionalSpecification.

    Inductive op_action := o_lsr | o_lsl | o_asr | o_slt | o_slice | o_slice_out | o_islice.
    Inductive op_inputs := in_a | in_b.
    Inductive op_outputs := out_r | out_f.

    Definition op_inputs_size (_: op_inputs) : nat := 32.
    Definition op_outputs_size (x: op_outputs) : nat := match x with out_r => 32 | out_f => 1 end.

    Definition op_ops (a: op_action) : @tf_ops Empty_set op_inputs op_outputs Empty_set :=
      match a with
      | o_lsr => {[ `mk_clear_outputs`; let $out_r := $in_a >> $in_b ]}
      | o_lsl => {[ `mk_clear_outputs`; let $out_r := $in_a << $in_b ]}
      | o_asr => {[ `mk_clear_outputs`; let $out_r := $in_a >>> $in_b ]}
      | o_slt => {[ `mk_clear_outputs`; let $out_f := $in_a <s[32] $in_b ]}
      | o_slice =>
          {[ `mk_clear_outputs`;
             let $out_r := `mk_zext 8 32 (tf_op1 (tf_resize 8) (tf_op1 (tf_slice 32 4) (tf_ivar in_a)))` ]}
      | o_slice_out =>
          {[ `mk_clear_outputs`;
             let $out_r := `mk_zext 8 32 (tf_op1 (tf_resize 8) (tf_op1 (tf_slice 32 28) (tf_ivar in_a)))` ]}
      | o_islice =>
          {[ `mk_clear_outputs`;
             let $out_r := `mk_zext 8 32 (tf_op1 (tf_resize 8)
                              (tf_op2 (tf_islice 32) (tf_ivar in_a) (tf_op1 (tf_resize 5) (tf_ivar in_b))))` ]}
      end.

End FunctionalSpecification.

Section Instance.

    Definition tfs_ctx : TFSchedContext := {|
        tfs_spec_states := Empty_set;
        tfs_spec_states_fin := _;
        tfs_spec_states_size := fun _ => 0;
        tfs_spec_states_init := fun x => match x with end;
        tfs_spec_inputs := op_inputs;
        tfs_spec_inputs_fin := _;
        tfs_spec_inputs_size := op_inputs_size;
        tfs_spec_inputs_class := fun _ => Public;
        tfs_spec_outputs := op_outputs;
        tfs_spec_outputs_fin := _;
        tfs_spec_outputs_size := op_outputs_size;
        tfs_spec_outputs_class := fun _ => Public;
        tfs_spec_action := op_action;
        tfs_spec_action_fin := _;
        tfs_spec_action_ops := op_ops;
        tfs_spec_ips := Empty_set;
        tfs_spec_ip := no_ips;
        tfs_spec_decls := []
    |}.

    Definition tf_ctx : TFSynthContext := mk_synth_ctx (tfs_schedule tfs_ctx 10).

    Definition package := Lowering.package tf_ctx "Regression_Operators".

End Instance.

Section Checks.

    Definition run (o: op_action) (a b: N) (x: op_outputs) : N :=
      sim_out tfs_ctx (sim_step tfs_ctx o (fun i => match i with in_a => a | in_b => b end)
                         (sim_init tfs_ctx)) x.

    Example lint_clean : tf_lint tfs_ctx = [].
    Proof. vm_compute. reflexivity. Qed.

    Example shifts :
      List.map (fun ab => run o_lsr (fst ab) (snd ab) out_r) [(0xF0000000, 4); (0xF0000000, 32); (0xF0000000, 40)]%N
      = [0x0F000000; 0; 0]%N.
    Proof. vm_compute. reflexivity. Qed.
    Example shifts_left :
      List.map (fun ab => run o_lsl (fst ab) (snd ab) out_r) [(1, 31); (1, 32); (0x00FF0000, 8)]%N
      = [0x80000000; 0; 0xFF000000]%N.
    Proof. vm_compute. reflexivity. Qed.
    Example shifts_arith :
      List.map (fun ab => run o_asr (fst ab) (snd ab) out_r)
        [(0x80000000, 4); (0x80000000, 40); (0x40000000, 40); (0x40000000, 4)]%N
      = [0xF8000000; 0xFFFFFFFF; 0; 0x04000000]%N.
    Proof. vm_compute. reflexivity. Qed.

    Example signed_less :
      List.map (fun ab => run o_slt (fst ab) (snd ab) out_f)
        [(0xFFFFFFFF, 0); (0, 0xFFFFFFFF); (0x80000000, 0x7FFFFFFF); (5, 5); (3, 7)]%N
      = [1; 0; 1; 0; 1]%N.
    Proof. vm_compute. reflexivity. Qed.

    Example slices :
      (run o_slice 0x12345678 0 out_r, run o_slice_out 0xF0000000 0 out_r) = (0x67, 0x0F)%N.
    Proof. vm_compute. reflexivity. Qed.
    Example dynamic_slices :
      List.map (fun ab => run o_islice (fst ab) (snd ab) out_r)
        [(0x12345678, 8); (0x12345678, 28); (0x12345678, 31); (0x80000000, 31); (0x12345678, 40)]%N
      = [0x56; 0x01; 0; 0x01; 0x56]%N.
    Proof. vm_compute. reflexivity. Qed.

End Checks.

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Regression_Operators.ml" prog.
