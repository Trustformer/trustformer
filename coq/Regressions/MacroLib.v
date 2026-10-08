Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Backend.Lowering.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Macros.

Section FunctionalSpecification.

    Inductive ml_cell := c0 | c1 | c2.

    Inductive ml_action :=
    | a_write | a_read | a_clear | a_mod | a_mod8 | a_bits | a_const | a_const2.

    Inductive ml_states := st_cell (k: ml_cell) | st_acc | st_acc8.
    Inductive ml_inputs := in_idx | in_val.
    Inductive ml_outputs := out_val | out_ok | out_wide.

    Definition ml_states_size (x: ml_states) : nat :=
      match x with st_cell _ => 8 | st_acc => 32 | st_acc8 => 8 end.
    Definition ml_inputs_size (x: ml_inputs) : nat :=
      match x with in_idx => 2 | in_val => 32 end.
    Definition ml_outputs_size (x: ml_outputs) : nat :=
      match x with out_val => 32 | out_ok => 1 | out_wide => 128 end.

    Definition ml_states_init (x: ml_states) : tf_states_type ml_states_size x :=
      Bits.zero.

    Local Notation E := (@tf_expr ml_states ml_inputs ml_outputs).
    Local Notation OPS := (@tf_ops ml_states ml_inputs ml_outputs Empty_set).

    Definition in_range : E := {[ $in_idx <[2] #3 ]}.

    Definition ml_ops (a: ml_action) : OPS :=
      match a with
      | a_write =>
          {[ `mk_clear_outputs`;
             `mk_arr_write 2 (tf_ivar in_idx) st_cell (tf_ivar in_val)`;
             let $out_ok := `in_range` ]}
      | a_read =>
          {[ `mk_clear_outputs`;
             let $out_val :=
               `mk_zext 8 32 (mk_arr_read 2 (tf_ivar in_idx)
                                (fun k => tf_svar (st_cell k)) (tf_const 0))`;
             let $out_ok := `in_range` ]}
      | a_clear =>
          {[ `mk_clear_outputs`;
             `mk_forall (fun k => {[ let $(st_cell k) := #0 ]})` ]}
      | a_mod =>
          {[ `mk_clear_outputs`;
             let $st_acc := $in_val;
             `mk_urem_const st_acc 32 1000000`;
             let $out_val := $st_acc ]}
      | a_mod8 =>
          {[ `mk_clear_outputs`;
             let $st_acc8 := $in_val;
             `mk_urem_const st_acc8 8 10`;
             let $out_val := `mk_zext 8 32 (tf_svar st_acc8)` ]}
      | a_bits =>
          {[ `mk_clear_outputs`;
             let $out_val := `mk_zext 16 32 (mk_slice 23 8 (tf_ivar in_val))`;
             let $out_ok := `mk_bit 31 (tf_ivar in_val)` ]}
      | a_const =>
          {[ `mk_clear_outputs`;
             let $out_val := (`mk_hex "dead_beef"%string` ^ `mk_N 32 16909060`);
             let $out_wide := `mk_hex "0123456789abcdef_fedcba9876543210"%string`;
             let $out_ok := #1 ]}
      | a_const2 =>
          {[ `mk_clear_outputs`;
             let $out_val := (`mk_rep 2 92` ++[16,16] `mk_zext 12 16 (mk_hex "abc"%string)`);
             let $out_wide := `mk_zext 20 128 (mk_N 20 703710)` ]}
      end.

End FunctionalSpecification.

Section Checks.

    Definition sysst := (ContextEnv.(env_t) (tf_states_type ml_states_size)
                         * ContextEnv.(env_t) (tf_outputs_type ml_outputs_size))%type.

    Definition initial : sysst :=
      (ContextEnv.(create) ml_states_init, ContextEnv.(create) (fun _ => Bits.zero)).

    Definition inp (idx: nat) (v: N) (x: ml_inputs) : bits_t (ml_inputs_size x) :=
      match x with
      | in_idx => Bits.of_nat 2 idx
      | in_val => Bits.of_N 32 v
      end.

    Definition run (a: ml_action) (idx: nat) (v: N) (s: sysst) : sysst :=
      tf_ops_run ml_states_size ml_inputs_size ml_outputs_size no_ips (ml_ops a) s (inp idx v).

    Definition val (s: sysst) : N := Bits.to_N (ContextEnv.(getenv) (snd s) out_val).
    Definition ok (s: sysst) : N := Bits.to_N (ContextEnv.(getenv) (snd s) out_ok).
    Definition wide (s: sysst) : N := Bits.to_N (ContextEnv.(getenv) (snd s) out_wide).
    Definition cells (s: sysst) : list N :=
      List.map (fun k => Bits.to_N (ContextEnv.(getenv) (fst s) (st_cell k))) [c0; c1; c2].

    Definition s1 := run a_write 1 0x1AB initial.
    Example write_one : cells s1 = [0; 0xAB; 0]%N.
    Proof. vm_compute. reflexivity. Qed.
    Example write_ok : ok s1 = 1%N.
    Proof. vm_compute. reflexivity. Qed.

    Definition s2 := run a_write 2 0x42 (run a_write 0 0x17 s1).
    Example write_all : cells s2 = [0x17; 0xAB; 0x42]%N.
    Proof. vm_compute. reflexivity. Qed.

    Example write_out_of_range : cells (run a_write 3 0xFF s2) = cells s2.
    Proof. vm_compute. reflexivity. Qed.
    Example write_out_of_range_flag : ok (run a_write 3 0xFF s2) = 0%N.
    Proof. vm_compute. reflexivity. Qed.

    Example read_each :
      List.map (fun i => val (run a_read i 0 s2)) [0; 1; 2; 3] = [0x17; 0xAB; 0x42; 0]%N.
    Proof. vm_compute. reflexivity. Qed.

    Example clear_after_read : val (run a_write 0 5 (run a_read 1 0 s2)) = 0%N.
    Proof. vm_compute. reflexivity. Qed.

    Example clear_all : cells (run a_clear 0 0 s2) = [0; 0; 0]%N.
    Proof. vm_compute. reflexivity. Qed.

    Example mod8_exhaustive :
      List.forallb (fun v => N.eqb (val (run a_mod8 0 (N.of_nat v) initial)) (N.of_nat v mod 10))
                   (List.seq 0 256) = true.
    Proof. vm_compute. reflexivity. Qed.

    Example mod_boundaries :
      List.map (fun v => val (run a_mod 0 v initial))
               [0; 999999; 1000000; 1000001; 123456789; 4294967295]%N
      = [0; 999999; 0; 1; 456789; 967295]%N.
    Proof. vm_compute. reflexivity. Qed.

    Example slice_mid : val (run a_bits 0 0xAABBCCDD initial) = 0xBBCC%N.
    Proof. vm_compute. reflexivity. Qed.
    Example bit_top : List.map (fun v => ok (run a_bits 0 v initial)) [0x80000000; 0x7FFFFFFF]%N
                      = [1; 0]%N.
    Proof. vm_compute. reflexivity. Qed.

    Example const_xor : val (run a_const 0 0 initial) = 0xDFAFBDEB%N.
    Proof. vm_compute. reflexivity. Qed.
    Example const_wide : wide (run a_const 0 0 initial) = 0x0123456789ABCDEFFEDCBA9876543210%N.
    Proof. vm_compute. reflexivity. Qed.
    Example const_rep_hex : val (run a_const2 0 0 initial) = 0x5C5C0ABC%N.
    Proof. vm_compute. reflexivity. Qed.
    Example const_N_top : wide (run a_const2 0 0 initial) = 0xABCDE%N.
    Proof. vm_compute. reflexivity. Qed.

End Checks.

Section Instance.

    Definition tfs_ctx : TFSchedContext := {|
        tfs_spec_states := ml_states;
        tfs_spec_states_fin := _;
        tfs_spec_states_size := ml_states_size;
        tfs_spec_states_init := ml_states_init;

        tfs_spec_inputs := ml_inputs;
        tfs_spec_inputs_fin := _;
        tfs_spec_inputs_size := ml_inputs_size;
        tfs_spec_inputs_class := fun _ => Public;
        tfs_spec_outputs := ml_outputs;
        tfs_spec_outputs_fin := _;
        tfs_spec_outputs_size := ml_outputs_size;
        tfs_spec_outputs_class := fun _ => Public;
        tfs_spec_action := ml_action;
        tfs_spec_action_fin := _;
        tfs_spec_action_ops := ml_ops;
        tfs_spec_ips := Empty_set;
        tfs_spec_ip := no_ips;
        tfs_spec_decls := []
    |}.

    Definition tf_ctx : TFSynthContext := mk_synth_ctx (tfs_schedule tfs_ctx 10).

    Example derived_reg_size : tf_action_reg_size tf_ctx = 4.
    Proof. reflexivity. Qed.

    Definition package := Lowering.package tf_ctx "Regression_MacroLib".

End Instance.

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Regression_MacroLib.ml" prog.
