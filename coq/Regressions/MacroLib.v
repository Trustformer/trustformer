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
    | a_write | a_read | a_clear | a_mod | a_mod8 | a_bits | a_const | a_const2
    | a_loop | a_concat | a_select | a_find | a_shift | a_case | a_sext | a_pset | a_pget
    | a_pset_wide | a_pget_wide | a_while.

    Inductive ml_states := st_cell (k: ml_cell) | st_acc | st_acc8 | st_pk.
    Inductive ml_inputs := in_idx | in_val.
    Inductive ml_outputs := out_val | out_ok | out_wide.

    Definition ml_states_size (x: ml_states) : nat :=
      match x with st_cell _ => 8 | st_acc => 32 | st_acc8 => 8 | st_pk => 32 end.
    Definition ml_inputs_size (x: ml_inputs) : nat :=
      match x with in_idx => 2 | in_val => 32 end.
    Definition ml_outputs_size (x: ml_outputs) : nat :=
      match x with out_val => 32 | out_ok => 1 | out_wide => 128 end.

    Definition ml_states_init (x: ml_states) : tf_states_type ml_states_size x :=
      Bits.zero.

    Local Notation E := (@tf_expr ml_states ml_inputs ml_outputs).
    Local Notation OPS := (@tf_ops ml_states ml_inputs ml_outputs Empty_set).

    Definition in_range : E := {[ $in_idx <[2] #3 ]}.
    Definition low_byte : E := mk_slice 7 0 (tf_ivar in_val).
    Definition cell_empty (k: ml_cell) : E := {[ $(st_cell k) ==[8] #0 ]}.
    Definition cell_full (k: ml_cell) : E := {[ $(st_cell k) !=[8] #0 ]}.
    Definition store_low (k: ml_cell) : OPS := tf_ops_base (tf_assign (st_cell k) low_byte).
    Definition set_out (n: nat) : OPS := tf_ops_base (tf_output out_val (tf_const n)).
    Definition wide_idx : E := mk_slice 2 0 (tf_ivar in_val).

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
      | a_loop =>
          {[ `mk_clear_outputs`;
             let $st_acc8 := #0;
             for i < 8 do let $st_acc8 := $st_acc8 + `mk_zext 1 8 (mk_bit i (tf_ivar in_val))` end;
             let $out_val := `mk_zext 8 32 (tf_svar st_acc8)`;
             let $out_ok := `mk_fold 32 (fun i acc => tf_op2 tf_xor acc (mk_bit i (tf_ivar in_val))) (tf_const 0)` ]}
      | a_concat =>
          {[ `mk_clear_outputs`;
             let $out_val := `mk_concat [(8, low_byte); (8, mk_slice 15 8 (tf_ivar in_val)); (16, tf_const 0)]` ]}
      | a_select =>
          {[ `mk_clear_outputs`;
             let $out_val :=
               `mk_zext 8 32 (mk_select 2 (tf_ivar in_idx) [tf_const 10; tf_const 20; tf_const 30] (tf_const 99))` ]}
      | a_find =>
          {[ `mk_clear_outputs`;
             `mk_first cell_empty store_low (tf_ops_base tf_nop)`;
             let $out_ok := `mk_all cell_full` ]}
      | a_shift =>
          {[ `mk_clear_outputs`; `mk_shift_down st_cell low_byte` ]}
      | a_case =>
          {[ `mk_clear_outputs`;
             `mk_case 32 (tf_ivar in_val) [(5%N, set_out 50); (0xDEADBEEF%N, set_out 1)] (set_out 7)` ]}
      | a_sext =>
          {[ `mk_clear_outputs`; let $out_val := `mk_sext 8 32 low_byte` ]}
      | a_pset =>
          {[ `mk_clear_outputs`;
             `mk_packed_set st_pk 32 8 2 (tf_ivar in_idx) (tf_ivar in_val)`;
             let $out_val := $st_pk ]}
      | a_pget =>
          {[ `mk_clear_outputs`;
             let $out_val := `mk_zext 8 32 (mk_packed_get 32 8 2 (tf_svar st_pk) (tf_ivar in_idx))` ]}
      | a_pset_wide =>
          {[ `mk_clear_outputs`;
             `mk_packed_set st_pk 32 8 3 wide_idx (mk_slice 15 8 (tf_ivar in_val))`;
             let $out_val := $st_pk ]}
      | a_pget_wide =>
          {[ `mk_clear_outputs`;
             let $out_val := `mk_zext 8 32 (mk_packed_get 32 8 3 (tf_svar st_pk) wide_idx)` ]}
      | a_while =>
          {[ `mk_clear_outputs`;
             let $st_acc := $in_val;
             let $st_acc8 := #0;
             for i < 8 while $st_acc !=[32] #0 do
               let $st_acc := $st_acc >> #1;
               let $st_acc8 := `tf_const (S i)`
             end;
             let $out_val := `mk_zext 8 32 (tf_svar st_acc8)`;
             let $out_ok := $st_acc ==[32] #0 ]}
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

    Example derived_reg_size : tf_action_reg_size tf_ctx = 5.
    Proof. reflexivity. Qed.

    Definition package := Lowering.package tf_ctx "Regression_MacroLib".

End Instance.

Section NewMacros.

    Local Open Scope N_scope.

    Definition ins (i v: N) (x: ml_inputs) : N := match x with in_idx => i | in_val => v end.
    Definition after (l: list (ml_action * N * N)) : sim_state tfs_ctx :=
      sim_steps tfs_ctx (List.map (fun c => (fst (fst c), ins (snd (fst c)) (snd c))) l) (sim_init tfs_ctx).
    Definition res (o: ml_outputs) (l: list (ml_action * N * N)) : N := sim_out tfs_ctx (after l) o.
    Definition cell_vals (l: list (ml_action * N * N)) : list N :=
      List.map (fun k => sim_reg tfs_ctx (after l) (st_cell k)) [c0; c1; c2].

    Example loop_popcount_parity :
      List.map (fun v => (res out_val [(a_loop, 0, v)], res out_ok [(a_loop, 0, v)]))
               [0xB7; 0x80000001; 0x80000003]%N
      = [(6, 0); (1, 0); (2, 1)]%N.
    Proof. vm_compute. reflexivity. Qed.

    Example while_bit_length :
      List.map (fun v => (res out_val [(a_while, 0, v)], res out_ok [(a_while, 0, v)]))
               [0; 1; 5; 0x80; 0xFF; 0x100; 0xFFFFFFFF]%N
      = [(0, 1); (1, 1); (3, 1); (8, 1); (8, 1); (8, 0); (8, 0)]%N.
    Proof. vm_compute. reflexivity. Qed.

    Example concat_swap : res out_val [(a_concat, 0, 0x1234)] = 0x34120000%N.
    Proof. vm_compute. reflexivity. Qed.

    Example select_table :
      List.map (fun i => res out_val [(a_select, i, 0)]) [0; 1; 2; 3]%N = [10; 20; 30; 99]%N.
    Proof. vm_compute. reflexivity. Qed.

    Example find_first_empty :
      (cell_vals [(a_find, 0, 0x11); (a_find, 0, 0x22)],
       res out_ok [(a_find, 0, 0x11); (a_find, 0, 0x22); (a_find, 0, 0x33)],
       cell_vals [(a_find, 0, 0x11); (a_find, 0, 0x22); (a_find, 0, 0x33); (a_find, 0, 0x44)])
      = ([0x11; 0x22; 0]%N, 1%N, [0x11; 0x22; 0x33]%N).
    Proof. vm_compute. reflexivity. Qed.

    Example shift_down :
      cell_vals [(a_write, 0, 0x11); (a_write, 1, 0x22); (a_write, 2, 0x33); (a_shift, 0, 0x144)]
      = [0x22; 0x33; 0x44]%N.
    Proof. vm_compute. reflexivity. Qed.

    Example case_arms :
      List.map (fun v => res out_val [(a_case, 0, v)]) [5; 0xDEADBEEF; 6]%N = [50; 1; 7]%N.
    Proof. vm_compute. reflexivity. Qed.

    Example sign_extend :
      List.map (fun v => res out_val [(a_sext, 0, v)]) [0x7F; 0x80; 0x1FF]%N
      = [0x7F; 0xFFFFFF80; 0xFFFFFFFF]%N.
    Proof. vm_compute. reflexivity. Qed.

    Example packed :
      (res out_val [(a_pset, 1, 0xAB)],
       res out_val [(a_pset, 1, 0xAB); (a_pset, 3, 0x1CD)],
       res out_val [(a_pset, 1, 0xAB); (a_pset, 3, 0x1CD); (a_pget, 3, 0)],
       res out_val [(a_pset, 1, 0xAB); (a_pget, 0, 0)])
      = (0x0000AB00, 0xCD00AB00, 0xCD, 0)%N.
    Proof. vm_compute. reflexivity. Qed.

    Example packed_out_of_range :
      (res out_val [(a_pset_wide, 0, 0xAB01)],
       res out_val [(a_pset_wide, 0, 0xAB01); (a_pset_wide, 0, 0xCD05)],
       List.map (fun i => res out_val [(a_pset_wide, 0, 0xAB01); (a_pset_wide, 0, 0xEF00); (a_pget_wide, 0, i)])
                [0; 1; 4; 5; 7])
      = (0x0000AB00, 0x0000AB00, [0xEF; 0xAB; 0; 0; 0]).
    Proof. vm_compute. reflexivity. Qed.

    Example ip_latency :
      (ip_lat (mk_ip 8 8 3 (fun x => x)), ip_lat (mk_ip 8 8 0 (fun x => x))) = (3, 1)%nat.
    Proof. reflexivity. Qed.

End NewMacros.

Section LintProbe.

    Definition lint_probe (explicit: bool) : @tf_ops ml_states ml_inputs ml_outputs Empty_set :=
      if explicit
      then {[ let $st_acc8 := `tf_op1 (tf_resize 8) (tf_ivar in_val)`;
              if ($in_val !=[32] #0) then pass else pass;
              let $out_val := (`mk_N 8 300` ++[8,24] `tf_op1 (tf_resize 24) (tf_ivar in_val)`) ]}
      else {[ let $st_acc8 := $in_val;
              if $in_val then pass else pass;
              let $out_val := (#300 ++[8,24] $in_val) ]}.

    Example lint_findings :
      lint_ops ml_states_size ml_inputs_size ml_outputs_size no_ips (lint_probe false)
      = [lint_assign 8 32; lint_condition 32; lint_concat 24 32; lint_const 8 300].
    Proof. vm_compute. reflexivity. Qed.

    Example lint_explicit :
      lint_ops ml_states_size ml_inputs_size ml_outputs_size no_ips (lint_probe true) = [].
    Proof. vm_compute. reflexivity. Qed.

End LintProbe.

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Regression_MacroLib.ml" prog.
