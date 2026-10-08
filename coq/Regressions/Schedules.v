(* Six vm_compute probes over three small contexts, printing the DFG, the cost
   map, the target cycles, the buffer table and the finished schedule for
   inspection.  A probe holds when the computation terminates. *)

Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.

Require Import Trustformer.Utils.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.

Require Import Coq.Lists.List.
Import ListNotations.

Module Examples.

  Inductive dfge_s := x | y | z.
  Definition dfge_s_size (s: dfge_s) : nat := 4.

  Inductive dfge_i := in_A | in_B.
  Definition dfge_i_size (i: dfge_i) : nat := 4.

  Inductive dfge_o := out_A | out_B.
  Definition dfge_o_size (o: dfge_o) : nat := 4.

  Inductive dfge_a := action.

  Definition shd_ctx1 : TFSchedContext :=
    {|
      tfs_spec_states := dfge_s;
      tfs_spec_states_size := dfge_s_size;
      tfs_spec_states_init := fun x => Bits.zero;

      tfs_spec_inputs := dfge_i;
      tfs_spec_inputs_size := dfge_i_size;
      tfs_spec_inputs_class := fun _ => Public;
      tfs_spec_outputs := dfge_o;
      tfs_spec_outputs_size := dfge_o_size;
      tfs_spec_outputs_class := fun _ => Public;
      tfs_spec_action := dfge_a;
      tfs_spec_action_ops := fun a =>
        match a with
        | _ => {[  
            let $x := $in_A + #10;
            let $out_A := $x + #1
        ]}
        end;
      (* no attached IP *)
      tfs_spec_ips := Empty_set;
      tfs_spec_ip := no_ips;
      tfs_spec_decls := [];
    |}. 

  Goal True. 
    pose (cost := 10).
    pose (shd := shd_ctx1).
    pose (debug_dfg := build_dfg shd (action)); vm_compute in debug_dfg.
    pose (debug_cost := calc_backward_cost shd cost debug_dfg); vm_compute in debug_cost.
    pose (debug_cycle := calc_target_cycle cost debug_cost); vm_compute in debug_cycle.
    pose (debug_bufs := require_buffer shd debug_dfg debug_cycle); vm_compute in debug_bufs.
    pose (debug_sched := schedule shd cost (buffer_needs shd cost) (Taint.get_tainted shd) (Taint.decl_facts shd) (action)); vm_compute in debug_sched.
  Abort.

  Goal True. 
    pose (cost := 4).
    pose (shd := shd_ctx1).
    pose (debug_dfg := build_dfg shd (action)); vm_compute in debug_dfg.
    pose (debug_cost := calc_backward_cost shd cost debug_dfg); vm_compute in debug_cost.
    pose (debug_cycle := calc_target_cycle cost debug_cost); vm_compute in debug_cycle.
    pose (debug_bufs := require_buffer shd debug_dfg debug_cycle); vm_compute in debug_bufs.
    pose (debug_sched := schedule shd cost (buffer_needs shd cost) (Taint.get_tainted shd) (Taint.decl_facts shd) (action)); time vm_compute in debug_sched. (* TIME: 0.2 Seconds *)
  Abort.

  Definition shd_ctx2 : TFSchedContext :=
    {|
      tfs_spec_states := dfge_s;
      tfs_spec_states_size := dfge_s_size;
      tfs_spec_states_init := fun x => Bits.zero;

      tfs_spec_inputs := dfge_i;
      tfs_spec_inputs_size := dfge_i_size;
      tfs_spec_inputs_class := fun _ => Public;
      tfs_spec_outputs := dfge_o;
      tfs_spec_outputs_size := dfge_o_size;
      tfs_spec_outputs_class := fun _ => Public;
      tfs_spec_action := dfge_a;
      tfs_spec_action_ops := fun a =>
        match a with
        | _ => {[  
            let $x := $x * $x;
            (if $in_A then
              let $y := $x * $y + #1
            else
              pass
            );
            let $out_A := $y 
        ]}
        end;
      (* no attached IP *)
      tfs_spec_ips := Empty_set;
      tfs_spec_ip := no_ips;
      tfs_spec_decls := [];
    |}.

  Goal True. 
    pose (cost := 15).
    pose (shd := shd_ctx2).
    pose (debug_dfg := build_dfg shd (action)); vm_compute in debug_dfg.
    pose (debug_cost := calc_backward_cost shd cost debug_dfg); vm_compute in debug_cost.
    pose (debug_cycle := calc_target_cycle cost debug_cost); vm_compute in debug_cycle.
    pose (debug_bufs := require_buffer shd debug_dfg debug_cycle); vm_compute in debug_bufs.
    pose (debug_sched := schedule shd cost (buffer_needs shd cost) (Taint.get_tainted shd) (Taint.decl_facts shd) (action)); vm_compute in debug_sched.
  Abort.

  Goal True. 
    pose (cost := 5).
    pose (shd := shd_ctx2).
    pose (debug_dfg := build_dfg shd (action)); vm_compute in debug_dfg.
    pose (debug_cost := calc_backward_cost shd cost debug_dfg); vm_compute in debug_cost.
    pose (debug_cycle := calc_target_cycle cost debug_cost); vm_compute in debug_cycle.
    pose (debug_bufs := require_buffer shd debug_dfg debug_cycle); vm_compute in debug_bufs.
    pose (debug_sched := schedule shd cost (buffer_needs shd cost) (Taint.get_tainted shd) (Taint.decl_facts shd) (action)); time vm_compute in debug_sched.
  Abort.

  Definition no_precompute := schedule shd_ctx2 5 (buffer_needs shd_ctx2 5) (Taint.get_tainted shd_ctx2) (Taint.decl_facts shd_ctx2) (action).
  Definition with_precompute := tc_compute (schedule shd_ctx2 5 (buffer_needs shd_ctx2 5) (Taint.get_tainted shd_ctx2) (Taint.decl_facts shd_ctx2) (action)).

  Goal True.
    pose (debug1 := no_precompute).
    pose (debug2 := with_precompute).
    time vm_compute in debug1.
    time vm_compute in debug2.
  Abort.

  Definition shd_ctx3 : TFSchedContext :=
    {|
      tfs_spec_states := dfge_s;
      tfs_spec_states_size := dfge_s_size;
      tfs_spec_states_init := fun x => Bits.zero;

      tfs_spec_inputs := dfge_i;
      tfs_spec_inputs_size := dfge_i_size;
      tfs_spec_inputs_class := fun _ => Public;
      tfs_spec_outputs := dfge_o;
      tfs_spec_outputs_size := dfge_o_size;
      tfs_spec_outputs_class := fun _ => Public;
      tfs_spec_action := dfge_a;
      tfs_spec_action_ops := fun a =>
        match a with
        | _ => {[  
            let $x := $y;
            let $y := $z;
            let $z := $x
        ]}
        end;
      (* no attached IP *)
      tfs_spec_ips := Empty_set;
      tfs_spec_ip := no_ips;
      tfs_spec_decls := [];
    |}.

  Goal True. 
    pose (cost := 15).
    pose (shd := shd_ctx3).
    pose (debug_dfg := build_dfg shd (action)); vm_compute in debug_dfg.
    pose (debug_cost := calc_backward_cost shd cost debug_dfg); vm_compute in debug_cost.
    pose (debug_cycle := calc_target_cycle cost debug_cost); vm_compute in debug_cycle.
    pose (debug_bufs := require_buffer shd debug_dfg debug_cycle); vm_compute in debug_bufs.
    pose (debug_sched := schedule shd cost (buffer_needs shd cost) (Taint.get_tainted shd) (Taint.decl_facts shd) (action)); vm_compute in debug_sched.
  Abort.

End Examples.
