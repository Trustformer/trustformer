(* ==================================================================== *)
(* Variable-scheduler simulation / correctness                          *)
(*                                                                      *)
(* One top-level SOURCE step of an action (tf_ops_run over the whole    *)
(* program) equals iterating the scheduled per-cycle transition         *)
(* (tfs_next_cycle) until the tf_dfg_done flag is set, modulo the state *)
(* mapping maps_to / maps_from.                                         *)
(*                                                                      *)
(* See agents/scheduler-simulation/PLAN.md for the campaign plan.       *)
(* ==================================================================== *)

Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.
Require Export Trustformer.Properties.SchedulerSimulationBase.

(* Split from SchedulerSimulationBase so that work on the round trip does not
   recompile 13,000 lines of builder invariants.  The shims below re-bind that
   file's discharged names at this section's [ctx] and [cost_limit]. *)
Section SchedulerSimulation.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation P_emit_expr := (SchedulerSimulationBase.P_emit_expr ctx).
  Local Notation P_emit_expr_calls := (SchedulerSimulationBase.P_emit_expr_calls ctx).
  Local Notation P_emit_expr_jst := (SchedulerSimulationBase.P_emit_expr_jst ctx).
  Local Notation P_emit_expr_samples := (SchedulerSimulationBase.P_emit_expr_samples ctx).
  Local Notation P_emit_expr_sdr := (SchedulerSimulationBase.P_emit_expr_sdr ctx).
  Local Notation P_emit_expr_sst := (SchedulerSimulationBase.P_emit_expr_sst ctx).
  Local Notation P_emit_expr_ssucc := (SchedulerSimulationBase.P_emit_expr_ssucc ctx).
  Local Notation Q_plain := (SchedulerSimulationBase.Q_plain ctx).
  Local Notation Q_plain_succ := (SchedulerSimulationBase.Q_plain_succ ctx).
  Local Notation act_idx_aligned := (SchedulerSimulationBase.act_idx_aligned ctx cost_limit).
  Local Notation all_bind_at := (SchedulerSimulationBase.all_bind_at ctx).
  Local Notation all_nodes := (SchedulerSimulationBase.all_nodes ctx).
  Local Notation all_nodes_emit := (SchedulerSimulationBase.all_nodes_emit ctx).
  Local Notation all_nodes_rev := (SchedulerSimulationBase.all_nodes_rev ctx).
  Local Notation always_ops_cons := (SchedulerSimulationBase.always_ops_cons ctx cost_limit).
  Local Notation always_ops_no_out := (SchedulerSimulationBase.always_ops_no_out ctx cost_limit).
  Local Notation always_ops_no_svar := (SchedulerSimulationBase.always_ops_no_svar ctx cost_limit).
  Local Notation arg_buffer_cycle_gt := (SchedulerSimulationBase.arg_buffer_cycle_gt ctx cost_limit).
  Local Notation arg_same_cycle_or_buffer := (SchedulerSimulationBase.arg_same_cycle_or_buffer ctx cost_limit).
  Local Notation args_lt := (SchedulerSimulationBase.args_lt ctx).
  Local Notation args_lt_fwd := (SchedulerSimulationBase.args_lt_fwd ctx cost_limit).
  Local Notation backward_cost_monotone := (SchedulerSimulationBase.backward_cost_monotone ctx cost_limit).
  Local Notation backward_cycle_monotone := (SchedulerSimulationBase.backward_cycle_monotone ctx cost_limit).
  Local Notation bind_pair := (SchedulerSimulationBase.bind_pair ctx).
  Local Notation bind_red := (SchedulerSimulationBase.bind_red ctx).
  Local Notation buf_valid_expr := (SchedulerSimulationBase.buf_valid_expr ctx cost_limit).
  Local Notation buf_value_expr := (SchedulerSimulationBase.buf_value_expr ctx cost_limit).
  Local Notation buffer_after_cycle := (SchedulerSimulationBase.buffer_after_cycle ctx cost_limit).
  Local Notation buffer_entry_at := (SchedulerSimulationBase.buffer_entry_at ctx cost_limit).
  Local Notation buffer_frozen_step := (SchedulerSimulationBase.buffer_frozen_step ctx cost_limit).
  Local Notation buffer_needs_eq := (SchedulerSimulationBase.buffer_needs_eq ctx cost_limit).
  Local Notation buffer_ops_concrete := (SchedulerSimulationBase.buffer_ops_concrete ctx cost_limit).
  Local Notation buffer_register_node_size := (SchedulerSimulationBase.buffer_register_node_size ctx cost_limit).
  Local Notation buffer_slot_eq := (SchedulerSimulationBase.buffer_slot_eq ctx cost_limit).
  Local Notation buffer_slot_of := (SchedulerSimulationBase.buffer_slot_of ctx cost_limit).
  Local Notation buffer_slot_size := (SchedulerSimulationBase.buffer_slot_size ctx cost_limit).
  Local Notation buffer_valid_gate := (SchedulerSimulationBase.buffer_valid_gate ctx cost_limit).
  Local Notation build_dfg_args_pos := (SchedulerSimulationBase.build_dfg_args_pos ctx cost_limit).
  Local Notation build_dfg_nids := (SchedulerSimulationBase.build_dfg_nids ctx cost_limit).
  Local Notation build_dfg_suffix_frozen := (SchedulerSimulationBase.build_dfg_suffix_frozen ctx cost_limit).
  Local Notation build_dfg_wf := (SchedulerSimulationBase.build_dfg_wf ctx cost_limit).
  Local Notation calc_backward_cost_fold := (SchedulerSimulationBase.calc_backward_cost_fold ctx cost_limit).
  Local Notation call_sequenced_join := (SchedulerSimulationBase.call_sequenced_join ctx cost_limit).
  Local Notation calls_main := (SchedulerSimulationBase.calls_main ctx).
  Local Notation calls_main_build_dfg := (SchedulerSimulationBase.calls_main_build_dfg ctx cost_limit).
  Local Notation calls_main_rev := (SchedulerSimulationBase.calls_main_rev ctx).
  Local Notation calls_sequenced := (SchedulerSimulationBase.calls_sequenced ctx).
  Local Notation calls_sequenced_cons_join := (SchedulerSimulationBase.calls_sequenced_cons_join ctx).
  Local Notation calls_sequenced_cons_sample := (SchedulerSimulationBase.calls_sequenced_cons_sample ctx).
  Local Notation calls_sequenced_head := (SchedulerSimulationBase.calls_sequenced_head ctx).
  Local Notation chain_gate_is_join := (SchedulerSimulationBase.chain_gate_is_join ctx cost_limit).
  Local Notation chain_gate_some := (SchedulerSimulationBase.chain_gate_some ctx cost_limit).
  Local Notation combine_valid_eval := (SchedulerSimulationBase.combine_valid_eval ctx cost_limit).
  Local Notation compile_buffered_valid := (SchedulerSimulationBase.compile_buffered_valid ctx cost_limit).
  Local Notation compile_buffered_value := (SchedulerSimulationBase.compile_buffered_value ctx cost_limit).
  Local Notation compile_dfg_buffers_entry := (SchedulerSimulationBase.compile_dfg_buffers_entry ctx cost_limit).
  Local Notation compile_dfg_buffers_no_out := (SchedulerSimulationBase.compile_dfg_buffers_no_out ctx cost_limit).
  Local Notation compile_dfg_buffers_no_svar := (SchedulerSimulationBase.compile_dfg_buffers_no_svar ctx cost_limit).
  Local Notation compile_dfg_drives_entry := (SchedulerSimulationBase.compile_dfg_drives_entry ctx cost_limit).
  Local Notation compile_dfg_drives_no_out := (SchedulerSimulationBase.compile_dfg_drives_no_out ctx cost_limit).
  Local Notation compile_dfg_drives_no_svar := (SchedulerSimulationBase.compile_dfg_drives_no_svar ctx cost_limit).
  Local Notation compile_drive_valid := (SchedulerSimulationBase.compile_drive_valid ctx cost_limit).
  Local Notation compile_fst_phi := (SchedulerSimulationBase.compile_fst_phi ctx cost_limit).
  Local Notation compile_fst_phi_gen := (SchedulerSimulationBase.compile_fst_phi_gen ctx cost_limit).
  Local Notation compile_fst_pi_irrel := (SchedulerSimulationBase.compile_fst_pi_irrel ctx cost_limit).
  Local Notation compile_fuel_irrel := (SchedulerSimulationBase.compile_fuel_irrel ctx cost_limit).
  Local Notation compile_fuel_irrel_gen := (SchedulerSimulationBase.compile_fuel_irrel_gen ctx cost_limit).
  Local Notation compile_join_valid := (SchedulerSimulationBase.compile_join_valid ctx cost_limit).
  Local Notation compile_nobuf_state_indep := (SchedulerSimulationBase.compile_nobuf_state_indep ctx cost_limit).
  Local Notation compile_nobuf_state_indep_gen := (SchedulerSimulationBase.compile_nobuf_state_indep_gen ctx cost_limit).
  Local Notation compile_nobuf_step_stable := (SchedulerSimulationBase.compile_nobuf_step_stable ctx cost_limit).
  Local Notation compile_sample_valid := (SchedulerSimulationBase.compile_sample_valid ctx cost_limit).
  Local Notation compile_stall_valid := (SchedulerSimulationBase.compile_stall_valid ctx cost_limit).
  Local Notation compile_stall_value := (SchedulerSimulationBase.compile_stall_value ctx cost_limit).
  Local Notation compile_subst_ref_valid_gen := (SchedulerSimulationBase.compile_subst_ref_valid_gen ctx cost_limit).
  Local Notation compile_subst_valid := (SchedulerSimulationBase.compile_subst_valid ctx cost_limit).
  Local Notation compile_subst_valid_gen := (SchedulerSimulationBase.compile_subst_valid_gen ctx cost_limit).
  Local Notation compile_valid_ones := (SchedulerSimulationBase.compile_valid_ones ctx cost_limit).
  Local Notation compile_valid_ones_gen := (SchedulerSimulationBase.compile_valid_ones_gen ctx cost_limit).
  Local Notation compile_valid_path_mono := (SchedulerSimulationBase.compile_valid_path_mono ctx cost_limit).
  Local Notation compile_valid_state_indep_gen := (SchedulerSimulationBase.compile_valid_state_indep_gen ctx cost_limit).
  Local Notation cost_frozen_fold := (SchedulerSimulationBase.cost_frozen_fold ctx cost_limit).
  Local Notation cost_ge_after_fold := (SchedulerSimulationBase.cost_ge_after_fold ctx cost_limit).
  Local Notation cost_mono_fold := (SchedulerSimulationBase.cost_mono_fold ctx cost_limit).
  Local Notation covers := (SchedulerSimulationBase.covers ctx).
  Local Notation covers_cons := (SchedulerSimulationBase.covers_cons ctx).
  Local Notation covers_mono := (SchedulerSimulationBase.covers_mono ctx).
  Local Notation cycle_done_val := (SchedulerSimulationBase.cycle_done_val ctx cost_limit).
  Local Notation cycle_updates := (SchedulerSimulationBase.cycle_updates ctx cost_limit).
  Local Notation cycle_updates_done := (SchedulerSimulationBase.cycle_updates_done ctx cost_limit).
  Local Notation cycle_updates_not_done := (SchedulerSimulationBase.cycle_updates_not_done ctx cost_limit).
  Local Notation dataflow_expr_all := (SchedulerSimulationBase.dataflow_expr_all ctx).
  Local Notation dataflow_expr_fg := (SchedulerSimulationBase.dataflow_expr_fg ctx).
  Local Notation dataflow_expr_full := (SchedulerSimulationBase.dataflow_expr_full ctx).
  Local Notation dataflow_expr_g := (SchedulerSimulationBase.dataflow_expr_g ctx).
  Local Notation dataflow_expr_grows := (SchedulerSimulationBase.dataflow_expr_grows ctx).
  Local Notation dataflow_expr_joins := (SchedulerSimulationBase.dataflow_expr_joins ctx).
  Local Notation dataflow_expr_pos := (SchedulerSimulationBase.dataflow_expr_pos ctx).
  Local Notation dataflow_expr_spec := (SchedulerSimulationBase.dataflow_expr_spec ctx).
  Local Notation dataflow_expr_sz := (SchedulerSimulationBase.dataflow_expr_sz ctx).
  Local Notation dataflow_ops_calls := (SchedulerSimulationBase.dataflow_ops_calls ctx).
  Local Notation dataflow_ops_fg := (SchedulerSimulationBase.dataflow_ops_fg ctx).
  Local Notation dataflow_ops_full := (SchedulerSimulationBase.dataflow_ops_full ctx).
  Local Notation dataflow_ops_joins := (SchedulerSimulationBase.dataflow_ops_joins ctx).
  Local Notation dataflow_ops_jst := (SchedulerSimulationBase.dataflow_ops_jst ctx).
  Local Notation dataflow_ops_pos := (SchedulerSimulationBase.dataflow_ops_pos ctx).
  Local Notation dataflow_ops_preserves_vmg := (SchedulerSimulationBase.dataflow_ops_preserves_vmg ctx).
  Local Notation dataflow_ops_sdr := (SchedulerSimulationBase.dataflow_ops_sdr ctx).
  Local Notation dataflow_ops_spec := (SchedulerSimulationBase.dataflow_ops_spec ctx).
  Local Notation dataflow_ops_sst := (SchedulerSimulationBase.dataflow_ops_sst ctx).
  Local Notation dataflow_ops_ssucc := (SchedulerSimulationBase.dataflow_ops_ssucc ctx).
  Local Notation dataflow_ops_succ := (SchedulerSimulationBase.dataflow_ops_succ ctx).
  Local Notation dataflow_var_fg := (SchedulerSimulationBase.dataflow_var_fg ctx).
  Local Notation dataflow_var_sz := (SchedulerSimulationBase.dataflow_var_sz ctx).
  Local Notation done_by_settle_bound := (SchedulerSimulationBase.done_by_settle_bound ctx cost_limit).
  Local Notation done_exprs_concrete := (SchedulerSimulationBase.done_exprs_concrete ctx cost_limit).
  Local Notation done_ops_no_done := (SchedulerSimulationBase.done_ops_no_done ctx cost_limit).
  Local Notation done_ops_no_dup := (SchedulerSimulationBase.done_ops_no_dup ctx cost_limit).
  Local Notation done_set := (SchedulerSimulationBase.done_set ctx cost_limit).
  Local Notation done_set_dec := (SchedulerSimulationBase.done_set_dec ctx cost_limit).
  Local Notation done_val_eval := (SchedulerSimulationBase.done_val_eval ctx cost_limit).
  Local Notation drive_after_cycle := (SchedulerSimulationBase.drive_after_cycle ctx cost_limit).
  Local Notation drive_after_sample := (SchedulerSimulationBase.drive_after_sample ctx cost_limit).
  Local Notation drive_at := (SchedulerSimulationBase.drive_at ctx).
  Local Notation drive_at_mono := (SchedulerSimulationBase.drive_at_mono ctx).
  Local Notation drive_nodes_complete := (SchedulerSimulationBase.drive_nodes_complete ctx cost_limit).
  Local Notation drive_nodes_desc := (SchedulerSimulationBase.drive_nodes_desc ctx cost_limit).
  Local Notation drive_nodes_spec := (SchedulerSimulationBase.drive_nodes_spec ctx cost_limit).
  Local Notation drive_nodes_split := (SchedulerSimulationBase.drive_nodes_split ctx cost_limit).
  Local Notation drive_payload := (SchedulerSimulationBase.drive_payload ctx cost_limit).
  Local Notation drive_payload_eval := (SchedulerSimulationBase.drive_payload_eval ctx cost_limit).
  Local Notation drive_payload_expr := (SchedulerSimulationBase.drive_payload_expr ctx cost_limit).
  Local Notation drive_payload_expr_hold := (SchedulerSimulationBase.drive_payload_expr_hold ctx cost_limit).
  Local Notation drive_payload_hold := (SchedulerSimulationBase.drive_payload_hold ctx cost_limit).
  Local Notation drive_payload_slice := (SchedulerSimulationBase.drive_payload_slice ctx cost_limit).
  Local Notation drive_payload_take := (SchedulerSimulationBase.drive_payload_take ctx cost_limit).
  Local Notation drive_payload_take_later := (SchedulerSimulationBase.drive_payload_take_later ctx cost_limit).
  Local Notation drive_pulse := (SchedulerSimulationBase.drive_pulse ctx cost_limit).
  Local Notation drive_pulse_excl := (SchedulerSimulationBase.drive_pulse_excl ctx cost_limit).
  Local Notation drive_pulse_zero_of_counter := (SchedulerSimulationBase.drive_pulse_zero_of_counter ctx cost_limit).
  Local Notation drive_pulse_zero_of_en := (SchedulerSimulationBase.drive_pulse_zero_of_en ctx cost_limit).
  Local Notation drive_pulse_zero_of_gate_reg := (SchedulerSimulationBase.drive_pulse_zero_of_gate_reg ctx cost_limit).
  Local Notation drive_pulse_zero_of_join := (SchedulerSimulationBase.drive_pulse_zero_of_join ctx cost_limit).
  Local Notation drive_pulse_zero_of_vfirst := (SchedulerSimulationBase.drive_pulse_zero_of_vfirst ctx cost_limit).
  Local Notation drive_pulse_zero_of_vgate := (SchedulerSimulationBase.drive_pulse_zero_of_vgate ctx cost_limit).
  Local Notation drive_sbufs := (SchedulerSimulationBase.drive_sbufs ctx cost_limit).
  Local Notation drive_strobe_expr := (SchedulerSimulationBase.drive_strobe_expr ctx cost_limit).
  Local Notation drive_value_expr := (SchedulerSimulationBase.drive_value_expr ctx cost_limit).
  Local Notation drive_value_expr_split := (SchedulerSimulationBase.drive_value_expr_split ctx cost_limit).
  Local Notation drive_vfirst := (SchedulerSimulationBase.drive_vfirst ctx cost_limit).
  Local Notation emit_eq := (SchedulerSimulationBase.emit_eq ctx).
  Local Notation emit_eval := (SchedulerSimulationBase.emit_eval ctx).
  Local Notation emit_fg := (SchedulerSimulationBase.emit_fg ctx).
  Local Notation emit_fspec := (SchedulerSimulationBase.emit_fspec ctx).
  Local Notation emit_full := (SchedulerSimulationBase.emit_full ctx).
  Local Notation emit_gmono := (SchedulerSimulationBase.emit_gmono ctx).
  Local Notation emit_pos := (SchedulerSimulationBase.emit_pos ctx).
  Local Notation emit_red := (SchedulerSimulationBase.emit_red ctx).
  Local Notation emit_spec := (SchedulerSimulationBase.emit_spec ctx).
  Local Notation emit_sz := (SchedulerSimulationBase.emit_sz ctx).
  Local Notation emit_var_node_at := (SchedulerSimulationBase.emit_var_node_at ctx cost_limit).
  Local Notation emit_vm := (SchedulerSimulationBase.emit_vm ctx).
  Local Notation emitted_node_at := (SchedulerSimulationBase.emitted_node_at ctx cost_limit).
  Local Notation ensure_var_eq := (SchedulerSimulationBase.ensure_var_eq ctx).
  Local Notation ensure_var_fg := (SchedulerSimulationBase.ensure_var_fg ctx).
  Local Notation ensure_var_full := (SchedulerSimulationBase.ensure_var_full ctx).
  Local Notation ensure_var_gmono := (SchedulerSimulationBase.ensure_var_gmono ctx).
  Local Notation ensure_var_graph := (SchedulerSimulationBase.ensure_var_graph ctx).
  Local Notation ensure_var_node_at := (SchedulerSimulationBase.ensure_var_node_at ctx cost_limit).
  Local Notation ensure_var_pos := (SchedulerSimulationBase.ensure_var_pos ctx).
  Local Notation ensure_var_spec := (SchedulerSimulationBase.ensure_var_spec ctx).
  Local Notation ensure_var_sz := (SchedulerSimulationBase.ensure_var_sz ctx).
  Local Notation ensure_var_vm_head := (SchedulerSimulationBase.ensure_var_vm_head ctx).
  Local Notation ensure_var_vm_inv := (SchedulerSimulationBase.ensure_var_vm_inv ctx).
  Local Notation ensure_var_vm_keep := (SchedulerSimulationBase.ensure_var_vm_keep ctx).
  Local Notation ensure_var_vmap := (SchedulerSimulationBase.ensure_var_vmap ctx).
  Local Notation espec := (SchedulerSimulationBase.espec ctx).
  Local Notation espec_ospec := (SchedulerSimulationBase.espec_ospec ctx).
  Local Notation espec_trans := (SchedulerSimulationBase.espec_trans ctx).
  Local Notation eval1_const1 := (SchedulerSimulationBase.eval1_const1 ctx cost_limit).
  Local Notation eval1_svar_v := (SchedulerSimulationBase.eval1_svar_v ctx cost_limit).
  Local Notation eval_convert_ivar := (SchedulerSimulationBase.eval_convert_ivar ctx cost_limit).
  Local Notation eval_convert_ovar := (SchedulerSimulationBase.eval_convert_ovar ctx cost_limit).
  Local Notation eval_convert_svar := (SchedulerSimulationBase.eval_convert_svar ctx cost_limit).
  Local Notation eval_pulse_fold_hold := (SchedulerSimulationBase.eval_pulse_fold_hold ctx cost_limit).
  Local Notation eval_pulse_fold_take := (SchedulerSimulationBase.eval_pulse_fold_take ctx cost_limit).
  Local Notation eval_stall_start_zero := (SchedulerSimulationBase.eval_stall_start_zero ctx cost_limit).
  Local Notation eval_svar_same := (SchedulerSimulationBase.eval_svar_same ctx cost_limit).
  Local Notation exists_act_idx := (SchedulerSimulationBase.exists_act_idx ctx cost_limit).
  Local Notation exports := (SchedulerSimulationBase.exports ctx cost_limit).
  Local Notation final_ops_concrete := (SchedulerSimulationBase.final_ops_concrete ctx cost_limit).
  Local Notation final_ops_no_ovar := (SchedulerSimulationBase.final_ops_no_ovar ctx cost_limit).
  Local Notation final_ops_no_svar := (SchedulerSimulationBase.final_ops_no_svar ctx cost_limit).
  Local Notation final_ops_ovar_in := (SchedulerSimulationBase.final_ops_ovar_in ctx cost_limit).
  Local Notation final_ops_svar_in := (SchedulerSimulationBase.final_ops_svar_in ctx cost_limit).
  Local Notation find_ge_desc := (SchedulerSimulationBase.find_ge_desc ctx).
  Local Notation find_out_update_app_None := (SchedulerSimulationBase.find_out_update_app_None ctx cost_limit).
  Local Notation find_out_update_app_r_None := (SchedulerSimulationBase.find_out_update_app_r_None ctx cost_limit).
  Local Notation find_out_update_not_in := (SchedulerSimulationBase.find_out_update_not_in ctx cost_limit).
  Local Notation find_out_update_not_in_raw := (SchedulerSimulationBase.find_out_update_not_in_raw ctx cost_limit).
  Local Notation find_out_update_output_head := (SchedulerSimulationBase.find_out_update_output_head ctx cost_limit).
  Local Notation find_out_update_skip_cons := (SchedulerSimulationBase.find_out_update_skip_cons ctx cost_limit).
  Local Notation find_out_update_skip_head := (SchedulerSimulationBase.find_out_update_skip_head ctx cost_limit).
  Local Notation find_out_update_unique_output := (SchedulerSimulationBase.find_out_update_unique_output ctx cost_limit).
  Local Notation find_st_update_app_r_None := (SchedulerSimulationBase.find_st_update_app_r_None ctx cost_limit).
  Local Notation find_st_update_assign_head := (SchedulerSimulationBase.find_st_update_assign_head ctx cost_limit).
  Local Notation find_st_update_map_init := (SchedulerSimulationBase.find_st_update_map_init ctx cost_limit).
  Local Notation find_st_update_not_in := (SchedulerSimulationBase.find_st_update_not_in ctx cost_limit).
  Local Notation find_st_update_not_in_raw := (SchedulerSimulationBase.find_st_update_not_in_raw ctx cost_limit).
  Local Notation find_st_update_skip_cons := (SchedulerSimulationBase.find_st_update_skip_cons ctx cost_limit).
  Local Notation find_st_update_skip_head := (SchedulerSimulationBase.find_st_update_skip_head ctx cost_limit).
  Local Notation find_st_update_unique_assign := (SchedulerSimulationBase.find_st_update_unique_assign ctx cost_limit).
  Local Notation fold_valid_and_ext := (SchedulerSimulationBase.fold_valid_and_ext ctx cost_limit).
  Local Notation fold_valid_and_ones := (SchedulerSimulationBase.fold_valid_and_ones ctx cost_limit).
  Local Notation fspec := (SchedulerSimulationBase.fspec ctx).
  Local Notation fspec_seq := (SchedulerSimulationBase.fspec_seq ctx).
  Local Notation g_bind_at := (SchedulerSimulationBase.g_bind_at ctx).
  Local Notation get_state_red := (SchedulerSimulationBase.get_state_red ctx).
  Local Notation get_var_cases := (SchedulerSimulationBase.get_var_cases ctx).
  Local Notation get_var_fg := (SchedulerSimulationBase.get_var_fg ctx).
  Local Notation get_var_fspec := (SchedulerSimulationBase.get_var_fspec ctx).
  Local Notation get_var_full := (SchedulerSimulationBase.get_var_full ctx).
  Local Notation get_var_pos := (SchedulerSimulationBase.get_var_pos ctx).
  Local Notation get_var_spec := (SchedulerSimulationBase.get_var_spec ctx).
  Local Notation get_var_sz := (SchedulerSimulationBase.get_var_sz ctx).
  Local Notation getenv_maps_from := (SchedulerSimulationBase.getenv_maps_from ctx cost_limit).
  Local Notation gmono := (SchedulerSimulationBase.gmono ctx).
  Local Notation gmono_refl := (SchedulerSimulationBase.gmono_refl ctx).
  Local Notation gmono_trans := (SchedulerSimulationBase.gmono_trans ctx).
  Local Notation gne_gmono := (SchedulerSimulationBase.gne_gmono ctx).
  Local Notation gpos := (SchedulerSimulationBase.gpos ctx).
  Local Notation graph_nid_has_cost := (SchedulerSimulationBase.graph_nid_has_cost ctx cost_limit).
  Local Notation graph_position_has_target_cycle := (SchedulerSimulationBase.graph_position_has_target_cycle ctx cost_limit).
  Local Notation grows := (SchedulerSimulationBase.grows ctx).
  Local Notation grows_bind := (SchedulerSimulationBase.grows_bind ctx).
  Local Notation grows_emit := (SchedulerSimulationBase.grows_emit ctx).
  Local Notation grows_get_var := (SchedulerSimulationBase.grows_get_var ctx).
  Local Notation grows_ret := (SchedulerSimulationBase.grows_ret ctx).
  Local Notation gsi_entry_at := (SchedulerSimulationBase.gsi_entry_at ctx).
  Local Notation gsi_idx_at := (SchedulerSimulationBase.gsi_idx_at ctx).
  Local Notation gsi_idx_bound := (SchedulerSimulationBase.gsi_idx_bound ctx).
  Local Notation gsi_length := (SchedulerSimulationBase.gsi_length ctx).
  Local Notation gsi_map_fst := (SchedulerSimulationBase.gsi_map_fst ctx).
  Local Notation gsi_size := (SchedulerSimulationBase.gsi_size ctx).
  Local Notation guard_expr_fold := (SchedulerSimulationBase.guard_expr_fold ctx cost_limit).
  Local Notation guard_expr_zero := (SchedulerSimulationBase.guard_expr_zero ctx cost_limit).
  Local Notation guard_lit := (SchedulerSimulationBase.guard_lit ctx cost_limit).
  Local Notation guards_disjoint_excl := (SchedulerSimulationBase.guards_disjoint_excl ctx cost_limit).
  Local Notation head_drives := (SchedulerSimulationBase.head_drives ctx).
  Local Notation head_drives_cons := (SchedulerSimulationBase.head_drives_cons ctx).
  Local Notation head_drives_emit := (SchedulerSimulationBase.head_drives_emit ctx).
  Local Notation head_drives_mono := (SchedulerSimulationBase.head_drives_mono ctx).
  Local Notation ids_desc := (SchedulerSimulationBase.ids_desc ctx).
  Local Notation ids_desc_cons := (SchedulerSimulationBase.ids_desc_cons ctx).
  Local Notation ids_desc_hd := (SchedulerSimulationBase.ids_desc_hd ctx).
  Local Notation ids_desc_tl := (SchedulerSimulationBase.ids_desc_tl ctx).
  Local Notation in_graph_fwd := (SchedulerSimulationBase.in_graph_fwd ctx cost_limit).
  Local Notation in_var_node_at := (SchedulerSimulationBase.in_var_node_at ctx cost_limit).
  Local Notation is_sample_of := (SchedulerSimulationBase.is_sample_of ctx cost_limit).
  Local Notation join_gate_zero_of_arg := (SchedulerSimulationBase.join_gate_zero_of_arg ctx cost_limit).
  Local Notation join_has_stall := (SchedulerSimulationBase.join_has_stall ctx cost_limit).
  Local Notation join_kind := (SchedulerSimulationBase.join_kind ctx).
  Local Notation join_nid_succ := (SchedulerSimulationBase.join_nid_succ ctx cost_limit).
  Local Notation join_pendings_calls := (SchedulerSimulationBase.join_pendings_calls ctx).
  Local Notation join_pendings_espec := (SchedulerSimulationBase.join_pendings_espec ctx).
  Local Notation join_pendings_fg := (SchedulerSimulationBase.join_pendings_fg ctx).
  Local Notation join_pendings_full := (SchedulerSimulationBase.join_pendings_full ctx).
  Local Notation join_pendings_g := (SchedulerSimulationBase.join_pendings_g ctx).
  Local Notation join_pendings_grows := (SchedulerSimulationBase.join_pendings_grows ctx).
  Local Notation join_pendings_js := (SchedulerSimulationBase.join_pendings_js ctx).
  Local Notation join_pendings_jst := (SchedulerSimulationBase.join_pendings_jst ctx).
  Local Notation join_pendings_leaves := (SchedulerSimulationBase.join_pendings_leaves ctx).
  Local Notation join_pendings_none := (SchedulerSimulationBase.join_pendings_none ctx).
  Local Notation join_pendings_pos := (SchedulerSimulationBase.join_pendings_pos ctx).
  Local Notation join_pendings_samples := (SchedulerSimulationBase.join_pendings_samples ctx).
  Local Notation join_pendings_succ := (SchedulerSimulationBase.join_pendings_succ ctx).
  Local Notation join_pendings_vm_eq := (SchedulerSimulationBase.join_pendings_vm_eq ctx).
  Local Notation join_waits_on_sample := (SchedulerSimulationBase.join_waits_on_sample ctx cost_limit).
  Local Notation joins_sequence := (SchedulerSimulationBase.joins_sequence ctx).
  Local Notation joins_sequence_build_dfg := (SchedulerSimulationBase.joins_sequence_build_dfg ctx cost_limit).
  Local Notation joins_sequence_cons := (SchedulerSimulationBase.joins_sequence_cons ctx).
  Local Notation joins_sequence_emit_comb := (SchedulerSimulationBase.joins_sequence_emit_comb ctx).
  Local Notation joins_sequence_emit_order := (SchedulerSimulationBase.joins_sequence_emit_order ctx).
  Local Notation joins_sequence_emit_other := (SchedulerSimulationBase.joins_sequence_emit_other ctx).
  Local Notation joins_sequence_graph_eq := (SchedulerSimulationBase.joins_sequence_graph_eq ctx).
  Local Notation joins_sequence_rev := (SchedulerSimulationBase.joins_sequence_rev ctx).
  Local Notation joins_stalled := (SchedulerSimulationBase.joins_stalled ctx).
  Local Notation joins_stalled_build_dfg := (SchedulerSimulationBase.joins_stalled_build_dfg ctx cost_limit).
  Local Notation joins_stalled_cons_nonjoin := (SchedulerSimulationBase.joins_stalled_cons_nonjoin ctx).
  Local Notation joins_stalled_rev := (SchedulerSimulationBase.joins_stalled_rev ctx).
  Local Notation js_bind_at := (SchedulerSimulationBase.js_bind_at ctx).
  Local Notation js_call_head := (SchedulerSimulationBase.js_call_head ctx).
  Local Notation jst_node := (SchedulerSimulationBase.jst_node ctx).
  Local Notation jst_node_cons := (SchedulerSimulationBase.jst_node_cons ctx).
  Local Notation jst_node_mono := (SchedulerSimulationBase.jst_node_mono ctx).
  Local Notation last_sample_found := (SchedulerSimulationBase.last_sample_found ctx).
  Local Notation last_sample_max := (SchedulerSimulationBase.last_sample_max ctx).
  Local Notation last_sample_nidwf := (SchedulerSimulationBase.last_sample_nidwf ctx).
  Local Notation last_sample_pos := (SchedulerSimulationBase.last_sample_pos ctx).
  Local Notation last_sample_spec := (SchedulerSimulationBase.last_sample_spec ctx).
  Local Notation later_drive_gate := (SchedulerSimulationBase.later_drive_gate ctx cost_limit).
  Local Notation later_drive_gate_full := (SchedulerSimulationBase.later_drive_gate_full ctx cost_limit).
  Local Notation max_cycle := (SchedulerSimulationBase.max_cycle ctx cost_limit).
  Local Notation merge_key_basic := (SchedulerSimulationBase.merge_key_basic ctx).
  Local Notation merge_key_fg := (SchedulerSimulationBase.merge_key_fg ctx).
  Local Notation merge_key_full := (SchedulerSimulationBase.merge_key_full ctx).
  Local Notation merge_key_pos := (SchedulerSimulationBase.merge_key_pos ctx).
  Local Notation merge_key_spec := (SchedulerSimulationBase.merge_key_spec ctx).
  Local Notation merge_loop_cover := (SchedulerSimulationBase.merge_loop_cover ctx).
  Local Notation merge_loop_fg := (SchedulerSimulationBase.merge_loop_fg ctx).
  Local Notation merge_loop_full := (SchedulerSimulationBase.merge_loop_full ctx).
  Local Notation merge_loop_gmono := (SchedulerSimulationBase.merge_loop_gmono ctx).
  Local Notation merge_loop_pos := (SchedulerSimulationBase.merge_loop_pos ctx).
  Local Notation merge_loop_spec := (SchedulerSimulationBase.merge_loop_spec ctx).
  Local Notation merge_maps_fg := (SchedulerSimulationBase.merge_maps_fg ctx).
  Local Notation merge_maps_full := (SchedulerSimulationBase.merge_maps_full ctx).
  Local Notation merge_maps_pos := (SchedulerSimulationBase.merge_maps_pos ctx).
  Local Notation merge_maps_spec := (SchedulerSimulationBase.merge_maps_spec ctx).
  Local Notation nid_seq := (SchedulerSimulationBase.nid_seq ctx).
  Local Notation nid_seq_bound := (SchedulerSimulationBase.nid_seq_bound ctx).
  Local Notation nid_seq_ids_desc := (SchedulerSimulationBase.nid_seq_ids_desc ctx).
  Local Notation nids_bounded := (SchedulerSimulationBase.nids_bounded ctx).
  Local Notation nids_bounded_cons := (SchedulerSimulationBase.nids_bounded_cons ctx).
  Local Notation nidwf := (SchedulerSimulationBase.nidwf ctx).
  Local Notation nidwf_gmono := (SchedulerSimulationBase.nidwf_gmono ctx).
  Local Notation no_stall_on_joined := (SchedulerSimulationBase.no_stall_on_joined ctx cost_limit).
  Local Notation node_args_range := (SchedulerSimulationBase.node_args_range ctx cost_limit).
  Local Notation node_args_sz := (SchedulerSimulationBase.node_args_sz ctx).
  Local Notation node_args_sz_gmono := (SchedulerSimulationBase.node_args_sz_gmono ctx).
  Local Notation node_at_nid := (SchedulerSimulationBase.node_at_nid ctx cost_limit).
  Local Notation node_cycle := (SchedulerSimulationBase.node_cycle ctx cost_limit).
  Local Notation node_cycle_is_div := (SchedulerSimulationBase.node_cycle_is_div ctx cost_limit).
  Local Notation node_cycle_le_max_cycle := (SchedulerSimulationBase.node_cycle_le_max_cycle ctx cost_limit).
  Local Notation node_nid_at := (SchedulerSimulationBase.node_nid_at ctx cost_limit).
  Local Notation node_op := (SchedulerSimulationBase.node_op ctx cost_limit).
  Local Notation node_op_not_empty := (SchedulerSimulationBase.node_op_not_empty ctx cost_limit).
  Local Notation node_op_range := (SchedulerSimulationBase.node_op_range ctx cost_limit).
  Local Notation node_rank := (SchedulerSimulationBase.node_rank ctx cost_limit).
  Local Notation node_rank_child := (SchedulerSimulationBase.node_rank_child ctx cost_limit).
  Local Notation node_rank_le := (SchedulerSimulationBase.node_rank_le ctx cost_limit).
  Local Notation node_rank_mono := (SchedulerSimulationBase.node_rank_mono ctx cost_limit).
  Local Notation node_rank_mono_le := (SchedulerSimulationBase.node_rank_mono_le ctx cost_limit).
  Local Notation node_rank_stall := (SchedulerSimulationBase.node_rank_stall ctx cost_limit).
  Local Notation node_ref_expr := (SchedulerSimulationBase.node_ref_expr ctx cost_limit).
  Local Notation node_ref_valid := (SchedulerSimulationBase.node_ref_valid ctx cost_limit).
  Local Notation not_sample_not_in_sample_bufs := (SchedulerSimulationBase.not_sample_not_in_sample_bufs ctx cost_limit).
  Local Notation nre_binary := (SchedulerSimulationBase.nre_binary ctx cost_limit).
  Local Notation nre_const := (SchedulerSimulationBase.nre_const ctx cost_limit).
  Local Notation nre_drive := (SchedulerSimulationBase.nre_drive ctx cost_limit).
  Local Notation nre_fuel := (SchedulerSimulationBase.nre_fuel ctx cost_limit).
  Local Notation nre_input := (SchedulerSimulationBase.nre_input ctx cost_limit).
  Local Notation nre_ovar := (SchedulerSimulationBase.nre_ovar ctx cost_limit).
  Local Notation nre_phi := (SchedulerSimulationBase.nre_phi ctx cost_limit).
  Local Notation nre_resize := (SchedulerSimulationBase.nre_resize ctx cost_limit).
  Local Notation nre_sample := (SchedulerSimulationBase.nre_sample ctx cost_limit).
  Local Notation nre_stall := (SchedulerSimulationBase.nre_stall ctx cost_limit).
  Local Notation nre_svar := (SchedulerSimulationBase.nre_svar ctx cost_limit).
  Local Notation nre_unary := (SchedulerSimulationBase.nre_unary ctx cost_limit).
  Local Notation nre_unfold := (SchedulerSimulationBase.nre_unfold ctx cost_limit).
  Local Notation nval := (SchedulerSimulationBase.nval ctx cost_limit).
  Local Notation nval_fresh_ovar := (SchedulerSimulationBase.nval_fresh_ovar ctx cost_limit).
  Local Notation nval_fresh_svar := (SchedulerSimulationBase.nval_fresh_svar ctx cost_limit).
  Local Notation nval_var_ovar := (SchedulerSimulationBase.nval_var_ovar ctx cost_limit).
  Local Notation nval_var_svar := (SchedulerSimulationBase.nval_var_svar ctx cost_limit).
  Local Notation op_assigns_st := (SchedulerSimulationBase.op_assigns_st ctx cost_limit).
  Local Notation op_writes_out := (SchedulerSimulationBase.op_writes_out ctx cost_limit).
  Local Notation ospec := (SchedulerSimulationBase.ospec ctx).
  Local Notation ospec_trans := (SchedulerSimulationBase.ospec_trans ctx).
  Local Notation ospecv := (SchedulerSimulationBase.ospecv ctx).
  Local Notation pending_samples_covers := (SchedulerSimulationBase.pending_samples_covers ctx).
  Local Notation pending_samples_nidwf := (SchedulerSimulationBase.pending_samples_nidwf ctx).
  Local Notation pending_samples_nidwf' := (SchedulerSimulationBase.pending_samples_nidwf' ctx).
  Local Notation pending_samples_pos := (SchedulerSimulationBase.pending_samples_pos ctx).
  Local Notation pending_samples_spec := (SchedulerSimulationBase.pending_samples_spec ctx).
  Local Notation pends := (SchedulerSimulationBase.pends ctx).
  Local Notation pends_cons := (SchedulerSimulationBase.pends_cons ctx).
  Local Notation pends_join := (SchedulerSimulationBase.pends_join ctx).
  Local Notation pends_mono := (SchedulerSimulationBase.pends_mono ctx).
  Local Notation pends_not_drive := (SchedulerSimulationBase.pends_not_drive ctx cost_limit).
  Local Notation pends_not_joined_drive := (SchedulerSimulationBase.pends_not_joined_drive ctx cost_limit).
  Local Notation pends_samp := (SchedulerSimulationBase.pends_samp ctx).
  Local Notation pleaf := (SchedulerSimulationBase.pleaf ctx).
  Local Notation pleaf_cons := (SchedulerSimulationBase.pleaf_cons ctx).
  Local Notation pleaf_here := (SchedulerSimulationBase.pleaf_here ctx).
  Local Notation pleaf_left := (SchedulerSimulationBase.pleaf_left ctx).
  Local Notation pleaf_mono := (SchedulerSimulationBase.pleaf_mono ctx).
  Local Notation pleaf_right := (SchedulerSimulationBase.pleaf_right ctx).
  Local Notation preserves_all := (SchedulerSimulationBase.preserves_all ctx).
  Local Notation preserves_all_bind := (SchedulerSimulationBase.preserves_all_bind ctx).
  Local Notation preserves_all_emit := (SchedulerSimulationBase.preserves_all_emit ctx).
  Local Notation preserves_all_ensure_var := (SchedulerSimulationBase.preserves_all_ensure_var ctx).
  Local Notation preserves_all_get_var := (SchedulerSimulationBase.preserves_all_get_var ctx).
  Local Notation preserves_all_merge_key := (SchedulerSimulationBase.preserves_all_merge_key ctx).
  Local Notation preserves_all_merge_loop := (SchedulerSimulationBase.preserves_all_merge_loop ctx).
  Local Notation preserves_all_ret := (SchedulerSimulationBase.preserves_all_ret ctx).
  Local Notation preserves_all_set_var := (SchedulerSimulationBase.preserves_all_set_var ctx).
  Local Notation preserves_g := (SchedulerSimulationBase.preserves_g ctx).
  Local Notation preserves_g_bind := (SchedulerSimulationBase.preserves_g_bind ctx).
  Local Notation preserves_g_emit := (SchedulerSimulationBase.preserves_g_emit ctx).
  Local Notation preserves_g_ensure_var := (SchedulerSimulationBase.preserves_g_ensure_var ctx).
  Local Notation preserves_g_get_var := (SchedulerSimulationBase.preserves_g_get_var ctx).
  Local Notation preserves_g_merge_key := (SchedulerSimulationBase.preserves_g_merge_key ctx).
  Local Notation preserves_g_merge_loop := (SchedulerSimulationBase.preserves_g_merge_loop ctx).
  Local Notation preserves_g_merge_maps := (SchedulerSimulationBase.preserves_g_merge_maps ctx).
  Local Notation preserves_g_ret := (SchedulerSimulationBase.preserves_g_ret ctx).
  Local Notation preserves_g_set_var := (SchedulerSimulationBase.preserves_g_set_var ctx).
  Local Notation preserves_js := (SchedulerSimulationBase.preserves_js ctx).
  Local Notation preserves_js_bind := (SchedulerSimulationBase.preserves_js_bind ctx).
  Local Notation preserves_js_bind_st := (SchedulerSimulationBase.preserves_js_bind_st ctx).
  Local Notation preserves_js_emit := (SchedulerSimulationBase.preserves_js_emit ctx).
  Local Notation preserves_js_ensure_var := (SchedulerSimulationBase.preserves_js_ensure_var ctx).
  Local Notation preserves_js_get_state := (SchedulerSimulationBase.preserves_js_get_state ctx).
  Local Notation preserves_js_get_var := (SchedulerSimulationBase.preserves_js_get_var ctx).
  Local Notation preserves_js_merge_key := (SchedulerSimulationBase.preserves_js_merge_key ctx).
  Local Notation preserves_js_merge_loop := (SchedulerSimulationBase.preserves_js_merge_loop ctx).
  Local Notation preserves_js_merge_maps := (SchedulerSimulationBase.preserves_js_merge_maps ctx).
  Local Notation preserves_js_ret := (SchedulerSimulationBase.preserves_js_ret ctx).
  Local Notation preserves_js_set_var := (SchedulerSimulationBase.preserves_js_set_var ctx).
  Local Notation put_state_red := (SchedulerSimulationBase.put_state_red ctx).
  Local Notation read_var_cases := (SchedulerSimulationBase.read_var_cases ctx).
  Local Notation read_var_vmap := (SchedulerSimulationBase.read_var_vmap ctx).
  Local Notation require_buffer_node_range := (SchedulerSimulationBase.require_buffer_node_range ctx cost_limit).
  Local Notation reset_states_has_v := (SchedulerSimulationBase.reset_states_has_v ctx cost_limit).
  Local Notation reset_states_not_done := (SchedulerSimulationBase.reset_states_not_done ctx cost_limit).
  Local Notation reset_states_not_svar := (SchedulerSimulationBase.reset_states_not_svar ctx cost_limit).
  Local Notation reset_updates_no_done := (SchedulerSimulationBase.reset_updates_no_done ctx cost_limit).
  Local Notation reset_updates_no_out := (SchedulerSimulationBase.reset_updates_no_out ctx cost_limit).
  Local Notation reset_updates_no_svar := (SchedulerSimulationBase.reset_updates_no_svar ctx cost_limit).
  Local Notation reset_updates_v := (SchedulerSimulationBase.reset_updates_v ctx cost_limit).
  Local Notation ret_fspec := (SchedulerSimulationBase.ret_fspec ctx).
  Local Notation ret_full := (SchedulerSimulationBase.ret_full ctx).
  Local Notation ret_pos := (SchedulerSimulationBase.ret_pos ctx).
  Local Notation run_n := (SchedulerSimulationBase.run_n ctx cost_limit).
  Local Notation run_preserves_ovar := (SchedulerSimulationBase.run_preserves_ovar ctx cost_limit).
  Local Notation run_preserves_svar := (SchedulerSimulationBase.run_preserves_svar ctx cost_limit).
  Local Notation sample_before_drive := (SchedulerSimulationBase.sample_before_drive ctx cost_limit).
  Local Notation sample_buffer_frozen := (SchedulerSimulationBase.sample_buffer_frozen ctx cost_limit).
  Local Notation sample_bufs := (SchedulerSimulationBase.sample_bufs ctx cost_limit).
  Local Notation sample_chain_between := (SchedulerSimulationBase.sample_chain_between ctx cost_limit).
  Local Notation sample_chain_no_drive := (SchedulerSimulationBase.sample_chain_no_drive ctx cost_limit).
  Local Notation sample_chain_no_sample := (SchedulerSimulationBase.sample_chain_no_sample ctx cost_limit).
  Local Notation sample_drive := (SchedulerSimulationBase.sample_drive ctx cost_limit).
  Local Notation sample_drive_head := (SchedulerSimulationBase.sample_drive_head ctx cost_limit).
  Local Notation sample_drive_head_op := (SchedulerSimulationBase.sample_drive_head_op ctx cost_limit).
  Local Notation sample_drive_head_shape := (SchedulerSimulationBase.sample_drive_head_shape ctx cost_limit).
  Local Notation sample_drive_in_drive_nodes := (SchedulerSimulationBase.sample_drive_in_drive_nodes ctx cost_limit).
  Local Notation sample_drive_lt := (SchedulerSimulationBase.sample_drive_lt ctx cost_limit).
  Local Notation sample_drive_op := (SchedulerSimulationBase.sample_drive_op ctx cost_limit).
  Local Notation sample_drive_req := (SchedulerSimulationBase.sample_drive_req ctx cost_limit).
  Local Notation sample_gate_cases := (SchedulerSimulationBase.sample_gate_cases ctx cost_limit).
  Local Notation sample_gate_is_stall_reg := (SchedulerSimulationBase.sample_gate_is_stall_reg ctx cost_limit).
  Local Notation sample_has_drive := (SchedulerSimulationBase.sample_has_drive ctx cost_limit).
  Local Notation sample_index := (SchedulerSimulationBase.sample_index ctx cost_limit).
  Local Notation sample_is_buffered := (SchedulerSimulationBase.sample_is_buffered ctx cost_limit).
  Local Notation sample_nid_succ := (SchedulerSimulationBase.sample_nid_succ ctx cost_limit).
  Local Notation sample_node_in_range := (SchedulerSimulationBase.sample_node_in_range ctx cost_limit).
  Local Notation sample_ref_is_register := (SchedulerSimulationBase.sample_ref_is_register ctx cost_limit).
  Local Notation sample_req := (SchedulerSimulationBase.sample_req ctx cost_limit).
  Local Notation sample_req_head := (SchedulerSimulationBase.sample_req_head ctx cost_limit).
  Local Notation sample_tok_is_stall := (SchedulerSimulationBase.sample_tok_is_stall ctx cost_limit).
  Local Notation samples_driven := (SchedulerSimulationBase.samples_driven ctx).
  Local Notation samples_driven_build_dfg := (SchedulerSimulationBase.samples_driven_build_dfg ctx cost_limit).
  Local Notation samples_driven_cons2 := (SchedulerSimulationBase.samples_driven_cons2 ctx).
  Local Notation samples_driven_cons_nonsample := (SchedulerSimulationBase.samples_driven_cons_nonsample ctx).
  Local Notation samples_driven_rev := (SchedulerSimulationBase.samples_driven_rev ctx).
  Local Notation samples_stalled := (SchedulerSimulationBase.samples_stalled ctx).
  Local Notation samples_stalled_build_dfg := (SchedulerSimulationBase.samples_stalled_build_dfg ctx cost_limit).
  Local Notation samples_stalled_cons2 := (SchedulerSimulationBase.samples_stalled_cons2 ctx).
  Local Notation samples_stalled_cons_nonsample := (SchedulerSimulationBase.samples_stalled_cons_nonsample ctx).
  Local Notation samples_stalled_rev := (SchedulerSimulationBase.samples_stalled_rev ctx).
  Local Notation samples_within := (SchedulerSimulationBase.samples_within ctx).
  Local Notation sched_input := (SchedulerSimulationBase.sched_input ctx cost_limit).
  Local Notation sched_step := (SchedulerSimulationBase.sched_step ctx cost_limit).
  Local Notation sched_step_done := (SchedulerSimulationBase.sched_step_done ctx cost_limit).
  Local Notation sched_step_done_ovar := (SchedulerSimulationBase.sched_step_done_ovar ctx cost_limit).
  Local Notation sched_step_done_ovar_untouched := (SchedulerSimulationBase.sched_step_done_ovar_untouched ctx cost_limit).
  Local Notation sched_step_done_set := (SchedulerSimulationBase.sched_step_done_set ctx cost_limit).
  Local Notation sched_step_done_svar := (SchedulerSimulationBase.sched_step_done_svar ctx cost_limit).
  Local Notation sched_step_done_svar_untouched := (SchedulerSimulationBase.sched_step_done_svar_untouched ctx cost_limit).
  Local Notation sched_step_done_v := (SchedulerSimulationBase.sched_step_done_v ctx cost_limit).
  Local Notation sched_step_done_valid := (SchedulerSimulationBase.sched_step_done_valid ctx cost_limit).
  Local Notation sched_step_eq := (SchedulerSimulationBase.sched_step_eq ctx cost_limit).
  Local Notation sched_step_getout := (SchedulerSimulationBase.sched_step_getout ctx cost_limit).
  Local Notation sched_step_getst := (SchedulerSimulationBase.sched_step_getst ctx cost_limit).
  Local Notation sched_step_preserves_ovar := (SchedulerSimulationBase.sched_step_preserves_ovar ctx cost_limit).
  Local Notation sched_step_preserves_svar := (SchedulerSimulationBase.sched_step_preserves_svar ctx cost_limit).
  Local Notation scheduler_reaches_done := (SchedulerSimulationBase.scheduler_reaches_done ctx cost_limit).
  Local Notation seq_full := (SchedulerSimulationBase.seq_full ctx).
  Local Notation seq_pos := (SchedulerSimulationBase.seq_pos ctx).
  Local Notation seq_sz := (SchedulerSimulationBase.seq_sz ctx).
  Local Notation set_var_fg := (SchedulerSimulationBase.set_var_fg ctx).
  Local Notation set_var_full := (SchedulerSimulationBase.set_var_full ctx).
  Local Notation set_var_graph := (SchedulerSimulationBase.set_var_graph ctx).
  Local Notation set_var_ospecv := (SchedulerSimulationBase.set_var_ospecv ctx).
  Local Notation set_var_pos := (SchedulerSimulationBase.set_var_pos ctx).
  Local Notation set_var_spec := (SchedulerSimulationBase.set_var_spec ctx).
  Local Notation set_var_vm_head := (SchedulerSimulationBase.set_var_vm_head ctx).
  Local Notation set_var_vm_inv := (SchedulerSimulationBase.set_var_vm_inv ctx).
  Local Notation set_var_vm_inv2 := (SchedulerSimulationBase.set_var_vm_inv2 ctx).
  Local Notation set_var_vm_keep := (SchedulerSimulationBase.set_var_vm_keep ctx).
  Local Notation settle_bound := (SchedulerSimulationBase.settle_bound ctx cost_limit).
  Local Notation slot_keys_nodup := (SchedulerSimulationBase.slot_keys_nodup ctx cost_limit).
  Local Notation ssucc_build_dfg := (SchedulerSimulationBase.ssucc_build_dfg ctx cost_limit).
  Local Notation stall_cost_gap := (SchedulerSimulationBase.stall_cost_gap ctx cost_limit).
  Local Notation stall_counter_run := (SchedulerSimulationBase.stall_counter_run ctx cost_limit).
  Local Notation stall_counter_step := (SchedulerSimulationBase.stall_counter_step ctx cost_limit).
  Local Notation stall_counter_wide := (SchedulerSimulationBase.stall_counter_wide ctx cost_limit).
  Local Notation stall_gate_walks := (SchedulerSimulationBase.stall_gate_walks ctx cost_limit).
  Local Notation stall_is_buffered := (SchedulerSimulationBase.stall_is_buffered ctx cost_limit).
  Local Notation stall_lat_of := (SchedulerSimulationBase.stall_lat_of ctx cost_limit).
  Local Notation stall_nid_succ := (SchedulerSimulationBase.stall_nid_succ ctx cost_limit).
  Local Notation stall_saturated_step := (SchedulerSimulationBase.stall_saturated_step ctx cost_limit).
  Local Notation stall_valid_next_inv := (SchedulerSimulationBase.stall_valid_next_inv ctx cost_limit).
  Local Notation stall_valid_next_ones := (SchedulerSimulationBase.stall_valid_next_ones ctx cost_limit).
  Local Notation stall_wait_start := (SchedulerSimulationBase.stall_wait_start ctx cost_limit).
  Local Notation stall_weight := (SchedulerSimulationBase.stall_weight ctx cost_limit).
  Local Notation start_rel := (SchedulerSimulationBase.start_rel ctx cost_limit).
  Local Notation succ_arg_node := (SchedulerSimulationBase.succ_arg_node ctx).
  Local Notation succ_args_build_dfg := (SchedulerSimulationBase.succ_args_build_dfg ctx cost_limit).
  Local Notation succ_sample_node := (SchedulerSimulationBase.succ_sample_node ctx).
  Local Notation tfs_get_updates_cons := (SchedulerSimulationBase.tfs_get_updates_cons ctx cost_limit).
  Local Notation valid_and_eval := (SchedulerSimulationBase.valid_and_eval ctx cost_limit).
  Local Notation valid_gates := (SchedulerSimulationBase.valid_gates ctx cost_limit).
  Local Notation valid_if_eval := (SchedulerSimulationBase.valid_if_eval ctx cost_limit).
  Local Notation valid_if_eval_inv := (SchedulerSimulationBase.valid_if_eval_inv ctx cost_limit).
  Local Notation valid_if_eval_sel := (SchedulerSimulationBase.valid_if_eval_sel ctx cost_limit).
  Local Notation valid_refs := (SchedulerSimulationBase.valid_refs ctx cost_limit).
  Local Notation valid_settled := (SchedulerSimulationBase.valid_settled ctx cost_limit).
  Local Notation valid_settled_run := (SchedulerSimulationBase.valid_settled_run ctx cost_limit).
  Local Notation valid_zero_run := (SchedulerSimulationBase.valid_zero_run ctx cost_limit).
  Local Notation validity_monotone_step := (SchedulerSimulationBase.validity_monotone_step ctx cost_limit).
  Local Notation valids_ones_run := (SchedulerSimulationBase.valids_ones_run ctx cost_limit).
  Local Notation var_map_entry_size := (SchedulerSimulationBase.var_map_entry_size ctx cost_limit).
  Local Notation var_map_node_range := (SchedulerSimulationBase.var_map_node_range ctx cost_limit).
  Local Notation var_map_output_has_cost := (SchedulerSimulationBase.var_map_output_has_cost ctx cost_limit).
  Local Notation var_map_snd_is_graph_nid := (SchedulerSimulationBase.var_map_snd_is_graph_nid ctx cost_limit).
  Local Notation var_node_at := (SchedulerSimulationBase.var_node_at ctx cost_limit).
  Local Notation vmg := (SchedulerSimulationBase.vmg ctx).
  Local Notation vreg_nid := (SchedulerSimulationBase.vreg_nid ctx cost_limit).
  Local Notation vreg_nid_in_require_buffer := (SchedulerSimulationBase.vreg_nid_in_require_buffer ctx cost_limit).
  Local Notation vreg_nid_inj := (SchedulerSimulationBase.vreg_nid_inj ctx cost_limit).
  Local Notation vreg_nid_node_range := (SchedulerSimulationBase.vreg_nid_node_range ctx cost_limit).
  Local Notation vreg_nid_of_entry := (SchedulerSimulationBase.vreg_nid_of_entry ctx cost_limit).
  Local Notation wfg := (SchedulerSimulationBase.wfg ctx).
  Local Notation wfg_build_dfg := (SchedulerSimulationBase.wfg_build_dfg ctx cost_limit).
  Local Notation wgmono := (SchedulerSimulationBase.wgmono ctx).
  Local Notation wgmono_refl := (SchedulerSimulationBase.wgmono_refl ctx).
  Local Notation wgmono_trans := (SchedulerSimulationBase.wgmono_trans ctx).
  Local Notation winv := (SchedulerSimulationBase.winv ctx).
  Local Notation wnidwf := (SchedulerSimulationBase.wnidwf ctx).
  Local Notation wnidwf_bound := (SchedulerSimulationBase.wnidwf_bound ctx).
  Local Notation wnidwf_gmono := (SchedulerSimulationBase.wnidwf_gmono ctx).
  Local Notation wsz := (SchedulerSimulationBase.wsz ctx).
  Local Notation wsz_fwd := (SchedulerSimulationBase.wsz_fwd ctx cost_limit).
  Local Notation wsz_gmono := (SchedulerSimulationBase.wsz_gmono ctx).
  Local Notation wsz_node_sz := (SchedulerSimulationBase.wsz_node_sz ctx cost_limit).
  Local Notation wvmg := (SchedulerSimulationBase.wvmg ctx).
  Local Notation wvsz := (SchedulerSimulationBase.wvsz ctx).
  Local Notation wvsz_build_dfg := (SchedulerSimulationBase.wvsz_build_dfg ctx cost_limit).
  Local Notation zeroed_at_start := (SchedulerSimulationBase.zeroed_at_start ctx cost_limit).

  Local Notation sched := (tfs_schedule ctx cost_limit).
  Local Notation s_var := (tfs_spec_states ctx).
  Local Notation i_var := (tfs_spec_inputs ctx).
  Local Notation o_var := (tfs_spec_outputs ctx).
  Local Notation s_sz  := (tfs_spec_states_size ctx).
  Local Notation i_sz  := (tfs_spec_inputs_size ctx).
  Local Notation o_sz  := (tfs_spec_outputs_size ctx).
  Hint Extern 0 (FiniteType s_var) => exact (tfs_spec_states_fin ctx)  : typeclass_instances.
  Hint Extern 0 (FiniteType i_var) => exact (tfs_spec_inputs_fin ctx)  : typeclass_instances.
  Hint Extern 0 (FiniteType o_var) => exact (tfs_spec_outputs_fin ctx) : typeclass_instances.
  Local Notation src_st_env  := (ContextEnv.(env_t) (tf_states_type s_sz)).
  Local Notation src_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation src_sys_state := (src_st_env * src_out_env)%type.
  Hint Extern 0 (FiniteType (tfs_states sched))  => exact (tfs_states_fin sched)  : typeclass_instances.
  Hint Extern 0 (FiniteType (tfs_outputs sched)) => exact (tfs_outputs_fin sched) : typeclass_instances.
  Local Notation sched_st_env  := (ContextEnv.(env_t) (tf_states_type (tfs_states_size sched))).
  Local Notation sched_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation sched_sys_state := (sched_st_env * sched_out_env)%type.
  Local Notation p_var  := (tfs_spec_ips ctx).
  Local Notation bneeds := (buffer_needs ctx cost_limit).
  Local Notation si_var := (tfs_inputs sched).
  Local Notation si_sz  := (tfs_inputs_size sched).
  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).
  Local Notation sched_input_t :=
    (forall x : tfs_inputs sched, type_denote (tf_inputs_type (tfs_inputs_size sched) x)).
  Local Notation ss_sz := (tfs_states_size sched).
  Local Notation oo_sz := (tfs_outputs_size sched).
  Local Notation eval_st  dst e ss input :=
    (tf_eval_expr ss_sz si_sz oo_sz (szB := ss_sz dst) e ss input).
  Local Notation eval_out dst e ss input :=
    (tf_eval_expr ss_sz si_sz oo_sz (szB := oo_sz dst) e ss input).
  Local Notation find_st_update_app_None := (find_st_update_app_None_gen sched).
  Local Notation eval1 e ss input :=
    (tf_eval_expr ss_sz si_sz oo_sz (szB := 1) e ss input).
  Local Notation act_cycle_map act :=
    (calc_target_cycle cost_limit (calc_backward_cost ctx cost_limit (build_dfg ctx act))).
  Local Notation buf_gate act a_idx n_idx :=
    (snd (compile_dfg_expr ctx bneeds
            (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act)
            (vreg_nid a_idx n_idx)
            (filter (fun '(b_nid, _) => negb (Nat.eqb b_nid (vreg_nid a_idx n_idx)))
               (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])))).
  Local Notation buf_valid_next act a_idx n_idx :=
    (buf_valid_expr act a_idx n_idx
       (snd (snd (nth (index_to_nat n_idx)
                    (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])
                    (0, (0, 0)))))
       (buf_gate act a_idx n_idx) (vreg_nid a_idx n_idx)).
  Local Notation gexpr act a_idx sbufs en :=
    (guard_expr ctx bneeds (get_tainted ctx (build_dfg ctx act))
       (decl_facts ctx (build_dfg ctx act)) (length (graph (build_dfg ctx act)))
       a_idx (build_dfg ctx act) sbufs en).
  Local Notation wst := (@dfg_state_t s_var i_var o_var p_var).
  Local Notation dstate :=
    (dfg_state_t (states_var:=s_var)(inputs_var:=i_var)(outputs_var:=o_var)(ips_var:=p_var)).
  Local Notation ppath tainted dfacts pi cnd b :=
    (phi_path (phi_crit tainted dfacts cnd pi) cnd b pi).
  Local Notation ppath_at act pi cnd b :=
    (phi_path (phi_crit (get_tainted ctx (build_dfg ctx act))
                 (decl_facts ctx (build_dfg ctx act)) cnd pi) cnd b pi).
  Local Notation act_slot a_idx :=
    (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []).
  Local Notation vm_expr act a_idx n :=
    (fst (compile_dfg_expr ctx bneeds (length (graph (build_dfg ctx act)))
            a_idx (build_dfg ctx act) n
            (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))).
  Local Notation find_st_update_app_Some := (find_st_update_app_Some_gen sched).
  Local Notation dvar := (@dfg_vars_t s_var o_var).

  (* ==================================================================== *)
  (* The combinational twins of [compile_stall_valid]: a node's compiled  *)
  (* validity written in terms of its arguments'.                         *)
  (* ==================================================================== *)

  Lemma compile_unary_valid
        (act: tfs_action sched) a_idx (n: nid_t) uop arg
        (bufs: list (nid_t * (nat * sz_t))) pi fuel :
    node_op act n = DFG_Unary uop arg ->
    BitsToLists.list_assoc bufs n = None ->
    0 < fuel ->
    snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act) n bufs)
    = snd (compile_dfg_expr_at ctx bneeds pi (pred fuel) a_idx
             (build_dfg ctx act) arg bufs).
  Proof.
    intros Hop Hbuf Hf. destruct fuel as [| fuel]; [ lia |]. cbn [Init.Nat.pred].
    cbn [compile_dfg_expr_aux].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:E;
      [ exfalso; rewrite Hbuf in E; congruence |].
    cbv beta iota. unfold SchedulerSimulationBase.node_op in Hop. rewrite Hop.
    destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                (build_dfg ctx act) arg bufs).
    reflexivity.
  Qed.

  Lemma compile_resize_valid
        (act: tfs_action sched) a_idx (n: nid_t) arg
        (bufs: list (nid_t * (nat * sz_t))) pi fuel :
    node_op act n = DFG_Resize arg ->
    BitsToLists.list_assoc bufs n = None ->
    0 < fuel ->
    snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act) n bufs)
    = snd (compile_dfg_expr_at ctx bneeds pi (pred fuel) a_idx
             (build_dfg ctx act) arg bufs).
  Proof.
    intros Hop Hbuf Hf. destruct fuel as [| fuel]; [ lia |]. cbn [Init.Nat.pred].
    cbn [compile_dfg_expr_aux].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:E;
      [ exfalso; rewrite Hbuf in E; congruence |].
    cbv beta iota. unfold SchedulerSimulationBase.node_op in Hop. rewrite Hop.
    destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                (build_dfg ctx act) arg bufs).
    reflexivity.
  Qed.

  Lemma compile_binary_valid
        (act: tfs_action sched) a_idx (n: nid_t) bop a1 a2
        (bufs: list (nid_t * (nat * sz_t))) pi fuel :
    node_op act n = DFG_Binary bop a1 a2 ->
    BitsToLists.list_assoc bufs n = None ->
    0 < fuel ->
    snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act) n bufs)
    = valid_expr_and ctx bneeds
        (snd (compile_dfg_expr_at ctx bneeds pi (pred fuel) a_idx
                (build_dfg ctx act) a1 bufs))
        (snd (compile_dfg_expr_at ctx bneeds pi (pred fuel) a_idx
                (build_dfg ctx act) a2 bufs)).
  Proof.
    intros Hop Hbuf Hf. destruct fuel as [| fuel]; [ lia |]. cbn [Init.Nat.pred].
    cbn [compile_dfg_expr_aux].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:E;
      [ exfalso; rewrite Hbuf in E; congruence |].
    cbv beta iota. unfold SchedulerSimulationBase.node_op in Hop. rewrite Hop.
    destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                (build_dfg ctx act) a1 bufs).
    destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                (build_dfg ctx act) a2 bufs).
    reflexivity.
  Qed.

  (* A CRITICAL phi reads both branches, under the unextended path. *)
  Lemma compile_phi_valid_crit
        (act: tfs_action sched) a_idx (n: nid_t) c t e
        (bufs: list (nid_t * (nat * sz_t))) pi fuel :
    node_op act n = DFG_Phi c t e ->
    BitsToLists.list_assoc bufs n = None ->
    0 < fuel ->
    phi_crit (get_tainted ctx (build_dfg ctx act))
             (decl_facts ctx (build_dfg ctx act)) c pi = true ->
    snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act) n bufs)
    = valid_expr_and ctx bneeds
        (valid_expr_and ctx bneeds
           (snd (compile_dfg_expr_at ctx bneeds pi (pred fuel) a_idx
                   (build_dfg ctx act) t bufs))
           (snd (compile_dfg_expr_at ctx bneeds pi (pred fuel) a_idx
                   (build_dfg ctx act) e bufs)))
        (snd (compile_dfg_expr_at ctx bneeds pi (pred fuel) a_idx
                (build_dfg ctx act) c bufs)).
  Proof.
    intros Hop Hbuf Hf Hcrit. destruct fuel as [| fuel]; [ lia |].
    cbn [Init.Nat.pred]. cbn [compile_dfg_expr_aux].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:E;
      [ exfalso; rewrite Hbuf in E; congruence |].
    cbv beta iota. unfold SchedulerSimulationBase.node_op in Hop. rewrite Hop.
    unfold phi_path. rewrite Hcrit.
    destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                (build_dfg ctx act) c bufs).
    destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                (build_dfg ctx act) t bufs).
    destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                (build_dfg ctx act) e bufs).
    reflexivity.
  Qed.

  (* A SELECTING phi reads the taken branch, under the path it extends. *)
  Lemma compile_phi_valid_sel
        (act: tfs_action sched) a_idx (n: nid_t) c t e
        (bufs: list (nid_t * (nat * sz_t))) pi fuel :
    node_op act n = DFG_Phi c t e ->
    BitsToLists.list_assoc bufs n = None ->
    0 < fuel ->
    phi_crit (get_tainted ctx (build_dfg ctx act))
             (decl_facts ctx (build_dfg ctx act)) c pi = false ->
    snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx (build_dfg ctx act) n bufs)
    = valid_expr_and ctx bneeds
        (snd (compile_dfg_expr_at ctx bneeds pi (pred fuel) a_idx
                (build_dfg ctx act) c bufs))
        (valid_expr_if ctx bneeds
           (fst (compile_dfg_expr_at ctx bneeds pi (pred fuel) a_idx
                   (build_dfg ctx act) c bufs))
           (snd (compile_dfg_expr_at ctx bneeds ((c, true) :: pi) (pred fuel) a_idx
                   (build_dfg ctx act) t bufs))
           (snd (compile_dfg_expr_at ctx bneeds ((c, false) :: pi) (pred fuel) a_idx
                   (build_dfg ctx act) e bufs))).
  Proof.
    intros Hop Hbuf Hf Hcrit. destruct fuel as [| fuel]; [ lia |].
    cbn [Init.Nat.pred]. cbn [compile_dfg_expr_aux].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:E;
      [ exfalso; rewrite Hbuf in E; congruence |].
    cbv beta iota. unfold SchedulerSimulationBase.node_op in Hop. rewrite Hop.
    unfold phi_path. rewrite Hcrit.
    destruct (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                (build_dfg ctx act) c bufs).
    destruct (compile_dfg_expr_at ctx bneeds ((c, true) :: pi) fuel a_idx
                (build_dfg ctx act) t bufs).
    destruct (compile_dfg_expr_at ctx bneeds ((c, false) :: pi) fuel a_idx
                (build_dfg ctx act) e bufs).
    reflexivity.
  Qed.

  (* Peeling a combinational node's validity onto its arguments, at the fuel
     the reference uses.  [nrv_peel_phi_sel] is the one that moves the path. *)
  Local Notation rvalid act a_idx pi n ss input :=
    (eval1 (snd (compile_dfg_expr_at ctx bneeds pi
                   (length (graph (build_dfg ctx act))) a_idx
                   (build_dfg ctx act) n (sample_bufs act a_idx))) ss input) (only parsing).
  (* An argument of the node at [n] sits below [n]. *)
  Lemma arg_lt_of_op (act: tfs_action sched) n a :
    n < length (graph (build_dfg ctx act)) ->
    In a (get_args ctx (nth n (graph (build_dfg ctx act))
                          {| nid := 0; op := DFG_Empty; sz := 0 |})) ->
    a < n.
  Proof.
    intros Hnlen Hin.
    assert (Hmem : In (nth n (graph (build_dfg ctx act))
                        {| nid := 0; op := DFG_Empty; sz := 0 |})
                      (graph (build_dfg ctx act)))
      by (apply nth_In; exact Hnlen).
    pose proof (args_lt_fwd act _ Hmem a Hin) as Hlt.
    rewrite (node_nid_at act n Hnlen) in Hlt. exact Hlt.
  Qed.

  Lemma nrv_peel_refuel (act: tfs_action sched) a_idx x pi
        (ss: sched_sys_state) (input: sched_input_t) :
    1 <= x -> x < pred (length (graph (build_dfg ctx act))) ->
    eval1 (snd (compile_dfg_expr_at ctx bneeds pi
                  (pred (length (graph (build_dfg ctx act)))) a_idx
                  (build_dfg ctx act) x (sample_bufs act a_idx))) ss input
    = Bits.ones 1 ->
    rvalid act a_idx pi x ss input = Bits.ones 1.
  Proof.
    intros Hx1 Hxlen Hval.
    assert (Hxl : x < length (graph (build_dfg ctx act))) by lia.
    rewrite (compile_fuel_irrel_gen act a_idx (sample_bufs act a_idx) _ _ x Hx1 Hxl
               (pred (length (graph (build_dfg ctx act))))
               (length (graph (build_dfg ctx act))) pi
               Hxlen Hxl) in Hval.
    exact Hval.
  Qed.

  Lemma nrv_peel_unary (act: tfs_action sched) a_idx n uop arg pi
        (ss: sched_sys_state) (input: sched_input_t) :
    node_op act n = DFG_Unary uop arg ->
    1 <= arg -> n < length (graph (build_dfg ctx act)) ->
    rvalid act a_idx pi n ss input = Bits.ones 1 ->
    rvalid act a_idx pi arg ss input = Bits.ones 1.
  Proof.
    intros Hop Ha1 Hnlen Hval.
    assert (Han : arg < n)
      by (apply (arg_lt_of_op act n arg Hnlen);
          unfold SchedulerSimulationBase.node_op in Hop; unfold get_args; rewrite Hop; left; reflexivity).
    rewrite (compile_unary_valid act a_idx n uop arg (sample_bufs act a_idx) pi
               (length (graph (build_dfg ctx act))) Hop
               (not_sample_not_in_sample_bufs act a_idx n
                  ltac:(unfold SchedulerSimulationBase.is_sample_of; rewrite Hop; reflexivity))
               ltac:(lia)) in Hval.
    exact (nrv_peel_refuel act a_idx arg pi ss input Ha1 ltac:(lia) Hval).
  Qed.

  Lemma nrv_peel_resize (act: tfs_action sched) a_idx n arg pi
        (ss: sched_sys_state) (input: sched_input_t) :
    node_op act n = DFG_Resize arg ->
    1 <= arg -> n < length (graph (build_dfg ctx act)) ->
    rvalid act a_idx pi n ss input = Bits.ones 1 ->
    rvalid act a_idx pi arg ss input = Bits.ones 1.
  Proof.
    intros Hop Ha1 Hnlen Hval.
    assert (Han : arg < n)
      by (apply (arg_lt_of_op act n arg Hnlen);
          unfold SchedulerSimulationBase.node_op in Hop; unfold get_args; rewrite Hop; left; reflexivity).
    rewrite (compile_resize_valid act a_idx n arg (sample_bufs act a_idx) pi
               (length (graph (build_dfg ctx act))) Hop
               (not_sample_not_in_sample_bufs act a_idx n
                  ltac:(unfold SchedulerSimulationBase.is_sample_of; rewrite Hop; reflexivity))
               ltac:(lia)) in Hval.
    exact (nrv_peel_refuel act a_idx arg pi ss input Ha1 ltac:(lia) Hval).
  Qed.

  Lemma nrv_peel_binary (act: tfs_action sched) a_idx n bop a1 a2 pi
        (ss: sched_sys_state) (input: sched_input_t) :
    node_op act n = DFG_Binary bop a1 a2 ->
    1 <= a1 -> 1 <= a2 ->
    n < length (graph (build_dfg ctx act)) ->
    rvalid act a_idx pi n ss input = Bits.ones 1 ->
    rvalid act a_idx pi a1 ss input = Bits.ones 1
    /\ rvalid act a_idx pi a2 ss input = Bits.ones 1.
  Proof.
    intros Hop H11 H21 Hnlen Hval.
    assert (H1n : a1 < n)
      by (apply (arg_lt_of_op act n a1 Hnlen);
          unfold SchedulerSimulationBase.node_op in Hop; unfold get_args; rewrite Hop; left; reflexivity).
    assert (H2n : a2 < n)
      by (apply (arg_lt_of_op act n a2 Hnlen);
          unfold SchedulerSimulationBase.node_op in Hop; unfold get_args; rewrite Hop; right; left; reflexivity).
    rewrite (compile_binary_valid act a_idx n bop a1 a2 (sample_bufs act a_idx) pi
               (length (graph (build_dfg ctx act))) Hop
               (not_sample_not_in_sample_bufs act a_idx n
                  ltac:(unfold SchedulerSimulationBase.is_sample_of; rewrite Hop; reflexivity))
               ltac:(lia)) in Hval.
    rewrite valid_and_eval in Hval.
    destruct (bits1_and_split _ _ Hval) as [Hv1 Hv2].
    split.
    - exact (nrv_peel_refuel act a_idx a1 pi ss input H11 ltac:(lia) Hv1).
    - exact (nrv_peel_refuel act a_idx a2 pi ss input H21 ltac:(lia) Hv2).
  Qed.

  Lemma nrv_peel_phi_crit (act: tfs_action sched) a_idx n c t e pi
        (ss: sched_sys_state) (input: sched_input_t) :
    node_op act n = DFG_Phi c t e ->
    phi_crit (get_tainted ctx (build_dfg ctx act))
             (decl_facts ctx (build_dfg ctx act)) c pi = true ->
    1 <= c -> 1 <= t -> 1 <= e ->
    n < length (graph (build_dfg ctx act)) ->
    rvalid act a_idx pi n ss input = Bits.ones 1 ->
    rvalid act a_idx pi c ss input = Bits.ones 1
    /\ rvalid act a_idx pi t ss input = Bits.ones 1
    /\ rvalid act a_idx pi e ss input = Bits.ones 1.
  Proof.
    intros Hop Hcrit Hc1 Ht1 He1 Hnlen Hval.
    assert (Hcn : c < n)
      by (apply (arg_lt_of_op act n c Hnlen);
          unfold SchedulerSimulationBase.node_op in Hop; unfold get_args; rewrite Hop; left; reflexivity).
    assert (Htn : t < n)
      by (apply (arg_lt_of_op act n t Hnlen);
          unfold SchedulerSimulationBase.node_op in Hop; unfold get_args; rewrite Hop; right; left; reflexivity).
    assert (Hen : e < n)
      by (apply (arg_lt_of_op act n e Hnlen);
          unfold SchedulerSimulationBase.node_op in Hop; unfold get_args; rewrite Hop; right; right; left; reflexivity).
    rewrite (compile_phi_valid_crit act a_idx n c t e (sample_bufs act a_idx) pi
               (length (graph (build_dfg ctx act))) Hop
               (not_sample_not_in_sample_bufs act a_idx n
                  ltac:(unfold SchedulerSimulationBase.is_sample_of; rewrite Hop; reflexivity))
               ltac:(lia) Hcrit) in Hval.
    rewrite valid_and_eval, valid_and_eval in Hval.
    destruct (bits1_and_split _ _ Hval) as [Hte Hcv].
    destruct (bits1_and_split _ _ Hte) as [Htv Hev].
    split; [| split ].
    - exact (nrv_peel_refuel act a_idx c pi ss input Hc1 ltac:(lia) Hcv).
    - exact (nrv_peel_refuel act a_idx t pi ss input Ht1 ltac:(lia) Htv).
    - exact (nrv_peel_refuel act a_idx e pi ss input He1 ltac:(lia) Hev).
  Qed.

  Lemma nrv_peel_phi_sel (act: tfs_action sched) a_idx n c t e pi
        (ss: sched_sys_state) (input: sched_input_t) :
    node_op act n = DFG_Phi c t e ->
    phi_crit (get_tainted ctx (build_dfg ctx act))
             (decl_facts ctx (build_dfg ctx act)) c pi = false ->
    1 <= c -> 1 <= t -> 1 <= e ->
    n < length (graph (build_dfg ctx act)) ->
    rvalid act a_idx pi n ss input = Bits.ones 1 ->
    rvalid act a_idx pi c ss input = Bits.ones 1
    /\ (eval1 (node_ref_expr act a_idx c) ss input <> Bits.zero ->
        rvalid act a_idx ((c, true) :: pi) t ss input = Bits.ones 1)
    /\ (eval1 (node_ref_expr act a_idx c) ss input = Bits.zero ->
        rvalid act a_idx ((c, false) :: pi) e ss input = Bits.ones 1).
  Proof.
    intros Hop Hcrit Hc1 Ht1 He1 Hnlen Hval.
    assert (Hcn : c < n)
      by (apply (arg_lt_of_op act n c Hnlen);
          unfold SchedulerSimulationBase.node_op in Hop; unfold get_args; rewrite Hop; left; reflexivity).
    assert (Htn : t < n)
      by (apply (arg_lt_of_op act n t Hnlen);
          unfold SchedulerSimulationBase.node_op in Hop; unfold get_args; rewrite Hop; right; left; reflexivity).
    assert (Hen : e < n)
      by (apply (arg_lt_of_op act n e Hnlen);
          unfold SchedulerSimulationBase.node_op in Hop; unfold get_args; rewrite Hop; right; right; left; reflexivity).
    rewrite (compile_phi_valid_sel act a_idx n c t e (sample_bufs act a_idx) pi
               (length (graph (build_dfg ctx act))) Hop
               (not_sample_not_in_sample_bufs act a_idx n
                  ltac:(unfold SchedulerSimulationBase.is_sample_of; rewrite Hop; reflexivity))
               ltac:(lia) Hcrit) in Hval.
    rewrite valid_and_eval in Hval.
    destruct (bits1_and_split _ _ Hval) as [Hcv Hif].
    assert (Hce : eval1 (fst (compile_dfg_expr_at ctx bneeds pi
                               (pred (length (graph (build_dfg ctx act)))) a_idx
                               (build_dfg ctx act) c (sample_bufs act a_idx))) ss input
                  = eval1 (node_ref_expr act a_idx c) ss input).
    { unfold SchedulerSimulationBase.node_ref_expr.
      rewrite (compile_fst_pi_irrel (get_tainted ctx (build_dfg ctx act))
                 (decl_facts ctx (build_dfg ctx act)) a_idx (build_dfg ctx act)
                 (sample_bufs act a_idx)
                 (pred (length (graph (build_dfg ctx act)))) c pi []).
      rewrite (compile_fuel_irrel act a_idx (sample_bufs act a_idx) c Hc1
                 ltac:(lia) (pred (length (graph (build_dfg ctx act))))
                 (length (graph (build_dfg ctx act))) ltac:(lia) ltac:(lia)).
      reflexivity. }
    destruct (valid_if_eval_inv _ _ _ ss input Hif) as [Hthen Helse].
    split; [| split ].
    - exact (nrv_peel_refuel act a_idx c pi ss input Hc1 ltac:(lia) Hcv).
    - intro Hne. apply (nrv_peel_refuel act a_idx t ((c, true) :: pi) ss input
                          Ht1 ltac:(lia)).
      apply Hthen. rewrite Hce. exact Hne.
    - intro Hz. apply (nrv_peel_refuel act a_idx e ((c, false) :: pi) ss input
                         He1 ltac:(lia)).
      apply Helse. rewrite Hce. exact Hz.
  Qed.

  Section DFGSem.
    Context (act: tfs_action sched)
            (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
            (ss: sched_sys_state) (input: input_t) (sinput: sched_input_t)
            (sp0: src_sys_state) (F: wst).
    Hypothesis HF  : exports act F.
    Hypothesis Hss : forall sv, (fst ss).[tf_dfg_s sv] = (fst sp0).[sv].
    Hypothesis Hoo : forall ov, (snd ss).[ov] = (snd sp0).[ov].
    Hypothesis Hali : act_idx_aligned act a_idx.
    (* the scheduled input carries the source's, plus the IP responses *)
    Hypothesis Hsin : forall v, sinput (inl v) = input v.
    (* The path condition of the ops being compiled, as the run sees it. *)
    Definition guard_holds (en: list (nid_t * bool)) : Prop :=
      forall n b, In (n, b) en ->
        (b = true  -> eval1 (node_ref_expr act a_idx n) ss sinput <> Bits.zero) /\
        (b = false -> eval1 (node_ref_expr act a_idx n) ss sinput = Bits.zero).

    (* THE ROUND TRIP: a sample.s register holds the IP.s answer to the
       request its OWN drive sent. *)
    Hypothesis Hrt : forall n_idx p tok en d av en',
      node_op act (vreg_nid a_idx n_idx) = DFG_Sample p tok en ->
      sample_drive act (vreg_nid a_idx n_idx) = Some d ->
      node_op act d = DFG_Drive p av en' ->
      sz (nth d (graph (build_dfg ctx act))
           {| nid := 0; op := DFG_Empty; sz := 0 |}) = ip_req_sz (tfs_spec_ip ctx p) ->
      (* only where the call FIRES: an untaken arm.s sample latches the wire
         the other arm drove, and says nothing *)
      guard_holds en ->
      (* and the answer has been latched *)
      (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
      (fst ss).[tf_dfg_b a_idx n_idx]
      = convert (ip_fn (tfs_spec_ip ctx p)
          (tf_eval_expr ss_sz si_sz oo_sz
             (szB := ip_req_sz (tfs_spec_ip ctx p))
             (node_ref_expr act a_idx av) ss sinput)).

    (* A latched sample's request carried a settled argument. *)
    Hypothesis Harg : forall n_idx p tok en d av en',
      node_op act (vreg_nid a_idx n_idx) = DFG_Sample p tok en ->
      sample_drive act (vreg_nid a_idx n_idx) = Some d ->
      node_op act d = DFG_Drive p av en' ->
      (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
      eval1 (node_ref_valid act a_idx av) ss sinput = Bits.ones 1.

    Local Notation NV szB n := (nval act a_idx ss sinput szB n).

    (* The source value of a DFG variable, at the variable's natural width. *)
    Definition src_get (sp: src_sys_state) (v: dvar) : bits_t (dfg_var_size ctx v) :=
      match v with
      | DFG_SVar sv => (fst sp).[sv]
      | DFG_OVar ov => (snd sp).[ov]
      end.

    (* A node's value is claimed under any path the run agrees with, at which
       its compiled validity reads ones: every sample it needs has latched. *)
    Definition vm_sem (vm: list (dvar * nid_t)) (sp: src_sys_state) : Prop :=
      forall v n pi, In (v, n) vm -> guard_holds pi ->
        eval1 (snd (compile_dfg_expr_at ctx bneeds pi
                      (length (graph (build_dfg ctx act))) a_idx
                      (build_dfg ctx act) n (sample_bufs act a_idx))) ss sinput
          = Bits.ones 1 ->
        NV (dfg_var_size ctx v) n = src_get sp v.

    Definition vm_frame (vm: list (dvar * nid_t)) (sp: src_sys_state) : Prop :=
      forall v, (forall n, ~ In (v, n) vm) -> src_get sp v = src_get sp0 v.

    Definition sem_inv (s: wst) (sp: src_sys_state) : Prop :=
      vm_sem (var_map s) sp /\ vm_frame (var_map s) sp.

    (* A freshly ensured variable node denotes the INITIAL source value. *)
    Lemma nval_fresh (s s': wst) (v: dvar) id :
      0 < length (graph s) ->
      ensure_var ctx v s = (id, s') -> wgmono s' F ->
      NV (dfg_var_size ctx v) id = src_get sp0 v.
    Proof.
      intros Hne Hev Hg. destruct v as [sv | ov]; cbn [src_get dfg_var_size].
      - rewrite (nval_fresh_svar act a_idx ss sinput F s s' sv id HF Hne Hev Hg).
        exact (Hss sv).
      - rewrite (nval_fresh_ovar act a_idx ss sinput F s s' ov id HF Hne Hev Hg).
        exact (Hoo ov).
    Qed.

    (* Same, for the node [read_var] hands back -- whether it emitted it or
       reused one that was already in the graph. *)
    Lemma nval_read (s s': wst) (v: dvar) id :
      0 < length (graph s) ->
      read_var ctx v s = (id, s') -> wgmono s' F ->
      NV (dfg_var_size ctx v) id = src_get sp0 v.
    Proof.
      intros Hne Her Hg.
      assert (Hat : var_node_at act v id).
      { destruct (read_var_cases v s id s' Her) as [[Hin [Hpos Hss']] | Hem].
        - subst s'. exact (in_var_node_at act F s v id HF Hin Hpos Hg).
        - exact (emit_var_node_at act F s s' v id HF Hne Hem Hg). }
      destruct v as [sv | ov]; cbn [src_get dfg_var_size].
      - rewrite (nval_var_svar act a_idx ss sinput sv id Hat). exact (Hss sv).
      - rewrite (nval_var_ovar act a_idx ss sinput ov id Hat). exact (Hoo ov).
    Qed.

    (* [get_var] returns a node denoting the CURRENT source value: either the
       binding existed, or the read node holds the initial value, which the
       frame condition makes the current one.  A read leaves [var_map] alone. *)
    Lemma get_var_sem (s s': wst) (v: dvar) id sp :
      0 < length (graph s) ->
      get_var ctx v s = (id, s') ->
      wgmono s' F ->
      sem_inv s sp ->
      sem_inv s' sp
      /\ (forall pi, guard_holds pi ->
            eval1 (snd (compile_dfg_expr_at ctx bneeds pi
                          (length (graph (build_dfg ctx act))) a_idx
                          (build_dfg ctx act) id (sample_bufs act a_idx))) ss sinput
              = Bits.ones 1 ->
            NV (dfg_var_size ctx v) id = src_get sp v).
    Proof.
      intros Hne Hgv Hg [Hsem Hfr].
      destruct (get_var_cases v s id s' Hgv) as [[Hin ->] | [Her Hnotin]].
      - split; [ split; assumption
               | intros pi Hgp Hv; exact (Hsem v id pi Hin Hgp Hv) ].
      - pose proof (nval_read s s' v id Hne Her Hg) as Hfresh.
        assert (Hval : NV (dfg_var_size ctx v) id = src_get sp v)
          by (rewrite Hfresh; symmetry; exact (Hfr v Hnotin)).
        pose proof (read_var_vmap v s id s' Her) as Hvm.
        split; [ | intros pi Hgp Hv; exact Hval ]. split.
        + intros v' n' pi Hin. rewrite Hvm in Hin. exact (Hsem v' n' pi Hin).
        + intros v' Hno. apply Hfr. intros n Hin. apply (Hno n).
          rewrite Hvm. exact Hin.
    Qed.
    (* Any builder step that does not touch [var_map] preserves [sem_inv]. *)
    Lemma sem_inv_vm (s s': wst) sp :
      var_map s' = var_map s -> sem_inv s sp -> sem_inv s' sp.
    Proof. intros Hvm [Ha Hb]. unfold sem_inv. rewrite Hvm. split; assumption. Qed.

    (* ================================================================= *)
    (* PHASE 3d, STEP 4: [dataflow_expr] is semantics-preserving.         *)
    (* The node it returns denotes, in the compiled scheduler state, the  *)
    (* source value of the expression in the CURRENT source state [sp].   *)
    (* ================================================================= *)
    Lemma dataflow_expr_sem :
      forall e szE (s s': wst) id sp,
        0 < length (graph s) -> winv s -> wvsz s -> gpos s ->
        dataflow_expr ctx e szE s = (id, s') ->
        wgmono s' F ->
        sem_inv s sp ->
        sem_inv s' sp
        /\ (forall pi, guard_holds pi ->
              eval1 (snd (compile_dfg_expr_at ctx bneeds pi
                            (length (graph (build_dfg ctx act))) a_idx
                            (build_dfg ctx act) id (sample_bufs act a_idx)))
                    ss sinput = Bits.ones 1 ->
              NV szE id = tf_eval_expr s_sz i_sz o_sz (szB := szE) e sp input).
    Proof.
      induction e as [ c | sv | iv | ov | uop e1 IH1
                     | bop e1 IH1 e2 IH2 | ec IHc et IHt ee IHe ];
        intros szE s s' id sp Hne Hinv Hvsz Hpos Hde Hg' Hsem.
      - (* tf_const *)
        cbn [dataflow_expr] in Hde.
        destruct (emitted_node_at act F s s' (DFG_Const c) szE id HF Hne Hde Hg')
          as [R1 [R2 [Rop _]]].
        split.
        + apply (sem_inv_vm s s'); [ exact (emit_vm _ _ _ _ _ Hde) | exact Hsem ].
        + unfold SchedulerSimulationBase.nval. rewrite (nre_const act a_idx id c R1 R2 Rop). reflexivity.
      - (* tf_svar *)
        cbn [dataflow_expr] in Hde. unfold bind in Hde.
        pose proof (get_var_sz (DFG_SVar sv) s Hinv Hvsz) as Hgv.
        destruct (get_var ctx (DFG_SVar sv) s) as [src_id s1] eqn:Egv.
        destruct Hgv as [Hg1 [Hn1 [Hp1 [Hq1 Hz1]]]].
        cbv beta in Hde.
        assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Hg1 Hne).
        destruct (Nat.eqb _ szE) eqn:Eb.
        + unfold ret in Hde. injection Hde as Hid Hs'. subst id. subst s'.
          destruct (get_var_sem s s1 (DFG_SVar sv) src_id sp Hne Egv Hg' Hsem)
            as [Hsem1 Hval].
          split; [ exact Hsem1 | ].
          apply Nat.eqb_eq in Eb. subst szE.
          intros pi Hgp Hv.
          rewrite (Hval pi Hgp Hv). cbn [src_get dfg_var_size tf_eval_expr].
          symmetry. apply convert_same.
        + assert (Hg1F : wgmono s1 F)
            by exact (wgmono_trans s1 s' F (emit_gmono _ _ _ _ _ Hde) Hg').
          destruct (get_var_sem s s1 (DFG_SVar sv) src_id sp Hne Egv Hg1F Hsem)
            as [Hsem1 Hval].
          destruct (emitted_node_at act F s1 s' (DFG_Resize src_id) szE id
                      HF Hne1 Hde Hg') as [R1 [R2 [Rop _]]].
          split.
          * apply (sem_inv_vm s1 s'); [ exact (emit_vm _ _ _ _ _ Hde) | exact Hsem1 ].
          * assert (Hsrcsz : sz (nth src_id (graph (build_dfg ctx act))
                                   {| nid := 0; op := DFG_Empty; sz := 0 |})
                             = dfg_var_size ctx (DFG_SVar sv)).
            { destruct (wsz_node_sz act src_id (dfg_var_size ctx (DFG_SVar sv))
                          (wsz_fwd act F src_id _ HF
                             (wsz_gmono s1 F src_id _ Hz1 Hg1F))) as [_ Hz]. exact Hz. }
            assert (Hsrcp : 1 <= src_id).
            { pose proof (get_var_pos (DFG_SVar sv) s Hpos) as Hp0.
              rewrite Egv in Hp0. exact (proj1 Hp0). }
            intros pi Hgp Hv.
            unfold SchedulerSimulationBase.nval in Hval |- *.
            rewrite (nre_resize act a_idx id src_id R1 R2 Rop), Hsrcsz.
            cbn [tf_eval_expr].
            rewrite (Hval pi Hgp (nrv_peel_resize act a_idx id src_id pi ss sinput
                                    Rop Hsrcp R2 Hv)).
            cbn [src_get dfg_var_size]. reflexivity.
      - (* tf_ivar *)
        cbn [dataflow_expr] in Hde. unfold bind in Hde.
        destruct (emit ctx (DFG_Input iv) szE s) as [src_id s1] eqn:Eem.
        cbv beta in Hde.
        assert (Hg1 : wgmono s s1) by exact (emit_gmono _ _ _ _ _ Eem).
        assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Hg1 Hne).
        destruct (Nat.eqb _ szE) eqn:Eb.
        + unfold ret in Hde. injection Hde as Hid Hs'. subst id. subst s'.
          destruct (emitted_node_at act F s s1 (DFG_Input iv) szE src_id
                      HF Hne Eem Hg') as [R1 [R2 [Rop _]]].
          split.
          * apply (sem_inv_vm s s1); [ exact (emit_vm _ _ _ _ _ Eem) | exact Hsem ].
          * unfold SchedulerSimulationBase.nval. rewrite (nre_input act a_idx src_id iv R1 R2 Rop).
            cbn [tf_eval_expr]. rewrite Hsin. reflexivity.
        + assert (Hg1F : wgmono s1 F)
            by exact (wgmono_trans s1 s' F (emit_gmono _ _ _ _ _ Hde) Hg').
          destruct (emitted_node_at act F s s1 (DFG_Input iv) szE src_id
                      HF Hne Eem Hg1F) as [R1 [R2 [Rop Rsz]]].
          destruct (emitted_node_at act F s1 s' (DFG_Resize src_id) szE id
                      HF Hne1 Hde Hg') as [Q1 [Q2 [Qop _]]].
          split.
          * apply (sem_inv_vm s s'); [ | exact Hsem ].
            rewrite (emit_vm _ _ _ _ _ Hde). exact (emit_vm _ _ _ _ _ Eem).
          * intros pi Hgp Hv.
            unfold SchedulerSimulationBase.nval.
            rewrite (nre_resize act a_idx id src_id Q1 Q2 Qop), Rsz.
            cbn [tf_eval_expr].
            rewrite (nre_input act a_idx src_id iv R1 R2 Rop).
            cbn [tf_eval_expr]. rewrite Hsin. apply convert_same.
      - (* tf_ovar *)
        cbn [dataflow_expr] in Hde. unfold bind in Hde.
        pose proof (get_var_sz (DFG_OVar ov) s Hinv Hvsz) as Hgv.
        destruct (get_var ctx (DFG_OVar ov) s) as [src_id s1] eqn:Egv.
        destruct Hgv as [Hg1 [Hn1 [Hp1 [Hq1 Hz1]]]].
        cbv beta in Hde.
        assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Hg1 Hne).
        destruct (Nat.eqb _ szE) eqn:Eb.
        + unfold ret in Hde. injection Hde as Hid Hs'. subst id. subst s'.
          destruct (get_var_sem s s1 (DFG_OVar ov) src_id sp Hne Egv Hg' Hsem)
            as [Hsem1 Hval].
          split; [ exact Hsem1 | ].
          apply Nat.eqb_eq in Eb. subst szE.
          intros pi Hgp Hv.
          rewrite (Hval pi Hgp Hv). cbn [src_get dfg_var_size tf_eval_expr].
          symmetry. apply convert_same.
        + assert (Hg1F : wgmono s1 F)
            by exact (wgmono_trans s1 s' F (emit_gmono _ _ _ _ _ Hde) Hg').
          destruct (get_var_sem s s1 (DFG_OVar ov) src_id sp Hne Egv Hg1F Hsem)
            as [Hsem1 Hval].
          destruct (emitted_node_at act F s1 s' (DFG_Resize src_id) szE id
                      HF Hne1 Hde Hg') as [R1 [R2 [Rop _]]].
          split.
          * apply (sem_inv_vm s1 s'); [ exact (emit_vm _ _ _ _ _ Hde) | exact Hsem1 ].
          * assert (Hsrcsz : sz (nth src_id (graph (build_dfg ctx act))
                                   {| nid := 0; op := DFG_Empty; sz := 0 |})
                             = dfg_var_size ctx (DFG_OVar ov)).
            { destruct (wsz_node_sz act src_id (dfg_var_size ctx (DFG_OVar ov))
                          (wsz_fwd act F src_id _ HF
                             (wsz_gmono s1 F src_id _ Hz1 Hg1F))) as [_ Hz]. exact Hz. }
            assert (Hsrcp : 1 <= src_id).
            { pose proof (get_var_pos (DFG_OVar ov) s Hpos) as Hp0.
              rewrite Egv in Hp0. exact (proj1 Hp0). }
            intros pi Hgp Hv.
            unfold SchedulerSimulationBase.nval in Hval |- *.
            rewrite (nre_resize act a_idx id src_id R1 R2 Rop), Hsrcsz.
            cbn [tf_eval_expr].
            rewrite (Hval pi Hgp (nrv_peel_resize act a_idx id src_id pi ss sinput
                                    Rop Hsrcp R2 Hv)).
            cbn [src_get dfg_var_size]. reflexivity.
      - (* tf_op1 *)
        destruct uop as [ | source_size ].
        + (* tf_not *)
          cbn [dataflow_expr] in Hde. unfold bind in Hde.
          pose proof (dataflow_expr_sz e1 szE s Hinv Hvsz) as Hsz1.
          destruct (dataflow_expr ctx e1 szE s) as [src_id s1] eqn:Ee1.
          destruct Hsz1 as [Hg1 [Hn1 [Hp1 [Hq1 Hz1]]]].
          cbv beta in Hde.
          assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Hg1 Hne).
          assert (Hg1F : wgmono s1 F)
            by exact (wgmono_trans s1 s' F (emit_gmono _ _ _ _ _ Hde) Hg').
          assert (Hposp : 1 <= src_id /\ gpos s1).
          { pose proof (dataflow_expr_pos e1 szE s Hpos) as Hq.
            rewrite Ee1 in Hq. exact Hq. }
          destruct Hposp as [Hsrcp Hpos1].
          destruct (IH1 szE s s1 src_id sp Hne Hinv Hvsz Hpos Ee1 Hg1F Hsem) as [Hsem1 Hv1].
          destruct (emitted_node_at act F s1 s' (DFG_Unary tf_not src_id) szE id
                      HF Hne1 Hde Hg') as [R1 [R2 [Rop _]]].
          split.
          * apply (sem_inv_vm s1 s'); [ exact (emit_vm _ _ _ _ _ Hde) | exact Hsem1 ].
          * intros pi Hgp Hv.
            unfold SchedulerSimulationBase.nval in Hv1 |- *.
            rewrite (nre_unary act a_idx id tf_not src_id R1 R2 Rop).
            cbn [tf_eval_expr].
            rewrite (Hv1 pi Hgp (nrv_peel_unary act a_idx id tf_not src_id pi ss sinput
                                   Rop Hsrcp R2 Hv)).
            reflexivity.
        + (* tf_resize *)
          cbn [dataflow_expr] in Hde. unfold bind in Hde.
          pose proof (dataflow_expr_sz e1 source_size s Hinv Hvsz) as Hsz1.
          destruct (dataflow_expr ctx e1 source_size s) as [src_id s1] eqn:Ee1.
          destruct Hsz1 as [Hg1 [Hn1 [Hp1 [Hq1 Hz1]]]].
          cbv beta in Hde.
          assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Hg1 Hne).
          assert (Hg1F : wgmono s1 F)
            by exact (wgmono_trans s1 s' F (emit_gmono _ _ _ _ _ Hde) Hg').
          assert (Hposp : 1 <= src_id /\ gpos s1).
          { pose proof (dataflow_expr_pos e1 source_size s Hpos) as Hq.
            rewrite Ee1 in Hq. exact Hq. }
          destruct Hposp as [Hsrcp Hpos1].
          destruct (IH1 source_size s s1 src_id sp Hne Hinv Hvsz Hpos Ee1 Hg1F Hsem)
            as [Hsem1 Hv1].
          destruct (emitted_node_at act F s1 s'
                      (DFG_Unary (tf_resize source_size) src_id) szE id
                      HF Hne1 Hde Hg') as [R1 [R2 [Rop _]]].
          split.
          * apply (sem_inv_vm s1 s'); [ exact (emit_vm _ _ _ _ _ Hde) | exact Hsem1 ].
          * intros pi Hgp Hv.
            unfold SchedulerSimulationBase.nval in Hv1 |- *.
            rewrite (nre_unary act a_idx id (tf_resize source_size) src_id R1 R2 Rop).
            cbn [tf_eval_expr].
            rewrite (Hv1 pi Hgp (nrv_peel_unary act a_idx id (tf_resize source_size)
                                   src_id pi ss sinput Rop Hsrcp R2 Hv)).
            reflexivity.
      - (* tf_op2 *)
        destruct bop as [ | | | | | | szC cop | hz lz ].
        1-6: (cbn [dataflow_expr] in Hde; unfold bind in Hde;
              pose proof (dataflow_expr_sz e1 szE s Hinv Hvsz) as Hsz1;
              destruct (dataflow_expr ctx e1 szE s) as [id1 s1] eqn:Ee1;
              destruct Hsz1 as [Hg1 [Hn1 [Hp1 [Hq1 Hz1]]]];
              pose proof (dataflow_expr_sz e2 szE s1 Hp1 Hq1) as Hsz2;
              destruct (dataflow_expr ctx e2 szE s1) as [id2 s2] eqn:Ee2;
              destruct Hsz2 as [Hg2 [Hn2 [Hp2 [Hq2 Hz2]]]];
              cbv beta in Hde;
              assert (Hpp1 : 1 <= id1 /\ gpos s1)
                by (pose proof (dataflow_expr_pos e1 szE s Hpos) as Hq;
                    rewrite Ee1 in Hq; exact Hq);
              destruct Hpp1 as [Hid1p Hpos1];
              assert (Hpp2 : 1 <= id2 /\ gpos s2)
                by (pose proof (dataflow_expr_pos e2 szE s1 Hpos1) as Hq;
                    rewrite Ee2 in Hq; exact Hq);
              destruct Hpp2 as [Hid2p Hpos2];
              assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Hg1 Hne);
              assert (Hne2 : 0 < length (graph s2)) by exact (gne_gmono s1 s2 Hg2 Hne1);
              assert (Hg2F : wgmono s2 F)
                by exact (wgmono_trans s2 s' F (emit_gmono _ _ _ _ _ Hde) Hg');
              assert (Hg1F : wgmono s1 F) by exact (wgmono_trans s1 s2 F Hg2 Hg2F);
              destruct (IH1 szE s s1 id1 sp Hne Hinv Hvsz Hpos Ee1 Hg1F Hsem)
                as [Hsem1 Hv1];
              destruct (IH2 szE s1 s2 id2 sp Hne1 Hp1 Hq1 Hpos1 Ee2 Hg2F Hsem1)
                as [Hsem2 Hv2];
              destruct (emitted_node_at act F s2 s' _ szE id HF Hne2 Hde Hg')
                as [R1 [R2 [Rop _]]];
              split;
              [ apply (sem_inv_vm s2 s');
                [ exact (emit_vm _ _ _ _ _ Hde) | exact Hsem2 ]
              | intros pi Hgp Hv;
                destruct (nrv_peel_binary act a_idx id _ id1 id2 pi ss sinput
                            Rop Hid1p Hid2p R2 Hv) as [Hb1 Hb2];
                unfold SchedulerSimulationBase.nval in Hv1, Hv2 |- *;
                rewrite (nre_binary act a_idx id _ id1 id2 R1 R2 Rop);
                cbn [tf_eval_expr];
                rewrite (Hv1 pi Hgp Hb1), (Hv2 pi Hgp Hb2); reflexivity ]).
        (* tf_cmp: both operands are compiled at the COMPARISON width szC. *)
        cbn [dataflow_expr] in Hde. unfold bind in Hde.
        pose proof (dataflow_expr_sz e1 szC s Hinv Hvsz) as Hsz1.
        destruct (dataflow_expr ctx e1 szC s) as [id1 s1] eqn:Ee1.
        destruct Hsz1 as [Hg1 [Hn1 [Hp1 [Hq1 Hz1]]]].
        pose proof (dataflow_expr_sz e2 szC s1 Hp1 Hq1) as Hsz2.
        destruct (dataflow_expr ctx e2 szC s1) as [id2 s2] eqn:Ee2.
        destruct Hsz2 as [Hg2 [Hn2 [Hp2 [Hq2 Hz2]]]].
        cbv beta in Hde.
        assert (Hpp1 : 1 <= id1 /\ gpos s1).
        { pose proof (dataflow_expr_pos e1 szC s Hpos) as Hq.
          rewrite Ee1 in Hq. exact Hq. }
        destruct Hpp1 as [Hid1p Hpos1].
        assert (Hpp2 : 1 <= id2 /\ gpos s2).
        { pose proof (dataflow_expr_pos e2 szC s1 Hpos1) as Hq.
          rewrite Ee2 in Hq. exact Hq. }
        destruct Hpp2 as [Hid2p Hpos2].
        assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Hg1 Hne).
        assert (Hne2 : 0 < length (graph s2)) by exact (gne_gmono s1 s2 Hg2 Hne1).
        assert (Hg2F : wgmono s2 F)
          by exact (wgmono_trans s2 s' F (emit_gmono _ _ _ _ _ Hde) Hg').
        assert (Hg1F : wgmono s1 F) by exact (wgmono_trans s1 s2 F Hg2 Hg2F).
        destruct (IH1 szC s s1 id1 sp Hne Hinv Hvsz Hpos Ee1 Hg1F Hsem) as [Hsem1 Hv1].
        destruct (IH2 szC s1 s2 id2 sp Hne1 Hp1 Hq1 Hpos1 Ee2 Hg2F Hsem1) as [Hsem2 Hv2].
        destruct (emitted_node_at act F s2 s' (DFG_Binary (tf_cmp szC cop) id1 id2)
                    szE id HF Hne2 Hde Hg') as [R1 [R2 [Rop _]]].
        split;
        [ apply (sem_inv_vm s2 s'); [ exact (emit_vm _ _ _ _ _ Hde) | exact Hsem2 ]
        | intros pi Hgp Hv;
          destruct (nrv_peel_binary act a_idx id (tf_cmp szC cop) id1 id2 pi ss sinput
                      Rop Hid1p Hid2p R2 Hv) as [Hb1 Hb2];
          unfold SchedulerSimulationBase.nval in Hv1, Hv2 |- *;
          rewrite (nre_binary act a_idx id (tf_cmp szC cop) id1 id2 R1 R2 Rop);
          cbn [tf_eval_expr];
          rewrite (Hv1 pi Hgp Hb1), (Hv2 pi Hgp Hb2); reflexivity ].
        (* tf_concat: e1 is compiled at hz and e2 at lz.  Every other binary op
           compiles both operands at ONE width, which is why this case cannot
           share the tactic above. *)
        cbn [dataflow_expr] in Hde. unfold bind in Hde.
        pose proof (dataflow_expr_sz e1 hz s Hinv Hvsz) as Hsz1.
        destruct (dataflow_expr ctx e1 hz s) as [id1 s1] eqn:Ee1.
        destruct Hsz1 as [Hg1 [Hn1 [Hp1 [Hq1 Hz1]]]].
        pose proof (dataflow_expr_sz e2 lz s1 Hp1 Hq1) as Hsz2.
        destruct (dataflow_expr ctx e2 lz s1) as [id2 s2] eqn:Ee2.
        destruct Hsz2 as [Hg2 [Hn2 [Hp2 [Hq2 Hz2]]]].
        cbv beta in Hde.
        assert (Hpp1 : 1 <= id1 /\ gpos s1).
        { pose proof (dataflow_expr_pos e1 hz s Hpos) as Hq.
          rewrite Ee1 in Hq. exact Hq. }
        destruct Hpp1 as [Hid1p Hpos1].
        assert (Hpp2 : 1 <= id2 /\ gpos s2).
        { pose proof (dataflow_expr_pos e2 lz s1 Hpos1) as Hq.
          rewrite Ee2 in Hq. exact Hq. }
        destruct Hpp2 as [Hid2p Hpos2].
        assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Hg1 Hne).
        assert (Hne2 : 0 < length (graph s2)) by exact (gne_gmono s1 s2 Hg2 Hne1).
        assert (Hg2F : wgmono s2 F)
          by exact (wgmono_trans s2 s' F (emit_gmono _ _ _ _ _ Hde) Hg').
        assert (Hg1F : wgmono s1 F) by exact (wgmono_trans s1 s2 F Hg2 Hg2F).
        destruct (IH1 hz s s1 id1 sp Hne Hinv Hvsz Hpos Ee1 Hg1F Hsem) as [Hsem1 Hv1].
        destruct (IH2 lz s1 s2 id2 sp Hne1 Hp1 Hq1 Hpos1 Ee2 Hg2F Hsem1) as [Hsem2 Hv2].
        destruct (emitted_node_at act F s2 s' (DFG_Binary (tf_concat hz lz) id1 id2)
                    szE id HF Hne2 Hde Hg') as [R1 [R2 [Rop _]]].
        split;
        [ apply (sem_inv_vm s2 s'); [ exact (emit_vm _ _ _ _ _ Hde) | exact Hsem2 ]
        | intros pi Hgp Hv;
          destruct (nrv_peel_binary act a_idx id (tf_concat hz lz) id1 id2 pi ss sinput
                      Rop Hid1p Hid2p R2 Hv) as [Hb1 Hb2];
          unfold SchedulerSimulationBase.nval in Hv1, Hv2 |- *;
          rewrite (nre_binary act a_idx id (tf_concat hz lz) id1 id2 R1 R2 Rop);
          cbn [tf_eval_expr];
          rewrite (Hv1 pi Hgp Hb1), (Hv2 pi Hgp Hb2); reflexivity ].
      - (* tf_expr_if *)
        cbn [dataflow_expr] in Hde. unfold bind in Hde.
        pose proof (dataflow_expr_sz ec 1 s Hinv Hvsz) as HszC.
        destruct (dataflow_expr ctx ec 1 s) as [cid s1] eqn:Ec.
        destruct HszC as [Hg1 [Hn1 [Hp1 [Hq1 Hz1]]]].
        pose proof (dataflow_expr_sz et szE s1 Hp1 Hq1) as HszT.
        destruct (dataflow_expr ctx et szE s1) as [tid s2] eqn:Et.
        destruct HszT as [Hg2 [Hn2 [Hp2 [Hq2 Hz2]]]].
        pose proof (dataflow_expr_sz ee szE s2 Hp2 Hq2) as HszEl.
        destruct (dataflow_expr ctx ee szE s2) as [eid s3] eqn:El.
        destruct HszEl as [Hg3 [Hn3 [Hp3 [Hq3 Hz3]]]].
        cbv beta in Hde.
        assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Hg1 Hne).
        assert (Hne2 : 0 < length (graph s2)) by exact (gne_gmono s1 s2 Hg2 Hne1).
        assert (Hne3 : 0 < length (graph s3)) by exact (gne_gmono s2 s3 Hg3 Hne2).
        assert (Hg3F : wgmono s3 F)
          by exact (wgmono_trans s3 s' F (emit_gmono _ _ _ _ _ Hde) Hg').
        assert (Hg2F : wgmono s2 F) by exact (wgmono_trans s2 s3 F Hg3 Hg3F).
        assert (Hg1F : wgmono s1 F) by exact (wgmono_trans s1 s2 F Hg2 Hg2F).
        assert (Hppc : 1 <= cid /\ gpos s1).
        { pose proof (dataflow_expr_pos ec 1 s Hpos) as Hq. rewrite Ec in Hq. exact Hq. }
        destruct Hppc as [Hcidp Hpos1].
        assert (Hppt : 1 <= tid /\ gpos s2).
        { pose proof (dataflow_expr_pos et szE s1 Hpos1) as Hq. rewrite Et in Hq. exact Hq. }
        destruct Hppt as [Htidp Hpos2].
        assert (Hppe : 1 <= eid /\ gpos s3).
        { pose proof (dataflow_expr_pos ee szE s2 Hpos2) as Hq. rewrite El in Hq. exact Hq. }
        destruct Hppe as [Heidp Hpos3].
        destruct (IHc 1 s s1 cid sp Hne Hinv Hvsz Hpos Ec Hg1F Hsem) as [Hsem1 Hvc].
        destruct (IHt szE s1 s2 tid sp Hne1 Hp1 Hq1 Hpos1 Et Hg2F Hsem1) as [Hsem2 Hvt].
        destruct (IHe szE s2 s3 eid sp Hne2 Hp2 Hq2 Hpos2 El Hg3F Hsem2) as [Hsem3 Hve].
        destruct (emitted_node_at act F s3 s' (DFG_Phi cid tid eid) szE id
                    HF Hne3 Hde Hg') as [R1 [R2 [Rop _]]].
        split.
        + apply (sem_inv_vm s3 s'); [ exact (emit_vm _ _ _ _ _ Hde) | exact Hsem3 ].
        + intros pi Hgp Hv.
          unfold SchedulerSimulationBase.nval in Hvc, Hvt, Hve |- *.
          rewrite (nre_phi act a_idx id cid tid eid R1 R2 Rop).
          destruct (phi_crit (get_tainted ctx (build_dfg ctx act))
                      (decl_facts ctx (build_dfg ctx act)) cid pi) eqn:Ecrit.
          * destruct (nrv_peel_phi_crit act a_idx id cid tid eid pi ss sinput
                        Rop Ecrit Hcidp Htidp Heidp R2 Hv) as [Hcv [Htv Hev]].
            cbn [tf_eval_expr].
            rewrite (Hvc pi Hgp Hcv), (Hvt pi Hgp Htv), (Hve pi Hgp Hev).
            reflexivity.
          * destruct (nrv_peel_phi_sel act a_idx id cid tid eid pi ss sinput
                        Rop Ecrit Hcidp Htidp Heidp R2 Hv) as [Hcv [Hthen Helse]].
            pose proof (Hvc pi Hgp Hcv) as Hc0.
            cbn [tf_eval_expr]. rewrite <- Hc0.
            match goal with
            | |- context [ @beq_dec ?T ?E ?x ?z ] => destruct (@beq_dec T E x z) eqn:Eb
            end.
            -- assert (Hz : tf_eval_expr ss_sz si_sz oo_sz (szB := 1)
                              (node_ref_expr act a_idx cid) ss sinput = Bits.zero)
                 by exact (proj1 (beq_dec_iff _ _ _) Eb).
               assert (Hgpe : guard_holds ((cid, false) :: pi)).
               { intros nn bb Hin. destruct Hin as [Heq | Hin].
                 - injection Heq as H1 H2; subst.
                   split; [ intro Hc; discriminate Hc | intros _; exact Hz ].
                 - exact (Hgp nn bb Hin). }
               exact (Hve ((cid, false) :: pi) Hgpe (Helse Hz)).
            -- assert (Hnz : tf_eval_expr ss_sz si_sz oo_sz (szB := 1)
                               (node_ref_expr act a_idx cid) ss sinput <> Bits.zero).
               { intro Hc. rewrite Hc, beq_dec_refl in Eb. discriminate Eb. }
               assert (Hgpt : guard_holds ((cid, true) :: pi)).
               { intros nn bb Hin. destruct Hin as [Heq | Hin].
                 - injection Heq as H1 H2; subst.
                   split; [ intros _; exact Hnz | intro Hc; discriminate Hc ].
                 - exact (Hgp nn bb Hin). }
               exact (Hvt ((cid, true) :: pi) Hgpt (Hthen Hnz)).
    Qed.

    (* The branch the run takes pins the condition's reference value. *)
    Lemma cond_of_Hb (cond_id: nid_t) (b: bool) :
      (forall szB E1 E2,
         tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
           (tf_expr_if (node_ref_expr act a_idx cond_id) E1 E2) ss sinput
         = if b then tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E2 ss sinput
                else tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E1 ss sinput) ->
      (b = true  -> eval1 (node_ref_expr act a_idx cond_id) ss sinput = Bits.zero) /\
      (b = false -> eval1 (node_ref_expr act a_idx cond_id) ss sinput <> Bits.zero).
    Proof.
      intro Hb.
      pose proof (Hb 1 (tf_const 0) (tf_const 1)) as H.
      cbn [tf_eval_expr] in H.
      split; intro Hbv; subst b; cbn beta iota in H;
        match type of H with
        | context [ @beq_dec ?T ?E ?x ?z ] => destruct (@beq_dec T E x z) eqn:Hd
        end.
      - exact (proj1 (beq_dec_iff _ _ _) Hd).
      - exfalso. vm_compute in H. discriminate H.
      - exfalso. vm_compute in H. discriminate H.
      - intro Hc. rewrite Hc in Hd. rewrite beq_dec_refl in Hd. discriminate Hd.
    Qed.
    (* From a phi's validity, the branch the run selects reads valid -- at the
       path that branch is compiled under. *)
    Lemma phi_branch_valid (cond_id: nid_t) (b: bool) phi tv ev pi :
      (forall szB E1 E2,
         tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
           (tf_expr_if (node_ref_expr act a_idx cond_id) E1 E2) ss sinput
         = if b then tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E2 ss sinput
                else tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E1 ss sinput) ->
      node_op act phi = DFG_Phi cond_id tv ev ->
      1 <= cond_id -> 1 <= tv -> 1 <= ev ->
      phi < length (graph (build_dfg ctx act)) ->
      guard_holds pi ->
      rvalid act a_idx pi phi ss sinput = Bits.ones 1 ->
      rvalid act a_idx pi cond_id ss sinput = Bits.ones 1
      /\ (b = false ->
         exists pi', guard_holds pi'
                     /\ rvalid act a_idx pi' tv ss sinput = Bits.ones 1)
      /\ (b = true ->
         exists pi', guard_holds pi'
                     /\ rvalid act a_idx pi' ev ss sinput = Bits.ones 1).
    Proof.
      intros Hb Hop Hc1 Ht1 He1 Hplen Hgp Hv.
      destruct (cond_of_Hb cond_id b Hb) as [Hbt Hbf].
      destruct (phi_crit (get_tainted ctx (build_dfg ctx act))
                  (decl_facts ctx (build_dfg ctx act)) cond_id pi) eqn:Ecrit.
      - destruct (nrv_peel_phi_crit act a_idx phi cond_id tv ev pi ss sinput
                    Hop Ecrit Hc1 Ht1 He1 Hplen Hv) as [Hcv [Htv Hev]].
        split; [ exact Hcv |].
        split; intros _; exists pi; split; assumption.
      - destruct (nrv_peel_phi_sel act a_idx phi cond_id tv ev pi ss sinput
                    Hop Ecrit Hc1 Ht1 He1 Hplen Hv) as [Hcv [Hthen Helse]].
        split; [ exact Hcv |].
        split.
        + intro Hbv. exists ((cond_id, true) :: pi). split.
          * intros nn bb Hin. destruct Hin as [Heq | Hin].
            -- injection Heq as H1 H2; subst nn; subst bb.
               split; [ intros _; exact (Hbf Hbv) | intro Hc; discriminate Hc ].
            -- exact (Hgp nn bb Hin).
          * exact (Hthen (Hbf Hbv)).
        + intro Hbv. exists ((cond_id, false) :: pi). split.
          * intros nn bb Hin. destruct Hin as [Heq | Hin].
            -- injection Heq as H1 H2; subst nn; subst bb.
               split; [ intro Hc; discriminate Hc | intros _; exact (Hbt Hbv) ].
            -- exact (Hgp nn bb Hin).
          * exact (Helse (Hbt Hbv)).
    Qed.

    (* ================================================================= *)
    (* PHASE 3d, STEP 5: the map merger is semantics-preserving.          *)
    (* [b] is the (abstract) branch selector: [true] means the ELSE side  *)
    (* was taken, matching [tf_expr_if]'s and [tf_ops_updates]'s          *)
    (* "cond = 0 -> else" convention.  Keeping it abstract avoids ever    *)
    (* writing [beq_dec] in a statement.                                  *)
    (* ================================================================= *)
    Lemma merge_key_sem (cond_id: nid_t) (k: dvar) vt_opt ve_opt
          (s s1: wst) res (b: bool) (spt spe spf: src_sys_state) :
      0 < length (graph s) -> gpos s ->
      merge_key ctx cond_id k vt_opt ve_opt s = (res, s1) ->
      wgmono s1 F ->
      (* [b] is the HARDWARE selector, so this is unconditional *)
      (forall szB E1 E2,
         tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
           (tf_expr_if (node_ref_expr act a_idx cond_id) E1 E2) ss sinput
         = if b then tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E2 ss sinput
                else tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E1 ss sinput) ->
      (* the source picks the same arm exactly where the condition reads valid *)
      (forall pi, guard_holds pi ->
         rvalid act a_idx pi cond_id ss sinput = Bits.ones 1 ->
         forall kk, src_get spf kk = if b then src_get spe kk else src_get spt kk) ->
      (* a key the two arms leave at ONE node carries no condition, and both
         arms hold its entry value *)
      (forall id, vt_opt = Some id -> ve_opt = Some id ->
         forall pi, guard_holds pi ->
           rvalid act a_idx pi id ss sinput = Bits.ones 1 ->
           src_get spf k = (if b then src_get spe k else src_get spt k)) ->
      1 <= cond_id ->
      (forall vt, vt_opt = Some vt -> 1 <= vt) ->
      (forall ve, ve_opt = Some ve -> 1 <= ve) ->
      (* only the SELECTED arm: an untaken arm.s call latches the wire the
         other arm drove, so its entries say nothing *)
      (b = false -> forall vt, vt_opt = Some vt ->
         forall pi, guard_holds pi ->
           rvalid act a_idx pi vt ss sinput = Bits.ones 1 ->
           NV (dfg_var_size ctx k) vt = src_get spt k) ->
      (b = true  -> forall ve, ve_opt = Some ve ->
         forall pi, guard_holds pi ->
           rvalid act a_idx pi ve ss sinput = Bits.ones 1 ->
           NV (dfg_var_size ctx k) ve = src_get spe k) ->
      (b = false -> vt_opt = None -> src_get spt k = src_get sp0 k) ->
      (b = true  -> ve_opt = None -> src_get spe k = src_get sp0 k) ->
      forall fid pi, res = Some fid -> guard_holds pi ->
        rvalid act a_idx pi fid ss sinput = Bits.ones 1 ->
        NV (dfg_var_size ctx k) fid = src_get spf k.
    Proof.
      intros Hne Hpos Hrun Hg1 Hb Hsel Hsh Hc1 Hvtp Hvep Hvt Hve Hvtn Hven fid pi Hfid Hgp Hv.
      unfold merge_key in Hrun.
      destruct vt_opt as [vt |]; destruct ve_opt as [ve |].
      - destruct (eq_dec vt ve) as [Heq | Hnee].
        + unfold ret in Hrun. injection Hrun as Hr Hs. subst res. subst s1.
          injection Hfid as Hf. subst fid. subst ve.
          rewrite (Hsh vt eq_refl eq_refl pi Hgp Hv). destruct b.
          * exact (Hve eq_refl vt eq_refl pi Hgp Hv).
          * exact (Hvt eq_refl vt eq_refl pi Hgp Hv).
        + destruct (emit ctx (DFG_Phi cond_id vt ve) (dfg_var_size ctx k) s)
            as [phi s2] eqn:Ee.
          rewrite (bind_red (emit ctx (DFG_Phi cond_id vt ve) (dfg_var_size ctx k))
                     _ s _ _ Ee) in Hrun.
          unfold ret in Hrun. injection Hrun as Hr Hs. subst res. subst s1.
          injection Hfid as Hf. subst fid.
          destruct (emitted_node_at act F s s2 (DFG_Phi cond_id vt ve)
                      (dfg_var_size ctx k) phi HF Hne Ee Hg1) as [R1 [R2 [Rop _]]].
          destruct (phi_branch_valid cond_id b phi vt ve pi Hb Rop Hc1
                      (Hvtp vt eq_refl) (Hvep ve eq_refl) R2 Hgp Hv) as [Hcv [Hbt Hbe]].
          unfold SchedulerSimulationBase.nval.
          rewrite (nre_phi act a_idx phi cond_id vt ve R1 R2 Rop).
          rewrite Hb, (Hsel pi Hgp Hcv). destruct b.
          * destruct (Hbe eq_refl) as [pi' [Hgp' Hv']].
            exact (Hve eq_refl ve eq_refl pi' Hgp' Hv').
          * destruct (Hbt eq_refl) as [pi' [Hgp' Hv']].
            exact (Hvt eq_refl vt eq_refl pi' Hgp' Hv').
      - destruct (ensure_var ctx k s) as [ve0 sA] eqn:Ev.
        rewrite (bind_red (ensure_var ctx k) _ s _ _ Ev) in Hrun.
        destruct (emit ctx (DFG_Phi cond_id vt ve0) (dfg_var_size ctx k) sA)
          as [phi s2] eqn:Ee.
        rewrite (bind_red (emit ctx (DFG_Phi cond_id vt ve0) (dfg_var_size ctx k))
                   _ sA _ _ Ee) in Hrun.
        unfold ret in Hrun. injection Hrun as Hr Hs. subst res. subst s1.
        injection Hfid as Hf. subst fid.
        assert (HgA : wgmono sA F)
          by exact (wgmono_trans sA s2 F (emit_gmono _ _ _ _ _ Ee) Hg1).
        assert (HneA : 0 < length (graph sA))
          by exact (gne_gmono s sA (ensure_var_gmono k s ve0 sA Ev) Hne).
        assert (Hve0p : 1 <= ve0).
        { pose proof (ensure_var_pos k s Hpos) as Hq. rewrite Ev in Hq.
          exact (proj1 Hq). }
        destruct (emitted_node_at act F sA s2 (DFG_Phi cond_id vt ve0)
                    (dfg_var_size ctx k) phi HF HneA Ee Hg1) as [R1 [R2 [Rop _]]].
        destruct (phi_branch_valid cond_id b phi vt ve0 pi Hb Rop Hc1
                    (Hvtp vt eq_refl) Hve0p R2 Hgp Hv) as [Hcv [Hbt _]].
        assert (Hve0 : b = true -> NV (dfg_var_size ctx k) ve0 = src_get spe k).
        { intro Hbt2. rewrite (nval_fresh s sA k ve0 Hne Ev HgA). symmetry.
          exact (Hven Hbt2 eq_refl). }
        unfold SchedulerSimulationBase.nval.
        rewrite (nre_phi act a_idx phi cond_id vt ve0 R1 R2 Rop).
        rewrite Hb, (Hsel pi Hgp Hcv). destruct b.
        + exact (Hve0 eq_refl).
        + destruct (Hbt eq_refl) as [pi' [Hgp' Hv']].
          exact (Hvt eq_refl vt eq_refl pi' Hgp' Hv').
      - destruct (ensure_var ctx k s) as [vt0 sA] eqn:Ev.
        rewrite (bind_red (ensure_var ctx k) _ s _ _ Ev) in Hrun.
        destruct (emit ctx (DFG_Phi cond_id vt0 ve) (dfg_var_size ctx k) sA)
          as [phi s2] eqn:Ee.
        rewrite (bind_red (emit ctx (DFG_Phi cond_id vt0 ve) (dfg_var_size ctx k))
                   _ sA _ _ Ee) in Hrun.
        unfold ret in Hrun. injection Hrun as Hr Hs. subst res. subst s1.
        injection Hfid as Hf. subst fid.
        assert (HgA : wgmono sA F)
          by exact (wgmono_trans sA s2 F (emit_gmono _ _ _ _ _ Ee) Hg1).
        assert (HneA : 0 < length (graph sA))
          by exact (gne_gmono s sA (ensure_var_gmono k s vt0 sA Ev) Hne).
        assert (Hvt0p : 1 <= vt0).
        { pose proof (ensure_var_pos k s Hpos) as Hq. rewrite Ev in Hq.
          exact (proj1 Hq). }
        destruct (emitted_node_at act F sA s2 (DFG_Phi cond_id vt0 ve)
                    (dfg_var_size ctx k) phi HF HneA Ee Hg1) as [R1 [R2 [Rop _]]].
        destruct (phi_branch_valid cond_id b phi vt0 ve pi Hb Rop Hc1
                    Hvt0p (Hvep ve eq_refl) R2 Hgp Hv) as [Hcv [_ Hbe]].
        assert (Hvt0 : b = false -> NV (dfg_var_size ctx k) vt0 = src_get spt k).
        { intro Hbf. rewrite (nval_fresh s sA k vt0 Hne Ev HgA). symmetry.
          exact (Hvtn Hbf eq_refl). }
        unfold SchedulerSimulationBase.nval.
        rewrite (nre_phi act a_idx phi cond_id vt0 ve R1 R2 Rop).
        rewrite Hb, (Hsel pi Hgp Hcv). destruct b.
        + destruct (Hbe eq_refl) as [pi' [Hgp' Hv']].
          exact (Hve eq_refl ve eq_refl pi' Hgp' Hv').
        + exact (Hvt0 eq_refl).
      - unfold ret in Hrun. injection Hrun as Hr Hs. subst res. discriminate Hfid.
    Qed.

    Lemma merge_loop_sem (cond_id: nid_t) mt me (b: bool) (spt spe spf: src_sys_state) :
      (forall szB E1 E2,
         tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
           (tf_expr_if (node_ref_expr act a_idx cond_id) E1 E2) ss sinput
         = if b then tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E2 ss sinput
                else tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E1 ss sinput) ->
      (forall pi, guard_holds pi ->
         rvalid act a_idx pi cond_id ss sinput = Bits.ones 1 ->
         forall kk, src_get spf kk = if b then src_get spe kk else src_get spt kk) ->
      (forall kk (id: nid_t), In (kk, id) mt -> In (kk, id) me ->
         forall pi, guard_holds pi ->
           rvalid act a_idx pi id ss sinput = Bits.ones 1 ->
           src_get spf kk = (if b then src_get spe kk else src_get spt kk)) ->
      1 <= cond_id ->
      (forall kk (id: nid_t), In (kk, id) mt -> 1 <= id) ->
      (forall kk (id: nid_t), In (kk, id) me -> 1 <= id) ->
      (b = false -> vm_sem mt spt) -> (b = false -> vm_frame mt spt) ->
      (b = true  -> vm_sem me spe) -> (b = true  -> vm_frame me spe) ->
      forall keys acc (s: wst) fin s',
        0 < length (graph s) -> gpos s ->
        (forall kk (id: nid_t), In (kk, id) acc -> 1 <= id) ->
        merge_loop ctx cond_id mt me keys acc s = (fin, s') ->
        wgmono s' F ->
        vm_sem acc spf ->
        vm_sem fin spf.
    Proof.
      intros Hb Hsel Hsh Hc1 Hmtp Hmep Hmt Hmtf Hme Hmef.
      induction keys as [| [k0 v0] rest IH];
        intros acc s fin s' Hne Hpos Haccp Hrun Hg' Hacc.
      - simpl in Hrun. unfold ret in Hrun. injection Hrun as Hf Hs.
        subst fin. exact Hacc.
      - simpl in Hrun.
        destruct (BitsToLists.list_assoc acc k0) as [existing |] eqn:Ek.
        + exact (IH acc s fin s' Hne Hpos Haccp Hrun Hg' Hacc).
        + unfold bind in Hrun. cbv beta in Hrun.
          destruct (merge_key ctx cond_id k0 (BitsToLists.list_assoc mt k0)
                      (BitsToLists.list_assoc me k0) s) as [res_opt s1] eqn:Emk.
          cbv beta iota in Hrun.
          destruct (merge_key_basic cond_id k0 _ _ s res_opt s1 Emk) as [Hgk _].
          assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Hgk Hne).
          match type of Emk with
          | merge_key ctx cond_id k0 ?vo ?eo s = _ =>
              assert (Hmtk : forall (vt: nid_t), vo = Some vt -> 1 <= vt)
                by (intros vt Hv; apply wla_in in Hv; exact (Hmtp k0 vt Hv));
              assert (Hmek : forall (ve: nid_t), eo = Some ve -> 1 <= ve)
                by (intros ve Hv; apply wla_in in Hv; exact (Hmep k0 ve Hv))
          end.
          destruct (merge_key_pos cond_id k0 _ _ s res_opt s1 Emk Hpos Hc1 Hmtk Hmek)
            as [Hpos1 Hresp].
          destruct res_opt as [final_id |].
          * assert (Hg1F : wgmono s1 F)
              by exact (wgmono_trans s1 s' F
                          (merge_loop_gmono cond_id mt me rest
                             ((k0, final_id) :: acc) s1 fin s' Hrun) Hg').
            assert (Hval : forall pi, guard_holds pi ->
                      rvalid act a_idx pi final_id ss sinput = Bits.ones 1 ->
                      NV (dfg_var_size ctx k0) final_id = src_get spf k0).
            { intros pi Hgp Hv.
              refine (merge_key_sem cond_id k0 _ _ s s1 (Some final_id) b spt spe spf
                        Hne Hpos Emk Hg1F Hb Hsel _ Hc1 Hmtk Hmek
                        _ _ _ _ final_id pi eq_refl Hgp Hv).
              - intros id Hvo Heo pi2 Hgp2 Hval2.
                apply wla_in in Hvo. apply wla_in in Heo.
                exact (Hsh k0 id Hvo Heo pi2 Hgp2 Hval2).
              - intros Hbf vt Hv2 pi2 Hgp2 Hval2. apply wla_in in Hv2.
                exact (Hmt Hbf k0 vt pi2 Hv2 Hgp2 Hval2).
              - intros Hbt ve Hv2 pi2 Hgp2 Hval2. apply wla_in in Hv2.
                exact (Hme Hbt k0 ve pi2 Hv2 Hgp2 Hval2).
              - intros Hbf Hn. apply (Hmtf Hbf). intros n Hin.
                exact (list_assoc_None_notin mt k0 Hn n Hin).
              - intros Hbt Hn. apply (Hmef Hbt). intros n Hin.
                exact (list_assoc_None_notin me k0 Hn n Hin). }
            apply (IH ((k0, final_id) :: acc) s1 fin s' Hne1 Hpos1).
            -- intros kk id Hin. destruct Hin as [Heq | Hin].
               ++ injection Heq as Hk Hn. subst id. exact (Hresp final_id eq_refl).
               ++ exact (Haccp kk id Hin).
            -- exact Hrun.
            -- exact Hg'.
            -- intros v n pi Hin Hgp Hv. destruct Hin as [Heq | Hin].
               ++ injection Heq as Hk Hn. subst v. subst n. exact (Hval pi Hgp Hv).
               ++ exact (Hacc v n pi Hin Hgp Hv).
          * assert (Hg1F : wgmono s1 F)
              by exact (wgmono_trans s1 s' F
                          (merge_loop_gmono cond_id mt me rest acc s1 fin s' Hrun) Hg').
            exact (IH acc s1 fin s' Hne1 Hpos1 Haccp Hrun Hg' Hacc).
    Qed.

    Lemma merge_maps_sem (cond_id: nid_t) mo mt me (b: bool)
          (spt spe spf: src_sys_state) (s: wst) fin s' :
      (forall szB E1 E2,
         tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
           (tf_expr_if (node_ref_expr act a_idx cond_id) E1 E2) ss sinput
         = if b then tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E2 ss sinput
                else tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E1 ss sinput) ->
      (forall pi, guard_holds pi ->
         rvalid act a_idx pi cond_id ss sinput = Bits.ones 1 ->
         forall kk, src_get spf kk = if b then src_get spe kk else src_get spt kk) ->
      (forall kk (id: nid_t), In (kk, id) mt -> In (kk, id) me ->
         forall pi, guard_holds pi ->
           rvalid act a_idx pi id ss sinput = Bits.ones 1 ->
           src_get spf kk = (if b then src_get spe kk else src_get spt kk)) ->
      (* a variable neither arm binds keeps its value whichever arm the SOURCE
         takes, so this one is not conditioned *)
      (forall v, (forall n, ~ In (v, n) mt) -> (forall n, ~ In (v, n) me) ->
         src_get spf v = src_get sp0 v) ->
      1 <= cond_id ->
      (forall kk (id: nid_t), In (kk, id) mt -> 1 <= id) ->
      (forall kk (id: nid_t), In (kk, id) me -> 1 <= id) ->
      (b = false -> vm_sem mt spt) -> (b = false -> vm_frame mt spt) ->
      (b = true  -> vm_sem me spe) -> (b = true  -> vm_frame me spe) ->
      0 < length (graph s) -> gpos s ->
      merge_maps ctx cond_id mo mt me s = (fin, s') ->
      wgmono s' F ->
      vm_sem fin spf /\ vm_frame fin spf.
    Proof.
      intros Hb Hsel Hsh Hfr0 Hc1 Hmtp Hmep Hmt Hmtf Hme Hmef Hne Hpos Hrun Hg'.
      unfold merge_maps in Hrun.
      split.
      - exact (merge_loop_sem cond_id mt me b spt spe spf Hb Hsel Hsh Hc1 Hmtp Hmep
                 Hmt Hmtf Hme Hmef
                 (mt ++ me) [] s fin s' Hne Hpos
                 (fun kk id Hin => match Hin with end)
                 Hrun Hg' (fun v n pi Hin => match Hin with end)).
      - intros v Hno.
        destruct (merge_loop_cover cond_id mt me (mt ++ me) [] s fin s' v Hrun Hno)
          as [_ Hcov].
        assert (Hnmt : forall p, ~ In (v, p) mt).
        { intros p Hin.
          destruct (Hcov p (in_or_app _ _ _ (or_introl Hin))) as [H1 _].
          exact (H1 p Hin). }
        assert (Hnme : forall p, ~ In (v, p) me).
        { intros p Hin.
          destruct (Hcov p (in_or_app _ _ _ (or_intror Hin))) as [_ H2].
          exact (H2 p Hin). }
        exact (Hfr0 v Hnmt Hnme).
    Qed.

    (* ================================================================= *)
    (* PHASE 3d, STEP 6: the operations compiler is semantics-preserving. *)
    (* ================================================================= *)

    Lemma sem_inv_ext (s: wst) (sp sq: src_sys_state) :
      (forall v, src_get sp v = src_get sq v) -> sem_inv s sp -> sem_inv s sq.
    Proof.
      intros Hext [Ha Hb]. split.
      - intros v n Hin. rewrite <- Hext. exact (Ha v n Hin).
      - intros v Hno. rewrite <- Hext. exact (Hb v Hno).
    Qed.

    (* The seed builder state (empty var_map) trivially satisfies the invariant
       against the initial source state. *)
    Lemma sem_inv_empty (s: wst) : var_map s = [] -> sem_inv s sp0.
    Proof.
      intro Hvm. unfold sem_inv, vm_sem, vm_frame. rewrite Hvm. split.
      - intros v n pi Hin. destruct Hin.
      - intros v _. reflexivity.
    Qed.

    Lemma ops_run_nop (sp: src_sys_state) :
      tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tf_ops_base tf_nop) sp input = (fst sp, snd sp).
    Proof. reflexivity. Qed.

    Lemma ops_run_assign (dst: s_var) e (sp: src_sys_state) :
      tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tf_ops_base (tf_assign dst e)) sp input
      = (ContextEnv.(putenv) (fst sp) dst
           (tf_eval_expr s_sz i_sz o_sz (szB := s_sz dst) e sp input), snd sp).
    Proof. reflexivity. Qed.

    (* THE DENOTATION at the spec level, in this file's R form: a call assigns its
       destination the value of its RESPONSE port, with the argument [e] absent
       from the right-hand side. *)
    (* V4: a call is ONE source update, the IP applied to the request.  The
       request port is the scheduler's own register and no declared output. *)
    Lemma ops_run_call (ip: p_var) (dst: s_var) e (sp: src_sys_state) :
      tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tf_ops_base (tf_call ip dst e)) sp input
      = (ContextEnv.(putenv) (fst sp) dst
           (convert (ip_fn (tfs_spec_ip ctx ip)
              (tf_eval_expr s_sz i_sz o_sz
                 (szB := ip_req_sz (tfs_spec_ip ctx ip)) e sp input))),
         snd sp).
    Proof. reflexivity. Qed.

    Lemma ops_run_output (dst: o_var) e (sp: src_sys_state) :
      tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tf_ops_base (tf_output dst e)) sp input
      = (fst sp, ContextEnv.(putenv) (snd sp) dst
           (tf_eval_expr s_sz i_sz o_sz (szB := o_sz dst) e sp input)).
    Proof. reflexivity. Qed.

    Lemma ops_run_cons o1 o2 (sp: src_sys_state) :
      tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tf_ops_cons o1 o2) sp input
      = tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) o2 (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) o1 sp input) input.
    Proof.
      unfold tf_ops_run. cbn [tf_ops_updates].
      destruct (tf_ops_updates s_sz i_sz o_sz (tfs_spec_ip ctx) o1 sp input) as [u1 sp1].
      cbn [snd].
      destruct (tf_ops_updates s_sz i_sz o_sz (tfs_spec_ip ctx) o2 sp1 input) as [u2 sp2].
      reflexivity.
    Qed.

    Lemma src_get_put_s_eq (sp: src_sys_state) (dst: s_var) (val: bits_t (s_sz dst)) :
      src_get (ContextEnv.(putenv) (fst sp) dst val, snd sp) (DFG_SVar dst) = val.
    Proof. cbn [src_get fst snd]. rewrite get_put_eq. reflexivity. Qed.

    Lemma src_get_put_s_neq (sp: src_sys_state) (dst: s_var) (val: bits_t (s_sz dst))
          (v: dvar) :
      v <> DFG_SVar dst ->
      src_get (ContextEnv.(putenv) (fst sp) dst val, snd sp) v = src_get sp v.
    Proof.
      intro Hne. destruct v as [sv | ov]; cbn [src_get fst snd].
      - rewrite get_put_neq;
          [ reflexivity | intro He; apply Hne; rewrite He; reflexivity ].
      - reflexivity.
    Qed.

    Lemma src_get_put_o_eq (sp: src_sys_state) (dst: o_var) (val: bits_t (o_sz dst)) :
      src_get (fst sp, ContextEnv.(putenv) (snd sp) dst val) (DFG_OVar dst) = val.
    Proof. cbn [src_get fst snd]. rewrite get_put_eq. reflexivity. Qed.

    Lemma src_get_put_o_neq (sp: src_sys_state) (dst: o_var) (val: bits_t (o_sz dst))
          (v: dvar) :
      v <> DFG_OVar dst ->
      src_get (fst sp, ContextEnv.(putenv) (snd sp) dst val) v = src_get sp v.
    Proof.
      intro Hne. destruct v as [sv | ov]; cbn [src_get fst snd].
      - reflexivity.
      - rewrite get_put_neq;
          [ reflexivity | intro He; apply Hne; rewrite He; reflexivity ].
    Qed.


    (* The graph only grows, so an id emitted later sits above every id the
       earlier state's [var_map] can hold. *)
    Lemma wgmono_len (s s': wst) :
      0 < length (graph s) -> nid_seq s -> nid_seq s' -> wgmono s s' ->
      length (graph s) <= length (graph s').
    Proof.
      intros Hne Hs Hs' Hg.
      unfold SchedulerSimulationBase.nid_seq in Hs.
      destruct (graph s) as [| nd rest] eqn:Egs; [ cbn in Hne; lia |].
      assert (Hnd : nid nd = length rest).
      { cbn [map length] in Hs. rewrite revseq_S in Hs.
        injection Hs as Hh _. exact Hh. }
      assert (Hnin : In nd (graph s)) by (rewrite Egs; apply in_eq).
      assert (Hin : In nd (graph s')) by exact (Hg nd Hnin).
      pose proof (nid_seq_bound s' nd Hs' Hin) as Hb.
      rewrite Hnd in Hb. cbn [length]. lia.
    Qed.

    (* ================================================================= *)
    (* Structural, and free of [guard_holds]: what the builder does to    *)
    (* [var_map] pins what the source does to the state.  Both arms of a  *)
    (* conditional have these, which is what breaks the circularity there.*)
    (* ================================================================= *)
    Lemma dataflow_ops_struct :
      forall (ops: @tf_ops s_var i_var o_var p_var) (en: list (nid_t * bool))
             (s: wst) sp,
        0 < length (graph s) -> winv s -> wvsz s -> wfg s -> gpos s ->
        sem_inv s sp ->
        let (u, s') := dataflow_ops ctx en ops s in
        wgmono s' F ->
        (* a variable the builder leaves unbound is one the source leaves alone *)
        vm_frame (var_map s')
          (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) ops sp input)
        (* every id is one [s] already held, or a node emitted since *)
        /\ (forall v n, In (v, n) (var_map s') ->
              In n (map snd (var_map s)) \/ length (graph s) <= n)
        (* an entry at an OLD node is one no call produced, so its value needs
           no path condition *)
        /\ (forall v n pi, In (v, n) (var_map s') -> n < length (graph s) ->
              guard_holds pi ->
              rvalid act a_idx pi n ss sinput = Bits.ones 1 ->
              NV (dfg_var_size ctx v) n
              = src_get (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) ops sp input) v).
    Proof.
    Admitted.

    Lemma dataflow_ops_sem :
      forall (ops: @tf_ops s_var i_var o_var p_var) (en: list (nid_t * bool))
             (s: wst) sp,
        0 < length (graph s) -> winv s -> wvsz s -> wfg s -> gpos s ->
        (forall x, In x (map fst en) -> wnidwf s x) ->
        (forall x, In x (map fst en) -> 1 <= x) ->
        guard_holds en ->
        sem_inv s sp ->
        let (u, s') := dataflow_ops ctx en ops s in
        wgmono s' F -> sem_inv s' (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) ops sp input).
    Proof.
      induction ops as [op | op1 IHops1 op2 IHops2 | cond op1 IHops1 op2 IHops2];
        intros en s sp Hne Hinv Hvsz Hfg Hpos Hen Henp Hgd Hsem.
      - destruct op as [ | dst expr | dst expr | ip dst expr ].
        + (* nop *)
          cbn [dataflow_ops]. unfold ret. intro Hg'.
          rewrite ops_run_nop.
          apply (sem_inv_ext s sp); [ intro v; destruct v; reflexivity | exact Hsem ].
        + (* assign to a state variable *)
          cbn [dataflow_ops].
          pose proof (dataflow_expr_fg expr (dfg_var_size ctx (DFG_SVar dst)) s
                        Hinv Hvsz Hfg) as He.
          destruct (dataflow_expr ctx expr (dfg_var_size ctx (DFG_SVar dst)) s)
            as [res_id s1] eqn:Ee.
          destruct He as [Ge [Ne [Pe [Qe [Se Fe]]]]].
          rewrite (bind_red (dataflow_expr ctx expr (dfg_var_size ctx (DFG_SVar dst)))
                     _ s _ _ Ee).
          pose proof (set_var_vm_head (DFG_SVar dst) res_id s1) as Hhead.
          pose proof (set_var_vm_keep (DFG_SVar dst) res_id s1) as Hkeep.
          pose proof (set_var_vm_inv2 (DFG_SVar dst) res_id s1) as Hminv.
          pose proof (set_var_full (DFG_SVar dst) res_id s1 Pe Ne) as Hs.
          destruct (set_var ctx (DFG_SVar dst) res_id s1) as [u s'] eqn:Es.
          cbn [snd] in Hhead, Hkeep, Hminv.
          destruct Hs as [Gs Ps].
          intro Hg'.
          assert (Hg1F : wgmono s1 F) by exact (wgmono_trans s1 s' F Gs Hg').
          destruct (dataflow_expr_sem expr (dfg_var_size ctx (DFG_SVar dst)) s s1
                      res_id sp Hne Hinv Hvsz Hpos Ee Hg1F Hsem) as [[Hvm1 Hfr1] Hval].
          rewrite ops_run_assign. split.
          * intros v n pi Hin Hgp Hv.
            destruct (Hminv v n Hin) as [[Hveq Hn] | [Hin0 Hnv]].
            -- subst v. subst n. rewrite (src_get_put_s_eq sp dst _).
               exact (Hval pi Hgp Hv).
            -- rewrite (src_get_put_s_neq sp dst _ v Hnv).
               exact (Hvm1 v n pi Hin0 Hgp Hv).
          * intros v Hno.
            assert (Hnv : v <> DFG_SVar dst).
            { intro He. subst v. exact (Hno res_id Hhead). }
            rewrite (src_get_put_s_neq sp dst _ v Hnv).
            apply Hfr1. intros n Hin. exact (Hno n (Hkeep v n Hin Hnv)).
        + (* assign to an output variable *)
          cbn [dataflow_ops].
          pose proof (dataflow_expr_fg expr (dfg_var_size ctx (DFG_OVar dst)) s
                        Hinv Hvsz Hfg) as He.
          destruct (dataflow_expr ctx expr (dfg_var_size ctx (DFG_OVar dst)) s)
            as [res_id s1] eqn:Ee.
          destruct He as [Ge [Ne [Pe [Qe [Se Fe]]]]].
          rewrite (bind_red (dataflow_expr ctx expr (dfg_var_size ctx (DFG_OVar dst)))
                     _ s _ _ Ee).
          pose proof (set_var_vm_head (DFG_OVar dst) res_id s1) as Hhead.
          pose proof (set_var_vm_keep (DFG_OVar dst) res_id s1) as Hkeep.
          pose proof (set_var_vm_inv2 (DFG_OVar dst) res_id s1) as Hminv.
          pose proof (set_var_full (DFG_OVar dst) res_id s1 Pe Ne) as Hs.
          destruct (set_var ctx (DFG_OVar dst) res_id s1) as [u s'] eqn:Es.
          cbn [snd] in Hhead, Hkeep, Hminv.
          destruct Hs as [Gs Ps].
          intro Hg'.
          assert (Hg1F : wgmono s1 F) by exact (wgmono_trans s1 s' F Gs Hg').
          destruct (dataflow_expr_sem expr (dfg_var_size ctx (DFG_OVar dst)) s s1
                      res_id sp Hne Hinv Hvsz Hpos Ee Hg1F Hsem) as [[Hvm1 Hfr1] Hval].
          rewrite ops_run_output. split.
          * intros v n pi Hin Hgp Hv.
            destruct (Hminv v n Hin) as [[Hveq Hn] | [Hin0 Hnv]].
            -- subst v. subst n. rewrite (src_get_put_o_eq sp dst _).
               exact (Hval pi Hgp Hv).
            -- rewrite (src_get_put_o_neq sp dst _ v Hnv).
               exact (Hvm1 v n pi Hin0 Hgp Hv).
          * intros v Hno.
            assert (Hnv : v <> DFG_OVar dst).
            { intro He. subst v. exact (Hno res_id Hhead). }
            rewrite (src_get_put_o_neq sp dst _ v Hnv).
            apply Hfr1. intros n Hin. exact (Hno n (Hkeep v n Hin Hnv)).
        + (* THE ROUND TRIP.  [dataflow_ops] emits arg -> drive -> (join) ->
             stall -> sample and binds [dst] to the SAMPLE, whose reference IS
             its register; [Hrt] says that register holds the IP's answer to
             this call's own request. *)
          simpl.
          rewrite (bind_red (get_state ctx) _ s _ _ (get_state_red s)).
          pose proof (dataflow_expr_fg expr (ip_req_sz (tfs_spec_ip ctx ip)) s
                        Hinv Hvsz Hfg) as Ha.
          destruct (dataflow_expr ctx expr (ip_req_sz (tfs_spec_ip ctx ip)) s)
            as [arg_id sa] eqn:Ea.
          destruct Ha as [Ga [Na [Pa [Qa [Sa Fa]]]]].
          rewrite (bind_red (dataflow_expr ctx expr (ip_req_sz (tfs_spec_ip ctx ip)))
                     _ s _ _ Ea).
          destruct (join_pendings ctx (pending_samples ctx s ip en) sa)
            as [prev_opt sj] eqn:Ejp.
          rewrite (bind_red _ _ sa _ _ Ejp).
          destruct (emit ctx (DFG_Drive ip arg_id en)
                      (ip_req_sz (tfs_spec_ip ctx ip)) sj) as [drive_id sd] eqn:Ed.
          rewrite (bind_red (emit ctx (DFG_Drive ip arg_id en)
                               (ip_req_sz (tfs_spec_ip ctx ip))) _ sj _ _ Ed).
          destruct (match prev_opt with
                    | None => ret ctx drive_id
                    | Some prev => emit ctx (DFG_Join drive_id prev) 1
                    end sd) as [head_id sh] eqn:Eh.
          rewrite (bind_red _ _ sd _ _ Eh).
          destruct (stall_chain ctx (ip_lat (tfs_spec_ip ctx ip)) head_id sh)
            as [stall_id s1] eqn:Es1.
          rewrite (bind_red (stall_chain ctx (ip_lat (tfs_spec_ip ctx ip)) head_id)
                     _ sh _ _ Es1).
          destruct (emit ctx (DFG_Sample ip stall_id en)
                      (dfg_var_size ctx (DFG_SVar dst)) s1) as [samp_id s2] eqn:Esm.
          rewrite (bind_red (emit ctx (DFG_Sample ip stall_id en)
                               (dfg_var_size ctx (DFG_SVar dst))) _ s1 _ _ Esm).
          pose proof (set_var_vm_head (DFG_SVar dst) samp_id s2) as Hhead.
          pose proof (set_var_vm_keep (DFG_SVar dst) samp_id s2) as Hkeep.
          pose proof (set_var_vm_inv2 (DFG_SVar dst) samp_id s2) as Hminv.
          destruct (set_var ctx (DFG_SVar dst) samp_id s2) as [u s'] eqn:Es.
          cbn [snd] in Hhead, Hkeep, Hminv.
          intro Hg'.
          (* --- the graph grows along the chain, so each emit lands in [F] --- *)
          assert (Gj : wgmono sa sj).
          { pose proof (join_pendings_grows (pending_samples ctx s ip en) sa) as Hgj.
            rewrite Ejp in Hgj. cbn [snd] in Hgj. exact Hgj. }
          assert (Gd : wgmono sj sd) by exact (emit_gmono _ _ _ _ _ Ed).
          assert (Gh : wgmono sd sh).
          { revert Eh. destruct prev_opt as [prev |].
            - intro E. exact (emit_gmono _ _ _ _ _ E).
            - unfold ret. intro E. injection E as _ <-. apply wgmono_refl. }
          assert (Gt : wgmono sh s1).
          { revert Es1. unfold stall_chain.
            destruct (ip_lat (tfs_spec_ip ctx ip)) as [| l].
            - unfold ret. intro E. injection E as _ <-. apply wgmono_refl.
            - intro E. exact (emit_gmono _ _ _ _ _ E). }
          assert (Gm : wgmono s1 s2) by exact (emit_gmono _ _ _ _ _ Esm).
          assert (Gs : wgmono s2 s').
          { intros n Hn.
            replace (graph s') with (graph s2);
              [ exact Hn | rewrite <- (set_var_graph (DFG_SVar dst) samp_id s2), Es;
                           reflexivity ]. }
          assert (GmF : wgmono s2 F) by (eapply wgmono_trans; [ exact Gs | exact Hg' ]).
          assert (Gt1F : wgmono s1 F) by (eapply wgmono_trans; [ exact Gm | exact GmF ]).
          assert (GhF : wgmono sh F) by (eapply wgmono_trans; [ exact Gt | exact Gt1F ]).
          assert (GdF : wgmono sd F) by (eapply wgmono_trans; [ exact Gh | exact GhF ]).
          assert (GjF : wgmono sj F) by (eapply wgmono_trans; [ exact Gd | exact GdF ]).
          assert (GaF : wgmono sa F) by (eapply wgmono_trans; [ exact Gj | exact GjF ]).
          (* --- and the nodes it records --- *)
          assert (Hnea : 0 < length (graph sa)) by exact (gne_gmono s sa Ga Hne).
          assert (Hnej : 0 < length (graph sj)) by exact (gne_gmono sa sj Gj Hnea).
          assert (Hned : 0 < length (graph sd)) by exact (gne_gmono sj sd Gd Hnej).
          assert (Hneh : 0 < length (graph sh)) by exact (gne_gmono sd sh Gh Hned).
          assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono sh s1 Gt Hneh).
          destruct (emitted_node_at act F s1 s2 (DFG_Sample ip stall_id en)
                      (dfg_var_size ctx (DFG_SVar dst)) samp_id HF Hne1 Esm GmF)
            as [Msm1 [Msm2 [MsmOp MsmSz]]].
          (* the head is the drive, or the ordering join in front of it -- and
             either way it is no stall, which is what pins the token's arm *)
          destruct (emitted_node_at act F sj sd (DFG_Drive ip arg_id en)
                      (ip_req_sz (tfs_spec_ip ctx ip)) drive_id HF Hnej Ed GdF)
            as [_ [_ [MdrOp MdrSz]]].
          assert (Hhd : sample_req_head act head_id = Some arg_id
                        /\ match node_op act head_id with
                           | DFG_Stall _ _ => False | _ => True end).
          { revert Eh. destruct prev_opt as [prev |].
            - intro E.
              destruct (emitted_node_at act F sd sh (DFG_Join drive_id prev) 1
                          head_id HF Hned E GhF) as [_ [_ [MjnOp _]]].
              unfold SchedulerSimulationBase.sample_req_head, SchedulerSimulationBase.node_op. rewrite MjnOp.
              split; [ rewrite MdrOp; reflexivity | exact I ].
            - unfold ret. intro E. injection E as <- _.
              unfold SchedulerSimulationBase.sample_req_head, SchedulerSimulationBase.node_op. rewrite MdrOp.
              split; [ reflexivity | exact I ]. }
          destruct Hhd as [Hhd1 Hhd2].
          (* the same walk, stopped at the drive and checked to be on [ip] *)
          assert (Hdh : sample_drive_head act ip head_id = Some drive_id).
          { revert Eh. destruct prev_opt as [prev |].
            - intro E.
              destruct (emitted_node_at act F sd sh (DFG_Join drive_id prev) 1
                          head_id HF Hned E GhF) as [_ [_ [MjnOp2 _]]].
              unfold SchedulerSimulationBase.sample_drive_head, SchedulerSimulationBase.node_op. rewrite MjnOp2, MdrOp.
              destruct ((tfs_spec_ips_eq_dec ctx).(eq_dec) ip ip) as [_ | Hnp];
                [ reflexivity | exfalso; exact (Hnp eq_refl) ].
            - unfold ret. intro E. injection E as <- _.
              unfold SchedulerSimulationBase.sample_drive_head, SchedulerSimulationBase.node_op. rewrite MdrOp.
              destruct ((tfs_spec_ips_eq_dec ctx).(eq_dec) ip ip) as [_ | Hnp];
                [ reflexivity | exfalso; exact (Hnp eq_refl) ]. }
          assert (Hdrv : sample_drive act samp_id = Some drive_id).
          { unfold SchedulerSimulationBase.sample_drive, SchedulerSimulationBase.node_op. rewrite MsmOp.
            revert Es1. unfold stall_chain.
            destruct (ip_lat (tfs_spec_ip ctx ip)) as [| l].
            - unfold ret. intro E. injection E as <- _.
              revert Hhd2 Hdh. unfold SchedulerSimulationBase.node_op.
              destruct (op (nth head_id (graph (build_dfg ctx act))
                              {| nid := 0; op := DFG_Empty; sz := 0 |}));
                try (intros _ H; exact H).
              intros [].
            - intro E.
              destruct (emitted_node_at act F sh s1 (DFG_Stall (S l) head_id)
                          (counter_sz (S l)) stall_id HF Hneh E Gt1F)
                as [_ [_ [MstOp2 _]]].
              unfold SchedulerSimulationBase.node_op. rewrite MstOp2. exact Hdh. }
          assert (Hreq : sample_req act samp_id = Some arg_id).
          { unfold SchedulerSimulationBase.sample_req, SchedulerSimulationBase.node_op. rewrite MsmOp.
            revert Es1. unfold stall_chain.
            destruct (ip_lat (tfs_spec_ip ctx ip)) as [| l].
            - unfold ret. intro E. injection E as <- _.
              revert Hhd2 Hhd1. unfold SchedulerSimulationBase.node_op.
              destruct (op (nth head_id (graph (build_dfg ctx act))
                              {| nid := 0; op := DFG_Empty; sz := 0 |}));
                try (intros _ H; exact H).
              intros [].
            - intro E.
              destruct (emitted_node_at act F sh s1 (DFG_Stall (S l) head_id)
                          (counter_sz (S l)) stall_id HF Hneh E Gt1F)
                as [_ [_ [MstOp _]]].
              unfold SchedulerSimulationBase.node_op. rewrite MstOp. exact Hhd1. }
          (* --- the semantics --- *)
          destruct (dataflow_expr_sem expr (ip_req_sz (tfs_spec_ip ctx ip)) s sa
                      arg_id sp Hne Hinv Hvsz Hpos Ea GaF Hsem) as [[Hvm1 Hfr1] Hval].
          assert (Hvm2 : var_map s2 = var_map sa).
          { rewrite (emit_vm _ _ _ _ _ Esm).
            assert (Hs1 : var_map s1 = var_map sh).
            { revert Es1. unfold stall_chain.
              destruct (ip_lat (tfs_spec_ip ctx ip)) as [| l].
              - unfold ret. intro E. injection E as _ <-. reflexivity.
              - intro E. exact (emit_vm _ _ _ _ _ E). }
            rewrite Hs1.
            assert (Hsh : var_map sh = var_map sd).
            { revert Eh. destruct prev_opt as [prev |].
              - intro E. exact (emit_vm _ _ _ _ _ E).
              - unfold ret. intro E. injection E as _ <-. reflexivity. }
            rewrite Hsh. rewrite (emit_vm _ _ _ _ _ Ed).
            pose proof (join_pendings_vm_eq (pending_samples ctx s ip en) sa) as Hvj.
            rewrite Ejp in Hvj. cbn [snd] in Hvj. exact Hvj. }
          (* the sample's reference IS its register, and [Hrt] reads it *)
          assert (Hsampv : is_sample_of act samp_id = true)
            by (unfold SchedulerSimulationBase.is_sample_of, SchedulerSimulationBase.node_op; rewrite MsmOp; reflexivity).
          destruct (sample_index act a_idx samp_id Hali Hsampv) as [n_idx Hvn].
          assert (Hbsz : ss_sz (tf_dfg_b a_idx n_idx)
                         = dfg_var_size ctx (DFG_SVar dst))
            by (rewrite (buffer_register_node_size act a_idx n_idx Hali), Hvn;
                exact MsmSz).
          assert (Hsmop : node_op act (vreg_nid a_idx n_idx) = DFG_Sample ip stall_id en)
            by (unfold SchedulerSimulationBase.node_op; rewrite Hvn, MsmOp; reflexivity).
          assert (Hsmdr : sample_drive act (vreg_nid a_idx n_idx) = Some drive_id)
            by (rewrite Hvn; exact Hdrv).
          assert (Hdrop2 : node_op act drive_id = DFG_Drive ip arg_id en)
            by (unfold SchedulerSimulationBase.node_op; rewrite MdrOp; reflexivity).
          assert (Hsamp : (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
                          NV (dfg_var_size ctx (DFG_SVar dst)) samp_id
                          = convert (ip_fn (tfs_spec_ip ctx ip)
                              (NV (ip_req_sz (tfs_spec_ip ctx ip)) arg_id))).
          { intro Hreg.
            unfold SchedulerSimulationBase.nval. rewrite <- Hvn.
            rewrite (nre_sample act a_idx n_idx Hali
                       ltac:(rewrite Hvn; exact Hsampv)).
            rewrite <- Hbsz, eval_svar_same.
            exact (Hrt n_idx ip stall_id en drive_id arg_id en
                     Hsmop Hsmdr Hdrop2 MdrSz Hgd Hreg). }
          assert (Hg0 : guard_holds []) by (intros q bb []).
          rewrite ops_run_call. split.
          * intros v n pi Hin Hgp Hv.
            destruct (Hminv v n Hin) as [[Hveq Hn] | [Hin0 Hnv]].
            -- subst v. subst n. rewrite (src_get_put_s_eq sp dst _).
               assert (Hreg : (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1).
               { rewrite <- Hvn in Hv.
                 destruct (vreg_nid_node_range act a_idx n_idx Hali) as [_ Hnlen].
                 rewrite (sample_ref_is_register act a_idx n_idx Hali
                            ltac:(rewrite Hvn; exact Hsampv) pi
                            (length (graph (build_dfg ctx act))) Hnlen) in Hv.
                 cbn [tf_eval_expr] in Hv. exact Hv. }
               rewrite (Hsamp Hreg).
               rewrite (Hval [] Hg0
                          (Harg n_idx ip stall_id en drive_id arg_id en
                             Hsmop Hsmdr Hdrop2 Hreg)).
               reflexivity.
            -- rewrite (src_get_put_s_neq sp dst _ v Hnv).
               apply (Hvm1 v n pi); [ rewrite <- Hvm2; exact Hin0 | exact Hgp | exact Hv ].
          * intros v Hno.
            assert (Hnv : v <> DFG_SVar dst).
            { intro He. subst v. exact (Hno samp_id Hhead). }
            rewrite (src_get_put_s_neq sp dst _ v Hnv).
            apply Hfr1. intros n Hin. apply (Hno n).
            apply (Hkeep v n); [ rewrite Hvm2; exact Hin | exact Hnv ].
      - (* sequential composition *)
        cbn [dataflow_ops].
        pose proof (dataflow_ops_fg op1 en s Hinv Hvsz Hfg Hen) as Fa.
        pose proof (IHops1 en s sp Hne Hinv Hvsz Hfg Hpos Hen Henp Hgd Hsem) as H1.
        destruct (dataflow_ops ctx en op1 s) as [u1 s1] eqn:E1.
        destruct Fa as [G1 [P1 [Q1 Ff1]]].
        rewrite (bind_red (dataflow_ops ctx en op1) _ s _ _ E1).
        assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 G1 Hne).
        assert (Hpos1 : gpos s1).
        { pose proof (dataflow_ops_pos op1 en s Hpos Henp) as Hq.
          rewrite E1 in Hq. exact Hq. }
        assert (Hen1 : forall x, In x (map fst en) -> wnidwf s1 x)
          by (intros x Hx; eapply wnidwf_gmono; [ apply Hen, Hx | exact G1 ]).
        pose proof (dataflow_ops_fg op2 en s1 P1 Q1 Ff1 Hen1) as Fb.
        pose proof (fun Hs =>
                      IHops2 en s1 (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) op1 sp input)
                        Hne1 P1 Q1 Ff1 Hpos1 Hen1 Henp Hgd Hs) as H2.
        destruct (dataflow_ops ctx en op2 s1) as [u2 s2] eqn:E2.
        destruct Fb as [G2 [P2 [Q2 Ff2]]].
        intro Hg'.
        assert (Hg1F : wgmono s1 F) by exact (wgmono_trans s1 s2 F G2 Hg').
        rewrite ops_run_cons.
        exact (H2 (H1 Hg1F) Hg').
      - (* conditional *)
        cbn [dataflow_ops].
        pose proof (dataflow_expr_fg cond 1 s Hinv Hvsz Hfg) as Hc.
        destruct (dataflow_expr ctx cond 1 s) as [cond_id s1] eqn:Ec.
        destruct Hc as [Gc [Nc [Pc [Qc [Sc Fc]]]]].
        rewrite (bind_red (dataflow_expr ctx cond 1) _ s _ _ Ec).
        rewrite (bind_red (get_state ctx) _ s1 _ _ (get_state_red s1)).
        assert (Hne1 : 0 < length (graph s1)) by exact (gne_gmono s s1 Gc Hne).
        assert (Hposc : 1 <= cond_id /\ gpos s1).
        { pose proof (dataflow_expr_pos cond 1 s Hpos) as Hq. rewrite Ec in Hq. exact Hq. }
        destruct Hposc as [Hcondp Hpos1].
        assert (Hen_tp : forall x, In x (map fst ((cond_id, true) :: en)) -> 1 <= x).
        { intros x Hx. cbn [map In] in Hx. destruct Hx as [<- | Hx];
            [ exact Hcondp | exact (Henp x Hx) ]. }
        assert (Hen_ep : forall x, In x (map fst ((cond_id, false) :: en)) -> 1 <= x).
        { intros x Hx. cbn [map In] in Hx. destruct Hx as [<- | Hx];
            [ exact Hcondp | exact (Henp x Hx) ]. }
        assert (Hen_t : forall x, In x (map fst ((cond_id, true) :: en)) -> wnidwf s1 x).
        { intros x Hx. cbn [map In] in Hx. destruct Hx as [<- | Hx]; [ exact Nc |].
          eapply wnidwf_gmono; [ apply Hen, Hx | exact Gc ]. }
        pose proof (dataflow_ops_fg op1 ((cond_id, true) :: en) s1 Pc Qc Fc Hen_t) as Ft.
        pose proof (fun Hg Hs =>
                      IHops1 ((cond_id, true) :: en) s1 sp Hne1 Pc Qc Fc Hpos1 Hen_t
                        Hen_tp Hg Hs) as Ht.
        destruct (dataflow_ops ctx ((cond_id, true) :: en) op1 s1) as [ut s_then] eqn:Et.
        destruct Ft as [Gthen [Pthen [Qthen Fthen]]].
        rewrite (bind_red (dataflow_ops ctx ((cond_id, true) :: en) op1) _ s1 _ _ Et).
        rewrite (bind_red (get_state ctx) _ s_then _ _ (get_state_red s_then)).
        set (sR := {| graph := graph s_then; var_map := var_map s1 |} : wst).
        rewrite (bind_red (put_state ctx sR) _ s_then _ _ (put_state_red sR s_then)).
        assert (Gthen_sR : wgmono s_then sR) by (intros n Hn; unfold sR; simpl; exact Hn).
        assert (GsR_then : wgmono sR s_then)
          by (intros n Hn; unfold sR in Hn; simpl in Hn; exact Hn).
        assert (PsR : winv sR).
        { destruct Pc as [Hv1 [Hns1 Hab1]]. destruct Pthen as [Hvt [Hnst Habt]].
          split; [ | split ].
          - intros k id Hin. unfold sR in Hin; simpl in Hin.
            destruct (Hv1 k id Hin) as [node [Hn Hnid]].
            exists node. split; [ unfold sR; simpl; apply Gthen; exact Hn | exact Hnid ].
          - unfold SchedulerSimulationBase.nid_seq, sR; simpl. exact Hnst.
          - unfold sR; simpl. exact Habt. }
        assert (QsR : wvsz sR).
        { intros v id Hin. unfold sR in Hin; simpl in Hin.
          eapply wsz_gmono; [ apply Qc; exact Hin | ].
          intros n Hn; unfold sR; simpl; apply Gthen; exact Hn. }
        assert (FsR : wfg sR).
        { intros node Hin. unfold sR in Hin; simpl in Hin.
          eapply node_args_sz_gmono; [ apply Fthen; exact Hin | exact GsR_then ]. }
        assert (HneR : 0 < length (graph sR)).
        { unfold sR; simpl. exact (gne_gmono s1 s_then Gthen Hne1). }
        assert (Hen_e : forall x, In x (map fst ((cond_id, false) :: en)) ->
                          wnidwf sR x).
        { assert (Gs1R : wgmono s1 sR)
            by (eapply wgmono_trans; [ exact Gthen | exact Gthen_sR ]).
          intros x Hx. cbn [map In] in Hx.
          destruct Hx as [<- | Hx];
            [ eapply wnidwf_gmono; [ exact Nc | exact Gs1R ]
            | eapply wnidwf_gmono;
              [ apply Hen, Hx
              | eapply wgmono_trans; [ exact Gc | exact Gs1R ] ] ]. }
        assert (Hpos_then : gpos s_then).
        { pose proof (dataflow_ops_pos op1 ((cond_id, true) :: en) s1 Hpos1 Hen_tp) as Hq.
          rewrite Et in Hq. exact Hq. }
        assert (HposR : gpos sR).
        { destruct Hpos1 as [_ [Hvm1p _]].
          pose proof Hpos_then as Hpt0; destruct Hpt0 as [Hl [_ [Hargs [Hsent Hnz]]]].
          unfold SchedulerSimulationBase.gpos, sR; cbn [graph var_map].
          split; [ exact Hl | split; [ exact Hvm1p | split; [ exact Hargs |
            split; [ exact Hsent | exact Hnz ] ] ] ]. }
        pose proof (dataflow_ops_fg op2 ((cond_id, false) :: en) sR PsR QsR FsR Hen_e) as Fe.
        pose proof (fun Hg Hs =>
                      IHops2 ((cond_id, false) :: en) sR sp HneR PsR QsR FsR HposR Hen_e
                        Hen_ep Hg Hs) as Hels.
        destruct (dataflow_ops ctx ((cond_id, false) :: en) op2 sR) as [ue s_else] eqn:Ee.
        destruct Fe as [Gelse [Pelse [Qelse Felse]]].
        rewrite (bind_red (dataflow_ops ctx ((cond_id, false) :: en) op2) _ sR _ _ Ee).
        rewrite (bind_red (get_state ctx) _ s_else _ _ (get_state_red s_else)).
        assert (Gs1_selse : wgmono s1 s_else)
          by (eapply wgmono_trans;
              [ exact Gthen | eapply wgmono_trans; [ exact Gthen_sR | exact Gelse ] ]).
        assert (Gthen_selse : wgmono s_then s_else)
          by (eapply wgmono_trans; [ exact Gthen_sR | exact Gelse ]).
        assert (HneE : 0 < length (graph s_else))
          by exact (gne_gmono sR s_else Gelse HneR).
        assert (Ncond : wnidwf s_else cond_id)
          by (eapply wnidwf_gmono; [ exact Nc | exact Gs1_selse ]).
        assert (Scond : wsz s_else cond_id 1)
          by (eapply wsz_gmono; [ exact Sc | exact Gs1_selse ]).
        assert (Hmtn : forall k id, In (k, id) (var_map s_then) -> wnidwf s_else id).
        { intros k id Hin. destruct Pthen as [Hvt _].
          destruct (Hvt k id Hin) as [node [Hn Hnid]].
          exists node. split; [ apply Gthen_selse; exact Hn | exact Hnid ]. }
        assert (Hmen : forall k id, In (k, id) (var_map s_else) -> wnidwf s_else id).
        { intros k id Hin. destruct Pelse as [Hve _]. exact (Hve k id Hin). }
        assert (Hmts : forall k id,
                   In (k, id) (var_map s_then) -> wsz s_else id (dfg_var_size ctx k)).
        { intros k id Hin. eapply wsz_gmono; [ apply Qthen; exact Hin | exact Gthen_selse ]. }
        assert (Hmes : forall k id,
                   In (k, id) (var_map s_else) -> wsz s_else id (dfg_var_size ctx k)).
        { intros k id Hin. apply Qelse; exact Hin. }
        pose proof (merge_maps_fg cond_id (var_map s1) (var_map s_then) (var_map s_else)
                      s_else Pelse Qelse Felse Ncond Scond Hmtn Hmen Hmts Hmes) as Hmerge.
        destruct (merge_maps ctx cond_id (var_map s1) (var_map s_then) (var_map s_else)
                    s_else) as [final_vars s_final] eqn:Em.
        destruct Hmerge as [Gmerge [Pfinal [Qfinal [Ffinal [Nfinal Sfinal]]]]].
        rewrite (bind_red (merge_maps ctx cond_id (var_map s1) (var_map s_then)
                             (var_map s_else)) _ s_else _ _ Em).
        rewrite (bind_red (get_state ctx) _ s_final _ _ (get_state_red s_final)).
        set (sF := {| graph := graph s_final; var_map := final_vars |} : wst).
        rewrite (put_state_red sF s_final).
        intro Hg'.
        assert (GsF : wgmono s_final sF) by (intros n Hn; unfold sF; simpl; exact Hn).
        assert (Hg_final : wgmono s_final F)
          by exact (wgmono_trans s_final sF F GsF Hg').
        assert (Hg_else : wgmono s_else F)
          by exact (wgmono_trans s_else s_final F Gmerge Hg_final).
        assert (Hg_sR : wgmono sR F) by exact (wgmono_trans sR s_else F Gelse Hg_else).
        assert (Hg_then : wgmono s_then F)
          by exact (wgmono_trans s_then sR F Gthen_sR Hg_sR).
        assert (Hg_s1 : wgmono s1 F) by exact (wgmono_trans s1 s_then F Gthen Hg_then).
        destruct (dataflow_expr_sem cond 1 s s1 cond_id sp Hne Hinv Hvsz Hpos Ec Hg_s1 Hsem)
          as [Hsem1 Hvc].
        unfold SchedulerSimulationBase.nval in Hvc.
        assert (HsemR : sem_inv sR sp).
        { apply (sem_inv_vm s1 sR); [ unfold sR; simpl; reflexivity | exact Hsem1 ]. }
        assert (HvmF : var_map sF = final_vars) by (unfold sF; reflexivity).
        (* gpos at the two arms, and the structural facts BOTH of them have *)
        assert (Hpos_else : gpos s_else).
        { pose proof (dataflow_ops_pos op2 ((cond_id, false) :: en) sR HposR Hen_ep) as Hq.
          rewrite Ee in Hq. exact Hq. }
        pose proof (dataflow_ops_struct op1 ((cond_id, true) :: en) s1 sp
                      Hne1 Pc Qc Fc Hpos1 Hsem1) as Hstt.
        rewrite Et in Hstt. destruct (Hstt Hg_then) as [Hfrt [Hsplt Hkeept]].
        pose proof (dataflow_ops_struct op2 ((cond_id, false) :: en) sR sp
                      HneR PsR QsR FsR HposR HsemR) as Hste.
        rewrite Ee in Hste. destruct (Hste Hg_else) as [Hfre [Hsple Hkeepe]].
        (* a key both arms leave at ONE node sits at an id [s1] already held,
           so neither arm's binding came from a call and both read the same *)
        assert (Hboth : forall kk (id: nid_t),
                  In (kk, id) (var_map s_then) -> In (kk, id) (var_map s_else) ->
                  forall pi, guard_holds pi ->
                    rvalid act a_idx pi id ss sinput = Bits.ones 1 ->
                  src_get (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) op1 sp input) kk
                  = src_get (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) op2 sp input) kk).
        { intros kk id Hint Hine pi Hgp Hv.
          assert (Hlt : id < length (graph s_then)).
          { apply (wnidwf_bound s_then id); [ exact (proj1 (proj2 Pthen)) |].
            exact (proj1 Pthen kk id Hint). }
          assert (HltR : id < length (graph sR))
            by (unfold sR; cbn [graph]; exact Hlt).
          assert (Hlow : id < length (graph s1)).
          { destruct (Hsple kk id Hine) as [Hin | Hge]; [| exfalso; lia ].
            apply in_map_iff in Hin. destruct Hin as [[v2 n2] [Heq Hmem]].
            cbn [snd] in Heq. subst n2.
            unfold sR in Hmem; cbn [var_map] in Hmem.
            exact (wnidwf_bound s1 id (proj1 (proj2 Pc)) (proj1 Pc v2 id Hmem)). }
          rewrite <- (Hkeept kk id pi Hint Hlow Hgp Hv).
          exact (Hkeepe kk id pi Hine HltR Hgp Hv). }
        unfold sem_inv. rewrite HvmF.
        unfold tf_ops_run. cbn [tf_ops_updates].
        destruct (bits1_cases (tf_eval_expr ss_sz si_sz oo_sz (szB := 1)
                    (node_ref_expr act a_idx cond_id) ss sinput)) as [Hhw | Hhw].
        + (* the HARDWARE takes the THEN arm *)
          assert (Hnz : tf_eval_expr ss_sz si_sz oo_sz (szB := 1)
                          (node_ref_expr act a_idx cond_id) ss sinput <> Bits.zero)
            by (rewrite Hhw; exact ones1_neq_zero).
          assert (Hgd_t : guard_holds ((cond_id, true) :: en)).
          { intros n bb Hin. cbn [In] in Hin. destruct Hin as [Heq | Hin].
            - injection Heq as H1 H2; subst n; subst bb.
              split; [ intros _; exact Hnz | intro Hc; discriminate Hc ].
            - exact (Hgd n bb Hin). }
          destruct (Ht Hgd_t Hsem1 Hg_then) as [Hmt1 Hmtf1].
          assert (Hb : forall szB E1 E2,
                     tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
                       (tf_expr_if (node_ref_expr act a_idx cond_id) E1 E2) ss sinput
                     = if false then tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E2 ss sinput
                               else tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E1 ss sinput).
          { intros szB E1 E2. cbn [tf_eval_expr]. rewrite Hhw.
            match goal with
            | |- context [ @beq_dec ?T ?E ?x ?z ] =>
                replace (@beq_dec T E x z) with false by (vm_compute; reflexivity)
            end. reflexivity. }
          refine (merge_maps_sem cond_id (var_map s1) (var_map s_then) (var_map s_else)
                    false
                    (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) op1 sp input)
                    (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) op2 sp input)
                    _ s_else final_vars s_final Hb _ _ _ Hcondp
                    _ _ (fun _ => Hmt1) (fun _ => Hmtf1) _ _ HneE Hpos_else Em Hg_final).
          * (* the source takes the same arm where the condition reads valid *)
            intros pi Hgp Hv kk. pose proof (Hvc pi Hgp Hv) as Hcv.
            rewrite Hhw in Hcv. rewrite <- Hcv.
            match goal with
            | |- context [ @beq_dec ?T ?E ?x ?z ] =>
                replace (@beq_dec T E x z) with false by (vm_compute; reflexivity)
            end. reflexivity.
          * (* a shared key: both arms leave it where it was *)
            intros kk id Hint Hine pi Hgp Hv.
            pose proof (Hboth kk id Hint Hine pi Hgp Hv) as Hk.
            cbn beta iota.
            match goal with
            | |- context [ @beq_dec ?T ?E ?x ?z ] => destruct (@beq_dec T E x z)
            end; first [ reflexivity | exact Hk | exact (eq_sym Hk) ].
          * (* a variable neither arm binds *)
            intros v Hnmt Hnme. cbn beta iota.
            match goal with
            | |- context [ @beq_dec ?T ?E ?x ?z ] => destruct (@beq_dec T E x z)
            end; first [ exact (Hfre v Hnme) | exact (Hfrt v Hnmt) ].
          * intros kk id Hin. exact (proj1 (proj2 Hpos_then) kk id Hin).
          * intros kk id Hin. exact (proj1 (proj2 Hpos_else) kk id Hin).
          * intro Hc. discriminate Hc.
          * intro Hc. discriminate Hc.
        + (* the HARDWARE takes the ELSE arm *)
          assert (Hgd_e : guard_holds ((cond_id, false) :: en)).
          { intros n bb Hin. cbn [In] in Hin. destruct Hin as [Heq | Hin].
            - injection Heq as H1 H2; subst n; subst bb.
              split; [ intro Hc; discriminate Hc | intros _; exact Hhw ].
            - exact (Hgd n bb Hin). }
          destruct (Hels Hgd_e HsemR Hg_else) as [Hme1 Hmef1].
          assert (Hb : forall szB E1 E2,
                     tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
                       (tf_expr_if (node_ref_expr act a_idx cond_id) E1 E2) ss sinput
                     = if true then tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E2 ss sinput
                               else tf_eval_expr ss_sz si_sz oo_sz (szB := szB) E1 ss sinput).
          { intros szB E1 E2. cbn [tf_eval_expr]. rewrite Hhw, beq_dec_refl.
            reflexivity. }
          refine (merge_maps_sem cond_id (var_map s1) (var_map s_then) (var_map s_else)
                    true
                    (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) op1 sp input)
                    (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) op2 sp input)
                    _ s_else final_vars s_final Hb _ _ _ Hcondp
                    _ _ _ _ (fun _ => Hme1) (fun _ => Hmef1) HneE Hpos_else Em Hg_final).
          * intros pi Hgp Hv kk. pose proof (Hvc pi Hgp Hv) as Hcv.
            rewrite Hhw in Hcv. rewrite <- Hcv, beq_dec_refl. reflexivity.
          * intros kk id Hint Hine pi Hgp Hv.
            pose proof (Hboth kk id Hint Hine pi Hgp Hv) as Hk.
            cbn beta iota.
            match goal with
            | |- context [ @beq_dec ?T ?E ?x ?z ] => destruct (@beq_dec T E x z)
            end; first [ reflexivity | exact Hk | exact (eq_sym Hk) ].
          * intros v Hnmt Hnme. cbn beta iota.
            match goal with
            | |- context [ @beq_dec ?T ?E ?x ?z ] => destruct (@beq_dec T E x z)
            end; first [ exact (Hfre v Hnme) | exact (Hfrt v Hnmt) ].
          * intros kk id Hin. exact (proj1 (proj2 Hpos_then) kk id Hin).
          * intros kk id Hin. exact (proj1 (proj2 Hpos_else) kk id Hin).
          * intro Hc. discriminate Hc.
          * intro Hc. discriminate Hc.
    Qed.

  End DFGSem.

  (* The exported DFG is the reverse of the final builder state's graph, and
     shares its var_map verbatim. *)
  Lemma build_dfg_final (act: tfs_action sched) :
    exists (Fin: wst),
      dataflow_ops ctx [] (tfs_spec_action_ops ctx act)
        {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |}
        = (tt, Fin)
      /\ exports act Fin
      /\ var_map (build_dfg ctx act) = var_map Fin.
  Proof.
    unfold SchedulerSimulationBase.exports, build_dfg.
    destruct (dataflow_ops ctx [] (tfs_spec_action_ops ctx act)
                {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |})
      as [u final] eqn:Ed.
    destruct u. exists final.
    split; [ reflexivity | cbn [graph var_map]; split; reflexivity ].
  Qed.

  (* ==================================================================== *)
  (* Phase 3d: the DFG really computes the source action.  This says       *)
  (* nothing about the scheduler, buffers, validity bits or cycles —       *)
  (* purely that [build_dfg] followed by the BUFFER-FREE                   *)
  (* [compile_dfg_expr] reproduces the source semantics [tf_ops_run].      *)
  (* ==================================================================== *)
  Lemma dfg_action_semantics (act: tfs_action sched) a_idx
        (sp: src_sys_state) (ss: sched_sys_state)
        (input: input_t) (sinput: sched_input_t) :
    act_idx_aligned act a_idx ->
    (forall v, sinput (inl v) = input v) ->
    (forall n_idx p tok en d av en',
       node_op act (vreg_nid a_idx n_idx) = DFG_Sample p tok en ->
       sample_drive act (vreg_nid a_idx n_idx) = Some d ->
       node_op act d = DFG_Drive p av en' ->
       sz (nth d (graph (build_dfg ctx act))
            {| nid := 0; op := DFG_Empty; sz := 0 |}) = ip_req_sz (tfs_spec_ip ctx p) ->
       guard_holds act a_idx ss sinput en ->
       (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
       (fst ss).[tf_dfg_b a_idx n_idx]
       = convert (ip_fn (tfs_spec_ip ctx p)
           (tf_eval_expr ss_sz si_sz oo_sz
              (szB := ip_req_sz (tfs_spec_ip ctx p))
              (node_ref_expr act a_idx av) ss sinput))) ->
    (* a latched sample's request carried a settled argument *)
    (forall n_idx p tok en d av en',
       node_op act (vreg_nid a_idx n_idx) = DFG_Sample p tok en ->
       sample_drive act (vreg_nid a_idx n_idx) = Some d ->
       node_op act d = DFG_Drive p av en' ->
       (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
       eval1 (node_ref_valid act a_idx av) ss sinput = Bits.ones 1) ->
    (forall sv, (fst ss).[tf_dfg_s sv] = (fst sp).[sv]) ->
    (forall ov, (snd ss).[ov] = (snd sp).[ov]) ->
    let sp1 := tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act) sp input in
    (forall sv n, In (DFG_SVar sv, n) (var_map (build_dfg ctx act)) ->
        eval1 (node_ref_valid act a_idx n) ss sinput = Bits.ones 1 ->
        eval_st (tf_dfg_s sv)
          (fst (compile_dfg_expr ctx bneeds
                  (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n (sample_bufs act a_idx)))
          ss sinput
        = (fst sp1).[sv])
    /\ (forall ov n, In (DFG_OVar ov, n) (var_map (build_dfg ctx act)) ->
        eval1 (node_ref_valid act a_idx n) ss sinput = Bits.ones 1 ->
        eval_out ov
          (fst (compile_dfg_expr ctx bneeds
                  (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n (sample_bufs act a_idx)))
          ss sinput
        = (snd sp1).[ov])
    /\ (forall sv, (forall n, ~ In (DFG_SVar sv, n) (var_map (build_dfg ctx act))) ->
        (fst sp1).[sv] = (fst sp).[sv])
    /\ (forall ov, (forall n, ~ In (DFG_OVar ov, n) (var_map (build_dfg ctx act))) ->
        (snd sp1).[ov] = (snd sp).[ov]).
  Proof.
    intros Halign Hsinp Hrtp Hargp Hs Ho.
    destruct (build_dfg_final act) as [Fin [Ed [Hgr Hvm]]].
    assert (Hempty : winv {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ];
                            var_map := [] |}).
    { split; [ | split ].
      - intros k id Hin. destruct Hin.
      - unfold SchedulerSimulationBase.nid_seq. reflexivity.
      - intros a Ha x Hx. simpl in Ha. destruct Ha as [<-|[]]. simpl in Hx. destruct Hx. }
    assert (Hemvsz : wvsz {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ];
                            var_map := [] |}).
    { intros v id Hin. destruct Hin. }
    assert (Hemfg : wfg {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ];
                          var_map := [] |}).
    { intros node Hin. simpl in Hin. destruct Hin as [<-|[]].
      unfold SchedulerSimulationBase.node_args_sz. cbn [op]. exact I. }
    assert (Hne0 : 0 < length (graph ({| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ];
                                        var_map := [] |} : wst))).
    { cbn [graph]. simpl. apply Nat.lt_0_1. }
    assert (Hpos0 : gpos ({| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ];
                            var_map := [] |} : wst)).
    { unfold SchedulerSimulationBase.gpos; cbn [graph var_map].
      split; [ apply Nat.le_refl |].
      split; [ intros k id [] |].
      split; [ intros node Hin x Hx; cbn [In] in Hin; destruct Hin as [<- | []];
               unfold get_args in Hx; cbn [op] in Hx; destruct Hx |].
      split; [ intros node Hin _; cbn [In] in Hin; destruct Hin as [<- | []];
               reflexivity |].
      intros node Hin Hop; cbn [In] in Hin; destruct Hin as [<- | []].
      exfalso. apply Hop. reflexivity. }
    pose proof (dataflow_ops_sem act a_idx ss input sinput sp Fin Hgr Hs Ho
                  Halign Hsinp Hrtp Hargp
                  (tfs_spec_action_ops ctx act) []
                  {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |}
                  sp Hne0 Hempty Hemvsz Hemfg Hpos0 ltac:(intros x [])
                  ltac:(intros x [])
                  ltac:(intros q bb [])
                  (sem_inv_empty act a_idx ss sinput sp
                     {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ];
                        var_map := [] |} eq_refl)) as Hmain.
    rewrite Ed in Hmain.
    destruct (Hmain (wgmono_refl Fin)) as [Hsem Hfr].
    assert (Hg0 : guard_holds act a_idx ss sinput []) by (intros q bb []).
    cbv zeta. split; [ | split; [ | split ] ].
    - intros sv n Hin Hv. rewrite Hvm in Hin.
      unfold SchedulerSimulationBase.node_ref_valid in Hv.
      exact (Hsem (DFG_SVar sv) n [] Hin Hg0 Hv).
    - intros ov n Hin Hv. rewrite Hvm in Hin.
      unfold SchedulerSimulationBase.node_ref_valid in Hv.
      exact (Hsem (DFG_OVar ov) n [] Hin Hg0 Hv).
    - intros sv Hno. apply (Hfr (DFG_SVar sv)).
      intros n Hin. apply (Hno n). rewrite Hvm. exact Hin.
    - intros ov Hno. apply (Hfr (DFG_OVar ov)).
      intros n Hin. apply (Hno n). rewrite Hvm. exact Hin.
  Qed.


  (* ==================================================================== *)
  (* THE ROUND TRIP.  Phase 3b settled which drives can take a port; what *)
  (* follows settles when, which is the cost model's business and not     *)
  (* this file's -- so it arrives as named hypotheses on the run.         *)
  (* ==================================================================== *)

  (* The buffers a guard keeps are the buffers a reference keeps. *)
  Lemma drive_sbufs_eq (act: tfs_action sched) a_idx :
    drive_sbufs act a_idx = sample_bufs act a_idx.
  Proof. reflexivity. Qed.

  (* A path condition with every literal up is up. *)
  Lemma guard_expr_ones (act: tfs_action sched) a_idx sbufs en
        (ss: sched_sys_state) (input: sched_input_t) :
    (forall l, In l en -> eval1 (guard_lit act a_idx sbufs l) ss input <> Bits.zero) ->
    eval1 (gexpr act a_idx sbufs en) ss input <> Bits.zero.
  Proof.
    rewrite guard_expr_fold. induction en as [| a en IH]; intro Hall.
    - cbn [fold_right]. rewrite eval1_const1. exact ones1_neq_zero.
    - cbn [fold_right tf_eval_expr].
      apply (proj2 (bits1_nonzero_ones _)).
      rewrite (proj1 (bits1_nonzero_ones _) (Hall a (or_introl eq_refl))).
      rewrite (proj1 (bits1_nonzero_ones _) (IH (fun l Hl => Hall l (or_intror Hl)))).
      reflexivity.
  Qed.

  (* [guard_holds] IS the compiled path condition being up. *)
  Lemma guard_holds_gexpr (act: tfs_action sched) a_idx
        (ss: sched_sys_state) (sinput: sched_input_t) en :
    guard_holds act a_idx ss sinput en ->
    eval1 (gexpr act a_idx (drive_sbufs act a_idx) en) ss sinput <> Bits.zero.
  Proof.
    intro Hgd. rewrite drive_sbufs_eq. apply guard_expr_ones.
    intros [c b] Hin. destruct (Hgd c b Hin) as [Ht Hf].
    unfold SchedulerSimulationBase.guard_lit. cbv zeta. cbn [fst snd].
    destruct b.
    - exact (Ht eq_refl).
    - cbn [tf_eval_expr]. unfold SchedulerSimulationBase.node_ref_expr in Hf. rewrite (Hf eq_refl).
      vm_compute. discriminate.
  Qed.

  (* A sample's VALUE is the response wire. *)
  Lemma compile_sample_value
        (dfg: dfg_state_t (states_var := s_var) (inputs_var := i_var)
                (outputs_var := o_var) (ips_var := p_var))
        tainted dfacts a_idx (n: nid_t) p tok en
        (bufs: list (nid_t * (nat * sz_t))) pi fuel :
    op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Sample p tok en ->
    BitsToLists.list_assoc bufs n = None ->
    0 < fuel ->
    fst (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx dfg n bufs)
    = tf_ivar (inr p).
  Proof.
    intros Hop Hbuf Hf. destruct fuel as [| fuel]; [ lia |].
    cbn [compile_dfg_expr_aux].
    destruct (BitsToLists.list_assoc bufs n) as [[m msz] |] eqn:E;
      [ exfalso; rewrite Hbuf in E; congruence |].
    cbv beta iota. rewrite Hop.
    destruct (compile_dfg_expr_aux ctx bneeds tainted dfacts pi fuel a_idx dfg tok bufs).
    reflexivity.
  Qed.

  (* A latched sample stays latched, and its answer stays put. *)
  Lemma sample_buffer_frozen_run
        (act: tfs_action sched) a_idx n_idx (input: input_t)
        (ss0: sched_sys_state) t d :
    act_idx_aligned act a_idx ->
    (forall m, (fst ss0).[tf_dfg_v a_idx m] = Bits.zero) ->
    (forall i, 1 <= i <= t + d -> ~ done_set (run_n i act input ss0)) ->
    is_sample_of act (vreg_nid a_idx n_idx) = true ->
    (fst (run_n t act input ss0)).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
    (fst (run_n (t + d) act input ss0)).[tf_dfg_b a_idx n_idx]
      = (fst (run_n t act input ss0)).[tf_dfg_b a_idx n_idx]
    /\ (fst (run_n (t + d) act input ss0)).[tf_dfg_v a_idx n_idx] = Bits.ones 1.
  Proof.
    intros Halign Hz0 Hpre Hsam Hv.
    induction d as [| d IH].
    - rewrite Nat.add_0_r. split; [ reflexivity | exact Hv ].
    - assert (Hpre' : forall i, 1 <= i <= t + d -> ~ done_set (run_n i act input ss0))
        by (intros i Hi; apply Hpre; lia).
      destruct (IH Hpre') as [Hb Hvd].
      assert (Hnd : ~ done_set (run_n (t + S d) act input ss0))
        by (apply Hpre; lia).
      rewrite Nat.add_succ_r in Hnd |- *.
      change (run_n (S (t + d)) act input ss0)
        with (sched_step act (run_n (t + d) act input ss0)
                (sched_input input (run_n (t + d) act input ss0))) in Hnd |- *.
      destruct (valid_settled_run act a_idx input ss0 (t + d) Halign Hz0)
        as [Hgates _].
      split.
      + rewrite <- (sample_buffer_frozen act a_idx n_idx
                      (run_n (t + d) act input ss0)
                      (sched_input input (run_n (t + d) act input ss0))
                      Halign Hnd Hsam Hvd).
        exact Hb.
      + exact (validity_monotone_step act a_idx n_idx
                 (run_n (t + d) act input ss0)
                 (sched_input input (run_n (t + d) act input ss0))
                 Halign Hnd Hgates Hvd).
  Qed.

  (* A validity bit that is up stays up for the rest of the run. *)
  Lemma validity_monotone_run
        (act: tfs_action sched) a_idx n_idx (input: input_t)
        (ss0: sched_sys_state) t d :
    act_idx_aligned act a_idx ->
    (forall m, (fst ss0).[tf_dfg_v a_idx m] = Bits.zero) ->
    (forall i, 1 <= i <= t + d -> ~ done_set (run_n i act input ss0)) ->
    (fst (run_n t act input ss0)).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
    (fst (run_n (t + d) act input ss0)).[tf_dfg_v a_idx n_idx] = Bits.ones 1.
  Proof.
    intros Halign Hz0 Hpre Hv.
    induction d as [| d IH].
    - rewrite Nat.add_0_r. exact Hv.
    - assert (Hpre' : forall i, 1 <= i <= t + d -> ~ done_set (run_n i act input ss0))
        by (intros i Hi; apply Hpre; lia).
      assert (Hnd : ~ done_set (run_n (t + S d) act input ss0)) by (apply Hpre; lia).
      rewrite Nat.add_succ_r in Hnd |- *.
      change (run_n (S (t + d)) act input ss0)
        with (sched_step act (run_n (t + d) act input ss0)
                (sched_input input (run_n (t + d) act input ss0))) in Hnd |- *.
      destruct (valid_settled_run act a_idx input ss0 (t + d) Halign Hz0) as [Hgates _].
      exact (validity_monotone_step act a_idx n_idx _ _ Halign Hnd Hgates (IH Hpre')).
  Qed.

  (* ... so a bit that is down now was down at every earlier cycle. *)
  Lemma validity_zero_earlier
        (act: tfs_action sched) a_idx n_idx (input: input_t)
        (ss0: sched_sys_state) j u :
    act_idx_aligned act a_idx ->
    (forall m, (fst ss0).[tf_dfg_v a_idx m] = Bits.zero) ->
    (forall i, 1 <= i <= u -> ~ done_set (run_n i act input ss0)) ->
    j <= u ->
    (fst (run_n u act input ss0)).[tf_dfg_v a_idx n_idx] = Bits.zero ->
    (fst (run_n j act input ss0)).[tf_dfg_v a_idx n_idx] = Bits.zero.
  Proof.
    intros Halign Hz0 Hpre Hle Hz.
    destruct (bits1_cases ((fst (run_n j act input ss0)).[tf_dfg_v a_idx n_idx]))
      as [Hj | Hj]; [ exfalso | exact Hj ].
    assert (Hu : j + (u - j) = u) by lia.
    pose proof (validity_monotone_run act a_idx n_idx input ss0 j (u - j)
                  Halign Hz0 ltac:(rewrite Hu; exact Hpre) Hj) as Hones.
    rewrite Hu, Hz in Hones. exact (ones1_neq_zero (eq_sym Hones)).
  Qed.

  (* A sample always has a buffer slot, and that slot is its register. *)
  Lemma sample_slot (act: tfs_action sched) a_idx n :
    act_idx_aligned act a_idx ->
    is_sample_of act n = true ->
    exists q qsz n_idx,
      BitsToLists.list_assoc
        (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) n = Some (q, qsz)
      /\ index_of_nat (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) q
         = Some n_idx
      /\ vreg_nid a_idx n_idx = n.
  Proof.
    intros Halign Hsam.
    destruct (BitsToLists.list_assoc (sample_bufs act a_idx) n) as [[q qsz] |] eqn:Hq;
      [| exfalso; exact (sample_is_buffered act a_idx n Halign Hsam Hq) ].
    pose proof (wla_in _ _ _ Hq) as Hin.
    unfold SchedulerSimulationBase.sample_bufs in Hin. apply filter_In in Hin. destruct Hin as [Hin _].
    assert (Hassoc : BitsToLists.list_assoc
                       (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) n
                     = Some (q, qsz))
      by (apply list_assoc_nodup_in; [ exact (slot_keys_nodup act a_idx Halign) | exact Hin ]).
    destruct (buffer_slot_of act a_idx n q qsz Halign Hassoc) as [n_idx [Hidx Hvn]].
    exists q, qsz, n_idx. split; [ exact Hassoc | split; [ exact Hidx | exact Hvn ] ].
  Qed.

  (* PHASE 3b'S PAYOFF.  While a call's answer is still outstanding, a LATER
     call on that port cannot take the wire: an exclusive path condition puts
     the pulse down directly, and every other one is held by the ordering join
     that waits on a sample no earlier than this one. *)


  (* Only the sentinel at position 0 is empty, so any node that carries an op
     sits strictly above it. *)
  Lemma build_dfg_nid_pos (act: tfs_action sched) :
    forall node, In node (graph (build_dfg ctx act)) ->
      op node <> DFG_Empty -> 1 <= nid node.
  Proof.
    assert (Hempty : gpos {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |}).
    { split; [ | split; [ | split; [ | split ] ] ].
      - cbn. lia.
      - intros k id Hin. destruct Hin.
      - intros node Hin x Hx. cbn in Hin. destruct Hin as [<-|[]]. cbn in Hx. destruct Hx.
      - intros node Hin He. cbn in Hin. destruct Hin as [<-|[]]. cbn. reflexivity.
      - intros node Hin He. cbn in Hin. destruct Hin as [<-|[]]. cbn in He.
        exfalso. apply He. reflexivity. }
    unfold build_dfg.
    pose proof (dataflow_ops_pos (tfs_spec_action_ops ctx act) []
                  {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |} Hempty
                  (fun x Hx => match Hx with end)) as Hop.
    destruct (dataflow_ops ctx [] (tfs_spec_action_ops ctx act)
                {| graph := [ {| nid := 0; op := DFG_Empty; sz := 0; |} ]; var_map := [] |})
      as [u final] eqn:Ed.
    destruct Hop as [_ [_ [_ [_ Hnz]]]].
    cbn [graph]. intros node Hin He. apply in_rev in Hin. exact (Hnz node Hin He).
  Qed.

  (* A node that carries an op is a real node of the graph. *)
  Lemma node_op_pos (act: tfs_action sched) n :
    node_op act n <> DFG_Empty ->
    1 <= n /\ n < length (graph (build_dfg ctx act)).
  Proof.
    intro Hne. pose proof (node_op_range act n Hne) as Hlt.
    split; [| exact Hlt ].
    pose proof (node_nid_at act n Hlt) as Hnid.
    rewrite <- Hnid. apply (build_dfg_nid_pos act); [ apply nth_In; exact Hlt | exact Hne ].
  Qed.
  (* A drive's compiled validity carries its guard's: wherever the drive is
     valid, the sources of every literal in its path condition have settled.
     This is what makes [guards_settled] a lemma rather than a hypothesis. *)
  Lemma compile_guard_sources_valid
        (act: tfs_action sched) a_idx n p arg en bufs pi fuel
        (ss: sched_sys_state) (input: sched_input_t) :
    node_op act n = DFG_Drive p arg en ->
    BitsToLists.list_assoc bufs n = None ->
    0 < fuel ->
    eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                  (build_dfg ctx act) n bufs)) ss input = Bits.ones 1 ->
    forall l, In l en ->
      eval1 (snd (compile_dfg_expr_at ctx bneeds pi (pred fuel) a_idx
                    (build_dfg ctx act) (fst l) bufs)) ss input = Bits.ones 1.
  Proof.
    intros Hop Hbuf Hf Hval l Hin.
    unfold SchedulerSimulationBase.node_op in Hop.
    rewrite (compile_drive_valid (build_dfg ctx act) _ _ a_idx n p arg en bufs pi fuel
               Hop Hbuf Hf) in Hval.
    refine (proj2 (proj1 (fold_valid_and_ones
              (fun m => snd (compile_dfg_expr_at ctx bneeds pi (pred fuel) a_idx
                               (build_dfg ctx act) m bufs)) _ ss input en) Hval) l Hin).
  Qed.

  (* A reference whose samples have all latched reads the same at every later
     cycle of the run: the state it reads is frozen from there on. *)
  Lemma node_ref_stable_run
        (act: tfs_action sched) a_idx (input: input_t) (ss0: sched_sys_state)
        (c: nid_t) w u szB :
    act_idx_aligned act a_idx ->
    (forall m, (fst ss0).[tf_dfg_v a_idx m] = Bits.zero) ->
    (forall i, 1 <= i <= u -> ~ done_set (run_n i act input ss0)) ->
    w <= u ->
    c < length (graph (build_dfg ctx act)) ->
    eval1 (node_ref_valid act a_idx c) (run_n w act input ss0)
      (sched_input input (run_n w act input ss0)) = Bits.ones 1 ->
    tf_eval_expr ss_sz si_sz oo_sz (szB := szB) (node_ref_expr act a_idx c)
      (run_n w act input ss0) (sched_input input (run_n w act input ss0))
    = tf_eval_expr ss_sz si_sz oo_sz (szB := szB) (node_ref_expr act a_idx c)
      (run_n u act input ss0) (sched_input input (run_n u act input ss0)).
  Proof.
    intros Halign Hz0 Hpre Hle Hclen Hval.
    assert (Hpw : forall i, 1 <= i <= w -> ~ done_set (run_n i act input ss0))
      by (intros i Hi; apply Hpre; lia).
    assert (Hsvar : forall s, (fst (run_n w act input ss0)).[tf_dfg_s s]
                      = (fst (run_n u act input ss0)).[tf_dfg_s s]).
    { intro s. rewrite (run_preserves_svar act input ss0 w Hpw s).
      rewrite (run_preserves_svar act input ss0 u Hpre s). reflexivity. }
    assert (Hovar : forall o, (snd (run_n w act input ss0)).[o]
                      = (snd (run_n u act input ss0)).[o]).
    { intro o. rewrite (run_preserves_ovar act input ss0 w Hpw o).
      rewrite (run_preserves_ovar act input ss0 u Hpre o). reflexivity. }
    assert (Hbfroz : forall q_idx, is_sample_of act (vreg_nid a_idx q_idx) = true ->
              (fst (run_n w act input ss0)).[tf_dfg_v a_idx q_idx] = Bits.ones 1 ->
              (fst (run_n w act input ss0)).[tf_dfg_b a_idx q_idx]
              = (fst (run_n u act input ss0)).[tf_dfg_b a_idx q_idx]).
    { intros q_idx Hsq Hvq.
      assert (He : w + (u - w) = u) by lia.
      assert (Hpt : forall i, 1 <= i <= w + (u - w) ->
                ~ done_set (run_n i act input ss0))
        by (intros i Hi; apply Hpre; lia).
      destruct (sample_buffer_frozen_run act a_idx q_idx input ss0 w (u - w)
                  Halign Hz0 Hpt Hsq Hvq) as [Hb _].
      rewrite He in Hb. exact (eq_sym Hb). }
    exact (compile_nobuf_state_indep act a_idx
             (sched_input input (run_n w act input ss0))
             (sched_input input (run_n u act input ss0))
             (run_n w act input ss0) (run_n u act input ss0)
             Halign Hsvar Hovar ltac:(intro v; reflexivity) Hbfroz
             (length (graph (build_dfg ctx act))) c szB Hclen Hval).
  Qed.

  (* The node whose validity gates a drive's pulse is the drive itself, or the
     ordering join in front of it. *)
  Lemma chain_gate_cases (act: tfs_action sched) n g h :
    chain_gate ctx (build_dfg ctx act) n = Some (g, h) ->
    g = n \/ exists prev, node_op act g = DFG_Join n prev.
  Proof.
    unfold chain_gate. cbv zeta.
    destruct (find (fun nd => match op nd with
                              | DFG_Stall _ a => Nat.eqb a n
                              | _ => false
                              end) (graph (build_dfg ctx act))) as [nds |].
    - intro H. injection H as <- _. left. reflexivity.
    - destruct (find (fun nd => match op nd with
                                | DFG_Join a _ => Nat.eqb a n
                                | _ => false
                                end) (graph (build_dfg ctx act))) as [j |] eqn:Ej;
        [| discriminate ].
      destruct (find (fun nd => match op nd with
                                | DFG_Stall _ a => Nat.eqb a (nid j)
                                | _ => false
                                end) (graph (build_dfg ctx act))) as [nd2 |];
        [| discriminate ].
      intro H. injection H as <- _. right.
      apply find_some in Ej. destruct Ej as [Hin Hpred].
      destruct (op j) as [ c | v | v | uop a1 | bop a1 a2 | a1 | cd t1 e1
                         | sl sa | dov dn den | siv sn sen | ja jb | ] eqn:Ejop;
        try discriminate.
      apply Nat.eqb_eq in Hpred. subst ja.
      exists jb. destruct (node_at_nid act j Hin) as [_ Hnth].
      unfold SchedulerSimulationBase.node_op. rewrite Hnth, Ejop. reflexivity.
  Qed.


  (* ... and so it has a slot in this action's table, which is the form
     [sample_gate_cases] and [stall_gate_walks] ask for. *)
  Lemma stall_has_slot (act: tfs_action sched) a_idx s t l a :
    act_idx_aligned act a_idx ->
    In s (graph (build_dfg ctx act)) ->
    In t (graph (build_dfg ctx act)) ->
    In (nid t) (get_args ctx s) ->
    op t = DFG_Stall l a ->
    BitsToLists.list_assoc
      (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) (nid t) <> None.
  Proof.
    intros Halign Hs Ht Harg Hop.
    pose proof (stall_is_buffered act s t l a Hs Ht Harg Hop) as Hin.
    assert (Hfst : In (nid t) (map fst (nth (index_to_nat a_idx)
                                          (buffer_needs ctx cost_limit) []))).
    { rewrite (buffer_slot_eq act a_idx Halign), gsi_map_fst. exact Hin. }
    apply in_map_iff in Hfst. destruct Hfst as [[n' v] [Heq Hentry]].
    cbn [fst] in Heq. subst n'.
    apply (list_assoc_in_some _ (nid t) v). exact Hentry.
  Qed.

  (* What [chain_gate] returns as its second component is a stall on the first. *)
  Lemma chain_gate_stall (act: tfs_action sched) n g h :
    chain_gate ctx (build_dfg ctx act) n = Some (g, h) ->
    exists l, node_op act h = DFG_Stall l g.
  Proof.
    assert (Hstall : forall m nd,
              find (fun nd0 => match op nd0 with
                               | DFG_Stall _ a => Nat.eqb a m
                               | _ => false
                               end) (graph (build_dfg ctx act)) = Some nd ->
              exists l, node_op act (nid nd) = DFG_Stall l m).
    { intros m nd Hf. apply find_some in Hf. destruct Hf as [Hin Hp].
      destruct (node_at_nid act nd Hin) as [_ Hnth].
      destruct (op nd) as [ | | | | | | | l aa | | | | ] eqn:Hop;
        try discriminate Hp.
      apply Nat.eqb_eq in Hp. subst aa.
      exists l. unfold SchedulerSimulationBase.node_op. rewrite Hnth. exact Hop. }
    unfold chain_gate. cbv zeta.
    destruct (find (fun nd => match op nd with
                              | DFG_Stall _ a => Nat.eqb a n
                              | _ => false
                              end) (graph (build_dfg ctx act))) as [nds |] eqn:E1.
    - intro H. injection H as <- <-. exact (Hstall n nds E1).
    - destruct (find (fun nd => match op nd with
                                | DFG_Join a _ => Nat.eqb a n
                                | _ => false
                                end) (graph (build_dfg ctx act))) as [ndj |] eqn:E2;
        [| discriminate ].
      destruct (find (fun nd => match op nd with
                                | DFG_Stall _ a => Nat.eqb a (nid ndj)
                                | _ => false
                                end) (graph (build_dfg ctx act))) as [nds2 |] eqn:E3;
        [| discriminate ].
      intro H. injection H as <- <-. exact (Hstall (nid ndj) nds2 E3).
  Qed.

  (* ... and it is the very stall the call's sample reads. *)
  Lemma chain_gate_stall_is_token
        (act: tfs_action sched) (p: p_var) samp tok en d g h :
    node_op act samp = DFG_Sample p tok en ->
    sample_drive act samp = Some d ->
    chain_gate ctx (build_dfg ctx act) d = Some (g, h) ->
    h = tok.
  Proof.
    intros Hsamp Hsd Hcg.
    destruct (chain_gate_stall act d g h Hcg) as [lh Hh].
    pose proof (stall_nid_succ act h lh g Hh) as Hhs.
    (* the token is a stall, on the head the walk used *)
    assert (Hslen : samp < length (graph (build_dfg ctx act)))
      by (apply node_op_range; rewrite Hsamp; discriminate).
    assert (Hsin : In (nth samp (graph (build_dfg ctx act))
                         {| nid := 0; op := DFG_Empty; sz := 0 |})
                      (graph (build_dfg ctx act)))
      by (apply nth_In; exact Hslen).
    assert (Hsraw : op (nth samp (graph (build_dfg ctx act))
                          {| nid := 0; op := DFG_Empty; sz := 0 |})
                    = DFG_Sample p tok en) by exact Hsamp.
    destruct (samples_stalled_build_dfg act _ p tok en Hsin Hsraw)
      as [t [lt [aa [Ht [Htid Htop]]]]].
    destruct (node_at_nid act t Ht) as [_ Hnth].
    assert (Htok : node_op act tok = DFG_Stall lt aa)
      by (unfold SchedulerSimulationBase.node_op; rewrite <- Htid, Hnth; exact Htop).
    pose proof (stall_nid_succ act tok lt aa Htok) as Htoks.
    assert (Hsdh : sample_drive_head act p aa = Some d)
      by (unfold SchedulerSimulationBase.sample_drive in Hsd; rewrite Hsamp, Htok in Hsd; exact Hsd).
    (* both heads are [d] itself or the ordering join above it *)
    destruct (sample_drive_head_shape act p aa d Hsdh)
      as [[Hdaa [ar1 [e1 Haadr]]] | [prev' [ar2 [e2 [Haaj Hd2dr]]]]];
      destruct (chain_gate_cases act d g h Hcg) as [Hgd | [prev Hgj]].
    - lia.
    - exfalso. subst d.
      exact (no_stall_on_joined act g aa prev tok lt p ar1 e1 Haadr Hgj Htok).
    - exfalso. subst g.
      exact (no_stall_on_joined act aa d prev' h lh p ar2 e2 Hd2dr Haaj Hh).
    - pose proof (join_nid_succ act g d prev p ar2 e2 Hgj Hd2dr) as Hgs.
      pose proof (join_nid_succ act aa d prev' p ar2 e2 Haaj Hd2dr) as Has.
      lia.
  Qed.

  (* [nre_fuel]'s twin for the validity half. *)
  Lemma nrv_fuel (act: tfs_action sched) a_idx x f :
    1 <= x -> x < length (graph (build_dfg ctx act)) -> x < f ->
    snd (compile_dfg_expr ctx bneeds f a_idx (build_dfg ctx act) x (sample_bufs act a_idx))
    = node_ref_valid act a_idx x.
  Proof.
    intros H1 H2 H3. unfold SchedulerSimulationBase.node_ref_valid.
    rewrite (compile_fuel_irrel act a_idx (sample_bufs act a_idx) x H1 H2 f
               (length (graph (build_dfg ctx act))) H3 H2).
    reflexivity.
  Qed.

  (* WHY [guards_settled] IS NOT A HYPOTHESIS.  A drive fires on the one cycle
     its stall starts, and its validity -- hence the gate that lets it fire --
     now carries its guard's.  So wherever a guarded call pulses, every source
     its path condition reads has already settled. *)
  Lemma drive_pulse_guard_valid
        (act: tfs_action sched) a_idx n p arg en
        (ss: sched_sys_state) (input: sched_input_t) :
    act_idx_aligned act a_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    valid_settled act a_idx ss input ->
    valid_refs act a_idx ss input ->
    node_op act n = DFG_Drive p arg en ->
    eval1 (drive_pulse act a_idx n) ss input <> Bits.zero ->
    forall l, In l en ->
      eval1 (node_ref_valid act a_idx (fst l)) ss input = Bits.ones 1.
  Proof.
    intros Halign Hlen Hinv Hrefs Hop Hpulse l Hin.
    destruct (node_op_pos act n ltac:(rewrite Hop; discriminate)) as [Hn1 Hnlen].
    assert (Hopb : op (nth n (graph (build_dfg ctx act))
                         {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Drive p arg en)
      by exact Hop.
    assert (Hsub : forall e,
              In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) ->
              In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))
      by (intros e He; exact He).
    assert (Hsam_sub : forall x,
              BitsToLists.list_assoc
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) x = None ->
              BitsToLists.list_assoc (sample_bufs act a_idx) x = None).
    { intros x Hx. apply list_assoc_key_none. intro Hin2.
      apply in_map_iff in Hin2. destruct Hin2 as [[x2 v2] [Hxx Hmem2]].
      cbn [fst] in Hxx. subst x2.
      unfold SchedulerSimulationBase.sample_bufs in Hmem2. apply filter_In in Hmem2.
      apply (list_assoc_none_key _ _ Hx), in_map_iff.
      exists (x, v2). split; [ reflexivity | exact (proj1 Hmem2) ]. }
    assert (Hsam_same : forall x m msz,
              BitsToLists.list_assoc
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) x
                = Some (m, msz) ->
              is_sample_of act x = true ->
              BitsToLists.list_assoc (sample_bufs act a_idx) x = Some (m, msz)).
    { intros x m msz Hx Hsx. apply list_assoc_nodup_in.
      - unfold SchedulerSimulationBase.sample_bufs. apply nodup_map_fst_filter.
        exact (slot_keys_nodup act a_idx Halign).
      - unfold SchedulerSimulationBase.sample_bufs. apply filter_In.
        split; [ exact (wla_in _ _ _ Hx) | exact Hsx ]. }
    (* the node whose validity gates the pulse, and that validity *)
    assert (Hgate : exists m, (m = n \/ exists prev, node_op act m = DFG_Join n prev)
              /\ eval1 (snd (compile_dfg_expr ctx bneeds
                               (length (graph (build_dfg ctx act))) a_idx
                               (build_dfg ctx act) m
                               (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])))
                   ss input = Bits.ones 1).
    { unfold SchedulerSimulationBase.drive_pulse in Hpulse. cbv zeta in Hpulse.
      destruct (chain_gate ctx (build_dfg ctx act) n) as [[g h] |] eqn:Hcg.
      - exists g. split; [ exact (chain_gate_cases act n g h Hcg) |].
        cbn [tf_eval_expr] in Hpulse.
        apply (proj1 (bits1_nonzero_ones _)) in Hpulse.
        destruct (bits1_and_split _ _ Hpulse) as [_ H2].
        exact (proj1 (bits1_and_split _ _ H2)).
      - exists n. split; [ left; reflexivity |].
        cbn [tf_eval_expr] in Hpulse.
        apply (proj1 (bits1_nonzero_ones _)) in Hpulse.
        destruct (bits1_and_split _ _ Hpulse) as [_ H2].
        exact (proj1 (bits1_and_split _ _ H2)). }
    destruct Hgate as [m [Hmshape Hmval]].
    assert (Hmpos : 1 <= m /\ m < length (graph (build_dfg ctx act))).
    { destruct Hmshape as [-> | [prev Hj]]; [ split; assumption |].
      exact (node_op_pos act m ltac:(rewrite Hj; discriminate)). }
    destruct Hmpos as [Hm1 Hmlen].
    assert (Hmref : eval1 (node_ref_valid act a_idx m) ss input = Bits.ones 1).
    { rewrite <- (nrv_fuel act a_idx m (length (graph (build_dfg ctx act)))
                    Hm1 Hmlen Hmlen).
      exact (compile_subst_ref_valid_gen act a_idx ss input Halign Hinv Hrefs
               (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])
               Hsub Hsam_sub Hsam_same (length (graph (build_dfg ctx act))) m []
               Hm1 Hmlen Hmlen Hmval). }
    (* down through the ordering join, if there is one, to the drive *)
    assert (Hnref : eval1 (node_ref_valid act a_idx n) ss input = Bits.ones 1).
    { destruct Hmshape as [-> | [prev Hj]]; [ exact Hmref |].
      pose proof (join_nid_succ act m n prev p arg en Hj Hop) as Hms.
      unfold SchedulerSimulationBase.node_ref_valid in Hmref.
      rewrite (compile_join_valid (build_dfg ctx act) _ _ a_idx m n prev
                 (sample_bufs act a_idx) [] (length (graph (build_dfg ctx act)))
                 Hj
                 (not_sample_not_in_sample_bufs act a_idx m
                    ltac:(unfold SchedulerSimulationBase.is_sample_of; rewrite Hj; reflexivity))
                 ltac:(lia)) in Hmref.
      rewrite valid_and_eval in Hmref.
      destruct (bits1_and_split _ _ Hmref) as [Hnv _].
      rewrite (nrv_fuel act a_idx n (pred (length (graph (build_dfg ctx act))))
                 Hn1 Hnlen ltac:(lia)) in Hnv.
      exact Hnv. }
    (* and on to the literal's own source *)
    unfold SchedulerSimulationBase.node_ref_valid in Hnref.
    pose proof (compile_guard_sources_valid act a_idx n p arg en
                  (sample_bufs act a_idx) [] (length (graph (build_dfg ctx act)))
                  ss input Hop
                  (not_sample_not_in_sample_bufs act a_idx n
                     ltac:(unfold SchedulerSimulationBase.is_sample_of; rewrite Hop; reflexivity))
                  ltac:(lia) Hnref l Hin) as Hl.
    assert (Hlin : In (fst l) (get_args ctx (nth n (graph (build_dfg ctx act))
                                 {| nid := 0; op := DFG_Empty; sz := 0 |})))
      by (unfold get_args; rewrite Hopb; right; exact (in_map fst en l Hin)).
    destruct (node_args_range act n Hn1 Hnlen (fst l) Hlin) as [Hl1 Hl2].
    rewrite (nrv_fuel act a_idx (fst l) (pred (length (graph (build_dfg ctx act))))
               Hl1 ltac:(lia) ltac:(lia)) in Hl.
    exact Hl.
  Qed.

  (* Two calls in mutually exclusive branches never hold one port at once --
     now at the level of the RUN, with no assumption about when guards settle.
     A drive that pulses has had its guard's sources settle, and a settled
     source reads the same at the end of the run, where [guard_holds] pins it. *)
  Lemma excl_drive_pulse_zero
        (act: tfs_action sched) a_idx (p: p_var) en_s mm arg_m en_m
        (input: input_t) (ss0: sched_sys_state) u M :
    act_idx_aligned act a_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    (forall q, (fst ss0).[tf_dfg_v a_idx q] = Bits.zero) ->
    (forall i, 1 <= i <= M -> ~ done_set (run_n i act input ss0)) ->
    u <= M ->
    node_op act mm = DFG_Drive p arg_m en_m ->
    guards_disjoint en_m en_s = true ->
    guard_holds act a_idx (run_n M act input ss0)
      (sched_input input (run_n M act input ss0)) en_s ->
    eval1 (drive_pulse act a_idx mm) (run_n u act input ss0)
      (sched_input input (run_n u act input ss0)) = Bits.zero.
  Proof.
    intros Halign Hlen Hzv Hpre Hu Hm Hdis Hgd.
    destruct (bits1_cases (eval1 (drive_pulse act a_idx mm) (run_n u act input ss0)
                             (sched_input input (run_n u act input ss0))))
      as [Hone | Hz]; [ exfalso | exact Hz ].
    assert (Hnz : eval1 (drive_pulse act a_idx mm) (run_n u act input ss0)
                    (sched_input input (run_n u act input ss0)) <> Bits.zero)
      by (rewrite Hone; exact ones1_neq_zero).
    destruct (valid_settled_run act a_idx input ss0 u Halign Hzv) as [_ [Hrefs Hinv]].
    (* the literal the two guards disagree on *)
    unfold guards_disjoint in Hdis.
    apply existsb_exists in Hdis. destruct Hdis as [l1 [Hin1 Hex2]].
    apply existsb_exists in Hex2. destruct Hex2 as [l2 [Hin2 Hb]].
    apply andb_true_iff in Hb. destruct Hb as [Hfst Hsnd].
    apply Nat.eqb_eq in Hfst. apply negb_true_iff in Hsnd.
    apply Bool.eqb_false_iff in Hsnd.
    destruct l1 as [c1 b1]; destruct l2 as [c2 b2].
    cbn [fst snd] in Hfst, Hsnd. subst c2.
    (* its source has settled wherever this drive pulses ... *)
    pose proof (drive_pulse_guard_valid act a_idx mm p arg_m en_m
                  (run_n u act input ss0) (sched_input input (run_n u act input ss0))
                  Halign Hlen Hinv Hrefs Hm Hnz (c1, b1) Hin1) as Hcv.
    cbn [fst] in Hcv.
    destruct (node_op_pos act mm ltac:(rewrite Hm; discriminate)) as [Hm1 Hmlen].
    assert (Hlin : In c1 (get_args ctx (nth mm (graph (build_dfg ctx act))
                            {| nid := 0; op := DFG_Empty; sz := 0 |})))
      by (unfold get_args; unfold SchedulerSimulationBase.node_op in Hm; rewrite Hm; right;
          exact (in_map fst en_m (c1, b1) Hin1)).
    destruct (node_args_range act mm Hm1 Hmlen c1 Hlin) as [Hc1 Hc2].
    (* ... so it reads the same at the end of the run, where [guard_holds] pins it *)
    pose proof (node_ref_stable_run act a_idx input ss0 c1 u M 1
                  Halign Hzv Hpre Hu ltac:(lia) Hcv) as Hst.
    destruct (Hgd c1 b2 Hin2) as [Ht Hf].
    assert (Hz2 : eval1 (drive_pulse act a_idx mm) (run_n u act input ss0)
                    (sched_input input (run_n u act input ss0)) = Bits.zero).
    { apply (drive_pulse_zero_of_en act a_idx mm p arg_m en_m _ _ Hm).
      rewrite drive_sbufs_eq.
      apply (guard_expr_zero act a_idx (sample_bufs act a_idx) en_m (c1, b1) _ _ Hin1).
      unfold SchedulerSimulationBase.guard_lit. cbv zeta. cbn [fst snd].
      unfold SchedulerSimulationBase.node_ref_expr in Hst, Ht, Hf.
      destruct b1; destruct b2; try (exfalso; apply Hsnd; reflexivity).
      - rewrite Hst. exact (Hf eq_refl).
      - cbn [tf_eval_expr]. rewrite Hst.
        rewrite (proj1 (bits1_nonzero_ones _) (Ht eq_refl)).
        exact bits1_neg_ones. }
    rewrite Hz2 in Hone. exact (ones1_neq_zero (eq_sym Hone)).
  Qed.

  (* THE PENDING TREE, DESCENDED.  Wherever the tree of joins a call waits on
     reads as valid, so does every sample in it; a buffered node inside speaks
     for the cycle before, which is why the run appears here. *)
  Lemma pleaf_valid_ones
        (act: tfs_action sched) a_idx (input: input_t) (ss0: sched_sys_state) :
    act_idx_aligned act a_idx ->
    (forall qv, (fst ss0).[tf_dfg_v a_idx qv] = Bits.zero) ->
    forall u, (forall i, 1 <= i <= u -> ~ done_set (run_n i act input ss0)) ->
    forall root s, pleaf (graph (build_dfg ctx act)) root s ->
    forall (s_idx : Vect.index
              (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])))
           bufs fuel q qsz,
      is_sample_of act s = true ->
      BitsToLists.list_assoc bufs s = Some (q, qsz) ->
      index_of_nat (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) q
        = Some s_idx ->
      (forall n e, BitsToLists.list_assoc bufs n = Some e ->
         BitsToLists.list_assoc
           (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) n = Some e) ->
      root < fuel ->
      eval1 (snd (compile_dfg_expr ctx bneeds fuel a_idx (build_dfg ctx act) root bufs))
        (run_n u act input ss0) (sched_input input (run_n u act input ss0))
        = Bits.ones 1 ->
      (fst (run_n u act input ss0)).[tf_dfg_v a_idx s_idx] = Bits.ones 1.
  Proof.
    intros Halign Hzv u.
    induction u as [u IHu] using (well_founded_induction lt_wf).
    intros Hpre root s Hleaf.
    induction Hleaf as [ n | nj a b s Hin Hop Hleaf IH | nj a b s Hin Hop Hleaf IH ];
      intros s_idx bufs fuel q qsz Hsam Hbs Hqidx Hsub Hfuel Hones.
    - assert (Hf0 : 0 < fuel) by lia.
      rewrite (compile_buffered_valid _ _ _ a_idx n bufs q qsz s_idx fuel []
                 Hbs Hqidx Hf0) in Hones.
      rewrite eval1_svar_v in Hones. exact Hones.
    - destruct (node_at_nid act nj Hin) as [Hnjlen Hnjat].
      assert (Hf0 : 0 < fuel) by lia.
      assert (Hopat : op (nth (nid nj) (graph (build_dfg ctx act))
                              {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Join a b)
        by (rewrite Hnjat; exact Hop).
      destruct (BitsToLists.list_assoc bufs (nid nj)) as [[m0 msz] |] eqn:Enj.
      + pose proof (Hsub (nid nj) (m0, msz) Enj) as Hreal.
        destruct (buffer_slot_of act a_idx (nid nj) m0 msz Halign Hreal)
          as [nj_idx [Hnjidx Hnjvn]].
        rewrite (compile_buffered_valid _ _ _ a_idx (nid nj) bufs m0 msz nj_idx fuel []
                   Enj Hnjidx Hf0) in Hones.
        rewrite eval1_svar_v in Hones.
        destruct u as [| j].
        { exfalso. cbn [run_n] in Hones. rewrite Hzv in Hones.
          exact (ones1_neq_zero (eq_sym Hones)). }
        assert (Hnd : ~ done_set (run_n (S j) act input ss0)) by (apply Hpre; lia).
        change (run_n (S j) act input ss0)
          with (sched_step act (run_n j act input ss0)
                  (sched_input input (run_n j act input ss0))) in Hones, Hnd.
        pose proof (buffer_valid_gate act a_idx nj_idx (run_n j act input ss0)
                      (sched_input input (run_n j act input ss0)) Halign Hnd Hones) as Hgate.
        rewrite Hnjvn in Hgate.
        assert (Hsnj : s <> nid nj).
        { intro He. rewrite He in Hsam. unfold SchedulerSimulationBase.is_sample_of in Hsam.
          unfold SchedulerSimulationBase.node_op in Hsam. rewrite Hopat in Hsam. discriminate Hsam. }
        assert (HsubF : forall n0 e,
                  BitsToLists.list_assoc
                    (filter (fun '(b_nid, _) => negb (Nat.eqb b_nid (nid nj)))
                       (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) n0
                    = Some e ->
                  BitsToLists.list_assoc
                    (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) n0 = Some e).
        { intros n0 e He. pose proof (wla_in _ _ _ He) as Hin0.
          apply filter_In in Hin0. destruct Hin0 as [Hin1 _].
          apply list_assoc_nodup_in;
            [ exact (slot_keys_nodup act a_idx Halign) | exact Hin1 ]. }
        assert (HfiltS : BitsToLists.list_assoc
                  (filter (fun '(b_nid, _) => negb (Nat.eqb b_nid (nid nj)))
                     (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) s
                  = Some (q, qsz)).
        { rewrite list_assoc_filter; [ exact (Hsub s (q, qsz) Hbs) |].
          intros [k v] _ Hfe. cbn [fst] in Hfe. subst k.
          apply negb_true_iff, Nat.eqb_neq. exact Hsnj. }
        assert (Hjlt : j < S j) by lia.
        assert (Hprej : forall i, 1 <= i <= j -> ~ done_set (run_n i act input ss0))
          by (intros i Hi; apply Hpre; lia).
        pose proof (IHu j Hjlt Hprej (nid nj) s
                      (pleaf_left (graph (build_dfg ctx act)) nj a b s Hin Hop Hleaf)
                      s_idx _ (length (graph (build_dfg ctx act))) q qsz
                      Hsam HfiltS Hqidx HsubF Hnjlen Hgate) as Hj.
        pose proof (validity_monotone_run act a_idx s_idx input ss0 j 1
                      Halign Hzv ltac:(rewrite Nat.add_1_r; exact Hpre) Hj) as Hmono.
        rewrite Nat.add_1_r in Hmono. exact Hmono.
      + rewrite (compile_join_valid _ _ _ a_idx (nid nj) a b bufs [] fuel
                   Hopat Enj Hf0) in Hones.
        rewrite valid_and_eval in Hones.
        destruct (bits1_and_split _ _ Hones) as [Ha _].
        assert (Hga : In a (get_args ctx nj)) by (unfold get_args; rewrite Hop; left; reflexivity).
        pose proof (args_lt_fwd act nj Hin a Hga) as Halt.
        assert (Hfa : a < pred fuel) by lia.
        exact (IH s_idx bufs (pred fuel) q qsz Hsam Hbs Hqidx Hsub Hfa Ha).
    - destruct (node_at_nid act nj Hin) as [Hnjlen Hnjat].
      assert (Hf0 : 0 < fuel) by lia.
      assert (Hopat : op (nth (nid nj) (graph (build_dfg ctx act))
                              {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Join a b)
        by (rewrite Hnjat; exact Hop).
      destruct (BitsToLists.list_assoc bufs (nid nj)) as [[m0 msz] |] eqn:Enj.
      + pose proof (Hsub (nid nj) (m0, msz) Enj) as Hreal.
        destruct (buffer_slot_of act a_idx (nid nj) m0 msz Halign Hreal)
          as [nj_idx [Hnjidx Hnjvn]].
        rewrite (compile_buffered_valid _ _ _ a_idx (nid nj) bufs m0 msz nj_idx fuel []
                   Enj Hnjidx Hf0) in Hones.
        rewrite eval1_svar_v in Hones.
        destruct u as [| j].
        { exfalso. cbn [run_n] in Hones. rewrite Hzv in Hones.
          exact (ones1_neq_zero (eq_sym Hones)). }
        assert (Hnd : ~ done_set (run_n (S j) act input ss0)) by (apply Hpre; lia).
        change (run_n (S j) act input ss0)
          with (sched_step act (run_n j act input ss0)
                  (sched_input input (run_n j act input ss0))) in Hones, Hnd.
        pose proof (buffer_valid_gate act a_idx nj_idx (run_n j act input ss0)
                      (sched_input input (run_n j act input ss0)) Halign Hnd Hones) as Hgate.
        rewrite Hnjvn in Hgate.
        assert (Hsnj : s <> nid nj).
        { intro He. rewrite He in Hsam. unfold SchedulerSimulationBase.is_sample_of in Hsam.
          unfold SchedulerSimulationBase.node_op in Hsam. rewrite Hopat in Hsam. discriminate Hsam. }
        assert (HsubF : forall n0 e,
                  BitsToLists.list_assoc
                    (filter (fun '(b_nid, _) => negb (Nat.eqb b_nid (nid nj)))
                       (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) n0
                    = Some e ->
                  BitsToLists.list_assoc
                    (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) n0 = Some e).
        { intros n0 e He. pose proof (wla_in _ _ _ He) as Hin0.
          apply filter_In in Hin0. destruct Hin0 as [Hin1 _].
          apply list_assoc_nodup_in;
            [ exact (slot_keys_nodup act a_idx Halign) | exact Hin1 ]. }
        assert (HfiltS : BitsToLists.list_assoc
                  (filter (fun '(b_nid, _) => negb (Nat.eqb b_nid (nid nj)))
                     (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) s
                  = Some (q, qsz)).
        { rewrite list_assoc_filter; [ exact (Hsub s (q, qsz) Hbs) |].
          intros [k v] _ Hfe. cbn [fst] in Hfe. subst k.
          apply negb_true_iff, Nat.eqb_neq. exact Hsnj. }
        assert (Hjlt : j < S j) by lia.
        assert (Hprej : forall i, 1 <= i <= j -> ~ done_set (run_n i act input ss0))
          by (intros i Hi; apply Hpre; lia).
        pose proof (IHu j Hjlt Hprej (nid nj) s
                      (pleaf_right (graph (build_dfg ctx act)) nj a b s Hin Hop Hleaf)
                      s_idx _ (length (graph (build_dfg ctx act))) q qsz
                      Hsam HfiltS Hqidx HsubF Hnjlen Hgate) as Hj.
        pose proof (validity_monotone_run act a_idx s_idx input ss0 j 1
                      Halign Hzv ltac:(rewrite Nat.add_1_r; exact Hpre) Hj) as Hmono.
        rewrite Nat.add_1_r in Hmono. exact Hmono.
      + rewrite (compile_join_valid _ _ _ a_idx (nid nj) a b bufs [] fuel
                   Hopat Enj Hf0) in Hones.
        rewrite valid_and_eval in Hones.
        destruct (bits1_and_split _ _ Hones) as [_ Hb].
        assert (Hgb : In b (get_args ctx nj))
          by (unfold get_args; rewrite Hop; right; left; reflexivity).
        pose proof (args_lt_fwd act nj Hin b Hgb) as Hblt.
        assert (Hfb : b < pred fuel) by lia.
        exact (IH s_idx bufs (pred fuel) q qsz Hsam Hbs Hqidx Hsub Hfb Hb).
  Qed.

  (* A sample is a LEAF of the reference, so its reference validity is just
     its own register: the one place where "has this latched" is visible. *)
  Lemma nrv_sample (act: tfs_action sched) a_idx n_idx :
    act_idx_aligned act a_idx ->
    is_sample_of act (vreg_nid a_idx n_idx) = true ->
    node_ref_valid act a_idx (vreg_nid a_idx n_idx)
    = tf_svar (tf_dfg_v a_idx n_idx).
  Proof.
    intros Halign Hsam.
    destruct (vreg_nid_node_range act a_idx n_idx Halign) as [_ Hnlen].
    unfold SchedulerSimulationBase.node_ref_valid.
    rewrite (sample_ref_is_register act a_idx n_idx Halign Hsam []
               (length (graph (build_dfg ctx act))) Hnlen).
    reflexivity.
  Qed.

  (* The twin of [compile_guard_sources_valid] on the fold's BASE: a drive
     that reads as valid has a settled ARGUMENT, not just a settled guard. *)
  Lemma compile_drive_arg_valid
        (act: tfs_action sched) a_idx n p arg en bufs pi fuel
        (ss: sched_sys_state) (input: sched_input_t) :
    node_op act n = DFG_Drive p arg en ->
    BitsToLists.list_assoc bufs n = None ->
    0 < fuel ->
    eval1 (snd (compile_dfg_expr_at ctx bneeds pi fuel a_idx
                  (build_dfg ctx act) n bufs)) ss input = Bits.ones 1 ->
    eval1 (snd (compile_dfg_expr_at ctx bneeds pi (pred fuel) a_idx
                  (build_dfg ctx act) arg bufs)) ss input = Bits.ones 1.
  Proof.
    intros Hop Hbuf Hf Hval.
    unfold SchedulerSimulationBase.node_op in Hop.
    rewrite (compile_drive_valid (build_dfg ctx act) _ _ a_idx n p arg en bufs pi fuel
               Hop Hbuf Hf) in Hval.
    exact (proj1 (proj1 (fold_valid_and_ones
                           (fun z => snd (compile_dfg_expr_at ctx bneeds pi (pred fuel)
                                            a_idx (build_dfg ctx act) z bufs))
                           (snd (compile_dfg_expr_at ctx bneeds pi (pred fuel)
                                   a_idx (build_dfg ctx act) arg bufs))
                           ss input en) Hval)).
  Qed.

  Lemma no_later_drive
        (act: tfs_action sched) a_idx (p: p_var) samp tok en_s d m
        (input: input_t) (ss0: sched_sys_state) (u: nat) :
    act_idx_aligned act a_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    (forall x, zeroed_at_start x -> (fst ss0).[x] = Bits.zero) ->
    (forall i, 1 <= i <= u -> ~ done_set (run_n i act input ss0)) ->
    node_op act samp = DFG_Sample p tok en_s ->
    sample_drive act samp = Some d ->
    In m (drive_nodes ctx (build_dfg ctx act) p) ->
    d < m ->
    (forall arg_m en_m, node_op act m = DFG_Drive p arg_m en_m ->
       guards_disjoint en_m en_s = true ->
       eval1 (drive_pulse act a_idx m) (run_n u act input ss0)
         (sched_input input (run_n u act input ss0)) = Bits.zero) ->
    (forall q_idx tok2 en3, samp <= vreg_nid a_idx q_idx ->
       node_op act (vreg_nid a_idx q_idx) = DFG_Sample p tok2 en3 ->
       (vreg_nid a_idx q_idx = samp \/ guards_disjoint en_s en3 = false) ->
       (fst (run_n u act input ss0)).[tf_dfg_v a_idx q_idx] = Bits.zero) ->
    eval1 (drive_pulse act a_idx m) (run_n u act input ss0)
      (sched_input input (run_n u act input ss0)) = Bits.zero.
  Proof.
    intros Halign Hlen Hz0 Hpre Hsamp Hsd Hin Hlt Hgm Hnl.
    assert (Hzv : forall q, (fst ss0).[tf_dfg_v a_idx q] = Bits.zero)
      by (intro q; exact (Hz0 (tf_dfg_v a_idx q) I)).
    assert (Hlen0 : 0 < length (graph (build_dfg ctx act))) by lia.
    assert (Hlenp : 0 < pred (length (graph (build_dfg ctx act)))) by lia.
    destruct (drive_nodes_spec act p m Hin) as [Hmlen [arg_m [en_m Hm]]].
    destruct (guards_disjoint en_m en_s) eqn:Hdis.
    - exact (Hgm arg_m en_m Hm Hdis).
    - destruct (later_drive_gate_full act p samp tok en_s d m arg_m en_m
                  Hsamp Hsd Hm Hlt Hdis)
        as [g [h [prev [Hcg [Hg Hcov]]]]].
      destruct Hcov as [s' [Hpl [Hle Hd]]].
      (* the covering leaf is a sample on [p] either way *)
      assert (Hs'sam : is_sample_of act s' = true).
      { destruct Hd as [Hq | [nd [tk [en'' [Hnd [Hnid [Hop _]]]]]]].
        - subst s'. unfold SchedulerSimulationBase.is_sample_of. rewrite Hsamp. reflexivity.
        - destruct (node_at_nid act nd Hnd) as [_ Hat].
          unfold SchedulerSimulationBase.is_sample_of, SchedulerSimulationBase.node_op. rewrite Hnid in Hat. rewrite Hat, Hop.
          reflexivity. }
      assert (Hs'op : exists tok2 en3, node_op act s' = DFG_Sample p tok2 en3
                        /\ (s' = samp \/ guards_disjoint en_s en3 = false)).
      { destruct Hd as [Hq | [nd [tk [en'' [Hnd [Hnid [Hop Hdisj]]]]]]].
        - subst s'. exists tok, en_s. split; [ exact Hsamp | left; reflexivity ].
        - destruct (node_at_nid act nd Hnd) as [_ Hat].
          exists tk, en''. rewrite Hnid in Hat.
          split; [ unfold SchedulerSimulationBase.node_op; rewrite Hat; exact Hop | right; exact Hdisj ]. }
      destruct Hs'op as [tok2 [en3 [Hs'sop Hdj]]].
      destruct (sample_slot act a_idx s' Halign Hs'sam)
        as [q0 [qsz [s_idx [Hassoc [Hidx Hvn]]]]].
      assert (Hpz : (fst (run_n u act input ss0)).[tf_dfg_v a_idx s_idx] = Bits.zero).
      { apply (Hnl s_idx tok2 en3).
        - rewrite Hvn. exact Hle.
        - rewrite Hvn. exact Hs'sop.
        - rewrite Hvn. exact Hdj. }
      (* [prev] is the join's second argument, so it sits one fuel step inside *)
      assert (Hglt : g < length (graph (build_dfg ctx act)))
        by (apply node_op_pos; rewrite Hg; discriminate).
      assert (Hgnode : In (nth g (graph (build_dfg ctx act))
                            {| nid := 0; op := DFG_Empty; sz := 0 |})
                          (graph (build_dfg ctx act)))
        by (apply nth_In; exact Hglt).
      assert (Hprevlt : prev < g).
      { pose proof (args_lt_fwd act _ Hgnode prev) as Hal.
        rewrite (node_nid_at act g Hglt) in Hal. apply Hal.
        unfold get_args. unfold SchedulerSimulationBase.node_op in Hg. rewrite Hg. right; left; reflexivity. }
      assert (Hpfuel : prev < pred (length (graph (build_dfg ctx act)))) by lia.
      (* the leaf's register is down, so the whole tree above it reads zero *)
      assert (Htree : forall bufs fuel k,
                (forall n e, BitsToLists.list_assoc bufs n = Some e ->
                   BitsToLists.list_assoc
                     (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) n = Some e) ->
                BitsToLists.list_assoc bufs s' = Some (q0, qsz) ->
                prev < fuel ->
                (forall i, 1 <= i <= k -> ~ done_set (run_n i act input ss0)) ->
                (fst (run_n k act input ss0)).[tf_dfg_v a_idx s_idx] = Bits.zero ->
                eval1 (snd (compile_dfg_expr ctx bneeds fuel a_idx
                              (build_dfg ctx act) prev bufs))
                  (run_n k act input ss0) (sched_input input (run_n k act input ss0))
                  = Bits.zero).
      { intros bufs fuel k Hsub Hbs Hf Hprek Hz.
        destruct (bits1_cases
                    (eval1 (snd (compile_dfg_expr ctx bneeds fuel a_idx
                                   (build_dfg ctx act) prev bufs))
                       (run_n k act input ss0)
                       (sched_input input (run_n k act input ss0))))
          as [Hone | Hzero]; [ exfalso | exact Hzero ].
        pose proof (pleaf_valid_ones act a_idx input ss0 Halign Hzv k Hprek prev s' Hpl
                      s_idx bufs fuel q0 qsz Hs'sam Hbs Hidx Hsub Hf Hone) as Hc.
        rewrite Hz in Hc. exact (ones1_neq_zero (eq_sym Hc)). }
      destruct (BitsToLists.list_assoc
                  (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) g)
        as [[m0 msz] |] eqn:Hgb.
      + (* the join is buffered: its own validity bit has yet to rise *)
        destruct (buffer_slot_of act a_idx g m0 msz Halign Hgb) as [g_idx [Hgidx Hgvn]].
        apply (drive_pulse_zero_of_gate_reg act a_idx m g h m0 msz g_idx _ _
                 Hcg Hgb Hgidx Hlen0).
        destruct u as [| j].
        { cbn [run_n]. exact (Hzv g_idx). }
        destruct (bits1_cases
                    ((fst (run_n (S j) act input ss0)).[tf_dfg_v a_idx g_idx]))
          as [Hone | Hzero]; [ exfalso | exact Hzero ].
        assert (Hnd : ~ done_set (run_n (S j) act input ss0)) by (apply Hpre; lia).
        change (run_n (S j) act input ss0)
          with (sched_step act (run_n j act input ss0)
                  (sched_input input (run_n j act input ss0))) in Hone, Hnd.
        pose proof (buffer_valid_gate act a_idx g_idx (run_n j act input ss0)
                      (sched_input input (run_n j act input ss0)) Halign Hnd Hone) as Hgate.
        assert (Hprevj : (fst (run_n j act input ss0)).[tf_dfg_v a_idx s_idx]
                         = Bits.zero)
          by (apply (validity_zero_earlier act a_idx s_idx input ss0 j (S j)
                       Halign Hzv Hpre ltac:(lia)); exact Hpz).
        assert (Hsg : s' <> vreg_nid a_idx g_idx).
        { rewrite Hgvn. intro He. rewrite He in Hs'sam.
          unfold SchedulerSimulationBase.is_sample_of, SchedulerSimulationBase.node_op in Hs'sam. unfold SchedulerSimulationBase.node_op in Hg.
          rewrite Hg in Hs'sam. discriminate Hs'sam. }
        assert (Hgnone : BitsToLists.list_assoc
                  (filter (fun '(b_nid, _) => negb (Nat.eqb b_nid (vreg_nid a_idx g_idx)))
                     (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))
                  (vreg_nid a_idx g_idx) = None).
        { apply list_assoc_key_none. intro Hin2.
          apply in_map_iff in Hin2. destruct Hin2 as [[k v] [Hk Hmem]].
          cbn [fst] in Hk. subst k. apply filter_In in Hmem.
          destruct Hmem as [_ Hq2]. rewrite Nat.eqb_refl in Hq2. discriminate Hq2. }
        assert (HsubF : forall n0 e,
                  BitsToLists.list_assoc
                    (filter (fun '(b_nid, _) =>
                               negb (Nat.eqb b_nid (vreg_nid a_idx g_idx)))
                       (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) n0
                    = Some e ->
                  BitsToLists.list_assoc
                    (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) n0 = Some e).
        { intros n0 e He. pose proof (wla_in _ _ _ He) as Hin0.
          apply filter_In in Hin0. destruct Hin0 as [Hin1 _].
          apply list_assoc_nodup_in;
            [ exact (slot_keys_nodup act a_idx Halign) | exact Hin1 ]. }
        assert (HfiltS : BitsToLists.list_assoc
                  (filter (fun '(b_nid, _) => negb (Nat.eqb b_nid (vreg_nid a_idx g_idx)))
                     (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) s'
                  = Some (q0, qsz)).
        { rewrite list_assoc_filter; [ exact Hassoc |].
          intros [k v] _ Hfe. cbn [fst] in Hfe. subst k.
          apply negb_true_iff, Nat.eqb_neq. exact Hsg. }
        assert (Hprej : forall i, 1 <= i <= j -> ~ done_set (run_n i act input ss0))
          by (intros i Hi; apply Hpre; lia).
        assert (Hgj : node_op act (vreg_nid a_idx g_idx) = DFG_Join m prev)
          by (rewrite Hgvn; exact Hg).
        assert (Hzg : eval1 (snd (compile_dfg_expr ctx bneeds
                        (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act)
                        (vreg_nid a_idx g_idx)
                        (filter (fun '(b_nid, _) =>
                                   negb (Nat.eqb b_nid (vreg_nid a_idx g_idx)))
                           (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))))
                      (run_n j act input ss0)
                      (sched_input input (run_n j act input ss0)) = Bits.zero).
        { apply (join_gate_zero_of_arg act a_idx (vreg_nid a_idx g_idx) m prev
                   (length (graph (build_dfg ctx act))) _ _ _ Hgj Hgnone Hlen).
          apply (Htree _ _ j HsubF HfiltS Hpfuel Hprej Hprevj). }
        rewrite Hgate in Hzg. exact (ones1_neq_zero Hzg).
      + apply (drive_pulse_zero_of_join act a_idx m g h m prev _ _ Hcg Hg Hgb Hlen0).
        apply (Htree _ _ u (fun n e H => H) Hassoc Hpfuel Hpre Hpz).
  Qed.


  (* ---- The timing facts the round trip needs ---------------------------- *)
  (* Each is a property of the SCHEDULE that this file's structural analysis  *)
  (* does not reach: the cost model certifies them for a constant-time        *)
  (* action, and every call-bearing action in the tree is one.                *)

  (* On one port the answers come back in the order the calls were emitted,
     for calls whose guards can hold together.  [pending_samples] filters by
     [negb (guards_disjoint ...)], so exclusive arms are sequenced by nothing
     and are excluded here; [covers] hands the same disjunction back. *)
  Definition samples_ordered (act: tfs_action sched) a_idx (input: input_t)
      (ss0: sched_sys_state) : Prop :=
    forall (p: p_var) s1 s2 tok1 en1 tok2 en2 k,
      (forall i, 1 <= i <= k -> ~ done_set (run_n i act input ss0)) ->
      node_op act (vreg_nid a_idx s1) = DFG_Sample p tok1 en1 ->
      node_op act (vreg_nid a_idx s2) = DFG_Sample p tok2 en2 ->
      vreg_nid a_idx s1 <= vreg_nid a_idx s2 ->
      (vreg_nid a_idx s2 = vreg_nid a_idx s1 \/ guards_disjoint en1 en2 = false) ->
      (fst (run_n k act input ss0)).[tf_dfg_v a_idx s2] = Bits.ones 1 ->
      (fst (run_n k act input ss0)).[tf_dfg_v a_idx s1] = Bits.ones 1.

  (* A call's request reaches the port before its answer is latched, carrying
     a settled argument, and no call emitted at or before it moves the port
     again while the answer is outstanding.  Only WHERE THE CALL FIRES: an
     untaken arm's sample latches too, and its drive never pulsed. *)
  Definition requests_sent (act: tfs_action sched) a_idx (input: input_t)
      (ss0: sched_sys_state) (M: nat) : Prop :=
    forall n_idx (p: p_var) tok en d j,
      node_op act (vreg_nid a_idx n_idx) = DFG_Sample p tok en ->
      sample_drive act (vreg_nid a_idx n_idx) = Some d ->
      guard_holds act a_idx (run_n M act input ss0)
        (sched_input input (run_n M act input ss0)) en ->
      j < M ->
      (fst (run_n j act input ss0)).[tf_dfg_v a_idx n_idx] = Bits.zero ->
      (fst (run_n (S j) act input ss0)).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
      exists t,
        t < j
        /\ eval1 (drive_pulse act a_idx d) (run_n t act input ss0)
             (sched_input input (run_n t act input ss0)) <> Bits.zero
        /\ eval1 (snd (compile_dfg_expr ctx bneeds
                         (length (graph (build_dfg ctx act))) a_idx
                         (build_dfg ctx act) d
                         (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])))
             (run_n t act input ss0)
             (sched_input input (run_n t act input ss0)) = Bits.ones 1
        /\ (forall mm, In mm (drive_nodes ctx (build_dfg ctx act) p) -> mm <= d ->
              forall w, t < w -> w < j ->
              eval1 (drive_pulse act a_idx mm) (run_n w act input ss0)
                (sched_input input (run_n w act input ss0)) = Bits.zero).

  (* The one left, at the last cycle before the action reports done. *)
  Definition call_discipline (act: tfs_action sched) a_idx (input: input_t)
      (ss0: sched_sys_state) (N: nat) : Prop :=
    requests_sent act a_idx input ss0 (pred N).


  Lemma pleaf_le (act: tfs_action sched) root s :
    pleaf (graph (build_dfg ctx act)) root s -> s <= root.
  Proof.
    intro H.
    induction H as [ n | nj a b n Hin Hop _ IHp | nj a b n Hin Hop _ IHp ].
    - lia.
    - assert (Hga : In a (get_args ctx nj))
        by (unfold get_args; rewrite Hop; left; reflexivity).
      pose proof (args_lt_fwd act nj Hin a Hga). lia.
    - assert (Hgb : In b (get_args ctx nj))
        by (unfold get_args; rewrite Hop; right; left; reflexivity).
      pose proof (args_lt_fwd act nj Hin b Hgb). lia.
  Qed.

  (* THE ORDER, as a lemma.  A later call on a port is sequenced behind every
     earlier one whose guard can hold with its own, so the earlier answer is
     latched first.  Strong induction on the later sample: the tree it waits
     on may name a sample that in turn covers the one we want. *)
  Lemma samples_ordered_holds
        (act: tfs_action sched) a_idx (input: input_t) (ss0: sched_sys_state) :
    act_idx_aligned act a_idx ->
    (forall x, zeroed_at_start x -> (fst ss0).[x] = Bits.zero) ->
    1 < length (graph (build_dfg ctx act)) ->
    samples_ordered act a_idx input ss0.
  Proof.
    intros Halign Hz0 Hlen.
    assert (Hzv : forall q, (fst ss0).[tf_dfg_v a_idx q] = Bits.zero)
      by (intro q; exact (Hz0 (tf_dfg_v a_idx q) I)).
    assert (Hlen0 : 0 < length (graph (build_dfg ctx act))) by lia.
    assert (MAIN : forall n2 (p: p_var) s1 s2 tok1 en1 tok2 en2 k,
              vreg_nid a_idx s2 <= n2 ->
              (forall i, 1 <= i <= k -> ~ done_set (run_n i act input ss0)) ->
              node_op act (vreg_nid a_idx s1) = DFG_Sample p tok1 en1 ->
              node_op act (vreg_nid a_idx s2) = DFG_Sample p tok2 en2 ->
              vreg_nid a_idx s1 <= vreg_nid a_idx s2 ->
              (vreg_nid a_idx s2 = vreg_nid a_idx s1
               \/ guards_disjoint en1 en2 = false) ->
              (fst (run_n k act input ss0)).[tf_dfg_v a_idx s2] = Bits.ones 1 ->
              (fst (run_n k act input ss0)).[tf_dfg_v a_idx s1] = Bits.ones 1).
    { intro n2. induction n2 as [n2 IH] using (well_founded_induction lt_wf).
      intros p s1 s2 tok1 en1 tok2 en2 k Hn2 Hpre Hs1 Hs2 Hle Hdj Hones.
      destruct (Nat.eq_dec (vreg_nid a_idx s1) (vreg_nid a_idx s2)) as [Heq | Hne12].
      { pose proof (vreg_nid_inj act a_idx s1 s2 Halign Heq) as ->. exact Hones. }
      assert (Hlt12 : vreg_nid a_idx s1 < vreg_nid a_idx s2) by lia.
      assert (Hdis : guards_disjoint en1 en2 = false)
        by (destruct Hdj as [Hq | Hq];
            [ exfalso; apply Hne12; exact (eq_sym Hq) | exact Hq ]).
      destruct (sample_has_drive act (vreg_nid a_idx s2) p tok2 en2 Hs2)
        as [d2 [arg2 [Hsd2 Hd2op]]].
      assert (Hs1d2 : vreg_nid a_idx s1 < d2).
      { destruct (Nat.lt_trichotomy (vreg_nid a_idx s1) d2) as [Hlt | [Heq2 | Hgt]].
        - exact Hlt.
        - exfalso. rewrite Heq2, Hd2op in Hs1. discriminate Hs1.
        - exfalso.
          destruct (sample_chain_between act (vreg_nid a_idx s2) p tok2 en2 d2
                      (vreg_nid a_idx s1) Hs2 Hsd2 Hgt Hlt12)
            as [[ll [aa2 Hst]] | [aa2 [bb2 Hjj]]];
            [ rewrite Hst in Hs1 | rewrite Hjj in Hs1 ]; discriminate Hs1. }
      assert (Hdis2 : guards_disjoint en2 en1 = false)
        by (rewrite guards_disjoint_sym; exact Hdis).
      destruct (call_sequenced_join act p d2 arg2 en2 (vreg_nid a_idx s1) tok1 en1
                  Hd2op Hs1 Hs1d2 Hdis2) as [j [prev [Hj Hcov]]].
      (* the stall the sample reads, and the head it hangs off *)
      assert (Hs2len : vreg_nid a_idx s2 < length (graph (build_dfg ctx act)))
        by (apply node_op_range; rewrite Hs2; discriminate).
      assert (Hs2in : In (nth (vreg_nid a_idx s2) (graph (build_dfg ctx act))
                            {| nid := 0; op := DFG_Empty; sz := 0 |})
                         (graph (build_dfg ctx act)))
        by (apply nth_In; exact Hs2len).
      assert (Hs2raw : op (nth (vreg_nid a_idx s2) (graph (build_dfg ctx act))
                             {| nid := 0; op := DFG_Empty; sz := 0 |})
                       = DFG_Sample p tok2 en2) by exact Hs2.
      destruct (samples_stalled_build_dfg act _ p tok2 en2 Hs2in Hs2raw)
        as [t [l [aa [Ht [Htid Htop]]]]].
      destruct (node_at_nid act t Ht) as [_ Hnth].
      assert (Htok2 : node_op act tok2 = DFG_Stall l aa)
        by (unfold SchedulerSimulationBase.node_op; rewrite <- Htid, Hnth; exact Htop).
      assert (Hsdh : sample_drive_head act p aa = Some d2).
      { unfold SchedulerSimulationBase.sample_drive in Hsd2. rewrite Hs2, Htok2 in Hsd2. exact Hsd2. }
      assert (Htoklt : tok2 < vreg_nid a_idx s2).
      { pose proof (args_lt_fwd act _ Hs2in tok2) as Hal.
        rewrite (node_nid_at act (vreg_nid a_idx s2) Hs2len) in Hal.
        apply Hal. unfold get_args. rewrite Hs2raw. left; reflexivity. }
      assert (Htok2len : tok2 < length (graph (build_dfg ctx act))) by lia.
      assert (Htok2in : In (nth tok2 (graph (build_dfg ctx act))
                              {| nid := 0; op := DFG_Empty; sz := 0 |})
                           (graph (build_dfg ctx act)))
        by (apply nth_In; exact Htok2len).
      assert (Htok2raw : op (nth tok2 (graph (build_dfg ctx act))
                               {| nid := 0; op := DFG_Empty; sz := 0 |})
                         = DFG_Stall l aa) by exact Htok2.
      assert (Haalt : aa < tok2).
      { pose proof (args_lt_fwd act _ Htok2in aa) as Hal.
        rewrite (node_nid_at act tok2 Htok2len) in Hal.
        apply Hal. unfold get_args. rewrite Htok2raw. left; reflexivity. }
      (* the head is the ordering join, and it is [j] *)
      destruct (sample_drive_head_shape act p aa d2 Hsdh)
        as [[Hdaa [ar1 [e1 Haadr]]] | [prev' [ar2 [e2 [Haaj Hd2dr]]]]].
      { exfalso. rewrite <- Hdaa in Htok2.
        exact (no_stall_on_joined act j d2 prev tok2 l p arg2 en2 Hd2op Hj Htok2). }
      pose proof (join_nid_succ act j d2 prev p arg2 en2 Hj Hd2op) as Hjn.
      pose proof (join_nid_succ act aa d2 prev' p ar2 e2 Haaj Hd2dr) as Han.
      assert (Haj : aa = j) by lia.
      assert (Hpv : prev' = prev).
      { rewrite Haj, Hj in Haaj. injection Haaj as Hq. exact (eq_sym Hq). }
      subst prev'.
      assert (Haalen : aa < length (graph (build_dfg ctx act))) by lia.
      assert (Haain : In (nth aa (graph (build_dfg ctx act))
                            {| nid := 0; op := DFG_Empty; sz := 0 |})
                         (graph (build_dfg ctx act)))
        by (apply nth_In; exact Haalen).
      assert (Haaraw : op (nth aa (graph (build_dfg ctx act))
                             {| nid := 0; op := DFG_Empty; sz := 0 |})
                       = DFG_Join d2 prev) by exact Haaj.
      assert (Hprevlt : prev < aa).
      { pose proof (args_lt_fwd act _ Haain prev) as Hal.
        rewrite (node_nid_at act aa Haalen) in Hal.
        apply Hal. unfold get_args. rewrite Haaraw. right; left; reflexivity. }
      (* the covering leaf *)
      destruct Hcov as [s' [Hpl [Hles' Hd']]].
      assert (Hplaa : pleaf (graph (build_dfg ctx act)) aa s').
      { pose proof (pleaf_right (graph (build_dfg ctx act))
                      (nth aa (graph (build_dfg ctx act))
                         {| nid := 0; op := DFG_Empty; sz := 0 |})
                      d2 prev s' Haain Haaraw Hpl) as Hp.
        rewrite (node_nid_at act aa Haalen) in Hp. exact Hp. }
      assert (Hs'le : s' <= prev) by (exact (pleaf_le act prev s' Hpl)).
      assert (Hs'sam : is_sample_of act s' = true).
      { destruct Hd' as [Hq | [nd [tk [en'' [Hnd [Hnid [Hop _]]]]]]].
        - rewrite Hq. unfold SchedulerSimulationBase.is_sample_of. rewrite Hs1. reflexivity.
        - destruct (node_at_nid act nd Hnd) as [_ Hat].
          unfold SchedulerSimulationBase.is_sample_of, SchedulerSimulationBase.node_op. rewrite Hnid in Hat. rewrite Hat, Hop.
          reflexivity. }
      destruct (sample_slot act a_idx s' Halign Hs'sam)
        as [q0 [qsz [s'_idx [Hassoc [Hidx Hvn]]]]].
      (* the lookups the descent needs, for either filtered table *)
      assert (HsubG : forall key n0 e,
                BitsToLists.list_assoc
                  (filter (fun '(b_nid, _) => negb (Nat.eqb b_nid key))
                     (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) n0
                  = Some e ->
                BitsToLists.list_assoc
                  (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) n0
                  = Some e).
      { intros key n0 e He. pose proof (wla_in _ _ _ He) as Hin0.
        apply filter_In in Hin0. destruct Hin0 as [Hin1 _].
        apply list_assoc_nodup_in;
          [ exact (slot_keys_nodup act a_idx Halign) | exact Hin1 ]. }
      assert (HfiltG : forall key, s' <> key ->
                BitsToLists.list_assoc
                  (filter (fun '(b_nid, _) => negb (Nat.eqb b_nid key))
                     (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])) s'
                = Some (q0, qsz)).
      { intros key Hne. rewrite list_assoc_filter; [ exact Hassoc |].
        intros [kk vv] _ Hfe. cbn [fst] in Hfe. subst kk.
        apply negb_true_iff, Nat.eqb_neq. exact Hne. }
      (* one cycle back from the sample's register *)
      destruct k as [| k0].
      { exfalso. cbn [run_n] in Hones. rewrite Hzv in Hones.
        exact (ones1_neq_zero (eq_sym Hones)). }
      assert (Hnd0 : ~ done_set (run_n (S k0) act input ss0)) by (apply Hpre; lia).
      assert (Hprek0 : forall i, 1 <= i <= k0 -> ~ done_set (run_n i act input ss0))
        by (intros i Hi; apply Hpre; lia).
      assert (Hfin : forall kk, kk <= S k0 ->
                (fst (run_n kk act input ss0)).[tf_dfg_v a_idx s1] = Bits.ones 1 ->
                (fst (run_n (S k0) act input ss0)).[tf_dfg_v a_idx s1] = Bits.ones 1).
      { intros kk Hkk Hv.
        assert (Hp' : forall i, 1 <= i <= kk + (S k0 - kk) ->
                  ~ done_set (run_n i act input ss0))
          by (intros i Hi; apply Hpre; lia).
        pose proof (validity_monotone_run act a_idx s1 input ss0 kk (S k0 - kk)
                      Halign Hzv Hp' Hv) as Hm.
        replace (kk + (S k0 - kk)) with (S k0) in Hm by lia. exact Hm. }
      assert (LEAF : forall kk, kk <= S k0 ->
                (forall i, 1 <= i <= kk -> ~ done_set (run_n i act input ss0)) ->
                (fst (run_n kk act input ss0)).[tf_dfg_v a_idx s'_idx] = Bits.ones 1 ->
                (fst (run_n (S k0) act input ss0)).[tf_dfg_v a_idx s1] = Bits.ones 1).
      { intros kk Hkk Hprekk Hv.
        destruct Hd' as [Hq | [nd [tk [en'' [Hnd [Hnid [Hop Hdisl]]]]]]].
        - assert (Hids : s'_idx = s1).
          { apply (vreg_nid_inj act a_idx); [ exact Halign |].
            rewrite Hvn, Hq. reflexivity. }
          rewrite Hids in Hv. exact (Hfin kk Hkk Hv).
        - destruct (node_at_nid act nd Hnd) as [_ Hat].
          assert (Hs'op : node_op act (vreg_nid a_idx s'_idx) = DFG_Sample p tk en'')
            by (unfold SchedulerSimulationBase.node_op; rewrite Hvn, <- Hnid, Hat; exact Hop).
          assert (Hs'lt : s' < n2) by lia.
          assert (Hbound : vreg_nid a_idx s'_idx <= s') by (rewrite Hvn; lia).
          assert (Hge' : vreg_nid a_idx s1 <= vreg_nid a_idx s'_idx)
            by (rewrite Hvn; exact Hles').
          assert (Hv1 : (fst (run_n kk act input ss0)).[tf_dfg_v a_idx s1]
                        = Bits.ones 1)
            by (exact (IH s' Hs'lt p s1 s'_idx tok1 en1 tk en'' kk Hbound Hprekk
                         Hs1 Hs'op Hge' (or_intror Hdisl) Hv)).
          exact (Hfin kk Hkk Hv1). }
      change (run_n (S k0) act input ss0)
        with (sched_step act (run_n k0 act input ss0)
                (sched_input input (run_n k0 act input ss0))) in Hones, Hnd0.
      pose proof (buffer_valid_gate act a_idx s2 (run_n k0 act input ss0)
                    (sched_input input (run_n k0 act input ss0)) Halign Hnd0 Hones)
        as Hgate.
      assert (Htokne : tok2 <> vreg_nid a_idx s2) by lia.
      destruct (sample_gate_cases act a_idx s2 p tok2 en2 l aa Halign Hs2 Htok2
                  Htokne Hlen)
        as [[m0 [msz [t_idx [Hta [Htidx [Htvn Hbg]]]]]] | [Htnone Hbg]].
      + (* the stall is buffered: one more cycle back, then it walks to the head *)
        rewrite Hbg, eval1_svar_v in Hgate.
        destruct k0 as [| k1].
        { exfalso. cbn [run_n] in Hgate. rewrite Hzv in Hgate.
          exact (ones1_neq_zero (eq_sym Hgate)). }
        assert (Hnd1 : ~ done_set (run_n (S k1) act input ss0)) by (apply Hpre; lia).
        assert (Hprek1 : forall i, 1 <= i <= k1 -> ~ done_set (run_n i act input ss0))
          by (intros i Hi; apply Hpre; lia).
        change (run_n (S k1) act input ss0)
          with (sched_step act (run_n k1 act input ss0)
                  (sched_input input (run_n k1 act input ss0))) in Hgate, Hnd1.
        pose proof (buffer_valid_gate act a_idx t_idx (run_n k1 act input ss0)
                      (sched_input input (run_n k1 act input ss0)) Halign Hnd1 Hgate)
          as Hgate2.
        assert (Htokstall : node_op act (vreg_nid a_idx t_idx) = DFG_Stall l aa)
          by (rewrite Htvn; exact Htok2).
        assert (Haane : aa <> vreg_nid a_idx t_idx) by (rewrite Htvn; lia).
        rewrite (stall_gate_walks act a_idx t_idx l aa Htokstall Haane Hlen0) in Hgate2.
        assert (Hs'ne : s' <> vreg_nid a_idx t_idx) by (rewrite Htvn; lia).
        assert (Haafuel : aa < pred (length (graph (build_dfg ctx act)))) by lia.
        pose proof (pleaf_valid_ones act a_idx input ss0 Halign Hzv k1 Hprek1 aa s'
                      Hplaa s'_idx _ (pred (length (graph (build_dfg ctx act))))
                      q0 qsz Hs'sam (HfiltG _ Hs'ne) Hidx (HsubG _) Haafuel Hgate2)
          as Hs'ones.
        exact (LEAF k1 ltac:(lia) Hprek1 Hs'ones).
      + (* the stall is not buffered: the gate reads the head directly *)
        rewrite Hbg in Hgate.
        assert (Hs'ne : s' <> vreg_nid a_idx s2) by lia.
        assert (Haafuel : aa < pred (pred (length (graph (build_dfg ctx act)))))
          by lia.
        pose proof (pleaf_valid_ones act a_idx input ss0 Halign Hzv k0 Hprek0 aa s'
                      Hplaa s'_idx _
                      (pred (pred (length (graph (build_dfg ctx act)))))
                      q0 qsz Hs'sam (HfiltG _ Hs'ne) Hidx (HsubG _) Haafuel Hgate)
          as Hs'ones.
        exact (LEAF k0 ltac:(lia) Hprek0 Hs'ones). }
    intros p s1 s2 tok1 en1 tok2 en2 k Hpre Hs1 Hs2 Hle Hdj Hones.
    exact (MAIN (vreg_nid a_idx s2) p s1 s2 tok1 en1 tok2 en2 k
             (le_n _) Hpre Hs1 Hs2 Hle Hdj Hones).
  Qed.

  (* THE PORT AT THE LATCH.  When a call's answer is latched, the port still
     carries that call's own request: its drive put it there, phase 3b keeps
     every later call off the wire, and [requests_sent] keeps the earlier
     ones off. *)
  Lemma port_holds_request
        (act: tfs_action sched) a_idx (input: input_t) (ss0: sched_sys_state) M
        n_idx (p: p_var) tok en d av en' j :
    act_idx_aligned act a_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    (forall x, zeroed_at_start x -> (fst ss0).[x] = Bits.zero) ->
    (forall i, 1 <= i <= M -> ~ done_set (run_n i act input ss0)) ->
    requests_sent act a_idx input ss0 M ->
    node_op act (vreg_nid a_idx n_idx) = DFG_Sample p tok en ->
    sample_drive act (vreg_nid a_idx n_idx) = Some d ->
    node_op act d = DFG_Drive p av en' ->
    sz (nth d (graph (build_dfg ctx act))
         {| nid := 0; op := DFG_Empty; sz := 0 |}) = ip_req_sz (tfs_spec_ip ctx p) ->
    guard_holds act a_idx (run_n M act input ss0)
      (sched_input input (run_n M act input ss0)) en ->
    j < M ->
    (fst (run_n j act input ss0)).[tf_dfg_v a_idx n_idx] = Bits.zero ->
    (fst (run_n (S j) act input ss0)).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
    drive_payload (run_n j act input ss0) p
    = tf_eval_expr ss_sz si_sz oo_sz (szB := ip_req_sz (tfs_spec_ip ctx p))
        (node_ref_expr act a_idx av)
        (run_n M act input ss0) (sched_input input (run_n M act input ss0)).
  Proof.
    intros Halign Hlen Hz0 Hpre Hrs Hsamp Hsd Hdop Hdsz Hgd Hjm Hvj HvSj.
    pose proof (samples_ordered_holds act a_idx input ss0 Halign Hz0 Hlen) as Hord.
    assert (Hzv : forall q, (fst ss0).[tf_dfg_v a_idx q] = Bits.zero)
      by (intro q; exact (Hz0 (tf_dfg_v a_idx q) I)).
    destruct (node_op_pos act d ltac:(rewrite Hdop; discriminate)) as [Hd1 Hdlen].
    (* no answer at or after this one has been latched, up to cycle [j] *)
    assert (Hnl : forall u, u <= j -> forall q_idx tok2 en3,
              vreg_nid a_idx n_idx <= vreg_nid a_idx q_idx ->
              node_op act (vreg_nid a_idx q_idx) = DFG_Sample p tok2 en3 ->
              (vreg_nid a_idx q_idx = vreg_nid a_idx n_idx
               \/ guards_disjoint en en3 = false) ->
              (fst (run_n u act input ss0)).[tf_dfg_v a_idx q_idx] = Bits.zero).
    { intros u Hu q_idx tok2 en3 Hge Hq Hdj.
      destruct (bits1_cases ((fst (run_n u act input ss0)).[tf_dfg_v a_idx q_idx]))
        as [Hone | Hz]; [ exfalso | exact Hz ].
      assert (Hpu' : forall i, 1 <= i <= u -> ~ done_set (run_n i act input ss0))
        by (intros i Hi; apply Hpre; lia).
      pose proof (Hord p n_idx q_idx tok en tok2 en3 u Hpu' Hsamp Hq Hge Hdj Hone)
        as Hsone.
      assert (Hpu : forall i, 1 <= i <= j -> ~ done_set (run_n i act input ss0))
        by (intros i Hi; apply Hpre; lia).
      rewrite (validity_zero_earlier act a_idx n_idx input ss0 u j Halign Hzv
                 Hpu Hu Hvj) in Hsone.
      exact (ones1_neq_zero (eq_sym Hsone)). }
    (* a call in an exclusive branch never takes the port -- a LEMMA now, not
       an assumption about when guards settle *)
    assert (Hgm : forall u, u <= M -> forall mm arg_m en_m,
              node_op act mm = DFG_Drive p arg_m en_m ->
              guards_disjoint en_m en = true ->
              eval1 (drive_pulse act a_idx mm) (run_n u act input ss0)
                (sched_input input (run_n u act input ss0)) = Bits.zero).
    { intros u Hu mm arg_m en_m Hmm Hdis.
      exact (excl_drive_pulse_zero act a_idx p en mm arg_m en_m input ss0 u M
               Halign Hlen Hzv Hpre Hu Hmm Hdis Hgd). }
    (* so no LATER call takes the port while the answer is outstanding *)
    assert (Hlater : forall u, u <= j -> forall mm,
              In mm (drive_nodes ctx (build_dfg ctx act) p) -> d < mm ->
              eval1 (drive_pulse act a_idx mm) (run_n u act input ss0)
                (sched_input input (run_n u act input ss0)) = Bits.zero).
    { intros u Hu mm Hinm Hltm.
      assert (Hpu : forall i, 1 <= i <= u -> ~ done_set (run_n i act input ss0))
        by (intros i Hi; apply Hpre; lia).
      assert (Hgu : forall arg_m en_m, node_op act mm = DFG_Drive p arg_m en_m ->
                guards_disjoint en_m en = true ->
                eval1 (drive_pulse act a_idx mm) (run_n u act input ss0)
                  (sched_input input (run_n u act input ss0)) = Bits.zero)
        by (intros arg_m en_m Hm2 Hdis; apply (Hgm u ltac:(lia) mm arg_m en_m Hm2 Hdis)).
      exact (no_later_drive act a_idx p (vreg_nid a_idx n_idx) tok en d mm input ss0 u
               Halign Hlen Hz0 Hpu Hsamp Hsd Hinm Hltm Hgu (Hnl u Hu)). }
    destruct (Hrs n_idx p tok en d j Hsamp Hsd Hgd Hjm Hvj HvSj)
      as [t [Htj [Hpulse [Hdval Hearly]]]].
    pose proof (sample_drive_in_drive_nodes act (vreg_nid a_idx n_idx) d p tok en
                  Hsamp Hsd) as Hdin.
    (* the drive puts its request on the port ... *)
    assert (Hndt : ~ done_set (sched_step act (run_n t act input ss0)
                     (sched_input input (run_n t act input ss0))))
      by (exact (Hpre (S t) ltac:(lia))).
    assert (Htake : drive_payload
                      (sched_step act (run_n t act input ss0)
                         (sched_input input (run_n t act input ss0))) p
              = tf_eval_expr ss_sz si_sz oo_sz (szB := ip_req_sz (tfs_spec_ip ctx p))
                  (fst (compile_dfg_expr ctx bneeds
                          (length (graph (build_dfg ctx act))) a_idx
                          (build_dfg ctx act) d
                          (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])))
                  (run_n t act input ss0) (sched_input input (run_n t act input ss0))).
    { apply (drive_payload_take_later act a_idx p d _ _ Halign Hndt Hdin);
        [ intros mm Hin2 Hlt2; exact (Hlater t ltac:(lia) mm Hin2 Hlt2) | exact Hpulse ]. }
    (* ... and nothing moves it before the answer is latched *)
    assert (Hhold : forall k, S t + k <= j ->
              drive_payload (run_n (S t + k) act input ss0) p
              = drive_payload (run_n (S t) act input ss0) p).
    { intro k. induction k as [| k IH]; intro Hk.
      - rewrite Nat.add_0_r. reflexivity.
      - rewrite <- (IH ltac:(lia)). rewrite Nat.add_succ_r.
        change (run_n (S (S t + k)) act input ss0)
          with (sched_step act (run_n (S t + k) act input ss0)
                  (sched_input input (run_n (S t + k) act input ss0))).
        apply (drive_payload_hold act a_idx p _ _ Halign (Hpre (S (S t + k)) ltac:(lia))).
        intros mm Hin2.
        destruct (Nat.ltb d mm) eqn:Hcmp.
        + apply Nat.ltb_lt in Hcmp. exact (Hlater (S t + k) ltac:(lia) mm Hin2 Hcmp).
        + apply Nat.ltb_ge in Hcmp.
          exact (Hearly mm Hin2 Hcmp (S t + k) ltac:(lia) ltac:(lia)). }
    assert (Hjeq : drive_payload (run_n j act input ss0) p
                   = drive_payload (run_n (S t) act input ss0) p).
    { assert (He : S t + (j - S t) = j) by lia.
      rewrite <- He. apply Hhold. lia. }
    rewrite Hjeq.
    change (run_n (S t) act input ss0)
      with (sched_step act (run_n t act input ss0)
              (sched_input input (run_n t act input ss0))).
    rewrite Htake.
    (* the request is the drive's own settled argument, and it does not move *)
    destruct (valid_settled_run act a_idx input ss0 t Halign Hzv) as [_ [Hrefs Hinv]].
    assert (Hsub : forall e,
              In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) ->
              In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))
      by (intros e He; exact He).
    assert (Hsam_sub : forall x,
              BitsToLists.list_assoc
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) x = None ->
              BitsToLists.list_assoc (sample_bufs act a_idx) x = None).
    { intros x Hx. apply list_assoc_key_none. intro Hin2.
      apply in_map_iff in Hin2. destruct Hin2 as [[x2 v2] [Hxx Hmem2]].
      cbn [fst] in Hxx. subst x2.
      unfold SchedulerSimulationBase.sample_bufs in Hmem2. apply filter_In in Hmem2.
      apply (list_assoc_none_key _ _ Hx), in_map_iff.
      exists (x, v2). split; [ reflexivity | exact (proj1 Hmem2) ]. }
    assert (Hsam_same : forall x m msz,
              BitsToLists.list_assoc
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) x
                = Some (m, msz) ->
              is_sample_of act x = true ->
              BitsToLists.list_assoc (sample_bufs act a_idx) x = Some (m, msz)).
    { intros x m msz Hx Hsx. apply list_assoc_nodup_in.
      - unfold SchedulerSimulationBase.sample_bufs. apply nodup_map_fst_filter.
        exact (slot_keys_nodup act a_idx Halign).
      - unfold SchedulerSimulationBase.sample_bufs. apply filter_In.
        split; [ exact (wla_in _ _ _ Hx) | exact Hsx ]. }
    rewrite (compile_subst_valid act a_idx (run_n t act input ss0)
               (sched_input input (run_n t act input ss0)) Halign Hinv
               (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])
               Hsub Hsam_sub Hsam_same
               (length (graph (build_dfg ctx act))) d
               (ip_req_sz (tfs_spec_ip ctx p)) Hd1 Hdlen Hdlen
               (eq_sym Hdsz) Hdval).
    assert (Hrv : eval1 (snd (compile_dfg_expr ctx bneeds
                        (length (graph (build_dfg ctx act))) a_idx
                        (build_dfg ctx act) d (sample_bufs act a_idx)))
              (run_n t act input ss0) (sched_input input (run_n t act input ss0))
              = Bits.ones 1).
    { exact (compile_subst_ref_valid_gen act a_idx (run_n t act input ss0)
               (sched_input input (run_n t act input ss0)) Halign Hinv Hrefs
               (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])
               Hsub Hsam_sub Hsam_same (length (graph (build_dfg ctx act))) d []
               Hd1 Hdlen Hdlen Hdval). }
    assert (Hsvar : forall s, (fst (run_n t act input ss0)).[tf_dfg_s s]
                      = (fst (run_n M act input ss0)).[tf_dfg_s s]).
    { intro s.
      assert (Hpt : forall i, 1 <= i <= t -> ~ done_set (run_n i act input ss0))
        by (intros i Hi; apply Hpre; lia).
      rewrite (run_preserves_svar act input ss0 t Hpt s).
      rewrite (run_preserves_svar act input ss0 M Hpre s). reflexivity. }
    assert (Hovar : forall o, (snd (run_n t act input ss0)).[o]
                      = (snd (run_n M act input ss0)).[o]).
    { intro o.
      assert (Hpt : forall i, 1 <= i <= t -> ~ done_set (run_n i act input ss0))
        by (intros i Hi; apply Hpre; lia).
      rewrite (run_preserves_ovar act input ss0 t Hpt o).
      rewrite (run_preserves_ovar act input ss0 M Hpre o). reflexivity. }
    assert (Hbfroz : forall q_idx, is_sample_of act (vreg_nid a_idx q_idx) = true ->
              (fst (run_n t act input ss0)).[tf_dfg_v a_idx q_idx] = Bits.ones 1 ->
              (fst (run_n t act input ss0)).[tf_dfg_b a_idx q_idx]
              = (fst (run_n M act input ss0)).[tf_dfg_b a_idx q_idx]).
    { intros q_idx Hsq Hvq.
      assert (He : t + (M - t) = M) by lia.
      assert (Hpt : forall i, 1 <= i <= t + (M - t) -> ~ done_set (run_n i act input ss0))
        by (intros i Hi; apply Hpre; lia).
      destruct (sample_buffer_frozen_run act a_idx q_idx input ss0 t (M - t)
                  Halign Hzv Hpt Hsq Hvq) as [Hb _].
      rewrite He in Hb. exact (eq_sym Hb). }
    rewrite (compile_nobuf_state_indep act a_idx
               (sched_input input (run_n t act input ss0))
               (sched_input input (run_n M act input ss0))
               (run_n t act input ss0) (run_n M act input ss0)
               Halign Hsvar Hovar ltac:(intro v; reflexivity) Hbfroz
               (length (graph (build_dfg ctx act))) d
               (ip_req_sz (tfs_spec_ip ctx p)) Hdlen Hrv).
    pose proof (nre_drive act a_idx d p av en' Hd1 Hdlen Hdop) as Hnre.
    unfold SchedulerSimulationBase.node_ref_expr in Hnre. rewrite Hnre. reflexivity.
  Qed.

  (* THE ROUND TRIP, discharged.  The sample latches on the cycle its validity
     rises, reading a port that still carries its own request, and holds that
     answer to the end of the run. *)
  Lemma round_trip
        (act: tfs_action sched) a_idx (input: input_t) (ss0: sched_sys_state) M
        n_idx (p: p_var) tok en d av en' :
    act_idx_aligned act a_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    (forall x, zeroed_at_start x -> (fst ss0).[x] = Bits.zero) ->
    (forall i, 1 <= i <= M -> ~ done_set (run_n i act input ss0)) ->
    (fst (run_n M act input ss0)).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
    requests_sent act a_idx input ss0 M ->
    node_op act (vreg_nid a_idx n_idx) = DFG_Sample p tok en ->
    sample_drive act (vreg_nid a_idx n_idx) = Some d ->
    node_op act d = DFG_Drive p av en' ->
    sz (nth d (graph (build_dfg ctx act))
         {| nid := 0; op := DFG_Empty; sz := 0 |}) = ip_req_sz (tfs_spec_ip ctx p) ->
    guard_holds act a_idx (run_n M act input ss0)
      (sched_input input (run_n M act input ss0)) en ->
    (fst (run_n M act input ss0)).[tf_dfg_b a_idx n_idx]
    = convert (ip_fn (tfs_spec_ip ctx p)
        (tf_eval_expr ss_sz si_sz oo_sz (szB := ip_req_sz (tfs_spec_ip ctx p))
           (node_ref_expr act a_idx av) (run_n M act input ss0)
           (sched_input input (run_n M act input ss0)))).
  Proof.
    intros Halign Hlen Hz0 Hpre HvM Hrs Hsamp Hsd Hdop Hdsz Hgd.
    assert (Hlen0 : 0 < length (graph (build_dfg ctx act))) by lia.
    assert (Hzv : forall q, (fst ss0).[tf_dfg_v a_idx q] = Bits.zero)
      by (intro q; exact (Hz0 (tf_dfg_v a_idx q) I)).
    assert (Hsamv : is_sample_of act (vreg_nid a_idx n_idx) = true)
      by (unfold SchedulerSimulationBase.is_sample_of; rewrite Hsamp; reflexivity).
    (* the cycle the answer is latched on *)
    assert (dec : forall k,
              {(fst (run_n k act input ss0)).[tf_dfg_v a_idx n_idx] = Bits.ones 1}
              + {~ (fst (run_n k act input ss0)).[tf_dfg_v a_idx n_idx] = Bits.ones 1}).
    { intro k.
      destruct (beq_dec ((fst (run_n k act input ss0)).[tf_dfg_v a_idx n_idx])
                  (Bits.ones 1)) eqn:Hb.
      - left. exact (proj1 (beq_dec_iff _ _ _) Hb).
      - right. intro Hc. rewrite Hc, beq_dec_refl in Hb. discriminate Hb. }
    destruct (least_witness _ dec M (ex_intro _ M (conj (Nat.le_refl M) HvM)))
      as [N [HPN Hmin]].
    assert (HN0 : N <> 0).
    { intro He. subst N. cbn [run_n] in HPN. rewrite Hzv in HPN.
      exact (ones1_neq_zero (eq_sym HPN)). }
    assert (HNM : N <= M).
    { destruct (Nat.le_gt_cases N M) as [H | H]; [ exact H |].
      exfalso. exact (Hmin M H HvM). }
    destruct N as [| j]; [ exfalso; exact (HN0 eq_refl) |].
    assert (Hjm : j < M) by lia.
    assert (Hvj : (fst (run_n j act input ss0)).[tf_dfg_v a_idx n_idx] = Bits.zero).
    { destruct (bits1_cases ((fst (run_n j act input ss0)).[tf_dfg_v a_idx n_idx]))
        as [H | H]; [ exfalso; exact (Hmin j (Nat.lt_succ_diag_r j) H) | exact H ]. }
    (* the answer is held from that cycle to the end of the run *)
    assert (Hfe : S j + (M - S j) = M) by lia.
    assert (Hpf : forall i, 1 <= i <= S j + (M - S j) ->
              ~ done_set (run_n i act input ss0))
      by (intros i Hi; apply Hpre; lia).
    destruct (sample_buffer_frozen_run act a_idx n_idx input ss0 (S j) (M - S j)
                Halign Hzv Hpf Hsamv HPN) as [Hfrz _].
    rewrite Hfe in Hfrz. rewrite Hfrz.
    (* the latch itself *)
    assert (Hnd : ~ done_set (sched_step act (run_n j act input ss0)
                    (sched_input input (run_n j act input ss0))))
      by (exact (Hpre (S j) ltac:(lia))).
    assert (HvSj : (fst (sched_step act (run_n j act input ss0)
                      (sched_input input (run_n j act input ss0)))).[tf_dfg_v a_idx n_idx]
                   = Bits.ones 1) by exact HPN.
    pose proof (buffer_valid_gate act a_idx n_idx (run_n j act input ss0)
                  (sched_input input (run_n j act input ss0)) Halign Hnd HvSj) as Hgate.
    pose proof (buffer_after_cycle act a_idx n_idx (run_n j act input ss0)
                  (sched_input input (run_n j act input ss0)) Halign Hnd) as Hba.
    cbv zeta in Hba. destruct Hba as [Hvalue _].
    change (fst (run_n (S j) act input ss0)) with
      (fst (sched_step act (run_n j act input ss0)
              (sched_input input (run_n j act input ss0)))).
    rewrite Hvalue.
    change (fst (nth (index_to_nat n_idx)
                   (nth (index_to_nat a_idx) bneeds []) (0, (0, 0))))
      with (vreg_nid a_idx n_idx).
    unfold SchedulerSimulationBase.buf_value_expr.
    destruct (stall_lat_of act (vreg_nid a_idx n_idx)) as [l |] eqn:Hst.
    { exfalso. unfold SchedulerSimulationBase.stall_lat_of, SchedulerSimulationBase.is_sample_of in Hst, Hsamv.
      destruct (node_op act (vreg_nid a_idx n_idx)); discriminate. }
    rewrite Hsamv.
    assert (Hnone : BitsToLists.list_assoc
              (filter (fun '(b_nid, _) => negb (Nat.eqb b_nid (vreg_nid a_idx n_idx)))
                 (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []))
              (vreg_nid a_idx n_idx) = None).
    { apply list_assoc_key_none. intro Hin2.
      apply in_map_iff in Hin2. destruct Hin2 as [[k v] [Hk Hmem]].
      cbn [fst] in Hk. subst k. apply filter_In in Hmem.
      destruct Hmem as [_ Hq2]. rewrite Nat.eqb_refl in Hq2. discriminate Hq2. }
    rewrite (compile_sample_value _ _ _ a_idx _ p tok en _ [] _ Hsamp Hnone Hlen0).
    cbn [tf_eval_expr]. rewrite !convert_same.
    (* the bit is down and the gate is up, so the register takes the wire *)
    match goal with
    | |- context [ Bits.neg ?x ] =>
        replace x with (@Bits.zero 1) by (symmetry; exact Hvj)
    end.
    rewrite Hgate.
    match goal with
    | |- context [ @beq_dec ?T ?E ?x ?z ] =>
        replace (@beq_dec T E x z) with false by (vm_compute; reflexivity)
    end.
    cbn beta iota. cbn [sched_input].
    rewrite (port_holds_request act a_idx input ss0 M n_idx p tok en d av en' j
               Halign Hlen Hz0 Hpre Hrs Hsamp Hsd Hdop Hdsz Hgd
               Hjm Hvj HPN).
    reflexivity.
  Qed.

  (* ==================================================================== *)
  (* THE OPEN OBLIGATION.                                                 *)
  (*                                                                      *)
  (* [Print Assumptions variable_scheduler_correct] names what is owed.   *)
  (* ==================================================================== *)

  (* OPEN.  The walk from a latched sample back to its drive's argument:
     register -> gate -> token -> head -> join, taking the join's FIRST
     argument, then [compile_drive_arg_valid]. *)
  Lemma sample_arg_settled
        (act: tfs_action sched) a_idx (input: input_t) (ss0: sched_sys_state) M
        n_idx (p: p_var) tok en d av en' :
    act_idx_aligned act a_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    (forall x, zeroed_at_start x -> (fst ss0).[x] = Bits.zero) ->
    (forall i, 1 <= i <= M -> ~ done_set (run_n i act input ss0)) ->
    node_op act (vreg_nid a_idx n_idx) = DFG_Sample p tok en ->
    sample_drive act (vreg_nid a_idx n_idx) = Some d ->
    node_op act d = DFG_Drive p av en' ->
    (fst (run_n M act input ss0)).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
    eval1 (node_ref_valid act a_idx av) (run_n M act input ss0)
      (sched_input input (run_n M act input ss0)) = Bits.ones 1.
  Proof.
  Admitted.

  (* OPEN.  The design is settled and its structural prerequisites are
     proved -- [stall_wait_start], [stall_is_buffered],
     [chain_gate_stall_is_token].  What is left is the walk from a sample's
     latch back to the cycle its drive pulsed on. *)
  Lemma requests_sent_holds
        (act: tfs_action sched) a_idx (input: input_t) (ss0: sched_sys_state) M :
    act_idx_aligned act a_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    (forall x, zeroed_at_start x -> (fst ss0).[x] = Bits.zero) ->
    (forall i, 1 <= i <= M -> ~ done_set (run_n i act input ss0)) ->
    requests_sent act a_idx input ss0 M.
  Proof.
  Admitted.
  (* PHASE 3 (correctness at done): once the done flag is set, the mapped
     final states and outputs match the one-shot source evaluation. *)
  Lemma scheduler_done_correct :
    forall (act: tfs_action sched) (sp0: src_sys_state)
           (ss0: sched_sys_state) (input: input_t) (N: nat),
      start_rel sp0 ss0 ->
      (forall k, k < N -> ~ done_set (run_n k act input ss0)) ->
      done_set (run_n N act input ss0) ->
      let sp1 := tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act) sp0 input in
      maps_from ctx bneeds (fst (run_n N act input ss0)) = fst sp1 /\
      snd (run_n N act input ss0) = snd sp1.
  Proof.
    intros act sp0 ss0 input N [Hout0 [Hst0 Hzero0]] Hbefore Hdone.
    destruct (exists_act_idx act) as [a_idx Halign].
    (* N = 0 is impossible: start_rel clears the done flag *)
    destruct N as [| M].
    { exfalso. apply Hdone. cbn [run_n]. apply (Hzero0 (tfs_done_signal sched) I). }
    set (ssM := run_n M act input ss0) in *.
    change (run_n (S M) act input ss0)
      with (sched_step act ssM (sched_input input ssM)) in *.
    assert (Hpre : forall i, 1 <= i <= M -> ~ done_set (run_n i act input ss0))
      by (intros i Hi; apply Hbefore; lia).
    (* the pre-done prefix leaves the base state and the outputs at sp0 *)
    assert (Hs : forall sv, (fst ssM).[tf_dfg_s sv] = (fst sp0).[sv]).
    { intro sv. unfold ssM. rewrite (run_preserves_svar act input ss0 M Hpre sv).
      rewrite <- Hst0, getenv_maps_from. reflexivity. }
    assert (Ho : forall ov, (snd ssM).[ov] = (snd sp0).[ov]).
    { intro ov. unfold ssM. rewrite (run_preserves_ovar act input ss0 M Hpre ov).
      rewrite Hout0. reflexivity. }
    (* the invariant holds at ssM *)
    assert (Hvr : valid_refs act a_idx ssM (sched_input input ssM)
                  /\ valid_settled act a_idx ssM (sched_input input ssM)).
    { destruct (valid_settled_run act a_idx input ss0 M Halign
                  ltac:(intro n_idx; apply (Hzero0 (tf_dfg_v a_idx n_idx) I)))
        as [_ [Hr Hi]]. exact (conj Hr Hi). }
    destruct Hvr as [Hrefs Hinv].
    (* the full table and [sample_bufs] agree wherever a sample has a slot *)
    assert (Hsub : forall e,
              In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) ->
              In e (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])).
    { intros e He. exact He. }
    assert (Hsam_sub : forall x,
              BitsToLists.list_assoc
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) x = None ->
              BitsToLists.list_assoc (sample_bufs act a_idx) x = None).
    { intros x Hx. apply list_assoc_key_none. intro Hin2.
      apply in_map_iff in Hin2. destruct Hin2 as [[x2 v2] [Hxx Hmem2]].
      cbn [fst] in Hxx. subst x2.
      unfold SchedulerSimulationBase.sample_bufs in Hmem2. apply filter_In in Hmem2.
      apply (list_assoc_none_key _ _ Hx), in_map_iff.
      exists (x, v2). split; [ reflexivity | exact (proj1 Hmem2) ]. }
    assert (Hsam_same : forall x m msz,
              BitsToLists.list_assoc
                (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []) x
                = Some (m, msz) ->
              is_sample_of act x = true ->
              BitsToLists.list_assoc (sample_bufs act a_idx) x = Some (m, msz)).
    { intros x m msz Hx Hsx. apply list_assoc_nodup_in.
      + unfold SchedulerSimulationBase.sample_bufs. apply nodup_map_fst_filter.
        exact (slot_keys_nodup act a_idx Halign).
      + unfold SchedulerSimulationBase.sample_bufs. apply filter_In.
        split; [ exact (wla_in _ _ _ Hx) | exact Hsx ]. }
    (* drop the buffers from any var_map node's compiled expression *)
    assert (Hdrop : forall v n szB,
              In (v, n) (var_map (build_dfg ctx act)) ->
              szB = dfg_var_size ctx v ->
              tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
                (fst (compile_dfg_expr ctx bneeds
                        (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n
                        (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])))
                ssM (sched_input input ssM)
              = tf_eval_expr ss_sz si_sz oo_sz (szB := szB)
                (fst (compile_dfg_expr ctx bneeds
                        (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n (sample_bufs act a_idx)))
                ssM (sched_input input ssM)).
    { intros v n szB Hin HszB.
      assert (Hmem : In n (map snd (var_map (build_dfg ctx act))))
        by (apply (in_map snd _ (v, n)); exact Hin).
      destruct (var_map_node_range act n Hmem) as [Hn1 Hnlen].
      apply (compile_subst_valid act a_idx ssM (sched_input input ssM)
               Halign Hinv).
      - exact Hsub.
      - exact Hsam_sub.
      - exact Hsam_same.
      - exact Hn1.
      - exact Hnlen.
      - exact Hnlen.
      - rewrite HszB. symmetry. exact (var_map_entry_size act v n Hin).
      - exact (sched_step_done_valid act a_idx ssM (sched_input input ssM) n Halign Hdone Hmem). }
    (* [done] is the AND of the roots' validity, so every root reads valid *)
    assert (Hvalid : forall n, In n (map snd (var_map (build_dfg ctx act))) ->
              eval1 (node_ref_valid act a_idx n) ssM (sched_input input ssM)
              = Bits.ones 1).
    { intros n Hmem.
      destruct (var_map_node_range act n Hmem) as [Hn1 Hnlen].
      rewrite <- (nrv_fuel act a_idx n (length (graph (build_dfg ctx act)))
                    Hn1 Hnlen Hnlen).
      exact (compile_subst_ref_valid_gen act a_idx ssM (sched_input input ssM)
               Halign Hinv Hrefs
               (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])
               Hsub Hsam_sub Hsam_same
               (length (graph (build_dfg ctx act))) n []
               Hn1 Hnlen Hnlen
               (sched_step_done_valid act a_idx ssM (sched_input input ssM) n
                  Halign Hdone Hmem)). }
    (* THE ROUND TRIP, at the state the action finishes from: a sample's
       register holds the IP's answer to the request its own drive sent. *)
    assert (Hrt_obligation : forall n_idx p tok en d av en',
              node_op act (vreg_nid a_idx n_idx) = DFG_Sample p tok en ->
              sample_drive act (vreg_nid a_idx n_idx) = Some d ->
              node_op act d = DFG_Drive p av en' ->
              sz (nth d (graph (build_dfg ctx act))
                   {| nid := 0; op := DFG_Empty; sz := 0 |})
                = ip_req_sz (tfs_spec_ip ctx p) ->
              guard_holds act a_idx ssM (sched_input input ssM) en ->
              (fst ssM).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
              (fst ssM).[tf_dfg_b a_idx n_idx]
              = convert (ip_fn (tfs_spec_ip ctx p)
                  (tf_eval_expr ss_sz si_sz oo_sz
                     (szB := ip_req_sz (tfs_spec_ip ctx p))
                     (node_ref_expr act a_idx av) ssM (sched_input input ssM)))).
    { intros n_idx p tok en d av en' Hsamp Hsd Hdop Hdsz Hgd Hv.
      destruct (node_op_pos act (vreg_nid a_idx n_idx)
                  ltac:(rewrite Hsamp; discriminate)) as [Hs1 Hslen].
      assert (Hlen2 : 1 < length (graph (build_dfg ctx act))) by lia.
      exact (round_trip act a_idx input ss0 M n_idx p tok en d av en'
               Halign Hlen2 Hzero0 Hpre Hv
               (requests_sent_holds act a_idx input ss0 M
                  Halign Hlen2 Hzero0 Hpre)
               Hsamp Hsd Hdop Hdsz Hgd). }
    (* THE REQUEST'S ARGUMENT, at the state the action finishes from. *)
    assert (Harg_obligation : forall n_idx p tok en d av en',
              node_op act (vreg_nid a_idx n_idx) = DFG_Sample p tok en ->
              sample_drive act (vreg_nid a_idx n_idx) = Some d ->
              node_op act d = DFG_Drive p av en' ->
              (fst ssM).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
              eval1 (node_ref_valid act a_idx av) ssM (sched_input input ssM)
              = Bits.ones 1).
    { intros n_idx p tok en d av en' Hsamp Hsd Hdop Hv.
      destruct (node_op_pos act (vreg_nid a_idx n_idx)
                  ltac:(rewrite Hsamp; discriminate)) as [Hs1 Hslen].
      assert (Hlen2 : 1 < length (graph (build_dfg ctx act))) by lia.
      exact (sample_arg_settled act a_idx input ss0 M n_idx p tok en d av en'
               Halign Hlen2 Hzero0 Hpre Hsamp Hsd Hdop Hv). }
    destruct (dfg_action_semantics act a_idx sp0 ssM input (sched_input input ssM)
                Halign ltac:(intro v; reflexivity) Hrt_obligation Harg_obligation Hs Ho)
      as [Hsem_s [Hsem_o [Hfix_s Hfix_o]]].
    split.
    - apply equiv_eq. unfold equiv. intro sv.
      rewrite getenv_maps_from.
      destruct (find_pair_dec eq_dec (var_map (build_dfg ctx act)) (DFG_SVar sv))
        as [[n Hn] | Hno].
      + rewrite (sched_step_done_svar act a_idx ssM (sched_input input ssM) sv n Halign Hdone Hn).
        rewrite (Hdrop (DFG_SVar sv) n (ss_sz (tf_dfg_s sv)) Hn eq_refl).
        assert (Hmem : In n (map snd (var_map (build_dfg ctx act))))
          by (apply (in_map snd _ (DFG_SVar sv, n)); exact Hn).
        exact (Hsem_s sv n Hn (Hvalid n Hmem)).
      + rewrite (sched_step_done_svar_untouched act a_idx ssM (sched_input input ssM) sv Halign Hdone Hno).
        rewrite (Hfix_s sv Hno). exact (Hs sv).
    - apply equiv_eq. unfold equiv. intro ov.
      destruct (find_pair_dec eq_dec (var_map (build_dfg ctx act)) (DFG_OVar ov))
        as [[n Hn] | Hno].
      + rewrite (sched_step_done_ovar act a_idx ssM (sched_input input ssM) ov n Halign Hdone Hn).
        rewrite (Hdrop (DFG_OVar ov) n (oo_sz ov) Hn eq_refl).
        assert (Hmem : In n (map snd (var_map (build_dfg ctx act))))
          by (apply (in_map snd _ (DFG_OVar ov, n)); exact Hn).
        exact (Hsem_o ov n Hn (Hvalid n Hmem)).
      + rewrite (sched_step_done_ovar_untouched act a_idx ssM (sched_input input ssM) ov Halign Hdone Hno).
        rewrite (Hfix_o ov Hno). exact (Ho ov).
  Qed.

  (* ==================================================================== *)
  (* Top-level correctness: one source step = run scheduled until done.   *)
  (* ==================================================================== *)
  Theorem variable_scheduler_correct :
    forall (act: tfs_action sched) (sp0: src_sys_state)
           (ss0: sched_sys_state) (input: input_t),
      start_rel sp0 ss0 ->
      exists N,
        (forall k, k < N -> ~ done_set (run_n k act input ss0)) /\
        done_set (run_n N act input ss0) /\
        let sp1 := tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act) sp0 input in
        maps_from ctx bneeds (fst (run_n N act input ss0)) = fst sp1 /\
        snd (run_n N act input ss0) = snd sp1.
  Proof.
    intros act sp0 ss0 input Hstart.
    destruct (scheduler_reaches_done act sp0 ss0 input Hstart) as [N [Hbefore Hdone]].
    exists N. split; [ exact Hbefore |]. split; [ exact Hdone |].
    apply (scheduler_done_correct act sp0 ss0 input N Hstart Hbefore Hdone).
  Qed.

End SchedulerSimulation.

(* Sanity check: the top-level theorem must depend on no axioms and no
   admitted lemmas. *)
Print Assumptions variable_scheduler_correct.
