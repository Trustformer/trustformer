(* ===================================================================== *)
(*  SPIKE: a call, through build_dfg, measured.                          *)
(* ===================================================================== *)
(*
    A call emits a DRIVE, written by an always-op; the request is not an output,
    so no done-op can write it; and the sample is scheduled [lat] cycles later.
*)

Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.DFG.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.

Require Import Coq.Lists.List.
Import ListNotations.

Section CallSpike.

  Definition cw := 256.          (* payload width, as for a crypto port group *)
  Definition clat := 3.          (* declared IP latency, in CYCLES *)
  Definition cclimit := 5.

  Inductive cs_action  := act_call.
  Inductive cs_states  := st_res.
  Inductive cs_inputs  := in_msg.
  (* No outputs at all: the IP request is a scheduler register, not a port. *)
  Definition cs_outputs := Empty_set.

  Definition cs_states_size  (_: cs_states)  : nat := cw.
  Definition cs_inputs_size  (_: cs_inputs)  : nat := cw.
  Definition cs_outputs_size (_: cs_outputs) : nat := cw.

  Definition cs_states_init (x: cs_states) : tf_states_type cs_states_size x :=
    match x with st_res => Bits.zero end.

  (* What the IP computes.  The lowering never reads it -- the circuit samples
     the wire -- but the SPEC does: a call denotes [dst := ip_fn arg]. *)
  Definition cs_f (v: bits_t cw) : bits_t cw := v.

  (* Neither IP port is a port of the design, so neither is classified here. *)

  Definition cs_in_class (_: cs_inputs) : port_class := Public.

  Definition cs_out_class (_: cs_outputs) : port_class := Secret.

  Inductive cs_ips := cs_crypto.
  Definition cs_ip (_: cs_ips) : ip_decl :=
    {| ip_req_sz := cw; ip_resp_sz := cw; ip_lat := clat; ip_fn := cs_f |}.

  Definition cs_ctx : TFSchedContext := {|
      tfs_spec_states := cs_states;   tfs_spec_states_fin := _;
      tfs_spec_states_size := cs_states_size;
      tfs_spec_states_init := cs_states_init;

      tfs_spec_inputs := cs_inputs;   tfs_spec_inputs_fin := _;
      tfs_spec_inputs_size := cs_inputs_size;
      tfs_spec_inputs_class := cs_in_class;

      tfs_spec_outputs := cs_outputs; tfs_spec_outputs_fin := _;
      tfs_spec_outputs_size := cs_outputs_size;
      tfs_spec_outputs_class := cs_out_class;

      tfs_spec_action := cs_action;   tfs_spec_action_fin := _;
      (* THE CALL: drive [in_msg] at the IP, wait clat cycles, read the answer
         into st_res. *)
      tfs_spec_action_ops := fun _ =>
        tf_ops_base (tf_call cs_crypto st_res (tf_ivar in_msg));

      tfs_spec_ips := cs_ips;      tfs_spec_ips_fin := _;
      tfs_spec_ip := cs_ip;

      tfs_spec_decls := []
  |}.

  Definition cs_dfg := build_dfg cs_ctx act_call.
  Definition cs_cycles :=
    calc_target_cycle cclimit (calc_backward_cost cs_ctx cclimit cs_dfg).

  Definition ccyc (n: nid_t) : nat :=
    match BitsToLists.list_assoc cs_cycles n with Some c => c | None => 999 end.

  (* ================================================================== *)
  (* 1.  THE REQUEST IS DRIVEN, NOT ASSIGNED.                           *)
  (* ================================================================== *)

  (* [driven_ports] is what [compile_dfg_drives] maps over, and that emission
     goes into the ALWAYS half -- so this is the statement that the request
     reaches the wire during the action rather than at done. *)
  Example req_is_driven : driven_ports cs_ctx cs_dfg = [cs_crypto].
  Proof. vm_compute. reflexivity. Qed.

  (* A request port is outside the design's outputs, so no action can name it
     and the drive/assign conflict is unsayable. *)

  (* exactly one drive for the one call *)
  Example one_drive : List.length (drive_nodes cs_ctx cs_dfg cs_crypto) = 1.
  Proof. vm_compute. reflexivity. Qed.

  (* ================================================================== *)
  (* 2.  THE WAIT IS REAL.                                              *)
  (* ================================================================== *)

  (* The wait is ONE [DFG_Stall clat], and the round trip costs TWO registers
     whatever [clat] is: the stall's counter, and the sample's latched answer.
     The port holds its answer only until the next call on it. *)
  Definition cs_bufs := require_buffer cs_ctx cs_dfg cs_cycles.

  Example wait_is_two_buffers : List.length cs_bufs = 2.
  Proof. vm_compute. reflexivity. Qed.

  (* The drive and the sample are clat cycles apart.  Cycles count BACKWARD
     from done, so the drive has the larger number. *)
  Definition drive_nid := List.hd 0 (drive_nodes cs_ctx cs_dfg cs_crypto).
  Definition samp_nid :=
    List.fold_left (fun acc nd => match op nd with
                                  | DFG_Sample _ _ _ => nid nd
                                  | _ => acc end) (graph cs_dfg) 0.

  Example round_trip_separated : ccyc drive_nid - ccyc samp_nid = clat.
  Proof. vm_compute. reflexivity. Qed.

  (* Its width is the counter's: a [DFG_Sample] uses only the token's validity. *)
  Example stall_is_a_counter :
    forallb (fun nd => match op nd with
                       | DFG_Stall l _ => Nat.eqb (sz nd) (counter_sz l)
                       | _ => true end)
            (graph cs_dfg) = true.
  Proof. vm_compute. reflexivity. Qed.

  Example one_stall_node :
    List.length (filter (fun nd => match op nd with
                                   | DFG_Stall _ _ => true | _ => false end)
                        (graph cs_dfg)) = 1.
  Proof. vm_compute. reflexivity. Qed.

  (* and the sample is not a source, so it has a defined sampling cycle *)
  Example sample_not_source : is_source cs_ctx cs_dfg samp_nid = false.
  Proof. vm_compute. reflexivity. Qed.

End CallSpike.

(* ===================================================================== *)
(*  End-to-end: through TypedSynthesis and out to Verilog.               *)
(* ===================================================================== *)
(* Extracted so the hardware can be READ and RUN (sim/tb_call.sv).  In
   build/Example_CallSpike.v: the request assigned from ALWAYS logic, its
   else-branch reading the port's own previous value so it HOLDS, one driver,
   and the response read LIVE off the wire. *)

Require Import Trustformer.TypedSynthesis.

Section CallSynthesis.

  Definition cs_action_encoding (a: cs_action) : bits_t 16 :=
    match a with act_call => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1 end.

  Lemma cs_action_encoding_inj :
    forall a1 a2, cs_action_encoding a1 = cs_action_encoding a2 -> a1 = a2.
  Proof. intros a1 a2 _. destruct a1; destruct a2; reflexivity. Qed.

  Definition cs_schedule := tfs_schedule cs_ctx cclimit.

  Definition cs_tf_ctx : TFSynthContext := {|
    tf_sched_ctx := cs_schedule;
    tf_action_encoding := cs_action_encoding;
    tf_action_encoding_inj := cs_action_encoding_inj;
  |}.

  Definition R := TypedSynthesis.R cs_tf_ctx.
  Definition r := TypedSynthesis.r cs_tf_ctx.
  Definition Sigma := TypedSynthesis.Sigma cs_tf_ctx.
  Definition system_schedule := TypedSynthesis.system_schedule cs_tf_ctx.
  Definition ext_fn_specs := TypedSynthesis.ext_fn_specs cs_tf_ctx.
  Instance ext_fn_names : Show _ := TypedSynthesis.ext_fn_names cs_tf_ctx.

  Definition package :=
    {| ip_koika := {| koika_reg_types := R;
                      koika_reg_names := TypedSynthesis.reg_names cs_tf_ctx;
                      koika_reg_init := r;
                      koika_reg_finite := TypedSynthesis._reg_t_finite cs_tf_ctx;
                      koika_ext_fn_types := Sigma;
                      koika_rules := TypedSynthesis.rules cs_tf_ctx;
                      koika_rule_names := TypedSynthesis.rule_names cs_tf_ctx;
                      koika_rule_external := (fun _ => false);
                      koika_scheduler := system_schedule;
                      koika_module_name := "Example_CallSpike" |};

    ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn; efs_method := false |};
                sp_prelude := None |};

    ip_verilog := {| vp_ext_fn_specs := ext_fn_specs |} |}.

End CallSynthesis.

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Example_CallSpike.ml" prog.

(* ===================================================================== *)
(*  Two calls to the SAME IP in one action.                              *)
(* ===================================================================== *)

Section TwoCalls.

  Inductive tc_states  := st_a | st_b.
  Definition tc_states_size (_: tc_states) : nat := cw.
  Definition tc_states_init (x: tc_states) : tf_states_type tc_states_size x :=
    match x with st_a => Bits.zero | st_b => Bits.zero end.

  (* two calls on the SAME req/resp pair, with INDEPENDENT arguments *)
  Definition tc_ops : @tf_ops tc_states cs_inputs cs_outputs cs_ips :=
    tf_ops_cons
      (tf_ops_base (tf_call cs_crypto st_a (tf_ivar in_msg)))
      (tf_ops_base (tf_call cs_crypto st_b
                      (tf_op1 tf_not (tf_ivar in_msg)))).

  Definition tc_ctx : TFSchedContext := {|
      tfs_spec_states := tc_states;   tfs_spec_states_fin := _;
      tfs_spec_states_size := tc_states_size;
      tfs_spec_states_init := tc_states_init;
      tfs_spec_inputs := cs_inputs;   tfs_spec_inputs_fin := _;
      tfs_spec_inputs_size := cs_inputs_size;
      tfs_spec_inputs_class := cs_in_class;
      tfs_spec_outputs := cs_outputs; tfs_spec_outputs_fin := _;
      tfs_spec_outputs_size := cs_outputs_size;
      tfs_spec_outputs_class := cs_out_class;
      tfs_spec_action := cs_action;   tfs_spec_action_fin := _;
      tfs_spec_action_ops := fun _ => tc_ops;
      tfs_spec_ips := cs_ips;      tfs_spec_ips_fin := _;
      tfs_spec_ip := cs_ip;

      tfs_spec_decls := []
  |}.

  Definition tc_dfg := build_dfg tc_ctx act_call.
  Definition tc_cycles :=
    calc_target_cycle cclimit (calc_backward_cost tc_ctx cclimit tc_dfg).
  Definition tcyc2 (n: nid_t) : nat :=
    match BitsToLists.list_assoc tc_cycles n with Some c => c | None => 999 end.

  (* BOTH calls drive the same port, so there are two drive nodes ... *)
  Definition tc_drives := drive_nodes tc_ctx tc_dfg cs_crypto.
  Example two_drives : List.length tc_drives = 2.
  Proof. vm_compute. reflexivity. Qed.

  (* ... but the port appears ONCE in driven_ports, so ONE tf_output op is
     emitted for it, folding both drives into one nested conditional. *)
  Example one_driven_port : driven_ports tc_ctx tc_dfg = [cs_crypto].
  Proof. vm_compute. reflexivity. Qed.

  (* Are the two drives in the SAME cycle?  If so they collide: the fold puts
     the latest outermost, so the earlier request never reaches the wire. *)
  Definition tc_d1 := List.nth 0 tc_drives 999.
  Definition tc_d2 := List.nth 1 tc_drives 999.

  Definition tc_samples :=
    List.fold_left (fun acc nd => match op nd with
                                  | DFG_Sample _ _ _ => nid nd :: acc
                                  | _ => acc end) (graph tc_dfg) [].

End TwoCalls.

(* The complement: call 2s argument READS call 1s result, so there is a data
   dependency between them.  Does the scheduler sequence them? *)
Section TwoCallsChained.

  Definition tc2_ops : @tf_ops tc_states cs_inputs cs_outputs cs_ips :=
    tf_ops_cons
      (tf_ops_base (tf_call cs_crypto st_a (tf_ivar in_msg)))
      (tf_ops_base (tf_call cs_crypto st_b (tf_svar st_a))).

  Definition tc2_ctx : TFSchedContext :=
    {| tfs_spec_states := tc_states;   tfs_spec_states_fin := _;
       tfs_spec_states_size := tc_states_size;
       tfs_spec_states_init := tc_states_init;
       tfs_spec_inputs := cs_inputs;   tfs_spec_inputs_fin := _;
       tfs_spec_inputs_size := cs_inputs_size;
       tfs_spec_inputs_class := cs_in_class;
       tfs_spec_outputs := cs_outputs; tfs_spec_outputs_fin := _;
       tfs_spec_outputs_size := cs_outputs_size;
       tfs_spec_outputs_class := cs_out_class;
       tfs_spec_action := cs_action;   tfs_spec_action_fin := _;
       tfs_spec_action_ops := fun _ => tc2_ops;
       tfs_spec_ips := cs_ips;      tfs_spec_ips_fin := _;
       tfs_spec_ip := cs_ip;
       tfs_spec_decls := [] |}.

  Definition tc2_dfg := build_dfg tc2_ctx act_call.
  Definition tc2_cycles :=
    calc_target_cycle cclimit (calc_backward_cost tc2_ctx cclimit tc2_dfg).
  Definition tcyc3 (n: nid_t) : nat :=
    match BitsToLists.list_assoc tc2_cycles n with Some c => c | None => 999 end.
  Definition tc2_drives := drive_nodes tc2_ctx tc2_dfg cs_crypto.
  Definition tc2_samples :=
    List.fold_left (fun acc nd => match op nd with
                                  | DFG_Sample _ _ _ => nid nd :: acc
                                  | _ => acc end) (graph tc2_dfg) [].

End TwoCallsChained.

(* ================================================================== *)
(* TWO CALLS ON ONE IP: BROKEN WHEN INDEPENDENT, CORRECT WHEN CHAINED *)
(* ================================================================== *)

(* INDEPENDENT calls SEQUENCE, as chained ones do: one set of request wires
   means two calls take turns.  The ordering join puts the second call's stall
   under the first call's sample, so the second drive lands in that sample's
   cycle, [lat] after the first drive. *)
Example independent_calls_sequence :
  List.map tcyc2 tc_drives = [3; 6].
Proof. vm_compute. reflexivity. Qed.

Example independent_samples_sequence :
  List.map tcyc2 tc_samples = [0; 3].
Proof. vm_compute. reflexivity. Qed.

(* ...and chained calls are unchanged: the data dependency already ordered them,
   so the join adds nothing. *)
Example chained_calls_sequence :
  List.map tcyc3 tc2_drives = [3; 6].
Proof. vm_compute. reflexivity. Qed.

Example chained_samples_sequence :
  List.map tcyc3 tc2_samples = [0; 3].
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  End-to-end for TWO sequenced calls on one IP.                        *)
(* ===================================================================== *)
(* Two calls on one IP with INDEPENDENT arguments.  In
   build/Example_TwoCallSpike.v: TWO strobe pulses on the request's top bit
   [lat] apart, the payload changing between them and HELD in between, and a
   single driver.  Run by sim/tb_two.sv. *)

Section TwoCallSynthesis.

  Definition tc_schedule := tfs_schedule tc_ctx cclimit.

  Definition tc_tf_ctx : TFSynthContext := {|
    tf_sched_ctx := tc_schedule;
    tf_action_encoding := cs_action_encoding;
    tf_action_encoding_inj := cs_action_encoding_inj;
  |}.

  Definition tcR := TypedSynthesis.R tc_tf_ctx.
  Definition tcr := TypedSynthesis.r tc_tf_ctx.
  Definition tcSigma := TypedSynthesis.Sigma tc_tf_ctx.
  Definition tc_system_schedule := TypedSynthesis.system_schedule tc_tf_ctx.
  Definition tc_ext_fn_specs := TypedSynthesis.ext_fn_specs tc_tf_ctx.
  Instance tc_ext_fn_names : Show _ := TypedSynthesis.ext_fn_names tc_tf_ctx.

  Definition tc_package :=
    {| ip_koika := {| koika_reg_types := tcR;
                      koika_reg_names := TypedSynthesis.reg_names tc_tf_ctx;
                      koika_reg_init := tcr;
                      koika_reg_finite := TypedSynthesis._reg_t_finite tc_tf_ctx;
                      koika_ext_fn_types := tcSigma;
                      koika_rules := TypedSynthesis.rules tc_tf_ctx;
                      koika_rule_names := TypedSynthesis.rule_names tc_tf_ctx;
                      koika_rule_external := (fun _ => false);
                      koika_scheduler := tc_system_schedule;
                      koika_module_name := "Example_TwoCallSpike" |};
    ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn; efs_method := false |};
                sp_prelude := None |};
    ip_verilog := {| vp_ext_fn_specs := tc_ext_fn_specs |} |}.

End TwoCallSynthesis.

Definition tc_prog := Interop.Backends.register tc_package.
Extraction "Example_TwoCallSpike.ml" tc_prog.

(* ===================================================================== *)
(*  End-to-end for two CHAINED calls: call 2's argument is call 1's       *)
(*  result, so the calls carry a real data dependency.                   *)
(* ===================================================================== *)
(* Call 2's payload exists only once call 1's answer has landed, so the drive,
   the sample latch and the ordering join must agree on WHEN.  A strobe held as
   a level would send a payload still being computed.  Run by sim/tb_chain.sv. *)

Section TwoCallsChainedSynthesis.

  Definition tc2_schedule := tfs_schedule tc2_ctx cclimit.

  Definition tc2_tf_ctx : TFSynthContext := {|
    tf_sched_ctx := tc2_schedule;
    tf_action_encoding := cs_action_encoding;
    tf_action_encoding_inj := cs_action_encoding_inj;
  |}.

  Definition tc2R := TypedSynthesis.R tc2_tf_ctx.
  Definition tc2r := TypedSynthesis.r tc2_tf_ctx.
  Definition tc2Sigma := TypedSynthesis.Sigma tc2_tf_ctx.
  Definition tc2_system_schedule := TypedSynthesis.system_schedule tc2_tf_ctx.
  Definition tc2_ext_fn_specs := TypedSynthesis.ext_fn_specs tc2_tf_ctx.
  Instance tc2_ext_fn_names : Show _ := TypedSynthesis.ext_fn_names tc2_tf_ctx.

  Definition tc2_package :=
    {| ip_koika := {| koika_reg_types := tc2R;
                      koika_reg_names := TypedSynthesis.reg_names tc2_tf_ctx;
                      koika_reg_init := tc2r;
                      koika_reg_finite := TypedSynthesis._reg_t_finite tc2_tf_ctx;
                      koika_ext_fn_types := tc2Sigma;
                      koika_rules := TypedSynthesis.rules tc2_tf_ctx;
                      koika_rule_names := TypedSynthesis.rule_names tc2_tf_ctx;
                      koika_rule_external := (fun _ => false);
                      koika_scheduler := tc2_system_schedule;
                      koika_module_name := "Example_ChainedCallSpike" |};
    ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn; efs_method := false |};
                sp_prelude := None |};
    ip_verilog := {| vp_ext_fn_specs := tc2_ext_fn_specs |} |}.

End TwoCallsChainedSynthesis.

Definition tc2_prog := Interop.Backends.register tc2_package.
Extraction "Example_ChainedCallSpike.ml" tc2_prog.

(* ===================================================================== *)
(*  A call under a BRANCH.                                               *)
(* ===================================================================== *)
(* Both arms of an [if] call the same IP with different payloads.  A call emits
   its drive, not the branch, so this measures whether the two drives are
   mutually exclusive in TIME.  MARS needs it: PcrExtend selects a PCR with an
   [if] and Quote a snapshot shape with four. *)

Section BranchCall.

  Inductive bc_states  := st_out.
  Definition bc_states_size (_: bc_states) : nat := cw.
  Definition bc_states_init (x: bc_states) : tf_states_type bc_states_size x :=
    match x with st_out => Bits.zero end.

  Inductive bc_inputs := in_sel | in_a.
  Definition bc_inputs_size (x: bc_inputs) : nat :=
    match x with in_sel => 16 | in_a => cw end.
  Definition bc_in_class (_: bc_inputs) : port_class := Public.

  (* sel = 0 -> ask the IP about  in_a
     sel = 1 -> ask the IP about ~in_a *)
  Definition bc_ops : @tf_ops bc_states bc_inputs Empty_set cs_ips :=
    tf_ops_if (tf_op2 (tf_cmp 16 tf_eq) (tf_ivar in_sel) (tf_const 0))
      (tf_ops_base (tf_call cs_crypto st_out (tf_ivar in_a)))
      (tf_ops_base (tf_call cs_crypto st_out (tf_op1 tf_not (tf_ivar in_a)))).

  Definition bc_ctx : TFSchedContext := {|
      tfs_spec_states := bc_states;   tfs_spec_states_fin := _;
      tfs_spec_states_size := bc_states_size;
      tfs_spec_states_init := bc_states_init;
      tfs_spec_inputs := bc_inputs;   tfs_spec_inputs_fin := _;
      tfs_spec_inputs_size := bc_inputs_size;
      tfs_spec_inputs_class := bc_in_class;
      tfs_spec_outputs := Empty_set;  tfs_spec_outputs_fin := _;
      tfs_spec_outputs_size := fun _ => cw;
      tfs_spec_outputs_class := fun _ => Secret;
      tfs_spec_action := cs_action;   tfs_spec_action_fin := _;
      tfs_spec_action_ops := fun _ => bc_ops;
      tfs_spec_ips := cs_ips;         tfs_spec_ips_fin := _;
      tfs_spec_ip := cs_ip;
      tfs_spec_decls := []
  |}.

  Definition bc_dfg := build_dfg bc_ctx act_call.

  (* BOTH branches emit a drive. *)
  Example branch_two_drives :
    List.length (drive_nodes bc_ctx bc_dfg cs_crypto) = 2.
  Proof. vm_compute. reflexivity. Qed.

End BranchCall.

Section BranchCallSynthesis.

  Definition bc_schedule := tfs_schedule bc_ctx cclimit.

  Definition bc_tf_ctx : TFSynthContext := {|
    tf_sched_ctx := bc_schedule;
    tf_action_encoding := cs_action_encoding;
    tf_action_encoding_inj := cs_action_encoding_inj;
  |}.
  Instance bc_ext_fn_names : Show _ := TypedSynthesis.ext_fn_names bc_tf_ctx.


  Definition bc_package :=
    {| ip_koika := {| koika_reg_types := TypedSynthesis.R bc_tf_ctx;
                      koika_reg_names := TypedSynthesis.reg_names bc_tf_ctx;
                      koika_reg_init := TypedSynthesis.r bc_tf_ctx;
                      koika_reg_finite := TypedSynthesis._reg_t_finite bc_tf_ctx;
                      koika_ext_fn_types := TypedSynthesis.Sigma bc_tf_ctx;
                      koika_rules := TypedSynthesis.rules bc_tf_ctx;
                      koika_rule_names := TypedSynthesis.rule_names bc_tf_ctx;
                      koika_rule_external := (fun _ => false);
                      koika_scheduler := TypedSynthesis.system_schedule bc_tf_ctx;
                      koika_module_name := "Example_BranchCallSpike" |};
    ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn; efs_method := false |};
                sp_prelude := None |};
    ip_verilog := {| vp_ext_fn_specs := TypedSynthesis.ext_fn_specs bc_tf_ctx |} |}.

End BranchCallSynthesis.

Definition bc_prog := Interop.Backends.register bc_package.
Extraction "Example_BranchCallSpike.ml" bc_prog.


(* ===================================================================== *)
(*  A branch on a CALL RESULT.                                           *)
(* ===================================================================== *)
(*
    The [if] tests a previous call's answer, so the guard reaches through a
    [DFG_Sample] -- the one source not stable across the action, which is why a
    guard must read its latch rather than the live wire.
*)

Section GuardOnResult.

  (* st_a := ip(in_msg);  if st_a = 0 then st_b := ip(7) else st_b := ip(9) *)
  Definition gr_ops : @tf_ops tc_states cs_inputs cs_outputs cs_ips :=
    tf_ops_cons
      (tf_ops_base (tf_call cs_crypto st_a (tf_ivar in_msg)))
      (tf_ops_if (tf_op2 (tf_cmp cw tf_eq) (tf_svar st_a) (tf_const 0))
        (tf_ops_base (tf_call cs_crypto st_b (tf_const 7)))
        (tf_ops_base (tf_call cs_crypto st_b (tf_const 9)))).

  Definition gr_ctx : TFSchedContext := {|
      tfs_spec_states := tc_states;   tfs_spec_states_fin := _;
      tfs_spec_states_size := tc_states_size;
      tfs_spec_states_init := tc_states_init;
      tfs_spec_inputs := cs_inputs;   tfs_spec_inputs_fin := _;
      tfs_spec_inputs_size := cs_inputs_size;
      tfs_spec_inputs_class := cs_in_class;
      tfs_spec_outputs := cs_outputs; tfs_spec_outputs_fin := _;
      tfs_spec_outputs_size := cs_outputs_size;
      tfs_spec_outputs_class := cs_out_class;
      tfs_spec_action := cs_action;   tfs_spec_action_fin := _;
      tfs_spec_action_ops := fun _ => gr_ops;
      tfs_spec_ips := cs_ips;         tfs_spec_ips_fin := _;
      tfs_spec_ip := cs_ip;
      tfs_spec_decls := []
  |}.

  Definition gr_dfg := build_dfg gr_ctx act_call.

  (* one for the first call, one per arm *)
  Example guard_three_drives :
    List.length (drive_nodes gr_ctx gr_dfg cs_crypto) = 3.
  Proof. vm_compute. reflexivity. Qed.

End GuardOnResult.

Section GuardOnResultSynthesis.

  Definition gr_schedule := tfs_schedule gr_ctx cclimit.

  Definition gr_tf_ctx : TFSynthContext := {|
    tf_sched_ctx := gr_schedule;
    tf_action_encoding := cs_action_encoding;
    tf_action_encoding_inj := cs_action_encoding_inj;
  |}.
  Instance gr_ext_fn_names : Show _ := TypedSynthesis.ext_fn_names gr_tf_ctx.

  Definition gr_package :=
    {| ip_koika := {| koika_reg_types := TypedSynthesis.R gr_tf_ctx;
                      koika_reg_names := TypedSynthesis.reg_names gr_tf_ctx;
                      koika_reg_init := TypedSynthesis.r gr_tf_ctx;
                      koika_reg_finite := TypedSynthesis._reg_t_finite gr_tf_ctx;
                      koika_ext_fn_types := TypedSynthesis.Sigma gr_tf_ctx;
                      koika_rules := TypedSynthesis.rules gr_tf_ctx;
                      koika_rule_names := TypedSynthesis.rule_names gr_tf_ctx;
                      koika_rule_external := (fun _ => false);
                      koika_scheduler := TypedSynthesis.system_schedule gr_tf_ctx;
                      koika_module_name := "Example_GuardCallSpike" |};
    ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn; efs_method := false |};
                sp_prelude := None |};
    ip_verilog := {| vp_ext_fn_specs := TypedSynthesis.ext_fn_specs gr_tf_ctx |} |}.

End GuardOnResultSynthesis.

Definition gr_prog := Interop.Backends.register gr_package.
Extraction "Example_GuardCallSpike.ml" gr_prog.
