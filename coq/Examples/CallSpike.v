(* ===================================================================== *)
(*  SPIKE: a call, through build_dfg, measured.                          *)
(* ===================================================================== *)
(*
    The first action in the tree that actually CONTAINS a [tf_call].  Every
    earlier measurement hand-built its graph, so nothing exercised the real
    lowering: "all 11 designs byte-identical" proved the new node kinds were
    inert and nothing more.

    What is measured here:

      1. a call emits a DRIVE, so its request port is in [driven_ports] and is
         therefore written by an ALWAYS-op rather than by a done-op;
      2. the request port is NOT in [var_map] -- it left the done half
         entirely, which is what [driven_port_not_assigned] needs;
      3. the delay chain buys REAL cycles: the sample is scheduled [lat] cycles
         after the drive, and costs [lat] buffers of one bit rather than one
         buffer at the payload width.

    (3) is the one that was missing.  A lone [DFG_Stall lat] compiles to its
    argument verbatim, so it never delayed anything -- it only declared a cost.
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
  Inductive cs_inputs  := in_msg | in_resp.
  Inductive cs_outputs := out_req.

  Definition cs_states_size  (_: cs_states)  : nat := cw.
  Definition cs_inputs_size  (_: cs_inputs)  : nat := cw.
  Definition cs_outputs_size (_: cs_outputs) : nat := cw.

  Definition cs_states_init (x: cs_states) : tf_states_type cs_states_size x :=
    match x with st_res => Bits.zero end.

  (* The IP's declared behaviour.  Inert here -- nothing in the lowering reads
     it, because the circuit samples the wire.  It is the spec's claim about
     what the attached chip computes. *)
  Definition cs_f (v: bits_t cw) : bits_t cw := v.

  (* Both ends of the IP link are Secret, which [tfs_spec_ip_secret] requires
     and which [driven_ports] independently filters on. *)
  Definition cs_in_class (i: cs_inputs) : port_class :=
    match i with in_msg => Public | in_resp => Secret end.
  Definition cs_out_class (_: cs_outputs) : port_class := Secret.

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
      (* THE CALL: drive [in_msg] onto out_req, wait clat cycles, read in_resp
         into st_res. *)
      tfs_spec_action_ops := fun _ =>
        tf_ops_base (tf_call out_req in_resp st_res (tf_ivar in_msg) cs_f);

      tfs_spec_ip_req := fun i => match i with in_resp => Some out_req | _ => None end;
      tfs_spec_ip_lat := fun i => match i with in_resp => clat | _ => 0 end;
      tfs_spec_ip_secret := ltac:(intros i o H; destruct i; cbn in H;
                                  [ discriminate | destruct o; split; reflexivity ]);
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
  Example req_is_driven : driven_ports cs_ctx cs_dfg = [out_req].
  Proof. vm_compute. reflexivity. Qed.

  (* ...and it is NOT in var_map, so no done-op writes it.  Before the drive
     landed this was exactly backwards: the port was in var_map and nowhere
     else. *)
  Example req_not_assigned : assigned_port cs_ctx cs_dfg out_req = false.
  Proof. vm_compute. reflexivity. Qed.

  (* exactly one drive for the one call *)
  Example one_drive : List.length (drive_nodes cs_ctx cs_dfg out_req) = 1.
  Proof. vm_compute. reflexivity. Qed.

  (* ================================================================== *)
  (* 2.  THE WAIT IS REAL.                                              *)
  (* ================================================================== *)

  (* [clat] chained unit stalls, so [clat] nodes each land in their own cycle
     bucket and each takes a buffer.  A buffer's valid bit is assigned from its
     input's validity once per cycle, so validity lags one cycle per hop.

     A lone [DFG_Stall clat] would give ONE buffer and no lag at all: it
     compiles to its argument verbatim. *)
  Definition cs_bufs := require_buffer cs_ctx cs_dfg cs_cycles.

  Example chain_buys_buffers : List.length cs_bufs = clat.
  Proof. vm_compute. reflexivity. Qed.

  (* The drive and the sample are clat cycles apart.  Cycles count BACKWARD
     from done, so the drive has the larger number. *)
  Definition drive_nid := List.hd 0 (drive_nodes cs_ctx cs_dfg out_req).
  Definition samp_nid :=
    List.fold_left (fun acc nd => match op nd with
                                  | DFG_Sample _ _ => nid nd
                                  | _ => acc end) (graph cs_dfg) 0.

  Example round_trip_separated : ccyc drive_nid - ccyc samp_nid = clat.
  Proof. vm_compute. reflexivity. Qed.

  (* The chain is WIDTH 1, which is the entire cost argument for preferring it
     to a counter: the archive's delay chain was rejected for being [lat] nodes
     at the PAYLOAD width, and this is [lat] nodes at one bit. *)
  Example chain_is_one_bit :
    forallb (fun nd => match op nd with
                       | DFG_Stall _ _ => Nat.eqb (sz nd) 1
                       | _ => true end)
            (graph cs_dfg) = true.
  Proof. vm_compute. reflexivity. Qed.

  (* and the sample is not a source, so it has a defined sampling cycle *)
  Example sample_not_source : is_source cs_ctx cs_dfg samp_nid = false.
  Proof. vm_compute. reflexivity. Qed.

End CallSpike.

(* ===================================================================== *)
(*  End-to-end: through TypedSynthesis and out to Verilog.               *)
(* ===================================================================== *)
(*
    The point of extracting this one is to READ THE GENERATED HARDWARE.  Every
    claim about the drive so far is Coq-level, and this project's record is that
    both of the archive's design bugs were timing bugs invisible in Coq.

    What to look for in build/Example_CallSpike.v:

      - out_req is assigned from ALWAYS logic, not only under the done gate;
      - its else-branch reads the port's own previous value, i.e. it HOLDS;
      - it has exactly one driver (scripts/check-drivers.sh);
      - in_resp is read LIVE, not out of the action-start input latch.
*)

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
  Definition tc_ops : @tf_ops tc_states cs_inputs cs_outputs :=
    tf_ops_cons
      (tf_ops_base (tf_call out_req in_resp st_a (tf_ivar in_msg) cs_f))
      (tf_ops_base (tf_call out_req in_resp st_b
                      (tf_op1 tf_not (tf_ivar in_msg)) cs_f)).

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
      tfs_spec_ip_req := fun i => match i with in_resp => Some out_req | _ => None end;
      tfs_spec_ip_lat := fun i => match i with in_resp => clat | _ => 0 end;
      tfs_spec_ip_secret := ltac:(intros i o H; destruct i; cbn in H;
                                  [ discriminate | destruct o; split; reflexivity ]);
      tfs_spec_decls := []
  |}.

  Definition tc_dfg := build_dfg tc_ctx act_call.
  Definition tc_cycles :=
    calc_target_cycle cclimit (calc_backward_cost tc_ctx cclimit tc_dfg).
  Definition tcyc2 (n: nid_t) : nat :=
    match BitsToLists.list_assoc tc_cycles n with Some c => c | None => 999 end.

  (* BOTH calls drive the same port, so there are two drive nodes ... *)
  Definition tc_drives := drive_nodes tc_ctx tc_dfg out_req.
  Example two_drives : List.length tc_drives = 2.
  Proof. vm_compute. reflexivity. Qed.

  (* ... but the port appears ONCE in driven_ports, so ONE tf_output op is
     emitted for it, folding both drives into one nested conditional. *)
  Example one_driven_port : driven_ports tc_ctx tc_dfg = [out_req].
  Proof. vm_compute. reflexivity. Qed.

  (* Are the two drives in the SAME cycle?  If so they collide: the fold puts
     the latest outermost, so the earlier request never reaches the wire. *)
  Definition tc_d1 := List.nth 0 tc_drives 999.
  Definition tc_d2 := List.nth 1 tc_drives 999.

  Definition tc_samples :=
    List.fold_left (fun acc nd => match op nd with
                                  | DFG_Sample _ _ => nid nd :: acc
                                  | _ => acc end) (graph tc_dfg) [].

End TwoCalls.

(* The complement: call 2s argument READS call 1s result, so there is a data
   dependency between them.  Does the scheduler sequence them? *)
Section TwoCallsChained.

  Definition tc2_ops : @tf_ops tc_states cs_inputs cs_outputs :=
    tf_ops_cons
      (tf_ops_base (tf_call out_req in_resp st_a (tf_ivar in_msg) cs_f))
      (tf_ops_base (tf_call out_req in_resp st_b (tf_svar st_a) cs_f)).

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
       tfs_spec_ip_req := fun i => match i with in_resp => Some out_req | _ => None end;
       tfs_spec_ip_lat := fun i => match i with in_resp => clat | _ => 0 end;
       tfs_spec_ip_secret := ltac:(intros i o H; destruct i; cbn in H;
                                   [ discriminate | destruct o; split; reflexivity ]);
       tfs_spec_decls := [] |}.

  Definition tc2_dfg := build_dfg tc2_ctx act_call.
  Definition tc2_cycles :=
    calc_target_cycle cclimit (calc_backward_cost tc2_ctx cclimit tc2_dfg).
  Definition tcyc3 (n: nid_t) : nat :=
    match BitsToLists.list_assoc tc2_cycles n with Some c => c | None => 999 end.
  Definition tc2_drives := drive_nodes tc2_ctx tc2_dfg out_req.
  Definition tc2_samples :=
    List.fold_left (fun acc nd => match op nd with
                                  | DFG_Sample _ _ => nid nd :: acc
                                  | _ => acc end) (graph tc2_dfg) [].

End TwoCallsChained.

(* ================================================================== *)
(* TWO CALLS ON ONE IP: BROKEN WHEN INDEPENDENT, CORRECT WHEN CHAINED *)
(* ================================================================== *)

(* INDEPENDENT calls now SEQUENCE, exactly as chained ones always did.

   There is one set of request wires, so two calls physically must take turns.
   Before the ordering join both drives landed in the SAME cycle: the fold kept
   only the latest, the earlier request never reached the IP, and both samples
   read the same wire -- so both destinations got the answer to the later
   request. One request sent, two identical results, no diagnostic.

   The join makes the second call's delay chain depend on the first call's
   sample, so the second drive lands in the first sample's cycle, lat after the
   first drive. *)
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
(*
    tc_ctx's action contains two calls on the same req/resp pair with
    INDEPENDENT arguments -- the case that silently collided before the
    ordering join.  What to look for in build/Example_TwoCallSpike.v:

      - TWO strobe pulses on ip_out_..._out_req_arg's top bit, lat apart;
      - the payload changing between them and HELD in between;
      - a single driver.
*)

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
