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
