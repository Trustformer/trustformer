Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.DFG.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.

Require Import Coq.Lists.List.
Import ListNotations.

(* A [DFG_Stall]'s latency PINS a producer earlier than its consumer, and this
   measures the gap and what the hold costs.  The graphs are hand-built, which
   [calc_backward_cost], [calc_target_cycle] and [require_buffer] accept
   directly -- they take a [dfg_state] rather than an action. *)

Section Spike.

  Definition w := 256.

  Inductive sl_action  := act_dummy.
  Inductive sl_states  := st_acc.
  Inductive sl_inputs  := in_x.
  Inductive sl_outputs := out_o.

  Definition sl_states_size  (_: sl_states)  : nat := w.
  Definition sl_inputs_size  (_: sl_inputs)  : nat := w.
  Definition sl_outputs_size (_: sl_outputs) : nat := w.

  Definition sl_states_init (x: sl_states) : tf_states_type sl_states_size x :=
    match x with st_acc => Bits.zero end.

  Inductive sl_ips := sl_ip_crypto.
  Definition sl_ip (_: sl_ips) : ip_decl :=
    {| ip_req_sz := w; ip_resp_sz := w; ip_lat := 0; ip_fn := fun v => v |}.

  Definition sl_ctx : TFSchedContext := {|
      tfs_spec_states := sl_states;   tfs_spec_states_fin := _;
      tfs_spec_states_size := sl_states_size;
      tfs_spec_states_init := sl_states_init;

      tfs_spec_inputs := sl_inputs;   tfs_spec_inputs_fin := _;
      tfs_spec_inputs_size := sl_inputs_size;
      tfs_spec_inputs_class := fun _ => Secret;

      tfs_spec_outputs := sl_outputs; tfs_spec_outputs_fin := _;
      tfs_spec_outputs_size := sl_outputs_size;
      tfs_spec_outputs_class := fun _ => Public;

      tfs_spec_action := sl_action;   tfs_spec_action_fin := _;
      tfs_spec_action_ops := fun _ => tf_ops_base tf_nop;
      tfs_spec_ips := sl_ips;   tfs_spec_ips_fin := _;
      tfs_spec_ip := sl_ip;

      tfs_spec_decls := []
  |}.

  Definition climit := 5.

  (* in_x ---> stall<L> ---> not
     The consumer is a [tf_not]; the stall sits on the edge between the value
     and its use, which is where a crypto round trip would sit. *)
  Definition hold (L: nat) : dfg_state_t (states_var := sl_states)
                                         (inputs_var := sl_inputs)
                                         (outputs_var := sl_outputs)
                                         (ips_var := sl_ips) := {|
    graph :=
      [ {| nid := 0; op := DFG_Empty;        sz := 0 |}
      ; {| nid := 1; op := DFG_Input in_x;   sz := w |}
      ; {| nid := 2; op := DFG_Stall L 1;    sz := w |}
      ; {| nid := 3; op := DFG_Unary tf_not 2; sz := w |}
      ];
    var_map := [ (DFG_SVar st_acc, 3) ]
  |}.

  Definition hold_cycles (L: nat) :=
    calc_target_cycle climit (calc_backward_cost sl_ctx climit (hold L)).

  Definition cyc (L: nat) (n: nid_t) : nat :=
    match BitsToLists.list_assoc (hold_cycles L) n with
    | Some c => c | None => 999 end.

  Definition hold_bufs (L: nat) : nat :=
    List.length (require_buffer sl_ctx (hold L) (hold_cycles L)).

  (* ================================================================== *)
  (* M1.  A PRODUCER CAN NOW BE PINNED ARBITRARILY EARLY.               *)
  (* ================================================================== *)

  (* The consumer stays at the end of the axis and the producer moves [L / climit]
     cycles away.  [bc_aux] gives a node and its arguments the same running max,
     so the gap comes from the NODE's own [cost_fn] ([backward_cost_arg_self]):
     the stall shares a cycle with its argument and the CONSUMER moves later.
     That is the round trip's shape -- drive and stall together, sample later. *)

  Example consumer_at_end_5  : cyc 5  3 = 0.  Proof. vm_compute. reflexivity. Qed.
  Example producer_pinned_5  : cyc 5  2 = 5.  Proof. vm_compute. reflexivity. Qed.
  Example producer_pinned_20 : cyc 20 2 = 20.  Proof. vm_compute. reflexivity. Qed.
  Example producer_pinned_80 : cyc 80 2 = 80. Proof. vm_compute. reflexivity. Qed.

  (* The argument rides with the stall rather than being separated from it. *)
  Example arg_rides_with_stall : cyc 80 1 = cyc 80 2.
  Proof. vm_compute. reflexivity. Qed.

  (* ================================================================== *)
  (* M2.  THE HOLD COSTS ONE BUFFER, AT EVERY LATENCY.                  *)
  (* ================================================================== *)

  (* [require_buffer] [nodup]s the arguments whose cycle differs from their
     consumer's, so a value held across sixteen cycles costs exactly one nid,
     the same as one held across a single cycle.  Against [chain_bufs 16 = 16]
     in StallCostSpike.v, both at 256 bits: the archive's (L+2) x width was the
     delay CHAIN, and a single node carries none of it. *)

  Example hold_one_buffer_5  : hold_bufs 5  = 1. Proof. vm_compute. reflexivity. Qed.
  Example hold_one_buffer_20 : hold_bufs 20 = 1. Proof. vm_compute. reflexivity. Qed.
  Example hold_one_buffer_80 : hold_bufs 80 = 1. Proof. vm_compute. reflexivity. Qed.

End Spike.

(* The round trip: [DFG_Drive] makes a port write a node and [DFG_Sample] makes
   a response read one, so the two are ordered by an edge.  PortDriveSpike.v
   measures what happens without them. *)

Section RoundTrip.

  (* in_x -> drive[out_o] -> stall<L> -> sample[in_resp] -> not
     The token edge runs drive -> stall -> sample; the sample's VALUE is the
     port, its VALIDITY is the token's. *)
  Definition trip (L: nat) : dfg_state_t (states_var := sl_states)
                                         (inputs_var := sl_inputs)
                                         (outputs_var := sl_outputs)
                                         (ips_var := sl_ips) := {|
    graph :=
      [ {| nid := 0; op := DFG_Empty;            sz := 0 |}
      ; {| nid := 1; op := DFG_Input in_x;       sz := w |}
      ; {| nid := 2; op := DFG_Drive sl_ip_crypto 1 []; sz := w |}
      ; {| nid := 3; op := DFG_Stall L 2;        sz := w |}
      ; {| nid := 4; op := DFG_Sample sl_ip_crypto 3 []; sz := w |}
      ; {| nid := 5; op := DFG_Unary tf_not 4;   sz := w |}
      ];
    var_map := [ (DFG_SVar st_acc, 5) ]
  |}.

  Definition trip_cycles (L: nat) :=
    calc_target_cycle climit (calc_backward_cost sl_ctx climit (trip L)).

  Definition tcyc (L: nat) (n: nid_t) : nat :=
    match BitsToLists.list_assoc (trip_cycles L) n with
    | Some c => c | None => 999 end.

  Definition trip_bufs (L: nat) : nat :=
    List.length (require_buffer sl_ctx (trip L) (trip_cycles L)).

  (* ================================================================== *)
  (* THE REQUEST IS NOW ORDERED BEFORE THE RESPONSE.                    *)
  (* ================================================================== *)

  (* 1.6, for comparison: with the answer feeding real work, the trusted-input
     read was scheduled in the SAME cycle as the request's own operand
     (PortDriveSpike.v, [resp_used_same_cycle_as_request]).  There was no edge
     to order them.  Now there is one, and the separation is the declared
     latency: drive at 20, sample at 0, i.e. exactly L cycles apart. *)

  Example drive_is_early : tcyc 20 2 = 20.
  Proof. vm_compute. reflexivity. Qed.

  Example sample_is_late : tcyc 20 4 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (* Stated as the separation, so it does not depend on which way the axis
     runs: the drive and the sample are L/climit cycles apart, and 1.6's
     measurement was that the same two things were 0 cycles apart. *)
  Example round_trip_separated : tcyc 20 2 - tcyc 20 4 = 20.
  Proof. vm_compute. reflexivity. Qed.

  (* The wait costs two registers whatever L is: the stall's counter, and the
     latched answer.  A sample is buffered wherever the schedule puts it, since
     the port carries its answer only until the next call on that port. *)
  Example round_trip_two_buffers : trip_bufs 20 = 2.
  Proof. vm_compute. reflexivity. Qed.

  (* And the sample is one of the two, at the cycle it is sampled. *)
  Example round_trip_sample_buffered :
    List.In 4 (require_buffer sl_ctx (trip 20) (trip_cycles 20)).
  Proof. vm_compute. tauto. Qed.

  (* ================================================================== *)
  (* A SAMPLE IS NOT A SOURCE OP                                        *)
  (* ================================================================== *)

  (* [require_buffer] leaves a [source_op] unbuffered because inputs are latched
     at action start -- true of a host input, false of a crypto result.  A
     [DFG_Sample] is buffered and has a defined sampling cycle; a plain
     [DFG_Input] stays a source, which is right for a host input. *)

  (* ================================================================== *)
  (* NO OFF-BY-ONE, AT ANY REMAINDER.                                   *)
  (* ================================================================== *)

  (* Cycles come from [calc_target_cycle], an integer DIVISION by [climit], and
     the gap is EXACT because [cost_fn] contributes a whole multiple of it:
     [(c + L*climit) / climit = c/climit + L] for every [c].  That is why the
     latency is declared in CYCLES.  [trip_pad L m] runs the sample's remainder
     through every residue mod [climit] = 5 as [m] goes 0..5. *)

  Fixpoint not_chain (base m: nat)
    : list (@dfg_node_t sl_states sl_inputs sl_outputs sl_ips) :=
    match m with
    | 0 => []
    | S m' => {| nid := base; op := DFG_Unary tf_not (base - 1); sz := w |}
                :: not_chain (S base) m'
    end.

  Definition trip_pad (L m: nat) : dfg_state_t (states_var := sl_states)
                                               (inputs_var := sl_inputs)
                                               (outputs_var := sl_outputs)
                                         (ips_var := sl_ips) := {|
    graph :=
      [ {| nid := 0; op := DFG_Empty;            sz := 0 |}
      ; {| nid := 1; op := DFG_Input in_x;       sz := w |}
      ; {| nid := 2; op := DFG_Drive sl_ip_crypto 1 []; sz := w |}
      ; {| nid := 3; op := DFG_Stall L 2;        sz := w |}
      ; {| nid := 4; op := DFG_Sample sl_ip_crypto 3 []; sz := w |}
      ] ++ not_chain 5 m;
    var_map := [ (DFG_SVar st_acc, 4 + m) ]
  |}.

  Definition pcyc (L m n: nat) : nat :=
    match BitsToLists.list_assoc
            (calc_target_cycle climit (calc_backward_cost sl_ctx climit (trip_pad L m))) n with
    | Some c => c | None => 999 end.

  (* separation = drive cycle - sample cycle, which must be exactly L *)
  Definition psep (L m: nat) : nat := pcyc L m 2 - pcyc L m 4.

  (* every residue of the downstream cost mod climit=5 *)
  Example sep_pad_r0 : psep 7 0 = 7. Proof. vm_compute. reflexivity. Qed.
  Example sep_pad_r1 : psep 7 1 = 7. Proof. vm_compute. reflexivity. Qed.
  Example sep_pad_r2 : psep 7 2 = 7. Proof. vm_compute. reflexivity. Qed.
  Example sep_pad_r3 : psep 7 3 = 7. Proof. vm_compute. reflexivity. Qed.
  Example sep_pad_r4 : psep 7 4 = 7. Proof. vm_compute. reflexivity. Qed.
  Example sep_pad_r5 : psep 7 5 = 7. Proof. vm_compute. reflexivity. Qed.

  (* and at latencies that straddle climit, including the ones a cost-unit
     declaration would have rounded away to zero *)
  Example sep_lat_1 : psep 1 3 = 1. Proof. vm_compute. reflexivity. Qed.
  Example sep_lat_2 : psep 2 3 = 2. Proof. vm_compute. reflexivity. Qed.
  Example sep_lat_4 : psep 4 3 = 4. Proof. vm_compute. reflexivity. Qed.
  Example sep_lat_5 : psep 5 3 = 5. Proof. vm_compute. reflexivity. Qed.
  Example sep_lat_6 : psep 6 3 = 6. Proof. vm_compute. reflexivity. Qed.

  (* a zero-latency (combinational) IP puts the sample in the request's cycle;
     kept as a regression because [tfs_spec_ip_lat] DEFAULTS to 0, so a call
     whose response port was never declared silently gets this shape *)
  Example sep_lat_0 : psep 0 3 = 0. Proof. vm_compute. reflexivity. Qed.

  (* ================================================================== *)
  (* THE TOKEN WAITS FOR ITS ARGUMENT AT EVERY LATENCY.                 *)
  (* ================================================================== *)

  (* [counter_sz 1 = 1] and [pred 1 = 0], so a latency-1 counter starts at the
     value it saturates at.  Its validity therefore has to AND the gate in:
     reading the count alone would let the token validate at cycle 1 whatever
     the argument did.  Latency 2 and up are gated by the count itself. *)
  Example lat_1_starts_saturated : Init.Nat.pred 1 = 0 /\ counter_sz 1 = 1.
  Proof. vm_compute. split; reflexivity. Qed.

  Example lat_2_counts_one_step : Init.Nat.pred 2 = 1.
  Proof. vm_compute. reflexivity. Qed.

  Example sample_is_not_a_source : is_source sl_ctx (trip 20) 4 = false.
  Proof. vm_compute. reflexivity. Qed.

  Example plain_input_still_is : is_source sl_ctx (trip 20) 1 = true.
  Proof. vm_compute. reflexivity. Qed.

End RoundTrip.
