Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.DFG.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.

Require Import Coq.Lists.List.
Import ListNotations.

(*
    SPIKE 1.6 (agents/one-action, 2026-09-10): can one action drive a port
    twice, and can anything order a request before its response?

    MARS_Quote is three round trips, two of them back-to-back on the SAME port
    group (Examples/Mars.v:775).  "One command = one action" therefore needs an
    action to drive one port with two different values at two different cycles
    and to read the two answers back in order.  Spike 1.5 settled where the
    answer's VALUE comes from; this file asks whether the request side can be
    expressed at all.

    Three measurements, all with machinery that exists today, so no proof risk.
    All three are negative, and the third is the one that decides the shape of
    Spike 2.

    A note on the cycle axis, because it is counter-intuitive and the numbers
    below are unreadable without it.  [calc_backward_cost] accumulates work
    BACKWARDS from the roots, and [calc_target_cycle] divides by the cost limit,
    so a node's number is the work REMAINING between it and the end of the
    action: bigger means EARLIER.  In act_reqresp below the input in_x is 4 and
    the final multiply that consumes it is 1, which is only consistent that way
    round -- a consumer cannot be ready before its producer.  (The comment at
    SchedulerSimulation.v:630 reads "the earliest cycle its value is available",
    which is loose about the direction while being right that the action is done
    at the MAX.)  Every claim below is stated so that it does not depend on
    which way the axis runs.
 *)

Section Spike.

  Definition w := 32.

  Inductive pd_action  := act_twice | act_reqresp | act_resp_used.
  Inductive pd_states  := st_acc.
  Inductive pd_inputs  := in_x | in_y | in_resp.
  Inductive pd_outputs := out_req.

  Definition pd_states_size  (_: pd_states)  : nat := w.
  Definition pd_inputs_size  (_: pd_inputs)  : nat := w.
  Definition pd_outputs_size (_: pd_outputs) : nat := w.

  Definition pd_states_init (x: pd_states) : tf_states_type pd_states_size x :=
    match x with st_acc => Bits.zero end.

  (* tf_mul costs 5 and the cost limit below is 5, so each multiply is a cycle
     of its own and [work k] is a k-cycle computation. *)
  Fixpoint work (k: nat) (e: @tf_expr pd_states pd_inputs pd_outputs)
    : @tf_expr pd_states pd_inputs pd_outputs :=
    match k with
    | 0 => e
    | S k' => tf_op2 tf_mul (work k' e) (tf_const 1)
    end.

  (* TWO DRIVES OF ONE PORT -- what a second crypto request inside one action
     looks like: message A on the port, then later message B. *)
  Definition ops_twice : @tf_ops pd_states pd_inputs pd_outputs :=
    tf_ops_cons
      (tf_ops_base (tf_output out_req (tf_ivar in_x)))
      (tf_ops_base (tf_output out_req (tf_ivar in_y))).

  (* REQUEST THEN RESPONSE -- build a message over four cycles, drive it, read
     the answer back.  Nothing in the DSL says the read follows the write. *)
  Definition ops_reqresp : @tf_ops pd_states pd_inputs pd_outputs :=
    tf_ops_cons
      (tf_ops_base (tf_output out_req (work 4 (tf_ivar in_x))))
      (tf_ops_base (tf_assign st_acc (tf_ivar in_resp))).

  (* THE SAME, BUT THE ANSWER IS USED.  In act_reqresp the answer lands straight
     in a register, so backward costing happens to put it at the far end and the
     schedule looks accidentally plausible.  Give the answer some work to feed
     and the accident disappears. *)
  Definition ops_resp_used : @tf_ops pd_states pd_inputs pd_outputs :=
    tf_ops_cons
      (tf_ops_base (tf_output out_req (work 4 (tf_ivar in_x))))
      (tf_ops_base (tf_assign st_acc (work 4 (tf_ivar in_resp)))).

  Definition pd_ctx : TFSchedContext := {|
      tfs_spec_states := pd_states;   tfs_spec_states_fin := _;
      tfs_spec_states_size := pd_states_size;
      tfs_spec_states_init := pd_states_init;

      tfs_spec_inputs := pd_inputs;   tfs_spec_inputs_fin := _;
      tfs_spec_inputs_size := pd_inputs_size;
      tfs_spec_inputs_class := fun _ => Secret;

      tfs_spec_outputs := pd_outputs; tfs_spec_outputs_fin := _;
      tfs_spec_outputs_size := pd_outputs_size;
      tfs_spec_outputs_class := fun _ => Secret;

      tfs_spec_action := pd_action;   tfs_spec_action_fin := _;
      tfs_spec_action_ops := fun a =>
        match a with
        | act_twice     => ops_twice
        | act_reqresp   => ops_reqresp
        | act_resp_used => ops_resp_used
        end;
      (* no attached IP: no call names a response port here *)
      tfs_spec_ip_req := fun _ => None;
      tfs_spec_ip_lat := fun _ => 0;
      tfs_spec_ip_secret := ltac:(intros ? ? H; cbn in H; discriminate);
      tfs_spec_decls := []
  |}.

  Definition climit := 5.

  Definition cyc (a: pd_action) (n: nid_t) : nat :=
    match BitsToLists.list_assoc
            (calc_target_cycle climit (calc_backward_cost pd_ctx climit (build_dfg pd_ctx a))) n with
    | Some c => c
    | None => 999
    end.

  (* ================================================================== *)
  (* M1.  THE SECOND DRIVE ERASES THE FIRST.                            *)
  (* ================================================================== *)

  (* [tf_output dst e] is [set_var (DFG_OVar dst) res_id] (VariableScheduler.v
     :279) and [var_map] holds ONE nid per variable.  Two writes to out_req
     therefore leave one entry, naming the SECOND value. *)

  Example twice_one_entry :
    List.length (var_map (build_dfg pd_ctx act_twice)) = 1.
  Proof. vm_compute. reflexivity. Qed.

  (* nid 2 is [DFG_Input in_y] -- the second write.  nid 1, [DFG_Input in_x],
     is the first, and it is gone from the map. *)
  Example twice_second_wins :
    map snd (var_map (build_dfg pd_ctx act_twice)) = [2].
  Proof. vm_compute. reflexivity. Qed.

  (* ...but the first value is still BUILT: three nodes (Empty, in_x, in_y).
     So the first message's logic is emitted and then driven nowhere.  Dead
     silicon, not a diagnostic. *)
  Example twice_first_is_dead_logic :
    List.length (graph (build_dfg pd_ctx act_twice)) = 3.
  Proof. vm_compute. reflexivity. Qed.

  (* ================================================================== *)
  (* M2.  A PORT IS DRIVEN ONLY AT THE DONE CYCLE.                      *)
  (* ================================================================== *)

  (* [schedule] returns (always_ops, done_ops); [compile_dfg_aux] (:1070) turns
     var_map into the tf_output/tf_assign writes and [schedule] (:1100) puts
     them in the DONE half, which tfs_next_cycle applies only when done fires
     (Contract.v:247).  So the port carries its value for the last cycle of the
     action and no earlier -- there is no cycle at which an IP could see a
     request AND the action still be running to receive the answer. *)

  Definition count_outputs {s i o} (ops: list (@tf_op s i o)) : nat :=
    List.length (filter (fun op => match op with
                                   | tf_output _ _ => true
                                   | _ => false end) ops).

  Example port_never_driven_early :
    count_outputs (fst (VariableScheduler.schedule pd_ctx climit act_twice)) = 0.
  Proof. vm_compute. reflexivity. Qed.

  Example port_driven_at_done :
    count_outputs (snd (VariableScheduler.schedule pd_ctx climit act_twice)) = 1.
  Proof. vm_compute. reflexivity. Qed.

  (* CONFIRMED IN THE GENERATED VERILOG, not only in Coq -- this is a hardware
     timing claim, and INSIGHTS says both design bugs the archived campaign
     found were timing bugs invisible in Coq.  In build/Example_Mars.v the port
     register updates as

       out_out_sha_msg <= _rule_cmd_act_init_out12

     whose Quote arm is gated by [_107 = _wF_rule_cmd_act_quote0 && _28], and
     [_28] -- a conjunction of the action's validity bits -- is the SAME wire
     that raises [st_done] (line 710).  The port changes on the done cycle and
     on no other. *)

  (* ================================================================== *)
  (* M3.  NOTHING ORDERS THE RESPONSE AFTER THE REQUEST.                *)
  (* ================================================================== *)

  (* A port write is not a DFG node -- var_map is a side table, and [get_args]
     (:328) has no case for it -- so there is no edge from the request to
     anything.  The response read is just an unrelated root.

     act_reqresp LOOKS fine: in_resp (nid 10) sits at the opposite end of the
     axis from in_x (nid 1). *)

  Example reqresp_looks_ordered : cyc act_reqresp 10 = 0.
  Proof. vm_compute. reflexivity. Qed.
  Example reqresp_request_input : cyc act_reqresp 1 = 4.
  Proof. vm_compute. reflexivity. Qed.

  (* But that is an artefact of the answer being stored without being used: its
     backward cost is 0 because nothing follows it.  Give it work to feed, and
     the response read lands in the SAME cycle as the request's own operand --
     nid 10 is [DFG_Input in_resp], nid 1 is [DFG_Input in_x].

     This is the measurement that matters, and it is independent of which way
     the cycle axis runs: whatever cycle the request's inputs are read in, the
     crypto ANSWER is read in that same cycle.  Not L cycles later.  Not after
     the request.  Together. *)

  Example resp_used_same_cycle_as_request :
    cyc act_resp_used 10 = cyc act_resp_used 1.
  Proof. vm_compute. reflexivity. Qed.

  Example resp_used_both_at_4 : cyc act_resp_used 10 = 4.
  Proof. vm_compute. reflexivity. Qed.

  (* And the cycle number is moot in any case.  [source_op] (:421) classifies
     DFG_Input as a source, and [require_buffer] never buffers a source; the
     comment there states the reason -- "inputs are latched at action start", so
     re-reading one in a later stage is free and always correct.  That is true
     of a host input and false of a crypto result.  In hardware every read of
     in_resp returns the value latched when the action began, whatever cycle the
     scheduler nominally assigned to the node.  REVIEW.md section 1.5, confirmed
     from the cost model rather than from the Verilog. *)

  (* ================================================================== *)
  (* WHAT SPIKE 2 HAS TO CARRY, GIVEN THE ABOVE                         *)
  (* ================================================================== *)

  (* A [DFG_Stall] with a latency is necessary and NOT sufficient.  A stall
     delays a value along an edge, and the request-to-response path has no edge
     to delay: the write is a var_map entry, the read is a source node, and
     nothing connects them.  Pinning an arbitrary producer (the Spike 2 rung as
     currently written) does not create that edge either.

     Three things have to become true together, and they are one change:

       1. a port drive is a NODE, so it has a cycle and can be an argument;
       2. a var can be driven at several cycles, so var_map stops being a
          one-nid-per-var table for driven ports;
       3. a trusted input read is a NODE that depends on a drive through a
          stall, so it stops being a source op and acquires a defined
          sampling cycle.

     (1) and (2) also move the output write out of the done half, which is the
     [Contract.v] / [TypedSynthesis.v] pair that INSIGHTS #25 says cannot land
     as two green steps.  That is the real cost of this rung, and it is not the
     DFG constructor. *)

End Spike.
