Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.DFG.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.

Require Import Coq.Lists.List.
Import ListNotations.

(* Three measurements of the port-write machinery WITHOUT a drive node, which
   is what MARS_Quote's back-to-back round trips need and what [DFG_Drive] /
   [DFG_Sample] were introduced for (StallLatencySpike.v).
   READING THE CYCLE AXIS: [calc_backward_cost] accumulates from the roots, so a
   node's number is the work REMAINING and bigger means EARLIER. *)

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
  Definition ops_twice : @tf_ops pd_states pd_inputs pd_outputs Empty_set :=
    tf_ops_cons
      (tf_ops_base (tf_output out_req (tf_ivar in_x)))
      (tf_ops_base (tf_output out_req (tf_ivar in_y))).

  (* REQUEST THEN RESPONSE -- build a message over four cycles, drive it, read
     the answer back.  Nothing in the DSL says the read follows the write. *)
  Definition ops_reqresp : @tf_ops pd_states pd_inputs pd_outputs Empty_set :=
    tf_ops_cons
      (tf_ops_base (tf_output out_req (work 4 (tf_ivar in_x))))
      (tf_ops_base (tf_assign st_acc (tf_ivar in_resp))).

  (* THE SAME, BUT THE ANSWER IS USED.  In act_reqresp the answer lands straight
     in a register, so backward costing happens to put it at the far end and the
     schedule looks accidentally plausible.  Give the answer some work to feed
     and the accident disappears. *)
  Definition ops_resp_used : @tf_ops pd_states pd_inputs pd_outputs Empty_set :=
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
      (* no IP drives any port here, so nothing can conflict with one *)
      tfs_spec_ips := Empty_set;
      tfs_spec_ip := no_ips;
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

  (* [var_map] holds nid 2, [DFG_Input in_y]: the SECOND write, one nid per var,
     so the first write's nid 1 is absent. *)
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

  (* [compile_dfg_aux] turns var_map into the tf_output/tf_assign writes and
     [schedule] puts them in the DONE half, which [tfs_next_cycle] applies as
     done fires.  So a var_map port carries its value on the action's LAST
     cycle only, leaving no cycle for the answer to arrive in. *)

  Definition count_outputs {s i o} (ops: list (@tf_op s i o Empty_set)) : nat :=
    List.length (filter (fun op => match op with
                                   | tf_output _ _ => true
                                   | _ => false end) ops).

  Example port_never_driven_early :
    count_outputs (fst (VariableScheduler.schedule pd_ctx climit (VariableScheduler.buffer_needs pd_ctx climit) act_twice)) = 0.
  Proof. vm_compute. reflexivity. Qed.

  Example port_driven_at_done :
    count_outputs (snd (VariableScheduler.schedule pd_ctx climit (VariableScheduler.buffer_needs pd_ctx climit) act_twice)) = 1.
  Proof. vm_compute. reflexivity. Qed.

  (* CONFIRMED IN THE GENERATED VERILOG, this being a hardware timing claim: the
     port register's Quote arm was gated by a conjunction of the action's
     validity bits -- the SAME wire that raises [st_done] -- so the port changed
     on the done cycle and on no other. *)

  (* ================================================================== *)
  (* M3.  NOTHING ORDERS THE RESPONSE AFTER THE REQUEST.                *)
  (* ================================================================== *)

  (* A var_map port write is a side-table entry, not a DFG node, and [get_args]
     has no case for one, so nothing edges the request to the response read.
     act_reqresp LOOKS fine: in_resp sits at the far end of the axis. *)

  Example reqresp_looks_ordered : cyc act_reqresp 10 = 0.
  Proof. vm_compute. reflexivity. Qed.
  Example reqresp_request_input : cyc act_reqresp 1 = 4.
  Proof. vm_compute. reflexivity. Qed.

  (* That is an artefact of the answer being stored unused, so its backward cost
     is 0.  Give it work to feed and the response read lands in the SAME cycle
     as the request's own operand.  This holds whichever way the axis runs:
     the answer is read in the cycle the request's inputs are. *)

  Example resp_used_same_cycle_as_request :
    cyc act_resp_used 10 = cyc act_resp_used 1.
  Proof. vm_compute. reflexivity. Qed.

  Example resp_used_both_at_4 : cyc act_resp_used 10 = 4.
  Proof. vm_compute. reflexivity. Qed.

  (* The cycle number is moot in any case: [source_op] classifies [DFG_Input] as
     a source and [require_buffer] leaves sources unbuffered, inputs being
     latched at action start.  So every read of a response port returns the
     value latched when the action began.  REVIEW.md section 1.5. *)

  (* ================================================================== *)
  (* WHAT SPIKE 2 HAS TO CARRY, GIVEN THE ABOVE                         *)
  (* ================================================================== *)

  (* A [DFG_Stall]'s latency delays a value along an EDGE, and the three
     measurements above show the request-to-response path has none.  Three
     things become true together: a port drive is a NODE with a cycle, a driven
     port leaves var_map's one-nid-per-var table, and a response read is a NODE
     under a stall with a defined sampling cycle. *)

End Spike.
