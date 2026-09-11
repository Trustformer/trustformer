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
    SPIKE 2a (agents/one-action, 2026-09-11): now that [DFG_Stall] carries a
    latency, can a producer actually be pinned EARLIER than its consumer, and
    what does the hold cost?

    Spike 1 could not answer this: with every node costing the same, backward
    costing placed a would-be-early producer right next to its consumer, so
    "computed early, consumed late" was inexpressible.  A stall with a declared
    latency is the missing pin.

    The graphs here are built BY HAND rather than through [build_dfg], because
    nothing in the DSL emits a stall yet -- that is the drive-node work of
    Spike 2b.  Hand-building is not a cheat: [calc_backward_cost],
    [calc_target_cycle] and [require_buffer] are exactly the functions the real
    pipeline runs, and they take a [dfg_state] rather than an action.
 *)

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
      tfs_spec_decls := []
  |}.

  Definition climit := 5.

  (* in_x ---> stall<L> ---> not
     The consumer is a [tf_not]; the stall sits on the edge between the value
     and its use, which is where a crypto round trip would sit. *)
  Definition hold (L: nat) : dfg_state_t (states_var := sl_states)
                                         (inputs_var := sl_inputs)
                                         (outputs_var := sl_outputs) := {|
    graph :=
      [ {| nid := 0; op := DFG_Empty;        sz := 0 |}
      ; {| nid := 1; op := DFG_Input in_x;   sz := w |}
      ; {| nid := 2; op := DFG_Stall L 1;    sz := w |}
      ; {| nid := 3; op := DFG_Unary tf_not 2; sz := w |}
      ];
    var_map := [ (DFG_SVar st_acc, 3) ]
  |}.

  Definition hold_cycles (L: nat) :=
    calc_target_cycle climit (calc_backward_cost sl_ctx (hold L)).

  Definition cyc (L: nat) (n: nid_t) : nat :=
    match BitsToLists.list_assoc (hold_cycles L) n with
    | Some c => c | None => 999 end.

  Definition hold_bufs (L: nat) : nat :=
    List.length (require_buffer sl_ctx (hold L) (hold_cycles L)).

  (* ================================================================== *)
  (* M1.  A PRODUCER CAN NOW BE PINNED ARBITRARILY EARLY.               *)
  (* ================================================================== *)

  (* The consumer stays at the end of the axis and the producer moves away from
     it by exactly [L / climit] cycles.  Spike 1 could not produce ANY
     separation: a lone [tf_not] placed beside a 16-deep chain was simply
     rescheduled into the last cycle, because nothing pinned it.

     Note WHERE the latency lands.  [bc_aux] assigns a node and its arguments
     the same running max, so the gap between a node and its consumer comes
     from the NODE's own [cost_fn], not the consumer's -- INSIGHTS #48,
     [backward_cost_arg_self].  The stall and its argument therefore share a
     cycle, and the CONSUMER is pushed L/climit cycles later.  That is the
     right shape for a round trip: drive and stall together, sample later. *)

  Example consumer_at_end_5  : cyc 5  3 = 0.  Proof. vm_compute. reflexivity. Qed.
  Example producer_pinned_5  : cyc 5  2 = 1.  Proof. vm_compute. reflexivity. Qed.
  Example producer_pinned_20 : cyc 20 2 = 4.  Proof. vm_compute. reflexivity. Qed.
  Example producer_pinned_80 : cyc 80 2 = 16. Proof. vm_compute. reflexivity. Qed.

  (* The argument rides with the stall rather than being separated from it. *)
  Example arg_rides_with_stall : cyc 80 1 = cyc 80 2.
  Proof. vm_compute. reflexivity. Qed.

  (* ================================================================== *)
  (* M2.  THE HOLD COSTS ONE BUFFER, AT EVERY LATENCY.                  *)
  (* ================================================================== *)

  (* This is Spike 1's unmeasurable half, now measured.  [require_buffer]
     collects the arguments whose cycle differs from their consumer's and
     [nodup]s them, so a value held across sixteen cycles contributes exactly
     one nid -- the same as one held across a single cycle.

     Against the archive, at the same sixteen cycles: [chain_bufs 16 = 16] in
     StallCostSpike.v, versus 1 here.  Both at 256 bits.  The archive's
     (L+2) x width was the delay CHAIN, not the waiting, and DEBT-2's warning
     about an inflated [cost_fn] does not carry over to a single node. *)

  Example hold_one_buffer_5  : hold_bufs 5  = 1. Proof. vm_compute. reflexivity. Qed.
  Example hold_one_buffer_20 : hold_bufs 20 = 1. Proof. vm_compute. reflexivity. Qed.
  Example hold_one_buffer_80 : hold_bufs 80 = 1. Proof. vm_compute. reflexivity. Qed.

  (* ================================================================== *)
  (* WHAT THIS DOES NOT SHOW                                            *)
  (* ================================================================== *)

  (* 1. Nothing in the DSL emits a stall.  These graphs are hand-built; giving
        the surface language a way to produce one is Spike 2b, and 1.6 showed
        that needs the PORT DRIVE to become a node -- a stall on its own has no
        request-to-response edge to sit on.
     2. The latency is in COST units because [cost_fn] does not see
        [cost_limit].  Cycles need it to, which is the ~27-site ripple
        INSIGHTS #13 measured and absorbed with a Local Notation.
     3. The validity network is untouched.  [compile_valid_ones_gen] still
        saturates over node IDs, so a stalling node's validity does not yet
        lag its value -- that is Spike 3, and it is what makes the hold real
        rather than merely scheduled.
     4. No [must_buffer] predicate was needed.  The plan anticipated one; the
        measurement says a declared cost already puts the value in exactly one
        buffer, so the extra mechanism is unmotivated until something else
        demands it. *)

End Spike.
