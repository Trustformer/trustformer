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
    SPIKE (agents/one-action, 2026-09-10): what does WAITING actually cost?

    The archived external-call mechanism cost (L+2) x argument_width flip-flops
    per call site, and it is easy to conclude from that that declared latency is
    inherently expensive.  It is not.  That cost was a property of the
    mechanism: `refactor/external2` emitted L+1 chained DFG_Delay nodes plus one
    more, each at the argument width, and `cost_fn (DFG_Delay _) = cost_limit`
    forced every one onto its own cycle and therefore into its own buffer.  It
    was a shift register, copying the value forward once per cycle, and it
    existed only because the scheduler advances validity monotonically by node
    RANK -- inserting nodes was the only way to express "later".

    A stall does not need any of that.  [require_buffer] allocates ONE buffer per
    value that crosses a cycle boundary -- it collects argument nids and
    [nodup]s them -- so a value held for one cycle and a value held for sixteen
    cost exactly the same.

    This file measures both shapes with the machinery that exists today, so it
    carries no proof risk:

      act_chain  the archive's shape: the value is passed THROUGH k nodes, each
                 costing a full cycle.  Buffers grow with k.
      act_hold   the stall's shape: one value is computed early and consumed k
                 cycles later, while unrelated work occupies those cycles.
                 One buffer, whatever k is.

    Multiplication costs 5 and the cost limit here is 5, so each [tf_mul] is a
    cycle of its own -- which is exactly what `cost_fn (DFG_Delay _) =
    cost_limit` did in the archive.
 *)

Section Spike.

  Definition w := 256.

  Inductive sc_action  := act_chain | act_hold.
  Inductive sc_states  := st_unused.
  Inductive sc_inputs  := in_x | in_y.
  Inductive sc_outputs := out_o.

  Definition sc_states_size  (_: sc_states)  : nat := w.
  Definition sc_inputs_size  (_: sc_inputs)  : nat := w.
  Definition sc_outputs_size (_: sc_outputs) : nat := w.

  Definition sc_states_init (x: sc_states) : tf_states_type sc_states_size x :=
    match x with st_unused => Bits.zero end.

  (* k nodes, each a full cycle, carrying the value forward: the delay chain. *)
  Fixpoint mulchain (k: nat) (e: @tf_expr sc_states sc_inputs sc_outputs)
    : @tf_expr sc_states sc_inputs sc_outputs :=
    match k with
    | 0 => e
    | S k' => tf_op2 tf_mul (mulchain k' e) (tf_const 1)
    end.

  (* --- what the chain costs, as a function of its length ------------- *)

  Definition chain_ctx (k: nat) : TFSchedContext := {|
      tfs_spec_states := sc_states;   tfs_spec_states_fin := _;
      tfs_spec_states_size := sc_states_size;
      tfs_spec_states_init := sc_states_init;

      tfs_spec_inputs := sc_inputs;   tfs_spec_inputs_fin := _;
      tfs_spec_inputs_size := sc_inputs_size;
      tfs_spec_inputs_class := fun _ => Public;

      tfs_spec_outputs := sc_outputs; tfs_spec_outputs_fin := _;
      tfs_spec_outputs_size := sc_outputs_size;
      tfs_spec_outputs_class := fun _ => Public;

      tfs_spec_action := sc_action;   tfs_spec_action_fin := _;
      tfs_spec_action_ops := fun _ =>
        tf_ops_base (tf_output out_o (mulchain k (tf_ivar in_x)));
      (* no attached IP: no call names a response port here *)
      (* no IP drives any port here, so nothing can conflict with one *)
      tfs_spec_ips := Empty_set;
      tfs_spec_ip := no_ips;
      tfs_spec_ip_resp_secret := ltac:(intros []);
      tfs_spec_decls := []
  |}.

  Definition chain_bufs (k: nat) : nat :=
    match map (@length _) (buffer_needs (chain_ctx k) 5) with
    | n :: _ => n
    | [] => 0
    end.

  (* THE ARCHIVE'S COST, REPRODUCED.  Each link costs a full cycle, exactly as
     [cost_fn (DFG_Delay _) = cost_limit] made every delay node do, so every
     link crosses a boundary and every link is a 256-bit buffer.  Linear in the
     wait.  This is where (L+2) x argument_width came from. *)
  Example chain_1  : chain_bufs 1  = 1.  Proof. vm_compute. reflexivity. Qed.
  Example chain_4  : chain_bufs 4  = 4.  Proof. vm_compute. reflexivity. Qed.
  Example chain_16 : chain_bufs 16 = 16. Proof. vm_compute. reflexivity. Qed.

  (* --- and what it would cost to HOLD instead ------------------------- *)

  (* This is the half that CANNOT be measured with the machinery that exists
     today, and finding that out is the useful part of the spike.

     [calc_backward_cost] costs the graph BACKWARD from the output, so a node
     with a short path to its consumer is placed as LATE as it can be.  A value
     computed "early" therefore is not early at all -- the scheduler simply
     schedules it next to its consumer and it never crosses a boundary.  A first
     attempt here put a [tf_not] alongside a 16-deep chain and measured no extra
     buffer at all, because the [tf_not] had been moved to the last cycle.

     Nothing in the current scheduler PINS a producer to an early cycle.  That
     is exactly what a stall node introduces, and it is also why the archive
     reached for a chain: with validity advancing monotonically by node rank,
     inserting nodes was the only way to express "later".

     What the allocator will do once a producer can be pinned is not in doubt,
     because it is structural.  [require_buffer] collects, for every node, the
     arguments whose cycle differs from its own, and [nodup]s the result: ONE
     entry per value that crosses a boundary, regardless of how many cycles it
     waits.  A held value is one nid however far apart producer and consumer
     are; a chain is k nids.  1 versus k, and the difference is the mechanism,
     not the waiting.

     Spike 2 is therefore not "measure the hold" but "make a producer pinnable",
     i.e. give [DFG_Stall] a latency and a [must_buffer], which is the campaign's
     first real rung. *)

End Spike.
