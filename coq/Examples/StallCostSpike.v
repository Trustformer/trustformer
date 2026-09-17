Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.DFG.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.

Require Import Coq.Lists.List.
Import ListNotations.

(* What WAITING costs, in two shapes.  [act_chain] passes a value THROUGH k
   nodes each costing a full cycle, so buffers grow with k -- the archived
   (L+2) x width per call site.  [act_hold] computes a value early and consumes
   it k cycles later, for ONE buffer whatever k is, since [require_buffer]
   [nodup]s per value crossing a boundary.  [tf_mul] costs a cycle at limit 5. *)

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

  (* Pinning a producer EARLY needs the stall's own latency: [calc_backward_cost]
     costs the graph backward from the output, so a node with a short path to its
     consumer is scheduled right beside it and crosses no boundary.  A [tf_not]
     placed alongside a 16-deep chain measures no extra buffer for exactly that
     reason.  StallLatencySpike.v measures the pinned shape. *)

End Spike.
