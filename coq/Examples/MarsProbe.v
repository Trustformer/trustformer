Require Import Koika.Frontend.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.
Require Import Trustformer.Examples.Mars.
Require Import Coq.Lists.List.
Import ListNotations.

(*
    Probe for the MARS module: how large is each command's DFG, how deep does
    the scheduler pipeline it, and how many cycles does a host wait?  Pinned so
    a change that silently rebalances the schedule fails loudly.

    These are CYCLE counts, not timing.  Two different things get confused here,
    so keep them apart:

    - MARS_PcrExtend builds a 1024-bit message through two concatenations and
      schedules to ONE cycle with ZERO buffers.  That is CORRECT, not a blind
      spot: cost_fn gives tf_concat cost 0 ("concatenation is pure wiring",
      VariableScheduler.v L358) because a concat picks wires and adds no logic.
      What is left on that path is a 16-bit equality, a few phis and one NOT.
      What 1024 bits does cost is AREA -- a 1024-bit 2:1 mux is ~1024 LUTs, wide
      but one gate deep -- which is a yosys question (Stage 6), not a scheduling
      one.
    - The real width-blindness (SPIKE.md section 5) is that tf_add/tf_sub cost a
      flat 2 and tf_cmp a flat 1 at every width, while a 256-bit ripple-carry
      adder is genuinely deeper than a 1-bit one.  This module barely touches
      that: its datapath is concat, mux and narrow compares.

    Still do not publish these as latency -- cost limit 10 is a scheduling
    parameter, not a delay model.
 *)

Definition dfg_cap  := build_dfg tfs_ctx act_capabilityget.
Definition dfg_reg  := build_dfg tfs_ctx act_regread.
Definition dfg_uns  := build_dfg tfs_ctx act_selftest.
Definition dfg_ext  := build_dfg tfs_ctx act_pcrextend.
Definition dfg_cont := build_dfg tfs_ctx act_continue.

Definition n_cap  := Eval vm_compute in (length (graph dfg_cap)).
Definition n_reg  := Eval vm_compute in (length (graph dfg_reg)).
Definition n_uns  := Eval vm_compute in (length (graph dfg_uns)).
Definition n_ext  := Eval vm_compute in (length (graph dfg_ext)).
Definition n_cont := Eval vm_compute in (length (graph dfg_cont)).

(* The eleven-tag lookup is no longer the biggest graph: PcrExtend's message
   construction and Continue's guard chain both overtake it in NODE COUNT --
   Continue by a distance, since it carries three outcomes (fault, completion,
   refusal) each writing most of the crypto port.
   Node count is not depth -- PcrExtend's extra nodes are wiring and wide muxes
   in parallel, while CapabilityGet's are a serial phi chain, which is why the
   smaller graph is the one that needs buffers.  An excluded command is the two
   [clear_results] writes, the failure test, the constant and the rc write. *)
Example probe_nodes_cap  : n_cap  = 87. Proof. reflexivity. Qed.
Example probe_nodes_reg  : n_reg  = 30. Proof. reflexivity. Qed.
Example probe_nodes_uns  : n_uns  = 9.  Proof. reflexivity. Qed.
Example probe_nodes_ext  : n_ext  = 91. Proof. reflexivity. Qed.
Example probe_nodes_cont : n_cont = 116. Proof. reflexivity. Qed.

(* Buffers per action, in [fs_action] constructor order, at the cost limit
   Mars.v ships with.  Index 1 is MARS_CapabilityGet -- still the only command
   whose graph does not fit in one cycle.  The 1024-bit crypto datapath needs
   none, because concatenation is free and a wide mux is shallow; it is the
   eleven-deep phi CHAIN in the tag lookup that costs cycles, and that chain is
   16 bits wide. *)
Definition nbufs := Eval vm_compute in (map (@length _) (buffer_needs tfs_ctx 10)).
Example probe_bufs : nbufs = [0; 3; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].
Proof. reflexivity. Qed.

(* Cycles per command: (lower bound, upper bound). *)
Definition b_cap  := Eval vm_compute in (action_bounds tfs_ctx 10 dfg_cap).
Definition b_reg  := Eval vm_compute in (action_bounds tfs_ctx 10 dfg_reg).
Definition b_uns  := Eval vm_compute in (action_bounds tfs_ctx 10 dfg_uns).
Definition b_ext  := Eval vm_compute in (action_bounds tfs_ctx 10 dfg_ext).
Definition b_cont := Eval vm_compute in (action_bounds tfs_ctx 10 dfg_cont).

(* fst = snd certifies constant time for the command itself.  Note this says
   nothing about how long the IP takes -- that latency lives between the issue
   action and the Continue action, outside any action's bounds, and is the
   host's to observe. *)
Example probe_bounds_reg  : b_reg  = (1, 1). Proof. reflexivity. Qed.
Example probe_bounds_uns  : b_uns  = (1, 1). Proof. reflexivity. Qed.
Example probe_bounds_ext  : b_ext  = (1, 1). Proof. reflexivity. Qed.
Example probe_bounds_cont : b_cont = (1, 1). Proof. reflexivity. Qed.

(* MARS_CapabilityGet is the module's one variable-latency command: fst <> snd,
   because an early Table 6 tag resolves in the first cycle and a late one has to
   wait for the buffered tail of the chain.  This is sound and intended -- IPR
   requires latency DERIVABLE from the attacker-visible sources, not constant
   latency (GENERAL_REQUIREMENTS.md section 1.2), and the only thing this
   latency reveals is the property tag, which is a public command argument the
   host chose itself.  No secret reaches this command at all. *)
Example probe_bounds_cap : b_cap = (1, 2). Proof. reflexivity. Qed.
