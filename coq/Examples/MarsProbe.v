Require Import Koika.Frontend.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.
Require Import Trustformer.Examples.Mars.
Require Import Coq.Lists.List.
Import ListNotations.

(*
    Probe for the Stage 1 MARS module: how large is each command's DFG, how deep
    does the scheduler pipeline it, and how many cycles does a host wait?  Pinned
    so a change that silently rebalances the schedule fails loudly.

    These are CYCLE counts, not timing.  cost_fn is width-blind (SPIKE.md
    section 5), so at 256 bits they track the cost limit rather than any physical
    delay -- do not publish them as latency.
 *)

Definition dfg_cap := build_dfg tfs_ctx fs_act_capabilityget.
Definition dfg_reg := build_dfg tfs_ctx fs_act_regread.
Definition dfg_uns := build_dfg tfs_ctx fs_act_selftest.

Definition n_cap := Eval vm_compute in (length (graph dfg_cap)).
Definition n_reg := Eval vm_compute in (length (graph dfg_reg)).
Definition n_uns := Eval vm_compute in (length (graph dfg_uns)).

(* The eleven-tag lookup is by far the biggest graph in the module; an excluded
   command is the two [clear_results] writes, the failure test, the constant and
   the rc write.  Clearing the result registers on every command cost +1 node on
   CapabilityGet, +0 on RegRead (the clear replaces the hold-read in the
   out-of-range branch) and +2 on an excluded command -- and nothing at all in
   buffers or cycle bounds. *)
Example probe_nodes_cap : n_cap = 81. Proof. reflexivity. Qed.
Example probe_nodes_reg : n_reg = 24. Proof. reflexivity. Qed.
Example probe_nodes_uns : n_uns = 9.  Proof. reflexivity. Qed.

(* Buffers per action, at the cost limit Mars.v ships with.  Action order is the
   [fs_action] constructor order, so index 1 is MARS_CapabilityGet: the only
   command whose graph does not fit in one cycle. *)
Definition nbufs := Eval vm_compute in (map (@length _) (buffer_needs tfs_ctx 10)).
Example probe_bufs : nbufs = [0; 3; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].
Proof. reflexivity. Qed.

(* Cycles per command: (lower bound, upper bound). *)
Definition b_cap := Eval vm_compute in (action_bounds tfs_ctx 10 dfg_cap).
Definition b_reg := Eval vm_compute in (action_bounds tfs_ctx 10 dfg_reg).
Definition b_uns := Eval vm_compute in (action_bounds tfs_ctx 10 dfg_uns).

Example probe_bounds_reg : b_reg = (1, 1). Proof. reflexivity. Qed.
Example probe_bounds_uns : b_uns = (1, 1). Proof. reflexivity. Qed.

(* MARS_CapabilityGet is the module's one variable-latency command: fst <> snd,
   because an early Table 6 tag resolves in the first cycle and a late one has to
   wait for the buffered tail of the chain.  This is sound and intended -- IPR
   requires latency DERIVABLE from the attacker-visible sources, not constant
   latency (GENERAL_REQUIREMENTS.md section 1.2), and the only thing this
   latency reveals is the property tag, which is a public command argument the
   host chose itself.  No secret reaches this command at all. *)
Example probe_bounds_cap : b_cap = (1, 2). Proof. reflexivity. Qed.
