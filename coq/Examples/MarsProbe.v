Require Import Koika.Frontend.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.
Require Import Trustformer.Examples.MarsSeq.
Require Import Coq.Lists.List.
Import ListNotations.

(* Probe for MARS: each command's DFG size, pipeline depth, host wait and
   constant-time share, pinned so a silent rebalance fails loudly.  These are
   CYCLE counts: [tf_concat] costs 0 (it selects wires), so width costs AREA and
   depth costs cycles -- here the eleven-arm capability lookup and the four-arm
   regSelect chain.  Cost limit 10 is a scheduling parameter. *)

Definition dfg_cap   := build_dfg tfs_ctx act_capabilityget.
Definition dfg_reg   := build_dfg tfs_ctx act_regread.
Definition dfg_uns   := build_dfg tfs_ctx act_selftest.
Definition dfg_ext   := build_dfg tfs_ctx act_pcrextend.
Definition dfg_cont  := build_dfg tfs_ctx act_continue.
Definition dfg_init  := build_dfg tfs_ctx act_init.
Definition dfg_quote := build_dfg tfs_ctx act_quote.

Definition n_cap   := Eval vm_compute in (length (graph dfg_cap)).
Definition n_reg   := Eval vm_compute in (length (graph dfg_reg)).
Definition n_uns   := Eval vm_compute in (length (graph dfg_uns)).
Definition n_ext   := Eval vm_compute in (length (graph dfg_ext)).
Definition n_cont  := Eval vm_compute in (length (graph dfg_cont)).
Definition n_init  := Eval vm_compute in (length (graph dfg_init)).
Definition n_quote := Eval vm_compute in (length (graph dfg_quote)).

(* MARS_Continue is by far the largest: it carries every completion step of
   every command plus two fault arms, each writing most of both crypto port
   groups.  That is the cost of the multi-action protocol, and it is exactly
   what V3/V4 deletes. *)
Example probe_nodes_cap   : n_cap   = 87.  Proof. reflexivity. Qed.
Example probe_nodes_reg   : n_reg   = 36.  Proof. reflexivity. Qed.
Example probe_nodes_uns   : n_uns   = 9.   Proof. reflexivity. Qed.
Example probe_nodes_ext   : n_ext   = 93.  Proof. reflexivity. Qed.
Example probe_nodes_cont  : n_cont  = 349. Proof. reflexivity. Qed.
Example probe_nodes_init  : n_init  = 65.  Proof. reflexivity. Qed.
Example probe_nodes_quote : n_quote = 178. Proof. reflexivity. Qed.

(* Buffers per action, in [fs_action] constructor order.  Index 1 is
   MARS_CapabilityGet (eleven-arm tag lookup) and index 10 is MARS_Quote
   (four-arm regSelect chain) -- the only two commands whose graphs do not fit
   in a single cycle.  Note the 1024-bit snapshot construction needs none:
   concatenation is wiring. *)
Definition nbufs := Eval vm_compute in (map (@length _) (buffer_needs tfs_ctx 10)).
Example probe_bufs : nbufs = [0; 3; 0; 0; 0; 0; 0; 0; 0; 0; 2; 0; 0; 0; 0].
Proof. reflexivity. Qed.

Definition b_cap   := Eval vm_compute in (action_bounds tfs_ctx 10 dfg_cap).
Definition b_reg   := Eval vm_compute in (action_bounds tfs_ctx 10 dfg_reg).
Definition b_ext   := Eval vm_compute in (action_bounds tfs_ctx 10 dfg_ext).
Definition b_cont  := Eval vm_compute in (action_bounds tfs_ctx 10 dfg_cont).
Definition b_init  := Eval vm_compute in (action_bounds tfs_ctx 10 dfg_init).
Definition b_quote := Eval vm_compute in (action_bounds tfs_ctx 10 dfg_quote).

(* fst = snd certifies the command is constant time.  This says nothing about
   how long the IP takes: that latency sits between the issue action and the
   Continue that consumes it, outside any action's bounds. *)
Example probe_bounds_reg  : b_reg  = (1, 1). Proof. reflexivity. Qed.
Example probe_bounds_ext  : b_ext  = (1, 1). Proof. reflexivity. Qed.
Example probe_bounds_cont : b_cont = (1, 1). Proof. reflexivity. Qed.
Example probe_bounds_init : b_init = (1, 1). Proof. reflexivity. Qed.

(* The two variable-latency commands, both sound: what varies is derivable from
   a PUBLIC argument the host chose -- the property tag and the register
   selector.  IPR requires latency derivable from the attacker-visible sources,
   not constant latency (GENERAL_REQUIREMENTS.md section 1.2). *)
Example probe_bounds_cap   : b_cap   = (1, 2). Proof. reflexivity. Qed.
Example probe_bounds_quote : b_quote = (1, 2). Proof. reflexivity. Qed.

(* Critical phi occurrences -- branches the scheduler must make constant-time
   because their condition is not derivable from public data. *)
Definition crit_cont  := Eval vm_compute in
  (List.length (crit_report_all tfs_ctx dfg_cont)).
Definition crit_ext   := Eval vm_compute in
  (List.length (crit_report_all tfs_ctx dfg_ext)).
Definition crit_init  := Eval vm_compute in
  (List.length (crit_report_all tfs_ctx dfg_init)).
Definition crit_quote := Eval vm_compute in
  (List.length (crit_report_all tfs_ctx dfg_quote)).

(* MARS_Continue guards on the valid and tag lines of both crypto groups, all
   Secret inputs, so every phi under them is forced constant-time. *)
Example probe_crit_cont : crit_cont = 61. Proof. reflexivity. Qed.

(* _MARS_Init branches on [in_init_req], a Secret input.  That is the
   over-classification accepted when a separate "platform" class was folded into
   Secret: init_req leaks nothing, its requirement is integrity, and treating it
   as secret is conservative but sound.  It costs nothing in cycles. *)
Example probe_crit_init : crit_init = 15. Proof. reflexivity. Qed.

(* Neither PcrExtend nor Quote has a single critical phi: every branch either of
   them takes is on a Public argument or a Public status bit.  For Quote in
   particular that is the interesting result -- the command that handles DP and
   the AK never branches on either. *)
Example probe_crit_ext   : crit_ext   = 0. Proof. reflexivity. Qed.
Example probe_crit_quote : crit_quote = 0. Proof. reflexivity. Qed.
