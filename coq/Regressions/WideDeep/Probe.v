Require Import Koika.Frontend.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Audit.
Require Import Trustformer.Regressions.WideDeep.Spec.
Require Import Coq.Lists.List.
Import ListNotations.

(* SPIKE probe: how deep and how wide did the scheduler actually go? *)
Definition dfg0 := build_dfg tfs_ctx fs_act_mix.
Definition nnodes := Eval vm_compute in (length (graph dfg0)).
Definition bufs := Eval vm_compute in (buffer_needs tfs_ctx 2).
Definition nbufs := Eval vm_compute in (map (@length _) bufs).
Definition bounds := Eval vm_compute in (action_bounds tfs_ctx 2 dfg0).

(* Regression: the spike must stay wide (256-bit buffers) and deep.  If a future
   change collapses this back to a shallow pipeline, these fail loudly. *)
Example probe_nodes : nnodes = 42. Proof. reflexivity. Qed.
Example probe_depth : nbufs = [15]. Proof. reflexivity. Qed.
Example probe_bounds : bounds = (16, 16). Proof. reflexivity. Qed.

(* cost_fn ignores width, so the SAME 256-bit chain packs more operators per
   cycle as the limit rises -- the scheduler believes a 256-bit add costs 2,
   exactly as a 1-bit add does. *)
Definition bufs10 := Eval vm_compute in (map (@length _) (buffer_needs tfs_ctx 10)).
Definition bounds10 := Eval vm_compute in (action_bounds tfs_ctx 10 dfg0).
Definition bufs20 := Eval vm_compute in (map (@length _) (buffer_needs tfs_ctx 20)).
Definition bounds20 := Eval vm_compute in (action_bounds tfs_ctx 20 dfg0).
(* Same chain and widths at three cost limits.  [cost_fn] discards [sz], so
   these track the LIMIT rather than a physical delay: at limit 20 the whole
   ten-operator 256-bit chain sits in ~2 cycles.  A width-aware model is free to
   adopt -- costing add/sub at [2 + sz/128] moves only these three values, to
   26/6/3, and leaves the eight 32-bit examples byte-identical. *)
Example probe_bounds10 : bounds10 = (4, 4). Proof. reflexivity. Qed.
Example probe_bounds20 : bounds20 = (2, 2). Proof. reflexivity. Qed.

(* SPIKE: pin tf_concat's bit ORDER by computation.  MARS correctness depends on
   this exactly (CryptSnapshot fixes regSelect big-endian first, then registers,
   then ctx), and Koika's [Bits.app] is a notation with SWAPPED arguments
   (vendor/koika/coq/Utils/Vect.v L935, flagged "!!" by its own authors), so the
   order is not something to assume.  0xA concat 0x3 at width 8 must be 0xA3. *)
Definition concat_test : bits_t 8 :=
  tf_eval_expr fs_states_size fs_inputs_size fs_outputs_size (szB:=8)
    (tf_op2 (tf_concat 4 4) (tf_const 10) (tf_const 3))
    (ContextEnv.(create) fs_states_init, ContextEnv.(create) (fun _ => Bits.zero))
    (fun _ => Bits.zero).
Example concat_hi_first : concat_test = Bits.of_nat 8 163. Proof. reflexivity. Qed.
