(* ===================================================================== *)
(*  SPIKE: does the lowering preserve SHARING?                           *)
(* ===================================================================== *)
(* [compile_dfg_expr_aux] turns a DAG into a binder-free [tf_expr], so a node
   reachable by K paths is written K times.  This chain uses each state var
   TWICE in the next -- st0 := in_a + in_a, stN := st(N-1) + st(N-1) -- giving
   N+1 nodes and 2^N paths: linear in N if the lowering shares, doubling per
   step if it duplicates. *)

Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.DFG.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.
Require Import Coq.Lists.List.
Import ListNotations.

Section ShareSpike.

  Definition sw := 32.

  Inductive sh_action := sh_act.
  Inductive sh_states := s0 | s1 | s2 | s3 | s4 | s5 | s6 | s7.
  Inductive sh_inputs := in_a.
  Inductive sh_outputs := out_r.

  Definition sh_states_size (_: sh_states) : nat := sw.
  Definition sh_inputs_size (_: sh_inputs) : nat := sw.
  Definition sh_outputs_size (_: sh_outputs) : nat := sw.
  Definition sh_states_init (x: sh_states) : tf_states_type sh_states_size x :=
    match x with
    | s0 | s1 | s2 | s3 | s4 | s5 | s6 | s7 => Bits.zero
    end.

  Definition dbl (prev: @tf_expr sh_states sh_inputs sh_outputs)
    : @tf_expr sh_states sh_inputs sh_outputs :=
    tf_op2 tf_add prev prev.

  Definition sh_ops : @tf_ops sh_states sh_inputs sh_outputs Empty_set :=
  {[
      let $s0 := `dbl (tf_ivar in_a)`;
      let $s1 := `dbl (tf_svar s0)`;
      let $s2 := `dbl (tf_svar s1)`;
      let $s3 := `dbl (tf_svar s2)`;
      let $s4 := `dbl (tf_svar s3)`;
      let $s5 := `dbl (tf_svar s4)`;
      let $s6 := `dbl (tf_svar s5)`;
      let $s7 := `dbl (tf_svar s6)`;
      let $out_r := $s7
  ]}.

  Definition sh_ctx : TFSchedContext := {|
      tfs_spec_states := sh_states;   tfs_spec_states_fin := _;
      tfs_spec_states_size := sh_states_size;
      tfs_spec_states_init := sh_states_init;
      tfs_spec_inputs := sh_inputs;   tfs_spec_inputs_fin := _;
      tfs_spec_inputs_size := sh_inputs_size;
      tfs_spec_inputs_class := fun _ => Public;
      tfs_spec_outputs := sh_outputs; tfs_spec_outputs_fin := _;
      tfs_spec_outputs_size := sh_outputs_size;
      tfs_spec_outputs_class := fun _ => Public;
      tfs_spec_action := sh_action;   tfs_spec_action_fin := _;
      tfs_spec_action_ops := fun _ => sh_ops;
      tfs_spec_ips := Empty_set;      tfs_spec_ips_fin := _;
      tfs_spec_ip := no_ips;
      tfs_spec_decls := []
  |}.

  Fixpoint esize {s i o} (e: @tf_expr s i o) : nat :=
    match e with
    | tf_const _ | tf_svar _ | tf_ivar _ | tf_ovar _ => 1
    | tf_op1 _ a => S (esize a)
    | tf_op2 _ a b => S (esize a + esize b)
    | tf_expr_if c t f => S (esize c + esize t + esize f)
    end.
  Definition osize {s i o p} (op: @tf_op s i o p) : nat :=
    match op with
    | tf_nop => 1 | tf_assign _ e => esize e
    | tf_output _ e => esize e | tf_call _ _ e => esize e end.
  Definition compiled_size (climit: nat) : nat :=
    let s := schedule sh_ctx climit (buffer_needs sh_ctx climit) sh_act in
    fold_left (fun acc op => acc + osize op) (fst s)
      (fold_left (fun acc op => acc + osize op) (snd s) 0).

  (* The same chain at HALF the depth, to show the growth is doubling and not
     merely large. *)
  Definition sh_ops4 : @tf_ops sh_states sh_inputs sh_outputs Empty_set :=
  {[
      let $s0 := `dbl (tf_ivar in_a)`;
      let $s1 := `dbl (tf_svar s0)`;
      let $s2 := `dbl (tf_svar s1)`;
      let $s3 := `dbl (tf_svar s2)`;
      let $out_r := $s3
  ]}.
  Definition sh_ctx4 : TFSchedContext := {|
      tfs_spec_states := sh_states;   tfs_spec_states_fin := _;
      tfs_spec_states_size := sh_states_size;
      tfs_spec_states_init := sh_states_init;
      tfs_spec_inputs := sh_inputs;   tfs_spec_inputs_fin := _;
      tfs_spec_inputs_size := sh_inputs_size;
      tfs_spec_inputs_class := fun _ => Public;
      tfs_spec_outputs := sh_outputs; tfs_spec_outputs_fin := _;
      tfs_spec_outputs_size := sh_outputs_size;
      tfs_spec_outputs_class := fun _ => Public;
      tfs_spec_action := sh_action;   tfs_spec_action_fin := _;
      tfs_spec_action_ops := fun _ => sh_ops4;
      tfs_spec_ips := Empty_set;      tfs_spec_ips_fin := _;
      tfs_spec_ip := no_ips;
      tfs_spec_decls := []
  |}.
  Definition compiled_size4 (climit: nat) : nat :=
    let s := schedule sh_ctx4 climit (buffer_needs sh_ctx4 climit) sh_act in
    fold_left (fun acc op => acc + osize op) (fst s)
      (fold_left (fun acc op => acc + osize op) (snd s) 0).

  (* MEASURED.  Four extra DFG nodes buy 17x the expression size: the growth is
     2x per level of sharing, which is the definition of the problem. *)
  Example share_dfg_4  : List.length (graph (build_dfg sh_ctx4 sh_act)) = 7.
  Proof. vm_compute. reflexivity. Qed.
  Example share_size_4 : compiled_size4 1000 = 88.
  Proof. vm_compute. reflexivity. Qed.

  Example share_dfg_8  : List.length (graph (build_dfg sh_ctx sh_act)) = 11.
  Proof. vm_compute. reflexivity. Qed.
  Example share_size_8 : compiled_size 1000 = 1524.
  Proof. vm_compute. reflexivity. Qed.

  (* Buffering is the ONLY thing that currently stops the duplication: a
     buffered node compiles to a register read.  Same graph, 70 instead of
     1524 -- but it happens only because a low cost limit forced a cycle
     boundary there, not because the node is shared. *)
  Example share_size_8_buffered : compiled_size 2 = 70.
  Proof. vm_compute. reflexivity. Qed.



End ShareSpike.
