Require Import Koika.Frontend.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.MergeCalls.

Inductive mc_states := st_a | st_r.
Inductive mc_inputs := in_x | in_y.
Inductive mc_outputs := out_o.
Inductive mc_ips := ip_p | ip_q.

Local Notation OPS := (@tf_ops mc_states mc_inputs mc_outputs mc_ips).

Fixpoint count_calls (o: OPS) : nat :=
  match o with
  | tf_ops_base (tf_call _ _ _) => 1
  | tf_ops_base _ => 0
  | tf_ops_cons a b | tf_ops_if _ a b => count_calls a + count_calls b
  end.

Definition chain : OPS := {[
  if ($in_y ==[2] #0) then let $st_r := call ip_p ($in_x); let $out_o := $st_r
  else if ($in_y ==[2] #1) then let $st_r := call ip_p ($in_x + #1); let $out_o := $st_r
  else let $st_r := call ip_p ($in_x + #2); let $out_o := $st_r ]}.

Definition two_ips : OPS := {[
  if ($in_y ==[2] #0) then let $st_r := call ip_p ($in_x) else let $st_r := call ip_q ($in_x) ]}.

Definition no_call_suffix : OPS := {[
  if ($in_y ==[2] #0) then let $st_a := $in_x; let $out_o := $st_a
  else let $st_a := $in_x + #1; let $out_o := $st_a ]}.

Definition call_suffix : OPS := {[
  if ($in_y ==[2] #0) then let $st_a := $in_x; let $st_r := call ip_p ($st_a)
  else let $st_a := $in_x + #1; let $st_r := call ip_p ($st_a) ]}.

Example chain_one_call : (count_calls chain, count_calls (merge_calls chain)) = (3, 1).
Proof. vm_compute. reflexivity. Qed.

Example two_ips_kept : merge_calls two_ips = two_ips.
Proof. vm_compute. reflexivity. Qed.

Example no_call_suffix_kept : merge_calls no_call_suffix = no_call_suffix.
Proof. vm_compute. reflexivity. Qed.

Example call_suffix_factored : (count_calls call_suffix, count_calls (merge_calls call_suffix)) = (2, 1).
Proof. vm_compute. reflexivity. Qed.
