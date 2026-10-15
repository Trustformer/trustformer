Require Import Koika.Frontend.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Scheduler.MergeCalls.
Require Import Trustformer.Theorems.IPRDefinitions.
Require IPR.Machine.

(* The spec a merged design is checked against steps exactly like the original:
   [ipr] for [merge_calls_ctx ctx] is IPR against the spec as written. *)
Section MergedSpec.
  Context (ctx: TFSchedContext) (cost_limit: nat).
  Local Notation ctx' := (merge_calls_ctx ctx).

  Definition merged_query (q: query ctx cost_limit) : query ctx' cost_limit :=
    match q with
    | Peek => @Peek ctx' cost_limit
    | Run act pin => @Run ctx' cost_limit act pin
    end.

  Lemma merged_spec_step (src: trusted_source ctx) s q r :
    IPR.Machine.step (closed_spec ctx' cost_limit src) s (merged_query q) r <->
    IPR.Machine.step (closed_spec ctx cost_limit src) s q r.
  Proof.
    destruct s as [sp seen], q as [| act pin]; cbn; [ reflexivity | ].
    rewrite merge_calls_correct. reflexivity.
  Qed.
End MergedSpec.
