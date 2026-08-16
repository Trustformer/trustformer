Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.

(*
    Regression cases for the forward taint analysis (`get_tainted`) and for the
    criticality test that `compile_dfg_expr` derives from it.

    Each action below isolates one rule. The assertions are stated over the *number
    of critical phi nodes* rather than over node ids, so they survive renumbering of
    the DFG.

    See agents/GENERAL_REQUIREMENTS.md 1.1/1.6 and
    agents/taint-tagging-soundness/PLAN.md for what each case is guarding against.
 *)

Section FunctionalSpecification.

    Definition w := 32.

    Inductive fs_action :=
    | act_secret_read
    | act_public_read
    | act_secret_root_cond
    | act_declassified_cond
    | act_derived_public
    | act_merge_phi
    | act_anon_phi
    | act_tries
    .

    Inductive fs_states :=
    | st_secret
    | st_tmp
    | st_tries
    .

    Inductive fs_inputs :=
    | in_pub
    .

    Inductive fs_outputs :=
    | out_pub
    | out_flag
    .

    Definition fs_states_size (_: fs_states) : nat := w.
    Definition fs_inputs_size (_: fs_inputs) : nat := w.
    Definition fs_outputs_size (_: fs_outputs) : nat := w.

    Definition fs_states_t := tf_states_type fs_states_size.

    Definition fs_states_init (x: fs_states) : (fs_states_t x) :=
        match x with
        | st_secret => Bits.zero
        | st_tmp => Bits.zero
        | st_tries => Bits.zero
        end.

    (* A phi in condition position, bound to no variable: no var_map rule can reach
       it, so only joining the condition's taint labels it correctly. *)
    Definition anon_cond : @tf_expr fs_states fs_inputs fs_outputs tf_no_externs :=
        tf_expr_if (tf_svar st_secret) (tf_const 1) (tf_const 0).

    Definition fs_transitions
        (act: fs_action)
        :
        (@tf_ops fs_states fs_inputs fs_outputs tf_no_externs)
        :=
        match act with
        (* Baseline: a read of pre-action secret state must taint. *)
        | act_secret_read =>
            {[
                if $st_secret then let $out_pub := #1 else let $out_pub := #0
            ]}
        (* 1.6: a read of the pre-action output state is visible to the attacker.
           The trailing write moves out_flag's var_map root off the read node, so
           declassification cannot mask an over-approximating source rule. *)
        | act_public_read =>
            {[
                (if $out_flag then let $out_pub := #1 else let $out_pub := #0);
                let $out_flag := #5
            ]}
        (* 1.1: the condition is the var_map root of a *secret* variable; storing a
           value in a secret register must not declassify it. *)
        | act_secret_root_cond =>
            {[
                let $st_tmp := $st_secret + #1;
                (if $st_tmp then let $out_pub := #1 else let $out_pub := #0)
            ]}
        (* Declassification still fires for a public destination, even when the node
           is simultaneously a secret read. *)
        | act_declassified_cond =>
            {[
                let $out_flag := $st_secret;
                (if $out_flag then let $out_pub := #1 else let $out_pub := #0)
            ]}
        (* Guard against "taint every secret var_map root": this value is derivable
           from the inputs, so it must stay untainted. *)
        | act_derived_public =>
            {[
                let $st_tmp := $in_pub + #1;
                (if $st_tmp then let $out_pub := #1 else let $out_pub := #0)
            ]}
        (* Issue A, merge form: the phi merging the two assignments is the condition
           of the second if. *)
        | act_merge_phi =>
            {[
                (if $st_secret then let $st_tmp := #1 else let $st_tmp := #0);
                (if $st_tmp then let $out_pub := #1 else let $out_pub := #0)
            ]}
        (* Issue A, anonymous form. *)
        | act_anon_phi =>
            {[
                if `anon_cond` then let $out_pub := #1 else let $out_pub := #0
            ]}
        (* The paper's tries counter: exercises buffering and variable latency. *)
        | act_tries =>
            {[
                if $st_tries !=[w] #0 then
                    let $st_tries := $st_tries - #1;
                    let $out_pub := #1
                else
                    let $out_pub := #0
            ]}
        end.

End FunctionalSpecification.

Section TaintAnalysis.

    Definition tfs_ctx : TFSchedContext := {|
        tfs_spec_states := fs_states;
        tfs_spec_states_fin := _;
        tfs_spec_states_size := fs_states_size;
        tfs_spec_states_init := fs_states_init;

        tfs_spec_inputs := fs_inputs;
        tfs_spec_inputs_fin := _;
        tfs_spec_inputs_size := fs_inputs_size;

        tfs_spec_outputs := fs_outputs;
        tfs_spec_outputs_fin := _;
        tfs_spec_outputs_size := fs_outputs_size;

        tfs_spec_externs := tf_no_externs;
        tfs_spec_externs_sig := tf_no_externs_sig;

        tfs_spec_action := fs_action;
        tfs_spec_action_fin := _;
        tfs_spec_action_ops := fs_transitions;
        tfs_spec_decls := []
    |}.

    Definition dfg_of (a: fs_action) := build_dfg tfs_ctx a.

    Definition tainted_of (a: fs_action) := get_tainted tfs_ctx (dfg_of a).

    (* The set `compile_dfg_expr` tests one phi at a time, materialised as a count so
       the assertions do not depend on node numbering. *)
    Definition critical_count (a: fs_action) : nat :=
        let dfg := dfg_of a in
        let tainted := tainted_of a in
        List.length (List.filter (fun n =>
            match op n with
            | DFG_Phi c _ _ => existsb (Nat.eqb c) tainted
            | _ => false
            end) (graph dfg)).

    Definition public_dst_count (a: fs_action) : nat :=
        List.length (public_dsts tfs_ctx (dfg_of a)).

    (* Baseline: a pre-action secret read taints, so the phi on it is critical.
       The read node is its own var_map root under DFG_SVar, which used to
       declassify it. *)
    Example secret_read_is_critical : critical_count act_secret_read = 1
        := ltac:(vm_compute; reflexivity).

    (* 1.6: a pre-action output read is attacker-visible, so nothing is tainted. *)
    Example public_read_is_not_critical : critical_count act_public_read = 0
        := ltac:(vm_compute; reflexivity).
    Example public_read_taints_nothing : tainted_of act_public_read = []
        := ltac:(vm_compute; reflexivity).

    (* 1.1: storing into a secret register must not declassify. *)
    Example secret_root_is_critical : critical_count act_secret_root_cond = 1
        := ltac:(vm_compute; reflexivity).

    (* Declassification still fires for a public destination. *)
    Example declassified_is_not_critical : critical_count act_declassified_cond = 0
        := ltac:(vm_compute; reflexivity).
    Example declassified_taints_nothing : tainted_of act_declassified_cond = []
        := ltac:(vm_compute; reflexivity).

    (* Guard against re-adding a "taint every secret var_map root" rule. *)
    Example derived_public_is_not_critical : critical_count act_derived_public = 0
        := ltac:(vm_compute; reflexivity).
    Example derived_public_taints_nothing : tainted_of act_derived_public = []
        := ltac:(vm_compute; reflexivity).

    (* Issue A: the condition's taint must reach the phi, in both the merge form
       and the anonymous form. *)
    Example merge_phi_is_critical : critical_count act_merge_phi = 2
        := ltac:(vm_compute; reflexivity).
    Example anon_phi_is_critical : critical_count act_anon_phi = 2
        := ltac:(vm_compute; reflexivity).

    (* 1.8: the paper's tries counter, exercising buffering and variable latency. *)
    Example tries_is_critical : critical_count act_tries = 2
        := ltac:(vm_compute; reflexivity).

    (* `public_dsts` on its own, so the whitebox extension has a baseline to diff
       against: only output destinations count, never secret ones. *)
    Example public_dsts_excludes_secrets : public_dst_count act_secret_read = 1
        := ltac:(vm_compute; reflexivity).
    Example public_dsts_counts_outputs : public_dst_count act_public_read = 2
        := ltac:(vm_compute; reflexivity).

End TaintAnalysis.
