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
    Regression for the V2a fix: declassification must happen only at outputs the
    attacker can actually SEE.

    The hole this pins (REVIEW.md section 2.3, and structurally
    GENERAL_REQUIREMENTS.md section 1.1 one step further out): [read_var]
    deliberately shares read nodes, so a TOP-LEVEL assignment of a secret to an
    output makes that output's [var_map] root the [DFG_Var (DFG_SVar _)] node
    itself.  [public_dsts] returns it, [untainted_roots] contains it, and
    [get_tainted] drops it -- untainting the secret for the WHOLE action,
    including a branch condition that reads it.  The branch then gets a
    branch-selecting valid signal and its latency leaks the comparison.

    [crit_report] cannot catch this: [phi_crit_reason] returns [None] exactly
    when the condition is untainted, which is the case here.

    One specification, two contexts differing only in the classification of
    [out_key].  Classified [Public] -- the pre-V2a behaviour, where every
    [DFG_OVar] root declassified -- the leak is present and silent.  Classified
    [Secret], the secret stays tainted and the branch is correctly critical.
 *)

Section FunctionalSpecification.

    Definition w := 32.

    Inductive sd_action := act_leak | act_read.
    Inductive sd_states := st_dp.
    Inductive sd_inputs := in_guess.
    Inductive sd_outputs := out_key | out_flag.

    Definition sd_states_size  (_: sd_states)  : nat := w.
    Definition sd_inputs_size  (_: sd_inputs)  : nat := w.
    Definition sd_outputs_size (x: sd_outputs) : nat :=
      match x with out_key => w | out_flag => 1 end.

    Definition sd_states_init (x: sd_states)
      : tf_states_type sd_states_size x :=
      match x with st_dp => Bits.zero end.

    (* The shape that matters: [out_key := $st_dp] is at TOP LEVEL, so the
       secret's read node is itself the destination's root.  Inside an [if] the
       root would be the merge phi and the exposure would not arise -- which is
       exactly why relying on "we happen to write it inside a branch" is not a
       fix. *)
    Definition sd_ops (a: sd_action) : @tf_ops sd_states sd_inputs sd_outputs Empty_set :=
      match a with
      | act_leak =>
        {[
            let $out_key := $st_dp;
            if ($st_dp ==[w] $in_guess)
            then let $out_flag := #1
            else let $out_flag := #0
        ]}
      (* The READ-side twin.  Nothing secret is written here: the branch reads
         [out_key], an output.  If a read of an output were unconditionally
         untainted -- as it was before the [self_tainted] fix -- the branch
         would be non-critical and its latency would leak whatever [out_key]
         holds, which for MARS is DP. *)
      | act_read =>
        {[
            if ($out_key ==[w] $in_guess)
            then let $out_flag := #1
            else let $out_flag := #0
        ]}
      end.

    Definition mk (key_class: port_class) : TFSchedContext := {|
        tfs_spec_states := sd_states;
        tfs_spec_states_fin := _;
        tfs_spec_states_size := sd_states_size;
        tfs_spec_states_init := sd_states_init;

        tfs_spec_inputs := sd_inputs;
        tfs_spec_inputs_fin := _;
        tfs_spec_inputs_size := sd_inputs_size;
        tfs_spec_inputs_class := fun _ => Public;

        tfs_spec_outputs := sd_outputs;
        tfs_spec_outputs_fin := _;
        tfs_spec_outputs_size := sd_outputs_size;
        tfs_spec_outputs_class := fun x => match x with
                                           | out_key => key_class
                                           | out_flag => Public
                                           end;

        tfs_spec_action := sd_action;
        tfs_spec_action_fin := _;
        tfs_spec_action_ops := sd_ops;
        (* no attached IP: no call names a response port here *)
        (* no IP drives any port here, so nothing can conflict with one *)
        tfs_spec_ips := Empty_set;
        tfs_spec_ip := no_ips;
        tfs_spec_decls := []
    |}.

    Definition ctx_leaky  := mk Public.   (* pre-V2a behaviour *)
    Definition ctx_fixed  := mk Secret.   (* the crypto port, classified *)

End FunctionalSpecification.

Section Contrast.

    Definition crit (ctx: TFSchedContext)
        (dfg: @dfg_state_t (tfs_spec_states ctx) (tfs_spec_inputs ctx)
                (tfs_spec_outputs ctx) (tfs_spec_ips ctx)) : nat :=
      List.length (crit_report_all ctx dfg).

    (* [out_key] treated as attacker-visible: the secret is declassified at it,
       so the branch on the secret is NOT critical and its latency leaks. *)
    Example leaky_branch_not_critical :
      crit ctx_leaky (build_dfg ctx_leaky act_leak) = 0.
    Proof. vm_compute. reflexivity. Qed.

    (* Classified [Secret]: no declassification there, the secret stays tainted,
       and the branch is correctly forced constant-time. *)
    Example fixed_branch_is_critical :
      crit ctx_fixed (build_dfg ctx_fixed act_leak) = 1.
    Proof. vm_compute. reflexivity. Qed.

    (* The mechanism, directly: the secret's read node is a declassification
       site in one context and not in the other. *)
    Example leaky_has_more_public_dsts :
      List.length (public_dsts ctx_leaky (build_dfg ctx_leaky act_leak))
      = S (List.length (public_dsts ctx_fixed (build_dfg ctx_fixed act_leak))).
    Proof. vm_compute. reflexivity. Qed.

    (* --- the read side ------------------------------------------------- *)

    (* Branching on an output that is attacker-visible is fine: the attacker
       already knows it, so variable latency reveals nothing new. *)
    Example read_public_not_critical :
      crit ctx_leaky (build_dfg ctx_leaky act_read) = 0.
    Proof. vm_compute. reflexivity. Qed.

    (* Branching on an output the attacker CANNOT see must be critical.  This
       is the twin of the write-side hole: [self_tainted] used to mark only
       [DFG_SVar] reads, so a read of [crypt_key] -- which holds DP -- was
       treated as public. *)
    Example read_secret_is_critical :
      crit ctx_fixed (build_dfg ctx_fixed act_read) = 1.
    Proof. vm_compute. reflexivity. Qed.

End Contrast.
