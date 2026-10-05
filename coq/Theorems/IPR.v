(*! NO SECRET LEAKS BY TIMING.  The number of cycles an action takes is a
    function of the data an attacker already has: equal public inputs and equal
    public outputs force equal latency.  [L] computes that cycle count, and the
    emulator says an attacker learns nothing from the run that the spec and its
    own observations do not already give.  Proved in Internal/IPRProof.v. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Export Trustformer.Theorems.Definitions.
Require Trustformer.Theorems.Internal.IPRProof.

Require Import Coq.Lists.List.
Import ListNotations.

Section IPR.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation sched := (tfs_schedule ctx cost_limit).
  Local Notation s_sz := (tfs_spec_states_size ctx).
  Local Notation i_sz := (tfs_spec_inputs_size ctx).
  Local Notation o_sz := (tfs_spec_outputs_size ctx).
  Local Notation src_sys_state :=
    (ContextEnv.(env_t) (tf_states_type s_sz) * ContextEnv.(env_t) (tf_outputs_type o_sz))%type.
  Local Notation sched_sys_state :=
    (ContextEnv.(env_t) (tf_states_type (tfs_states_size sched))
     * ContextEnv.(env_t) (tf_outputs_type o_sz))%type.
  Local Notation input_t :=
    (forall x : tfs_spec_inputs ctx, type_denote (tf_inputs_type i_sz x)).
  Local Notation resp_val :=
    (forall p : tfs_ips sched, bits_t (ip_resp_sz (tfs_ip sched p))).
  Local Notation a_index := (Vect.index (length (buffer_needs ctx cost_limit))).
  Local Notation spec_run act sp input :=
    (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act)
       sp input).
  Local Notation ss_run := (run_n ctx cost_limit).

  (* The side conditions on the design, all three discharged by construction
     for any action the scheduler itself compiled. *)
  Local Notation plumbing_not_root := (plumbing_not_root ctx cost_limit).
  Local Notation drives_sized := (drives_sized ctx cost_limit).
  Local Notation guards_sized := (guards_sized ctx cost_limit).

  Local Notation first_done := (first_done ctx cost_limit).
  Local Notation emulate := (emulate ctx).
  Local Notation L := (L ctx cost_limit).
  Local Notation L_pub := (L_pub ctx cost_limit).
  Local Notation vals_sound := (vals_sound ctx cost_limit).
  Local Notation selectors_extractable := (selectors_extractable ctx cost_limit).
  Local Notation sched_input := (sched_input ctx cost_limit).

  (* ------------------------------------------------------------------- *)
  (* THE ONE ASSUMPTION ON THE USER.  Everything below holds for a design
     whose declassification rules are sound: each unconditional instance
     really does recover its target from its sources, and each guarded one
     does so under the guard it records.  A rule library discharges these by
     proving [instance_sound] per rule and applying
     [IPRProof.uncond_sound_of_instances] / [IPRProof.decl_sound_of_instances];
     a design with [tfs_spec_decls := []] gets them for free.  They are
     hypotheses, not axioms, so they travel with every theorem here. *)
  Context (Hdecls  : forall act a_idx input, uncond_sound ctx cost_limit act a_idx input).
  Context (Hdguard : forall act a_idx input, decl_sound ctx cost_limit act a_idx input).

  (* B2.  V4 states it over the SPEC's public outputs rather than over [pub_eq]
     at cycle 0, which has no content before the latches fire.  That is the
     shape B1 already had, so the two now coincide; [_start] and
     [latency_from_outputs] below are the same statement under their own
     names. *)
  Theorem latency_noninterference (act: tfs_action sched) (a_idx: a_index)
      (input input': input_t) (resp resp': nat -> resp_val)
      (sp0 sp0': src_sys_state) (ss0 ss0': sched_sys_state) (N N': nat) :
    act_idx_aligned ctx cost_limit act a_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    plumbing_not_root act ->
    drives_sized act ->
    guards_sized act ->
    start_rel ctx cost_limit sp0  ss0  ->
    start_rel ctx cost_limit sp0' ss0' ->
    Definitions.ip_contract ctx cost_limit act input  resp  ss0  ->
    Definitions.ip_contract ctx cost_limit act input' resp' ss0' ->
    (* PUBLIC data only: the two runs may differ in secret state AND secret
       inputs, so everything constrained here is something the attacker already
       drives or observes. *)
    (forall v,  tfs_spec_inputs_class  ctx v  = Public -> input v = input' v) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd sp0).[ov] = (snd sp0').[ov]) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd (spec_run act sp0  input )).[ov]
              = (snd (spec_run act sp0' input')).[ov]) ->
    first_done act input  resp  ss0  N ->
    first_done act input' resp' ss0' N' ->
    N = N'.
  Proof. exact (IPRProof.latency_noninterference ctx cost_limit Hdecls Hdguard act a_idx input input' resp resp' sp0 sp0' ss0 ss0' N N'). Qed.

  (* V3 read the zeroing side conditions off [start_rel] here; V4 needs
     [start_rel] in the theorem itself, so this is the same statement. *)
  Corollary latency_noninterference_start (act: tfs_action sched) (a_idx: a_index)
      (input input': input_t) (resp resp': nat -> resp_val)
      (sp0 sp0': src_sys_state) (ss0 ss0': sched_sys_state) (N N': nat) :
    act_idx_aligned ctx cost_limit act a_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    plumbing_not_root act ->
    drives_sized act ->
    guards_sized act ->
    start_rel ctx cost_limit sp0  ss0  ->
    start_rel ctx cost_limit sp0' ss0' ->
    Definitions.ip_contract ctx cost_limit act input  resp  ss0  ->
    Definitions.ip_contract ctx cost_limit act input' resp' ss0' ->
    (forall v,  tfs_spec_inputs_class  ctx v  = Public -> input v = input' v) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd sp0).[ov] = (snd sp0').[ov]) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd (spec_run act sp0  input )).[ov]
              = (snd (spec_run act sp0' input')).[ov]) ->
    first_done act input  resp  ss0  N ->
    first_done act input' resp' ss0' N' ->
    N = N'.
  Proof. exact (IPRProof.latency_noninterference_start ctx cost_limit Hdecls Hdguard act a_idx input input' resp resp' sp0 sp0' ss0 ss0' N N'). Qed.

  (* B1, the campaign's headline in observable terms: the cycle count depends
     only on the action, the input, and the outputs before and after. *)
  Corollary latency_from_outputs (act: tfs_action sched) (a_idx: a_index)
      (input input': input_t) (resp resp': nat -> resp_val)
      (sp0 sp0': src_sys_state) (ss0 ss0': sched_sys_state) (N N': nat) :
    act_idx_aligned ctx cost_limit act a_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    plumbing_not_root act ->
    drives_sized act ->
    guards_sized act ->
    start_rel ctx cost_limit sp0  ss0  ->
    start_rel ctx cost_limit sp0' ss0' ->
    Definitions.ip_contract ctx cost_limit act input  resp  ss0  ->
    Definitions.ip_contract ctx cost_limit act input' resp' ss0' ->
    (forall v,  tfs_spec_inputs_class  ctx v  = Public -> input v = input' v) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd sp0).[ov] = (snd sp0').[ov]) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd (spec_run act sp0  input )).[ov]
              = (snd (spec_run act sp0' input')).[ov]) ->
    first_done act input  resp  ss0  N ->
    first_done act input' resp' ss0' N' ->
    N = N'.
  Proof. exact (IPRProof.latency_from_outputs ctx cost_limit Hdecls Hdguard act a_idx input input' resp resp' sp0 sp0' ss0 ss0' N N'). Qed.

  Theorem emulator_correct (act: tfs_action sched) (sp0: src_sys_state)
      (ss0: sched_sys_state) (input: input_t) (resp: nat -> resp_val) (N: nat) :
    start_rel ctx cost_limit sp0 ss0 ->
    Definitions.ip_contract ctx cost_limit act input resp ss0 ->
    first_done act input resp ss0 N ->
    forall k, k <= N ->
      forall ov, (snd (ss_run k act input resp ss0)).[ov]
               = emulate (snd sp0) (snd (spec_run act sp0 input)) N k ov.
  Proof. exact (IPRProof.emulator_correct ctx cost_limit act sp0 ss0 input resp N). Qed.

  (* [L] is a function of the action and the PUBLIC data -- the public inputs
     and the public outputs before and after.  Never of the secret state, and
     never of a secret input.  The IP answers are free: each run carries its
     own, constrained only by its own datasheet. *)
  Corollary L_public (act: tfs_action sched) (a_idx: a_index)
      (input input': input_t) (resp resp': nat -> resp_val)
      (sp0 sp0': src_sys_state) (ss0 ss0': sched_sys_state) :
    act_idx_aligned ctx cost_limit act a_idx ->
    1 < length (graph (build_dfg ctx act)) ->
    plumbing_not_root act ->
    drives_sized act ->
    guards_sized act ->
    start_rel ctx cost_limit sp0  ss0  ->
    start_rel ctx cost_limit sp0' ss0' ->
    Definitions.ip_contract ctx cost_limit act input  resp  ss0  ->
    Definitions.ip_contract ctx cost_limit act input' resp' ss0' ->
    (* Public data only -- see [obs_eq_pub_eq]. *)
    (forall v,  tfs_spec_inputs_class  ctx v  = Public -> input v = input' v) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd sp0).[ov] = (snd sp0').[ov]) ->
    (forall ov, tfs_spec_outputs_class ctx ov = Public ->
                (snd (spec_run act sp0  input )).[ov]
              = (snd (spec_run act sp0' input')).[ov]) ->
    L act input resp ss0 = L act input' resp' ss0'.
  Proof. exact (IPRProof.L_public ctx cost_limit Hdecls Hdguard act a_idx input input' resp resp' sp0 sp0' ss0 ss0'). Qed.

  (* [L] IS A PUBLIC FUNCTION, BY CONSTRUCTION.  [L_public] above says the cycle
     count cannot tell two runs apart; this says what it IS.  [L_pub] takes the
     action, its slot in the buffer table, and the values the declassification
     rules recover -- no state, no input and no IP answer appears among its
     arguments, so no secret can reach it.  The two hypotheses on [vals] are
     what the rules discharge: it answers with the run's own values wherever a
     node has settled, and it answers at all for the selector of every phi the
     analysis did not call critical. *)
  Theorem L_is_public (act: tfs_action sched) (a_idx: a_index)
      (vals: nid_t -> option (list bool))
      (sp0: src_sys_state) (ss0: sched_sys_state)
      (input: input_t) (resp: nat -> resp_val) :
    act_idx_aligned ctx cost_limit act a_idx ->
    start_rel ctx cost_limit sp0 ss0 ->
    (forall k, (forall i, 1 <= i <= k ->
                  ~ done_set ctx cost_limit (ss_run i act input resp ss0)) ->
       selectors_extractable act a_idx vals (ss_run k act input resp ss0)
         (sched_input input (resp k))) ->
    (forall k, (forall i, 1 <= i <= k ->
                  ~ done_set ctx cost_limit (ss_run i act input resp ss0)) ->
       vals_sound act a_idx vals (ss_run k act input resp ss0)
         (sched_input input (resp k))) ->
    L act input resp ss0 = L_pub act a_idx vals.
  Proof.
    intros Halign Hstart Hsel Hvals.
    exact (IPRProof.L_pub_correct ctx cost_limit act a_idx vals input resp ss0
             Halign (proj2 (proj2 Hstart)) Hsel Hvals).
  Qed.

  (* THE COMPLETION CYCLE IS THE PUBLIC ONE: the design is done at the cycle the
     attacker computes from public data, and at no earlier cycle. *)
  Theorem L_pub_is_latency (act: tfs_action sched) (a_idx: a_index)
      (vals: nid_t -> option (list bool))
      (sp0: src_sys_state) (ss0: sched_sys_state)
      (input: input_t) (resp: nat -> resp_val) :
    act_idx_aligned ctx cost_limit act a_idx ->
    start_rel ctx cost_limit sp0 ss0 ->
    (forall k, (forall i, 1 <= i <= k ->
                  ~ done_set ctx cost_limit (ss_run i act input resp ss0)) ->
       selectors_extractable act a_idx vals (ss_run k act input resp ss0)
         (sched_input input (resp k))) ->
    (forall k, (forall i, 1 <= i <= k ->
                  ~ done_set ctx cost_limit (ss_run i act input resp ss0)) ->
       vals_sound act a_idx vals (ss_run k act input resp ss0)
         (sched_input input (resp k))) ->
    first_done act input resp ss0 (L_pub act a_idx vals).
  Proof.
    intros Halign Hstart Hsel Hvals.
    rewrite <- (L_is_public act a_idx vals sp0 ss0 input resp
                  Halign Hstart Hsel Hvals).
    exact (IPRProof.L_first_done ctx cost_limit act sp0 ss0 input resp Hstart).
  Qed.

  (* THE EMULATOR, OVER PUBLIC DATA ALONE.  Every cycle up to the attacker's own
     [L_pub], the outputs are what its two published snapshots say they are: the
     pre-action outputs until that cycle, the post-action outputs from it.  No
     argument of the right-hand side is anything a run keeps to itself. *)
  Corollary emulator_correct_L (act: tfs_action sched) (a_idx: a_index)
      (vals: nid_t -> option (list bool))
      (sp0: src_sys_state) (ss0: sched_sys_state)
      (input: input_t) (resp: nat -> resp_val) :
    act_idx_aligned ctx cost_limit act a_idx ->
    start_rel ctx cost_limit sp0 ss0 ->
    Definitions.ip_contract ctx cost_limit act input resp ss0 ->
    (forall k, (forall i, 1 <= i <= k ->
                  ~ done_set ctx cost_limit (ss_run i act input resp ss0)) ->
       selectors_extractable act a_idx vals (ss_run k act input resp ss0)
         (sched_input input (resp k))) ->
    (forall k, (forall i, 1 <= i <= k ->
                  ~ done_set ctx cost_limit (ss_run i act input resp ss0)) ->
       vals_sound act a_idx vals (ss_run k act input resp ss0)
         (sched_input input (resp k))) ->
    forall k, k <= L_pub act a_idx vals ->
      forall ov, (snd (ss_run k act input resp ss0)).[ov]
               = emulate (snd sp0) (snd (spec_run act sp0 input))
                   (L_pub act a_idx vals) k ov.
  Proof.
    intros Halign Hstart Hipc Hsel Hvals.
    rewrite <- (L_is_public act a_idx vals sp0 ss0 input resp
                  Halign Hstart Hsel Hvals).
    exact (IPRProof.emulator_correct_L ctx cost_limit act sp0 ss0 input resp
             Hstart Hipc).
  Qed.

End IPR.
