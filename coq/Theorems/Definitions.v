(*! The vocabulary the guarantees are stated in.  Everything a theorem in
    coq/Theorems/ mentions is defined here or in the compiler it talks about, so
    this file plus the four statement files are the whole proof-layer audit.
    The proofs themselves live under Internal/. !*)

Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Export Trustformer.Scheduler.Schedule.

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

(* The scheduler record is huge; deprioritise unfolding it during conversion. *)
Strategy 1000 [tfs_schedule].

Section SchedulerWorld.

  (* The variable scheduler is parameterised by a source scheduling context and
     a per-cycle cost limit; every name below is relative to those. *)
  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation sched := (tfs_schedule ctx cost_limit).

  (* ---- Source (spec) world ---- *)
  Local Notation s_var := (tfs_spec_states ctx).
  Local Notation i_var := (tfs_spec_inputs ctx).
  Local Notation o_var := (tfs_spec_outputs ctx).
  Local Notation s_sz  := (tfs_spec_states_size ctx).
  Local Notation i_sz  := (tfs_spec_inputs_size ctx).
  Local Notation o_sz  := (tfs_spec_outputs_size ctx).

  Local Notation src_st_env  := (ContextEnv.(env_t) (tf_states_type s_sz)).
  Local Notation src_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation src_sys_state := (src_st_env * src_out_env)%type.

  (* ---- Scheduled (target) world ---- *)
  Local Notation sched_st_env  := (ContextEnv.(env_t) (tf_states_type (tfs_states_size sched))).
  Local Notation sched_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation sched_sys_state := (sched_st_env * sched_out_env)%type.

  Local Notation p_var  := (tfs_spec_ips ctx).
  Local Notation bneeds := (buffer_needs ctx cost_limit).
  Local Notation si_var := (tfs_inputs sched).
  Local Notation si_sz  := (tfs_inputs_size sched).
  Local Notation ss_sz  := (tfs_states_size sched).
  Local Notation oo_sz  := (tfs_outputs_size sched).

  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).
  Local Notation sched_input_t :=
    (forall x : tfs_inputs sched, type_denote (tf_inputs_type (tfs_inputs_size sched) x)).

  (* What each IP presents on its response channel during one cycle. *)
  Local Notation resp_val :=
    (forall p : tfs_ips sched, bits_t (ip_resp_sz (tfs_ip sched p))).


  (* [tf_dfg_ov p] carries {strobe, payload} with the payload in the low bits,
     and holds a request's payload from its pulse until the next one. *)
  Definition drive_payload (ss: sched_sys_state) (p: tfs_ips sched)
    : bits_t (ip_req_sz (tfs_ip sched p)) :=
    Bits.slice 0 (ip_req_sz (tfs_ip sched p))
      ((fst ss).[tfs_drive_reg sched p]).

  (* The request strobe the IP sees on the port: one cycle per pulse. *)
  Definition port_strobe (ss: sched_sys_state) (p: tfs_ips sched) : bits_t 1 :=
    Bits.slice (ip_req_sz (tfs_ip sched p)) 1
      ((fst ss).[tfs_drive_reg sched p]).

  (* A [DFG_Sample] reads the response channel LIVE, so a cycle's inputs are the
     action's own plus whatever each IP is presenting that cycle. *)
  Definition sched_input (input: input_t) (r: resp_val) : sched_input_t :=
    fun x => match x with
             | inl v => input v
             | inr p => r p
             end.

  (* ---- One scheduled cycle and its bounded iteration ---- *)
  Definition sched_step (act: tfs_action sched) (ss: sched_sys_state) (input: sched_input_t)
    : sched_sys_state :=
    tfs_next_cycle sched act ss input.

  (* [resp k] is what the IPs present during cycle [k]. *)
  Fixpoint run_n (n: nat) (act: tfs_action sched) (input: input_t) (resp: nat -> resp_val) (ss: sched_sys_state) : sched_sys_state :=
    match n with
    | 0 => ss
    | S k => let ss1 := run_n k act input resp ss in
             sched_step act ss1 (sched_input input (resp k))
    end.

  (* THE IP's DATASHEET.  A request strobed on the port and left undisturbed for
     the IP's flight time is answered [ip_lat] cycles after the pulse that sent
     it; at every other cycle the channel promises nothing. *)
  Definition ip_contract (act: tfs_action sched) (input: input_t) (resp: nat -> resp_val) (ss0: sched_sys_state) : Prop :=
    forall (p: tfs_ips sched) (s: nat),
      port_strobe (run_n s act input resp ss0) p = Bits.ones 1 ->
      (forall w, s < w -> w < s + pred (ip_lat (tfs_ip sched p)) ->
         port_strobe (run_n w act input resp ss0) p = Bits.zero) ->
      resp (s + pred (ip_lat (tfs_ip sched p))) p
      = ip_fn (tfs_ip sched p) (drive_payload (run_n s act input resp ss0) p).

  (* The done flag is set when the tf_dfg_done register is non-zero. *)
  Definition done_set (ss: sched_sys_state) : Prop :=
    (fst ss).[tfs_done_signal sched] <> Bits.zero.

  (* done_set is decidable (a size-1 register is zero or all-ones). *)
  Lemma done_set_dec (ss: sched_sys_state) : {done_set ss} + {~ done_set ss}.
  Proof.
    unfold done_set.
    destruct (eq_dec ((fst ss).[tfs_done_signal sched]) Bits.zero) as [H | H].
    - right. intro Hc. apply Hc. exact H.
    - left. exact H.
  Qed.

  (* Registers that must start zeroed: the done flag and every validity bit.
     (Buffer value registers tf_dfg_b may hold arbitrary data, since their
     validity bit is 0.) *)
  (* A stall's buffer is a COUNTER, so its start value is observable: the
     validity it publishes is "counter = lat-1".  The hardware resets it --
     [reset_states] lists [tf_dfg_b] beside [tf_dfg_v] and [maps_to] zeroes it
     -- so saying so here is reading the design, not strengthening it. *)
  Definition zeroed_at_start (x: tfs_states sched) : Prop :=
    match x with
    | tf_dfg_b _ _ => True
    | tf_dfg_v _ _ => True
    | tf_dfg_done  => True
    | _            => False
    end.

  (* Starting relation between a spec state and a scheduled state. *)
  Definition start_rel (sp: src_sys_state) (ss: sched_sys_state) : Prop :=
    snd ss = snd sp                                     (* outputs coincide *)
    /\ maps_from ctx bneeds (fst ss) = fst sp       (* tf_dfg_s slots = spec state *)
    /\ (forall x, zeroed_at_start x -> (fst ss).[x] = Bits.zero).

  Definition node_op (act: tfs_action sched) (n: nid_t) :=
    op (nth n (graph (build_dfg ctx act)) {| nid := 0; op := DFG_Empty; sz := 0 |}).

  Definition stall_lat_of (act: tfs_action sched) (n: nid_t) : option nat :=
    match node_op act n with DFG_Stall l _ => Some l | _ => None end.

  Definition is_sample_of (act: tfs_action sched) (n: nid_t) : bool :=
    match node_op act n with DFG_Sample _ _ _ => true | _ => false end.

  (* SATURATION RANK.  Ranking by node id alone is unsound in V4: a stall makes
     its consumer wait [lat] cycles, not one.  The rank is the id plus the extra
     cycles every stall UP TO AND INCLUDING it costs -- including its own, so a
     stall's rank already covers its wait and everything above it sits past it. *)
  Definition stall_weight (act: tfs_action sched) (n: nid_t) : nat :=
    match stall_lat_of act n with Some l => pred l | None => 0 end.

  Fixpoint node_rank (act: tfs_action sched) (n: nat) : nat :=
    match n with
    | 0 => stall_weight act 0
    | S m => S (node_rank act m) + stall_weight act (S m)
    end.

  (* SETTLE BOUND.  Buffers rank by NODE ID (args_lt_fwd), so a buffer caching
     node [n] settles by cycle [n] and the run is bounded by the graph size.
     The target cycle is NOT a rank: two buffers can share one. *)
  Definition settle_bound (act: tfs_action sched) : nat :=
    node_rank act (length (graph (build_dfg ctx act))).

  (* The buffers a reference expression KEEPS: exactly the sample ones.  This
     is [guard_expr]'s [sbufs] -- "buffers are substituted only for samples,
     every other source is stable across the action".  A sample reads a LIVE
     wire and its buffer LATCHES, so inlining through one would compare a
     latched answer against whatever the port carries now; with two calls on a
     port those differ, and MARS's Quote has eight samples on one. *)
  Definition sample_bufs
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
    : list (nid_t * (nat * sz_t)) :=
    filter (fun '(n, _) => is_sample_of act n)
           (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []).

  (* Reference expression for DFG node n of act: inlined down to the sample
     buffers, which stand for the answers already received. *)
  Definition node_ref_expr
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (n: nat) : @tf_expr (tfs_states sched) si_var o_var :=
    fst (compile_dfg_expr ctx bneeds
           (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n
           (sample_bufs act a_idx)).

  (* The buffer-free value of forward-graph node [n], demanded at width [szB],
     in scheduler state [ss].  This is what [dfg_action_semantics] talks about. *)
  Definition nval (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (ss: sched_sys_state) (input: sched_input_t) (szB: nat) (n: nid_t) : bits_t szB :=
    tf_eval_expr ss_sz si_sz oo_sz (szB := szB) (node_ref_expr act a_idx n) ss input.

  (* [a_idx] indexes the SAME action as [act]: buffer_needs is built by mapping
     over spec_all_actions, so length (buffer_needs …) = length spec_all_actions
     and act's slot is finite_index act. *)
  Definition act_idx_aligned
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit))) : Prop :=
    index_to_nat a_idx = @finite_index _ (tfs_action_fin sched) act.

End SchedulerWorld.
