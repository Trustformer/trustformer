(*! The scheduled IR the proofs run through: its cycle and run, the IR form of the
    IP datasheet, the start relation, and how a Kôika state matches an IR state.
    None of it is in a headline statement; Theorems/*Definitions.v are. !*)

Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Backend.Lowering.

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* The scheduler record is huge; deprioritise unfolding it during conversion. *)
Strategy 1000 [tfs_schedule].

Section IRWorld.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation sched := (tfs_schedule ctx cost_limit).

  Local Notation o_var := (tfs_spec_outputs ctx).
  Local Notation s_sz  := (tfs_spec_states_size ctx).
  Local Notation i_sz  := (tfs_spec_inputs_size ctx).
  Local Notation o_sz  := (tfs_spec_outputs_size ctx).

  Local Notation src_st_env  := (ContextEnv.(env_t) (tf_states_type s_sz)).
  Local Notation src_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation src_sys_state := (src_st_env * src_out_env)%type.

  Local Notation sched_st_env  := (ContextEnv.(env_t) (tf_states_type (tfs_states_size sched))).
  Local Notation sched_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation sched_sys_state := (sched_st_env * sched_out_env)%type.

  Local Notation bneeds := (buffer_needs ctx cost_limit).

  Local Notation input_t := (forall x : tfs_spec_inputs ctx, type_denote (tf_inputs_type i_sz x)).
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

  (* The done flag is set when the tf_dfg_done register is non-zero. *)
  Definition done_set (ss: sched_sys_state) : Prop :=
    (fst ss).[tfs_done_signal sched] <> Bits.zero.

  (* THE IP's DATASHEET on one action's run: a request left undisturbed for its
     flight time is answered [ip_lat] cycles after its pulse, unless done by then. *)
  Definition ip_contract (act: tfs_action sched) (input: input_t) (resp: nat -> resp_val) (ss0: sched_sys_state) : Prop :=
    forall (p: tfs_ips sched) (s: nat),
      (forall i, 0 < i <= s + pred (ip_lat (tfs_ip sched p)) ->
         ~ done_set (run_n i act input resp ss0)) ->
      port_strobe (run_n s act input resp ss0) p = Bits.ones 1 ->
      (forall w, s < w -> w < s + pred (ip_lat (tfs_ip sched p)) ->
         port_strobe (run_n w act input resp ss0) p = Bits.zero) ->
      resp (s + pred (ip_lat (tfs_ip sched p))) p
      = ip_fn (tfs_ip sched p) (drive_payload (run_n s act input resp ss0) p).

  (* Registers that start zeroed, as [reset_states] clears them: every validity bit
     and buffer (a stall's buffer is a counter, so its start is observable).  Not
     the done flag: a done cycle leaves it set for the next action. *)
  Definition zeroed_at_start (x: tfs_states sched) : Prop :=
    match x with
    | tf_dfg_b _ _ => True
    | tf_dfg_v _ _ => True
    | _            => False
    end.

  (* Starting relation between a spec state and a scheduled state. *)
  Definition start_rel (sp: src_sys_state) (ss: sched_sys_state) : Prop :=
    snd ss = snd sp                                     (* outputs coincide *)
    /\ maps_from ctx bneeds (fst ss) = fst sp       (* tf_dfg_s slots = spec state *)
    /\ (forall x, zeroed_at_start x -> (fst ss).[x] = Bits.zero).

  (* Counted from cycle 1: cycle 0 is the start state, whose done flag is
     whatever the previous action left there. *)
  Definition first_done (act: tfs_action sched) (input: input_t)
      (resp: nat -> resp_val) (ss0: sched_sys_state) (N: nat) : Prop :=
    0 < N
    /\ done_set (run_n N act input resp ss0)
    /\ forall i, 0 < i < N -> ~ done_set (run_n i act input resp ss0).

  (* One action's outputs: at [pre] until cycle [N], at [post] from there. *)
  Definition emulate (pre post: src_out_env) (N k: nat) (ov: o_var) :=
    if Nat.ltb k N then pre.[ov] else post.[ov].

End IRWorld.


(* ==================================================================== *)
(* How a Kôika register file matches an IR state, one cycle at a time.  *)
(* ==================================================================== *)

Section SynthWorld.

  Context (tf_ctx: TFSynthContext).

  Local Notation sched_ctx := (tf_sched_ctx tf_ctx).
  Local Notation spec_states := (tfs_states sched_ctx).
  Local Notation spec_states_size := (tfs_states_size sched_ctx).
  Local Notation spec_inputs := (tfs_inputs sched_ctx).
  Local Notation spec_inputs_size := (tfs_inputs_size sched_ctx).
  Local Notation spec_outputs := (tfs_outputs sched_ctx).
  Local Notation spec_outputs_size := (tfs_outputs_size sched_ctx).
  Local Notation spec_action := (tfs_action sched_ctx).
  Local Notation spec_states_init := (tfs_states_init sched_ctx).
  Local Notation spec_action_encoding := (tf_action_encoding tf_ctx).
  Local Notation st_env  := (ContextEnv.(env_t) (tf_states_type spec_states_size)).
  Local Notation out_env := (ContextEnv.(env_t) (tf_outputs_type spec_outputs_size)).
  Local Notation sys_state_t := (st_env * out_env)%type.
  Local Notation input_t :=
    (forall x : spec_inputs, type_denote (tf_inputs_type spec_inputs_size x)).
  Local Notation R := (R tf_ctx).
  Local Notation r := (r tf_ctx).
  Local Notation Sigma := (Sigma tf_ctx).
  Local Notation spec_ips := (tfs_ips sched_ctx).
  Local Notation reg_t := (@_reg_t spec_states spec_inputs spec_outputs spec_ips).

  Hint Extern 0 (FiniteType reg_t) => exact (_reg_t_finite tf_ctx) : typeclass_instances.

  Definition state_matches (sys: sys_state_t) (r: ContextEnv.(env_t) R) : Prop :=
    (* State variables map cleanly *)
    (forall (x: spec_states), r.[tf_reg x] = (fst sys).[x]) /\
    (* Output variables map cleanly *)
    (forall (x: spec_outputs), r.[tf_out x] = (snd sys).[x]).

  Definition env_matches (act: spec_action) (input: input_t) (r: ContextEnv.(env_t) R) : Prop :=
    (* action variable maps cleanly *)
    (r.[tf_cmd] = spec_action_encoding act) /\
    (* THE LATCHED inputs map cleanly.  A response port is read live off the
       wire, so its latch holds the value from the dispatch cycle and
       [live_inputs_match] below is what pins it. *)
    (forall (x: spec_inputs),
       tfs_inputs_resp sched_ctx x = None -> r.[tf_in x] = input x).

  Definition state_env_matches (sys: sys_state_t) (act: spec_action) (input: input_t) (r: ContextEnv.(env_t) R) : Prop :=
    state_matches sys r /\
    env_matches act input r.

  Definition input_matches (act: spec_action) (input: input_t) (sigma: forall f, Sig_denote (Sigma f)) : Prop :=
    let cmd_res := sigma ext_in_cmd Ob~1 in
    (fst cmd_res) = Ob~1 /\ (* TODO: implicit params should be given explicitly once known *)
    (@fst (vect bool (tf_action_reg_size tf_ctx)) unit
      (@snd (vect_cons_t bool (vect_nil_t bool)) (prod (vect bool (tf_action_reg_size tf_ctx)) unit) cmd_res) = spec_action_encoding act) /\
    (forall (x: spec_inputs), sigma (ext_input x) (Ob~1) = input x).

  Definition abstract_init_state (sys: sys_state_t) : Prop :=
    (forall x, (fst sys).[x] = spec_states_init x) /\
    (forall x, (snd sys).[x] = Bits.zero).

  (* A response input is sampled off the wire, so its value comes from [sigma]
     in EVERY cycle -- [env_matches] covers the latched inputs only. *)
  Definition live_inputs_match (input: input_t) (sigma: forall f, Sig_denote (Sigma f)) : Prop :=
    forall v p, tfs_inputs_resp (tf_sched_ctx tf_ctx) v = Some p ->
                sigma (ext_input v) Ob~1 = input v.
End SynthWorld.
