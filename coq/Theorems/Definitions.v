(*! The vocabulary the guarantees are stated in: everything a theorem in
    coq/Theorems/ mentions is defined here or in the compiler, so this file and
    the four statement files are the whole proof-layer audit. !*)

Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Export Trustformer.Scheduler.Schedule.
Require Import Trustformer.Backend.Lowering.
Require Trustformer.Theorems.Internal.AttackerClock.

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

  (* The done flag is set when the tf_dfg_done register is non-zero. *)
  Definition done_set (ss: sched_sys_state) : Prop :=
    (fst ss).[tfs_done_signal sched] <> Bits.zero.

  (* THE IP's DATASHEET, while the action runs: a request left undisturbed for its
     flight time is answered [ip_lat] cycles after its pulse, unless done by then.
     Cycles past done belong to the next action, see [queue_ip_contract]. *)
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

  (* ================================================================ *)
  (* The attacker model: what the timing guarantees are stated over.     *)
  (* ================================================================ *)

  Local Notation o_cls   := (tfs_spec_outputs_class ctx).
  Local Notation ips     := (tfs_spec_ip ctx).
  Local Notation ss_run  := run_n.
  Local Notation ss_done := done_set.
  Local Notation sys_state :=
    (ContextEnv.(env_t) (tf_states_type s_sz)
     * ContextEnv.(env_t) (tf_outputs_type o_sz))%type.
  Local Notation run ops sys input :=
    (tf_ops_run s_sz i_sz o_sz ips ops sys input).

  (* Counted from cycle 1: cycle 0 is the start state, whose done flag is
     whatever the previous action left there. *)
  Definition first_done (act: tfs_action sched) (input: input_t)
      (resp: nat -> resp_val) (ss0: sched_sys_state) (N: nat) : Prop :=
    0 < N
    /\ ss_done (ss_run N act input resp ss0)
    /\ forall i, 0 < i < N -> ~ ss_done (ss_run i act input resp ss0).

  (* THE ATTACKER'S MODEL OF A RUN, over the two published snapshots and the
     cycle count: the outputs stand at [pre] until cycle [N] and at [post] from
     there.  The arguments are the whole of what it may read. *)
  Definition emulate (pre post: src_out_env) (N k: nat) (ov: o_var) :=
    if Nat.ltb k N then pre.[ov] else post.[ov].

  (* WHAT THE ATTACKER SEES: each public input, and each public output before
     and after the action.  A secret port reads [None]. *)
  Record public_view := {
    seen_in   : forall v: i_var, option (type_denote (tf_inputs_type i_sz v));
    seen_pre  : forall o: o_var, option (type_denote (tf_outputs_type o_sz o));
    seen_post : forall o: o_var, option (type_denote (tf_outputs_type o_sz o));
  }.

  Definition observe (input: input_t) (pre post: src_out_env) : public_view := {|
    seen_in v   := match tfs_spec_inputs_class ctx v with
                   | Public => Some (input v) | Secret => None end;
    seen_pre o  := match tfs_spec_outputs_class ctx o with
                   | Public => Some pre.[o] | Secret => None end;
    seen_post o := match tfs_spec_outputs_class ctx o with
                   | Public => Some post.[o] | Secret => None end;
  |}.

  (* THE LATENCY, OVER PUBLIC DATA.  Its arguments are the whole of what it
     reads: the action and the view.  The calculation is internal. *)
  Definition L_pub (act: tfs_action sched) (view: public_view) : nat :=
    AttackerClock.latency ctx cost_limit act
      (seen_in view) (seen_pre view) (seen_post view).


  (* ================================================================ *)
  (* Several actions in a row.                                        *)
  (* ================================================================ *)

  (* A command: an action and the inputs it latches when it is accepted. *)
  Local Notation command := (tfs_action sched * input_t)%type.

  (* ONE CYCLE OF A COMMAND QUEUE: the head command steps, and on the cycle that
     raises done the next takes over, as [rule_cmd] does once [tf_ready] is up.
     Commands run back to back; an empty queue holds its state. *)
  Definition queue_step (q: list command) (r: resp_val) (ss: sched_sys_state)
    : list command * sched_sys_state :=
    match q with
    | [] => ([], ss)
    | (act, input) :: rest =>
        let ss' := sched_step act ss (sched_input input r) in
        if beq_dec (fst ss').[tfs_done_signal sched] Bits.zero
        then (q, ss')
        else (rest, ss')
    end.

  (* [resp k] is what the IPs present during cycle [k], counted from the start
     of the whole sequence. *)
  Fixpoint queue_run (n: nat) (q: list command) (resp: nat -> resp_val)
      (ss: sched_sys_state) : list command * sched_sys_state :=
    match n with
    | 0 => (q, ss)
    | S k => let qs := queue_run k q resp ss in
             queue_step (fst qs) (resp k) (snd qs)
    end.

  (* THE IP's DATASHEET over a command sequence: [ip_contract]'s promise, read
     off the run that actually happens. *)
  Definition queue_ip_contract (q: list command) (resp: nat -> resp_val)
      (ss0: sched_sys_state) : Prop :=
    forall (p: tfs_ips sched) (s: nat),
      port_strobe (snd (queue_run s q resp ss0)) p = Bits.ones 1 ->
      (forall w, s < w -> w < s + pred (ip_lat (tfs_ip sched p)) ->
         port_strobe (snd (queue_run w q resp ss0)) p = Bits.zero) ->
      resp (s + pred (ip_lat (tfs_ip sched p))) p
      = ip_fn (tfs_ip sched p) (drive_payload (snd (queue_run s q resp ss0)) p).

  (* Each command with the outputs it leaves, as the specification computes
     them: the snapshots the attacker reads between commands. *)
  Fixpoint spec_outputs_seq (q: list command) (sp: src_sys_state)
    : list (tfs_action sched * input_t * src_out_env) :=
    match q with
    | [] => []
    | (act, input) :: rest =>
        let sp1 := run (tfs_spec_action_ops ctx act) sp input in
        (act, input, snd sp1) :: spec_outputs_seq rest sp1
    end.

  (* THE ATTACKER'S MODEL OF A SEQUENCE: [emulate], one command after the
     other.  Each command takes [L_pub] of its own public view, so every
     switch-over cycle is computed from public data alone. *)
  Fixpoint emulate_seq (pre: src_out_env)
      (obs: list (tfs_action sched * input_t * src_out_env)) (k: nat) (ov: o_var) :=
    match obs with
    | [] => pre.[ov]
    | (act, input, post) :: rest =>
        let N := L_pub act (observe input pre post) in
        if Nat.ltb k N then pre.[ov] else emulate_seq post rest (k - N) ov
    end.

  (* How many commands the attacker's model has finished by cycle [k]. *)
  Fixpoint emulate_progress (pre: src_out_env)
      (obs: list (tfs_action sched * input_t * src_out_env)) (k: nat) : nat :=
    match obs with
    | [] => 0
    | (act, input, post) :: rest =>
        let N := L_pub act (observe input pre post) in
        if Nat.ltb k N then 0 else S (emulate_progress post rest (k - N))
    end.


  (* ================================================================ *)
  (* The confidentiality criterion, over the spec alone.                *)
  (* ================================================================ *)

  Definition pub_agree (sys sys': sys_state) : Prop :=
    forall o : o_var, o_cls o = Public -> (snd sys).[o] = (snd sys').[o].

  (* "Secret-free": mentions no secret register and no read of a Secret output.
     Inputs are free at any class, since the theorem shares them between the two
     runs.  The Secret-output clause is REVIEW.md 2.4. *)
  Fixpoint sf_expr (e: @tf_expr s_var i_var o_var) : bool :=
    match e with
    | tf_const _ => true
    | tf_svar _  => false
    | tf_ivar _  => true
    | tf_ovar o  => match o_cls o with Public => true | Secret => false end
    | tf_op1 _ a => sf_expr a
    | tf_op2 _ a b => sf_expr a && sf_expr b
    | tf_expr_if c t f => sf_expr c && (sf_expr t && sf_expr f)
    end.

  (* [g] records a secret-dependent enclosing branch condition.  Under such a
     guard every Public output stays unwritten: assigning even a CONSTANT to one
     inside a branch on [dp] leaks [dp]. *)
  Fixpoint sf_ops (g: bool) (ops: @tf_ops s_var i_var o_var p_var) : bool :=
    match ops with
    | tf_ops_base tf_nop => true
    | tf_ops_base (tf_assign _ _) => true    (* a secret register may hold anything *)
    (* V4 denotes a call as [dst := ip_fn arg], a STATE update: its request port is
       no declared output, so no [o_cls] applies and it is [tf_assign].  The IP bus
       is outside this attacker view -- see THEOREM-AUDIT.md B5. *)
    | tf_ops_base (tf_call _ _ _) => true
    | tf_ops_base (tf_output o e) =>
        match o_cls o with
        | Secret => true                     (* Secret outputs may be arbitrary *)
        | Public => negb g && sf_expr e
        end
    | tf_ops_cons a b => sf_ops g a && sf_ops g b
    | tf_ops_if c t f =>
        let g' := (g || negb (sf_expr c))%bool in
        sf_ops g' t && sf_ops g' f
    end.

  Definition sf_action (a: tfs_spec_action ctx) : bool :=
    sf_ops false (tfs_spec_action_ops ctx a).

  Fixpoint run_seq (acts: list (tfs_spec_action ctx))
      (sys: sys_state) (input: input_t) : sys_state :=
    match acts with
    | [] => sys
    | a :: rest =>
        run_seq rest (run (tfs_spec_action_ops ctx a) sys input) input
    end.

End SchedulerWorld.


(* ==================================================================== *)
(* The synthesis relations: the Kôika circuit implements a design.      *)
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
