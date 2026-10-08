(*! The vocabulary the guarantees are stated in: the attacker's view and clock,
    the circuit Lowering emits, and the emulator it is held to.  With the
    statement files in coq/Theorems/, this is the whole proof-layer audit. !*)

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

  Local Notation s_var := (tfs_spec_states ctx).
  Local Notation i_var := (tfs_spec_inputs ctx).
  Local Notation o_var := (tfs_spec_outputs ctx).
  Local Notation p_var := (tfs_spec_ips ctx).
  Local Notation s_sz  := (tfs_spec_states_size ctx).
  Local Notation i_sz  := (tfs_spec_inputs_size ctx).
  Local Notation o_sz  := (tfs_spec_outputs_size ctx).
  Local Notation o_cls := (tfs_spec_outputs_class ctx).
  Local Notation ips   := (tfs_spec_ip ctx).

  Local Notation src_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation sys_state :=
    (ContextEnv.(env_t) (tf_states_type s_sz) * src_out_env)%type.
  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).
  Local Notation run ops sys input :=
    (tf_ops_run s_sz i_sz o_sz ips ops sys input).

  (* ================================================================ *)
  (* The attacker model: what the timing guarantees are stated over.  *)
  (* ================================================================ *)

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
  (* The confidentiality criterion, over the spec alone.              *)
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
(* The circuit Lowering emits, its environment, and its emulator.       *)
(* ==================================================================== *)

Section CircuitWorld.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation sched := (tfs_schedule ctx cost_limit).

  (* How [in_cmd] encodes an action.  With it, [synth] is the context Lowering
     compiles, so [rules synth] are the circuit's rules. *)
  Context (enc_sz: nat) (enc: tfs_action sched -> bits_t enc_sz)
          (enc_inj: forall a b, enc a = enc b -> a = b)
          (names: Show (tfs_action sched)).

  Definition synth : TFSynthContext := {|
    tf_sched_ctx := sched;
    tf_action_reg_size := enc_sz;
    tf_action_encoding := enc;
    tf_action_encoding_inj := enc_inj;
    tf_action_names := names |}.

  Local Notation tsched := (tf_sched_ctx synth).
  Local Notation reg_t :=
    (@_reg_t (tfs_states tsched) (tfs_inputs tsched) (tfs_outputs tsched) (tfs_ips tsched)).
  Hint Extern 0 (FiniteType reg_t) => exact (_reg_t_finite synth) : typeclass_instances.
  Local Notation circuit_state := (ContextEnv.(env_t) (R synth)).
  Local Notation wires := (forall f, Sig_denote (Sigma synth f)).

  Local Notation s_sz := (tfs_spec_states_size ctx).
  Local Notation i_sz := (tfs_spec_inputs_size ctx).
  Local Notation o_sz := (tfs_spec_outputs_size ctx).
  Local Notation src_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation src_sys_state :=
    (ContextEnv.(env_t) (tf_states_type s_sz) * src_out_env)%type.
  Local Notation input_t :=
    (forall x : tfs_spec_inputs ctx, type_denote (tf_inputs_type i_sz x)).
  Local Notation run act sp input :=
    (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act) sp input).

  (* A command: an action and the inputs it latches when it is taken. *)
  Local Notation command := (tfs_action sched * input_t)%type.

  (* THE CIRCUIT: Kôika's cycle over the lowered rules, from state [c0], with
     [env k] what the environment drives in cycle [k]. *)
  Fixpoint circuit_run (c0: circuit_state) (env: nat -> wires) (n: nat) : circuit_state :=
    match n with
    | 0 => c0
    | S k => interp_cycle (env k) (rules synth) (system_schedule synth) (circuit_run c0 env k)
    end.

  (* THE CIRCUIT AT REST, holding spec state [sp]: ready, its state slots and
     outputs are the spec's, and every buffer and validity bit is cleared. *)
  Definition at_rest (c: circuit_state) (sp: src_sys_state) : Prop :=
    c.[tf_ready] = Ob~1
    /\ (forall o, c.[tf_out o] = (snd sp).[o])
    /\ (forall x: tfs_states tsched,
          match x with
          | tf_dfg_s s => c.[tf_reg (tf_dfg_s s)] = (fst sp).[s]
          | tf_dfg_b _ _ | tf_dfg_v _ _ => c.[tf_reg x] = Bits.zero
          | _ => True
          end).

  (* What the environment offers in a cycle while ready is up: [Some (act, input)]
     is a valid [in_cmd] with the inputs on their ports, [None] an invalid one. *)
  Definition presents (w: wires) (c: option command) : Prop :=
    let cmd := w ext_in_cmd Ob~1 in
    match c with
    | None => fst cmd = Ob~0
    | Some (act, input) =>
        fst cmd = Ob~1 /\ fst (snd cmd) = tf_action_encoding synth act
        /\ forall v, w (ext_input (inl v)) Ob~1 = input v
    end.

  (* THE IP's DATASHEET on the circuit: a request register raised at cycle [s]
     and left quiet for the flight time is answered on the response wire. *)
  Definition ip_contract (c0: circuit_state) (env: nat -> wires) : Prop :=
    forall (p: tfs_ips tsched) (s: nat),
      let req k := (circuit_run c0 env k).[tf_reg (tfs_drive_reg tsched p)] in
      let sz := ip_req_sz (tfs_ip tsched p) in
      let lat := pred (ip_lat (tfs_ip tsched p)) in
      Bits.slice sz 1 (req s) = Bits.ones 1 ->
      (forall w, s < w < s + lat -> Bits.slice sz 1 (req w) = Bits.zero) ->
      env (s + lat) (ext_input (inr p)) Ob~1 = ip_fn (tfs_ip tsched p) (Bits.slice 0 sz (req s)).

  (* THE EMULATOR, which never sees the spec: it shows [em_pre] for [em_left] more
     cycles, then [em_post].  Taking a command, it is told only the outputs after
     it, and is busy for [L_pub] cycles of the public view. *)
  Record emulator := { em_pre : src_out_env; em_post : src_out_env; em_left : nat }.

  Definition em_start (outs: src_out_env) : emulator :=
    {| em_pre := outs; em_post := outs; em_left := 0 |}.

  Definition em_ready (e: emulator) : bool := Nat.eqb (em_left e) 0.

  Definition em_shown (e: emulator) : src_out_env :=
    if em_ready e then em_post e else em_pre e.

  Definition em_tick (e: emulator) : emulator :=
    {| em_pre := em_pre e; em_post := em_post e; em_left := pred (em_left e) |}.

  Definition em_take (e: emulator) (act: tfs_action sched) (input: input_t)
      (post: src_out_env) : emulator :=
    {| em_pre := em_post e; em_post := post;
       em_left := pred (L_pub ctx cost_limit act (observe ctx input (em_post e) post)) |}.

  (* THE IDEAL WORLD: the spec runs beside the emulator from [sp0], a state the
     emulator never reads, and answers each command it takes with the outputs. *)
  Fixpoint ideal_run (sp0: src_sys_state) (cmds: nat -> option command) (n: nat)
    : src_sys_state * emulator :=
    match n with
    | 0 => (sp0, em_start (snd sp0))
    | S k =>
        let '(sp, e) := ideal_run sp0 cmds k in
        match cmds k with
        | Some (act, input) =>
            if em_ready e
            then let sp' := run act sp input in (sp', em_take e act input (snd sp'))
            else (sp, em_tick e)
        | None => (sp, em_tick e)
        end
    end.

End CircuitWorld.

Arguments em_pre {ctx}. Arguments em_post {ctx}. Arguments em_left {ctx}.
Arguments em_start {ctx}. Arguments em_ready {ctx}. Arguments em_shown {ctx}. Arguments em_tick {ctx}.
