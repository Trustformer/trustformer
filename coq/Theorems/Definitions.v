(*! The vocabulary the guarantees are stated in: the attacker's view and clock,
    the circuit Lowering emits, its trusted environment, and IPR's machines.  With
    the statement files in coq/Theorems/, this is the whole proof-layer audit. !*)

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
Require IPR.Common IPR.Machine IPR.Driver IPR.Emulator IPR.Definition.
Import IPR.Common (result(..)) IPR.Driver (dproc(..)).

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

  (* A command's inputs and the outputs as the attacker sees them: a secure port
     reads [None]. *)
  Definition mask_in (input: input_t) : forall v: i_var, option (type_denote (tf_inputs_type i_sz v)) :=
    fun v => match tfs_spec_inputs_class ctx v with Public => Some (input v) | Secret => None end.

  Definition mask_out (outs: src_out_env) : forall o: o_var, option (type_denote (tf_outputs_type o_sz o)) :=
    fun o => match tfs_spec_outputs_class ctx o with Public => Some outs.[o] | Secret => None end.

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
(* The circuit Lowering emits, its trusted environment, and the spec.   *)
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

  Local Notation pub_inputs := (forall v, option (type_denote (tf_inputs_type i_sz v))).
  Local Notation pub_outputs := (forall o, option (type_denote (tf_outputs_type o_sz o))).

  (* ================================================================ *)
  (* What the attacker sees, and what the spec answers.               *)
  (* ================================================================ *)

  (* WHAT THE ATTACKER SEES in a cycle: ready on [in_cmd], and the public output
     ports, which show the outputs as the cycle leaves them. *)
  Definition atk_out : Type := (bits_t 1 * pub_outputs)%type.

  Definition circuit_outputs (c: circuit_state) : src_out_env :=
    ContextEnv.(create) (fun o => c.[tf_out o]).

  Definition atk_out_of (c c': circuit_state) : atk_out :=
    (c.[tf_ready], mask_out ctx (circuit_outputs c')).

  (* WHAT THE SPEC IS ASKED: its public outputs, or to run a command on public
     inputs [pin]. *)
  Inductive query := Peek | Run (act: tfs_action sched) (pin: pub_inputs).

  (* A command's inputs: the public ones from [pin], the secure ones from [ports]. *)
  Definition fill (pin: pub_inputs) (ports: input_t) : input_t :=
    fun v => match tfs_spec_inputs_class ctx v, pin v with
             | Public, Some x => x
             | Public, None => Bits.zero
             | Secret, _ => ports v
             end.

  Definition spec_init : src_sys_state :=
    (ContextEnv.(create) (tfs_spec_states_init ctx), ContextEnv.(create) (fun _ => Bits.zero)).

  (* ================================================================ *)
  (* The trusted environment: whatever drives the wires the attacker  *)
  (* does not.  With no IP and no secure port, it drives none.        *)
  (* ================================================================ *)

  Local Notation req_t p := (R synth (tf_reg (tfs_drive_reg tsched p))).

  (* A TRUSTED IP: its answer in a cycle, from what its request register held at
     the start of every cycle so far, this one last. *)
  Definition trusted_ip : Type :=
    forall p: tfs_ips tsched, list (req_t p) -> bits_t (ip_resp_sz (tfs_ip tsched p)).

  (* ITS DATASHEET: a request strobed and then left quiet is answered, [lat]
     cycles on, with [ip_fn] of its payload. *)
  Definition datasheet (ip: trusted_ip) : Prop :=
    forall p (h t: list (req_t p)) (q: req_t p),
      let sz := ip_req_sz (tfs_ip tsched p) in
      let lat := pred (ip_lat (tfs_ip tsched p)) in
      Bits.slice sz 1 q = Bits.ones 1 -> length t = lat ->
      (forall q', In q' (firstn (pred lat) t) -> Bits.slice sz 1 q' = Bits.zero) ->
      ip p (h ++ q :: t) = ip_fn (tfs_ip tsched p) (Bits.slice 0 sz q).

  (* A TRUSTED SOURCE on the secure input ports: their values, from the outputs
     shown at every command taken so far, this one last. *)
  Definition trusted_source : Type := list src_out_env -> input_t.

  (* THE WIRES OF A CYCLE: the attacker's [w], except the secure ports, the IPs'
     answers, and the acknowledgements a trusted party gives, which the trusted
     environment drives. *)
  Definition close (ip: trusted_ip) (src: trusted_source) (c: circuit_state)
      (hs: forall p, list (req_t p)) (seen: list src_out_env) (w: wires) : wires :=
    fun f => match f return Sig_denote (Sigma synth f) with
             | ext_in_cmd => w ext_in_cmd
             | ext_input (inl v) =>
                 match tfs_spec_inputs_class ctx v with
                 | Public => w (ext_input (inl v))
                 | Secret => fun _ => src (seen ++ [circuit_outputs c]) v
                 end
             | ext_input (inr p) => fun _ => ip p (hs p ++ [c.[tf_reg (tfs_drive_reg tsched p)]])
             | ext_output o =>
                 match tfs_spec_outputs_class ctx o with
                 | Public => w (ext_output o)
                 | Secret => fun _ => Ob~0
                 end
             | ext_ip_req _ => fun _ => Ob~0
             end.

  (* Whether the circuit takes a command in this cycle: it is ready, and [in_cmd]
     is valid and names an action. *)
  Definition takes (c: circuit_state) (w: wires) : bool :=
    let cmd := w ext_in_cmd Ob~1 in
    Bits.single c.[tf_ready] && Bits.single (fst cmd)
    && existsb (fun a => beq_dec (enc a) (fst (snd cmd))) (@finite_elements _ (tfs_action_fin sched)).

  (* ================================================================ *)
  (* IPR's two machines and its driver.                               *)
  (* ================================================================ *)

  (* THE CIRCUIT AS AN IPR MACHINE: a step is one cycle on the attacker's wires,
     closed over the trusted environment, which keeps each IP's requests and the
     outputs the source has been shown. *)
  Definition closed_circuit (ip: trusted_ip) (src: trusted_source)
    : IPR.Machine.machine wires atk_out := {|
    IPR.Machine.state := (circuit_state * (forall p, list (req_t p)) * list src_out_env)%type;
    IPR.Machine.init := (ContextEnv.(create) (r synth), fun _ => [], []);
    IPR.Machine.step := fun '(c, hs, seen) w res =>
      let c' := interp_cycle (close ip src c hs seen w) (rules synth) (system_schedule synth) c in
      res = Result (atk_out_of c c')
                   (c', fun p => hs p ++ [c.[tf_reg (tfs_drive_reg tsched p)]],
                    if takes c w then seen ++ [circuit_outputs c] else seen);
    IPR.Machine.reset := fun _ s' => s' = (ContextEnv.(create) (r synth), fun _ => [], []) |}.

  (* THE SPEC AS AN IPR MACHINE, closed over the same source and answering with
     public outputs only. *)
  Definition closed_spec (src: trusted_source) : IPR.Machine.machine query pub_outputs := {|
    IPR.Machine.state := (src_sys_state * list src_out_env)%type;
    IPR.Machine.init := (spec_init, []);
    IPR.Machine.step := fun '(sp, seen) q res =>
      res = match q with
            | Peek => Result (mask_out ctx (snd sp)) (sp, seen)
            | Run act pin =>
                let seen' := seen ++ [snd sp] in
                let sp' := run act sp (fill pin (src seen')) in
                Result (mask_out ctx (snd sp')) (sp', seen')
            end;
    IPR.Machine.reset := fun _ s' => s' = (spec_init, []) |}.

  (* Wires offering nothing, and wires offering [act] on public inputs [pin]. *)
  Definition idle_wires : wires :=
    fun f => match f return Sig_denote (Sigma synth f) with
             | ext_in_cmd => fun _ => (Ob~0, (Bits.zero, tt))
             | ext_input _ => fun _ => Bits.zero
             | ext_output _ => fun _ => Ob~0
             | ext_ip_req _ => fun _ => Ob~0
             end.

  Definition offer_wires (act: tfs_action sched) (pin: pub_inputs) : wires :=
    fun f => match f return Sig_denote (Sigma synth f) with
             | ext_in_cmd => fun _ => (Ob~1, (tf_action_encoding synth act, tt))
             | ext_input (inl v) => fun _ => fill pin (fun _ => Bits.zero) v
             | ext_input (inr _) => fun _ => Bits.zero
             | ext_output _ => fun _ => Ob~0
             | ext_ip_req _ => fun _ => Ob~0
             end.

  (* THE DRIVER: a spec operation as cycles -- offer it, idle until ready is seen
     again, then read the public outputs off one more idle cycle. *)
  Definition driver : IPR.Driver.driver wires atk_out query pub_outputs :=
    fun q => match q with
             | Peek => DBind (DCall idle_wires) (fun o => DRet (snd o))
             | Run act pin =>
                 DBind (DCall (offer_wires act pin)) (fun _ =>
                 DBind (DWhile (DBind (DCall idle_wires) (fun o => DRet (negb (Bits.single (fst o)))))
                               (DRet tt)) (fun _ =>
                 DBind (DCall idle_wires) (fun o => DRet (snd o))))
             end.

End CircuitWorld.

Arguments Peek {ctx cost_limit}. Arguments Run {ctx cost_limit}.
