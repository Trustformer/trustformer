(*! The vocabulary Theorems/IPR.v is stated in: the circuit Lowering emits, its
    trusted environment, the spec, and IPR's driver.  With IPR.v, this is the
    whole audit of the IPR guarantee. !*)

Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Export Trustformer.Scheduler.Schedule.
Require Import Trustformer.Backend.Lowering.
Require IPR.Common IPR.Machine IPR.Driver IPR.Emulator IPR.Definition.
Import IPR.Common (result(..)) IPR.Driver (dproc(..)).

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

(* The scheduler record is huge; deprioritise unfolding it during conversion. *)
Strategy 1000 [tfs_schedule].

Section AttackerOutputs.

  Context (ctx: TFSchedContext).

  Local Notation o_var := (tfs_spec_outputs ctx).
  Local Notation o_sz  := (tfs_spec_outputs_size ctx).
  Local Notation src_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).

  (* The outputs as the attacker sees them: a Secret port reads [None]. *)
  Definition mask_out (outs: src_out_env) : forall o: o_var, option (type_denote (tf_outputs_type o_sz o)) :=
    fun o => match tfs_spec_outputs_class ctx o with Public => Some outs.[o] | Secret => None end.

End AttackerOutputs.

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
