(*! The circuit-level vocabulary the proofs use: runs over open wires, the
    circuit at rest, the datasheet on the wires.  None of it is in a headline
    statement; Theorems/IPRDefinitions.v is. !*)

Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Backend.Lowering.
Require Import Trustformer.Theorems.IPRDefinitions.

Section AttackerInputs.

  Context (ctx: TFSchedContext).

  Local Notation i_var := (tfs_spec_inputs ctx).
  Local Notation i_sz  := (tfs_spec_inputs_size ctx).
  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).

  (* A command's inputs as the attacker sees them: a secure port reads [None]. *)
  Definition mask_in (input: input_t) : forall v: i_var, option (type_denote (tf_inputs_type i_sz v)) :=
    fun v => match tfs_spec_inputs_class ctx v with Public => Some (input v) | Secret => None end.

End AttackerInputs.

Section CircuitVocab.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation sched := (tfs_schedule ctx cost_limit).
  Context (enc_sz: nat) (enc: tfs_action sched -> bits_t enc_sz)
          (enc_inj: forall a b, enc a = enc b -> a = b)
          (names: Show (tfs_action sched)).

  Local Notation synth := (synth ctx cost_limit enc_sz enc enc_inj names).
  Local Notation tsched := (tf_sched_ctx synth).
  Local Notation reg_t :=
    (@_reg_t (tfs_states tsched) (tfs_inputs tsched) (tfs_outputs tsched) (tfs_ips tsched)).
  Hint Extern 0 (FiniteType reg_t) => exact (_reg_t_finite synth) : typeclass_instances.
  Local Notation circuit_state := (ContextEnv.(env_t) (R synth)).
  Local Notation wires := (forall f, Sig_denote (Sigma synth f)).

  Local Notation s_sz := (tfs_spec_states_size ctx).
  Local Notation i_sz := (tfs_spec_inputs_size ctx).
  Local Notation o_sz := (tfs_spec_outputs_size ctx).
  Local Notation src_sys_state :=
    (ContextEnv.(env_t) (tf_states_type s_sz) * ContextEnv.(env_t) (tf_outputs_type o_sz))%type.
  Local Notation input_t :=
    (forall x : tfs_spec_inputs ctx, type_denote (tf_inputs_type i_sz x)).
  Local Notation pub_inputs := (forall v, option (type_denote (tf_inputs_type i_sz v))).

  (* Kôika's cycle over the lowered rules, from [c0], with [env k] the wires of cycle [k]. *)
  Fixpoint circuit_run (c0: circuit_state) (env: nat -> wires) (n: nat) : circuit_state :=
    match n with
    | 0 => c0
    | S k => interp_cycle (env k) (rules synth) (system_schedule synth) (circuit_run c0 env k)
    end.

  (* The circuit at rest, holding spec state [sp]: ready, its state slots and
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

  (* The IPs' datasheet on a run's wires: a request register raised at cycle [s]
     and left quiet for the flight time is answered on the response wire. *)
  Definition ip_contract (c0: circuit_state) (env: nat -> wires) : Prop :=
    forall (p: tfs_ips tsched) (s: nat),
      let req k := (circuit_run c0 env k).[tf_reg (tfs_drive_reg tsched p)] in
      let sz := ip_req_sz (tfs_ip tsched p) in
      let lat := pred (ip_lat (tfs_ip tsched p)) in
      Bits.slice sz 1 (req s) = Bits.ones 1 ->
      (forall w, s < w < s + lat -> Bits.slice sz 1 (req w) = Bits.zero) ->
      env (s + lat) (ext_input (inr p)) Ob~1 = ip_fn (tfs_ip tsched p) (Bits.slice 0 sz (req s)).

  (* The input ports' values in a cycle, secure ones included. *)
  Definition port_inputs (w: wires) : input_t := fun v => w (ext_input (inl v)) Ob~1.

  (* What the emulator reads off a cycle's wires: [in_cmd] and the public ports. *)
  Definition atk_in : Type := (bits_t 1 * bits_t enc_sz * pub_inputs)%type.

  Definition atk_in_of (w: wires) : atk_in :=
    let cmd := w ext_in_cmd Ob~1 in (fst cmd, fst (snd cmd), mask_in ctx (port_inputs w)).

  (* A cycle offering command [act] with inputs [input]. *)
  Definition offers (w: wires) (act: tfs_action sched) (input: input_t) : Prop :=
    let cmd := w ext_in_cmd Ob~1 in
    fst cmd = Ob~1 /\ fst (snd cmd) = tf_action_encoding synth act
    /\ forall v, port_inputs w v = input v.

End CircuitVocab.
