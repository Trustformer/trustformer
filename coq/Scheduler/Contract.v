Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Export Trustformer.Scheduler.DFG.
Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

(* Confidentiality classification of a spec variable's port.

   [Public]  attacker-visible by design.  The confidentiality guarantee
             quantifies over exactly these, and only these may be memory-mapped.
   [Secret]  may carry a secret, so it is outside that guarantee and must never
             be attacker-visible.  Over-classifying is safe: a port that happens
             to carry nothing sensitive but must not be host-driven -- a
             protected reset request, say -- is [Secret] too, because "never
             bus-mapped" is the protection wanted and a separate class would buy
             vocabulary rather than safety.

   The classification is DECLARED here and generated into the port name by
   [TypedSynthesis.ext_fn_specs].  It is deliberately not part of the variable's
   own name: a hand-written prefix can disagree with the declaration and nothing
   would catch it. *)
Inductive port_class := Public | Secret.

Definition class_tag (c: port_class) : string :=
  match c with Public => "pub" | Secret => "sec" end.

Record TFSchedContext := {
  tfs_spec_states : Type;
  tfs_spec_states_eq_dec : EqDec tfs_spec_states;
  tfs_spec_states_fin : FiniteType tfs_spec_states;
  tfs_spec_states_names : Show tfs_spec_states;
  tfs_spec_states_size : tfs_spec_states -> nat;
  tfs_spec_states_init : forall x: tfs_spec_states, tf_states_type tfs_spec_states_size x;

  tfs_spec_inputs : Type;
  tfs_spec_inputs_eq_dec : EqDec tfs_spec_inputs;
  tfs_spec_inputs_fin : FiniteType tfs_spec_inputs;
  tfs_spec_inputs_names : Show tfs_spec_inputs;
  tfs_spec_inputs_size : tfs_spec_inputs -> nat;
  tfs_spec_inputs_class : tfs_spec_inputs -> port_class;

  tfs_spec_outputs : Type;
  tfs_spec_outputs_eq_dec : EqDec tfs_spec_outputs;
  tfs_spec_outputs_fin : FiniteType tfs_spec_outputs;
  tfs_spec_outputs_names : Show tfs_spec_outputs;
  tfs_spec_outputs_size : tfs_spec_outputs -> nat;
  tfs_spec_outputs_class : tfs_spec_outputs -> port_class;

  tfs_spec_ip_req : tfs_spec_inputs -> option tfs_spec_outputs;
  tfs_spec_ip_lat : tfs_spec_inputs -> nat;

  (* BOTH ends of an IP link are Secret, and this is enforced HERE -- as a field
     of the context -- so a TFSchedContext naming a Public request or response
     port cannot be constructed at all.  A free-standing Prop would have to be
     remembered at every use site; a field is discharged once, where the ports
     are declared, and is then available to every proof for free.

     Why it must hold.  A request port moves mid-action, in a data-dependent
     way, by construction -- that is the whole point of a drive.  A PUBLIC port
     doing that is directly attacker-visible timing, which is the thing IPR
     exists to rule out (Probe 2d: [driven_ports] admits only Secret ports, and
     the proof obligation and the security obligation coincide).  A public
     response port is the mirror image: it would let the attacker read the IP's
     answer straight off the wire.

     This covers every port named in an IP DECLARATION.  The companion condition
     -- that a [tf_call] may only name a declared (req,resp) pair -- is what
     extends it to every port named by a CALL. *)
  tfs_spec_ip_secret :
    forall v o, tfs_spec_ip_req v = Some o ->
      tfs_spec_inputs_class v = Secret /\ tfs_spec_outputs_class o = Secret;

  tfs_spec_action : Type;
  tfs_spec_action_eq_dec : EqDec tfs_spec_action;
  tfs_spec_action_fin : FiniteType tfs_spec_action;
  tfs_spec_action_ops : tfs_spec_action -> @tf_ops tfs_spec_states tfs_spec_inputs tfs_spec_outputs;

  (* whitebox untainting: [] reproduces the blackbox behaviour *)
  tfs_spec_decls : list (decl_rule tfs_spec_states tfs_spec_inputs tfs_spec_outputs)
}.

Inductive _tfs_ops_t {s_t o_t} :=
  | StOp (s: s_t)
  | OutOp (o: o_t).

Definition tfs_ops_no_duplicates {s i o} (ops: list (@tf_op s i o)) : Prop :=
  NoDup (flat_map (fun op => 
    match op with 
      | tf_assign dst _ => [StOp dst]  
      | tf_output dst _ => [OutOp dst]
      | tf_call req _ dst _ _ => [OutOp req; StOp dst]  (* a call writes BOTH *)
      | _ => []
    end) ops).

Record TFSchedule := {
  tfs_ctx: TFSchedContext;

  tfs_states : Type;
  tfs_states_size : tfs_states -> nat;
  tfs_states_fin : FiniteType tfs_states;
  tfs_states_names : Show tfs_states;
  tfs_states_init : forall x: tfs_states, tf_states_type tfs_states_size x;

  tfs_inputs : Type;
  tfs_inputs_size : tfs_inputs -> nat;
  tfs_inputs_names : Show tfs_inputs;
  tfs_inputs_fin : FiniteType tfs_inputs;
  (* Mirrored from the context, like size and names: [tfs_inputs] is the spec's
     input type, but that is not definitionally visible through an abstract
     [TFSchedule], so the classification has to be carried across. *)
  tfs_inputs_class : tfs_inputs -> port_class;
  (* Also mirrored from the context: which inputs are IP RESPONSE ports.  These
     are the only inputs that are not latched at action start -- a response
     arrives mid-action, so latching it would read the value from BEFORE the
     request was even driven.  The lowering has to be able to tell them apart,
     and [tfs_spec_ip_req] is not definitionally visible through an abstract
     [TFSchedule], so it is carried across exactly as the class is. *)
  tfs_inputs_is_resp : tfs_inputs -> bool;

  tfs_outputs : Type;
  tfs_outputs_size : tfs_outputs -> nat;
  tfs_outputs_names : Show tfs_outputs;
  tfs_outputs_fin : FiniteType tfs_outputs;
  tfs_outputs_class : tfs_outputs -> port_class;

  tfs_action : Type;
  tfs_action_fin : FiniteType tfs_action;

  tfs_map_to: ((ContextEnv (FT:=(tfs_spec_states_fin tfs_ctx))).(env_t) (tf_states_type (tfs_spec_states_size tfs_ctx))) -> ((ContextEnv (FT:=tfs_states_fin)).(env_t) (tf_states_type tfs_states_size));
  tfs_map_from: ((ContextEnv (FT:=tfs_states_fin)).(env_t) (tf_states_type tfs_states_size)) -> ((ContextEnv (FT:=(tfs_spec_states_fin tfs_ctx))).(env_t) (tf_states_type (tfs_spec_states_size tfs_ctx)));

  (* returns the operations that should always run (fst) and the operations that should only run when the done signal is set (snd) *)
  tfs_schedule: tfs_action -> list (@tf_op tfs_states tfs_inputs tfs_outputs) * list (@tf_op tfs_states tfs_inputs tfs_outputs);
  (* after the done signal is set, the next cycle the module is ready for new input & the modules output is valid (if the above schedule is respected) *)
  tfs_done_signal: tfs_states;
  (* these states have to be reset to Bits.zero if the done signal is set *)
  tfs_reset_states: list tfs_states;

  tfs_schedule_no_duplicates: forall a, tfs_ops_no_duplicates (fst (tfs_schedule a) ++ snd (tfs_schedule a));

  (* the done signal is a single bit; the HW gates the done-branch on its low bit
     while the spec gates on `done_val <> 0`, so they must coincide *)
  tfs_done_signal_size: tfs_states_size tfs_done_signal = 1;

  (* the done signal is (re)computed every cycle by the always-ops (fst); combined
     with tfs_schedule_no_duplicates this guarantees the done register is NOT written
     by the done-ops (snd), which the HW requires since it reads the done register at
     P1 in the done-gate before the done-ops run their P0 writes *)
  tfs_done_signal_assigned_by_always: forall a,
    In (StOp tfs_done_signal)
       (flat_map (fun op =>
          match op with
          | tf_assign dst _ => [StOp dst]
          | tf_output dst _ => [OutOp dst]
          | tf_call req _ dst _ _ => [OutOp req; StOp dst]  (* a call writes BOTH *)
          | _ => []
          end) (fst (tfs_schedule a)));

  (* the buffer-reset registers are pairwise distinct; the HW resets them with a
     fold of P1 writes, whose validity requires no register is written twice *)
  tfs_reset_states_nodup: NoDup tfs_reset_states;

  (* the buffer-reset registers are reset to Bits.zero by the HW; the spec resets
     them to their init value, so those must coincide for the reset states *)
  tfs_reset_states_init_zero: forall v, In v tfs_reset_states -> tfs_states_init v = Bits.zero;
}.

Section SchedulerSpec.

  Context (tf_sched_ctx : TFSchedule).

  Local Notation s_var := (tfs_states tf_sched_ctx).
  Local Notation i_var := (tfs_inputs tf_sched_ctx).
  Local Notation o_var := (tfs_outputs tf_sched_ctx).
  Local Notation s_sz := (tfs_states_size tf_sched_ctx).
  Local Notation i_sz := (tfs_inputs_size tf_sched_ctx).
  Local Notation o_sz := (tfs_outputs_size tf_sched_ctx).
  
  Local Notation st_env := (ContextEnv.(env_t) (tf_states_type s_sz)).
  Local Notation out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation sys_state_t := (st_env * out_env)%type.
  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).

  Hint Extern 0 (FiniteType s_var) => exact (tfs_states_fin (tf_sched_ctx)) : typeclass_instances.
  Hint Extern 0 (FiniteType i_var) => exact (tfs_inputs_fin (tf_sched_ctx)) : typeclass_instances.
  Hint Extern 0 (FiniteType o_var) => exact (tfs_outputs_fin (tf_sched_ctx)) : typeclass_instances.

  Definition tfs_get_updates
    (ops: list (@tf_op s_var i_var o_var))
    (sys_state: sys_state_t)
    (input: input_t) :=
    List.map (fun op => tf_op_step_updates s_sz i_sz o_sz op sys_state input) ops.

  (* Definition tfs_reset_states_list
    (states_to_reset: list s_var)
    (sys_state: sys_state_t)
    : sys_state_t :=
    List.fold_left (fun (st : sys_state_t) (v : s_var) =>
      let st_env' := ContextEnv.(putenv) (fst st) v (tfs_states_init tf_sched_ctx v) in
      (st_env', snd st)
    ) states_to_reset sys_state. *)

  Definition tfs_reset_updates
    (states_to_reset: list s_var)
    :=
    List.map (fun v => tf_st_update s_sz o_sz v (tfs_states_init tf_sched_ctx v)) states_to_reset.

  (* Definition tfs_commit_updates
    updates
    (sys_state: sys_state_t)
    : sys_state_t :=
    List.fold_left (fun (st : sys_state_t) u => tf_op_step_commit s_sz o_sz st u) updates sys_state. *)

  Fixpoint find_st_update (x: s_var) (ups: list (tf_update s_sz o_sz)) : option (bits_t (s_sz x)) :=
    match ups with
    | nil => None
    | u :: rest =>
        match u with
        | tf_st_update _ _ var val =>
            match eq_dec var x with
            | left eq_proof => 
                Some (match eq_proof in (_ = y) return bits_t (s_sz y) with
                      | eq_refl => val
                      end)
            | right _ => find_st_update x rest
            end
        (* a call writes a state var too, and must be found here or the spec's
           state update would be invisible to the simulation *)
        | tf_call_update _ _ _ _ var val =>
            match eq_dec var x with
            | left eq_proof =>
                Some (match eq_proof in (_ = y) return bits_t (s_sz y) with
                      | eq_refl => val
                      end)
            | right _ => find_st_update x rest
            end
        | _ => find_st_update x rest
        end
    end.

  Definition find_st_val (x: s_var) (ups: list (tf_update s_sz o_sz)) (sys_state: sys_state_t) : bits_t (s_sz x) :=
    match find_st_update x ups with
    | Some v => v
    | None => (fst sys_state).[x]
    end.

  Fixpoint find_out_update (x: o_var) (ups: list (tf_update s_sz o_sz)) : option (bits_t (o_sz x)) :=
    match ups with
    | nil => None
    | u :: rest =>
        match u with
        | tf_out_update _ _ var val =>
            match eq_dec var x with
            | left eq_proof => 
                Some (match eq_proof in (_ = y) return bits_t (o_sz y) with
                      | eq_refl => val
                      end)
            | right _ => find_out_update x rest
            end
        (* a call writes its REQUEST port here *)
        | tf_call_update _ _ var val _ _ =>
            match eq_dec var x with
            | left eq_proof =>
                Some (match eq_proof in (_ = y) return bits_t (o_sz y) with
                      | eq_refl => val
                      end)
            | right _ => find_out_update x rest
            end
        | _ => find_out_update x rest
        end
    end.

  Definition find_out_val (x: o_var) (ups: list (tf_update s_sz o_sz)) (sys_state: sys_state_t) : bits_t (o_sz x) :=
    match find_out_update x ups with
    | Some v => v
    | None => (snd sys_state).[x]
    end.

  Definition tfs_next_cycle
    (action: tfs_action tf_sched_ctx)
    (sys_state: sys_state_t)
    (input: input_t)
    : sys_state_t :=
    let always_ops := fst (tfs_schedule tf_sched_ctx action) in
    let done_ops := snd (tfs_schedule tf_sched_ctx action) in

    (* Evaluate ALL updates based on the clean initial cycle state *)
    let always_updates := tfs_get_updates always_ops sys_state input in
    let done_updates := tfs_get_updates done_ops sys_state input in
    let reset_updates := tfs_reset_updates (tfs_reset_states tf_sched_ctx) in
     
    let done_val := find_st_val (tfs_done_signal tf_sched_ctx) always_updates sys_state in

    let updates := if beq_dec done_val Bits.zero then always_updates else (reset_updates ++ done_updates ++ always_updates) in

    ( 
      ContextEnv.(create) (fun x => find_st_val x updates sys_state),
      ContextEnv.(create) (fun x => find_out_val x updates sys_state)
    ).

End SchedulerSpec.
