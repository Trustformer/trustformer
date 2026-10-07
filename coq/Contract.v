Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Export Trustformer.DFG.

(* Confidentiality classification of a spec variable's port: [Public] is
   attacker-visible and memory-mappable, [Secret] is everything else, and
   [Lowering.ext_fn_specs] generates the declared class into the name. *)
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

  tfs_spec_ips : Type;
  tfs_spec_ips_eq_dec : EqDec tfs_spec_ips;
  tfs_spec_ips_fin : FiniteType tfs_spec_ips;
  tfs_spec_ips_names : Show tfs_spec_ips;
  tfs_spec_ip : tfs_spec_ips -> ip_decl;

  tfs_spec_action : Type;
  tfs_spec_action_eq_dec : EqDec tfs_spec_action;
  tfs_spec_action_fin : FiniteType tfs_spec_action;
  tfs_spec_action_ops : tfs_spec_action ->
    @tf_ops tfs_spec_states tfs_spec_inputs tfs_spec_outputs tfs_spec_ips;

  (* whitebox untainting: [] reproduces the blackbox behaviour *)
  tfs_spec_decls : list (decl_packet tfs_spec_states tfs_spec_inputs tfs_spec_outputs tfs_spec_ips)
}.

Inductive _tfs_ops_t {s_t o_t} :=
  | StOp (s: s_t)
  | OutOp (o: o_t).

Definition tfs_ops_no_duplicates {s i o p} (ops: list (@tf_op s i o p)) : Prop :=
  NoDup (flat_map (fun op =>
    match op with
      | tf_assign dst _ => [StOp dst]
      | tf_output dst _ => [OutOp dst]
      | tf_call _ dst _ => [StOp dst]
      | _ => []
    end) ops).

Record TFSchedule := {
  tfs_ctx: TFSchedContext;

  tfs_states : Type;
  tfs_states_size : tfs_states -> nat;
  tfs_states_fin : FiniteType tfs_states;
  tfs_states_names : Show tfs_states;
  tfs_states_init : forall x: tfs_states, tf_states_type tfs_states_size x;

  (* Mirrored from the context like the sizes and names.  [tfs_drive_reg] is the
     register carrying an IP request's {strobe, payload}. *)
  tfs_ips : Type;
  tfs_ips_fin : FiniteType tfs_ips;
  tfs_ips_names : Show tfs_ips;
  tfs_ip : tfs_ips -> ip_decl;
  tfs_drive_reg : tfs_ips -> tfs_states;
  tfs_drive_reg_size : forall p,
    tfs_states_size (tfs_drive_reg p) = 1 + ip_req_sz (tfs_ip p);

  (* The design's inputs PLUS one per IP response.  The response summand is what
     lets the lowering read an answer without the spec having a port for it. *)
  tfs_inputs : Type;
  tfs_inputs_size : tfs_inputs -> nat;
  tfs_inputs_names : Show tfs_inputs;
  tfs_inputs_fin : FiniteType tfs_inputs;
  tfs_inputs_class : tfs_inputs -> port_class;
  (* A response is read LIVE, not latched at action start, and routed to
     [ext_ip_resp]. *)
  tfs_inputs_resp : tfs_inputs -> option tfs_ips;
  tfs_inputs_resp_size : forall v p,
    tfs_inputs_resp v = Some p -> tfs_inputs_size v = ip_resp_sz (tfs_ip p);

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
  (* [Empty_set]: a call is a spec-level op, so a lowered schedule carries none. *)
  tfs_schedule: tfs_action -> list (@tf_op tfs_states tfs_inputs tfs_outputs Empty_set)
                            * list (@tf_op tfs_states tfs_inputs tfs_outputs Empty_set);
  (* after the done signal is set, the next cycle the module is ready for new input & the modules output is valid (if the above schedule is respected) *)
  tfs_done_signal: tfs_states;
  (* these states have to be reset to Bits.zero if the done signal is set *)
  tfs_reset_states: list tfs_states;

  tfs_schedule_no_duplicates: forall a, tfs_ops_no_duplicates (fst (tfs_schedule a) ++ snd (tfs_schedule a));

  (* the done signal is a single bit; the HW gates the done-branch on its low bit
     while the spec gates on `done_val <> 0`, so they must coincide *)
  tfs_done_signal_size: tfs_states_size tfs_done_signal = 1;

  (* The always-ops (fst) recompute done every cycle; with
     tfs_schedule_no_duplicates that leaves done to them alone, which the HW
     needs because the done-gate reads the register at P1 before the P0 writes. *)
  tfs_done_signal_assigned_by_always: forall a,
    In (StOp tfs_done_signal)
       (flat_map (fun op =>
          match op with
          | tf_assign dst _ => [StOp dst]
          | tf_output dst _ => [OutOp dst]
          | tf_call _ dst _ => [StOp dst]
          | _ => []
          end) (fst (tfs_schedule a)));

  (* the buffer-reset registers are pairwise distinct; the HW resets them with a
     fold of P1 writes, whose validity requires no register is written twice *)
  tfs_reset_states_nodup: NoDup tfs_reset_states;

  (* the buffer-reset registers are reset to Bits.zero by the HW; the spec resets
     them to their init value, so those must coincide for the reset states *)
  tfs_reset_states_init_zero: forall v, In v tfs_reset_states -> tfs_states_init v = Bits.zero;
}.

(* The two records carry their own [FiniteType], [Show] and [EqDec] evidence,
   and resolution cannot see through a projection on its own.  Matching on the
   projection fires for any context, so each file that opens one needs no hints
   of its own. *)

#[export] Hint Extern 0 (FiniteType (tfs_spec_states ?c))  => exact (tfs_spec_states_fin c)  : typeclass_instances.
#[export] Hint Extern 0 (FiniteType (tfs_spec_inputs ?c))  => exact (tfs_spec_inputs_fin c)  : typeclass_instances.
#[export] Hint Extern 0 (FiniteType (tfs_spec_outputs ?c)) => exact (tfs_spec_outputs_fin c) : typeclass_instances.
#[export] Hint Extern 0 (FiniteType (tfs_spec_ips ?c))     => exact (tfs_spec_ips_fin c)     : typeclass_instances.
#[export] Hint Extern 0 (FiniteType (tfs_spec_action ?c))  => exact (tfs_spec_action_fin c)  : typeclass_instances.
#[export] Hint Extern 0 (Show (tfs_spec_states ?c))        => exact (tfs_spec_states_names c)  : typeclass_instances.
#[export] Hint Extern 0 (Show (tfs_spec_inputs ?c))        => exact (tfs_spec_inputs_names c)  : typeclass_instances.
#[export] Hint Extern 0 (Show (tfs_spec_outputs ?c))       => exact (tfs_spec_outputs_names c) : typeclass_instances.
#[export] Hint Extern 0 (Show (tfs_spec_ips ?c))           => exact (tfs_spec_ips_names c)     : typeclass_instances.
#[export] Hint Extern 0 (EqDec (tfs_spec_states ?c))       => exact (tfs_spec_states_eq_dec c)  : typeclass_instances.
#[export] Hint Extern 0 (EqDec (tfs_spec_inputs ?c))       => exact (tfs_spec_inputs_eq_dec c)  : typeclass_instances.
#[export] Hint Extern 0 (EqDec (tfs_spec_outputs ?c))      => exact (tfs_spec_outputs_eq_dec c) : typeclass_instances.
#[export] Hint Extern 0 (EqDec (tfs_spec_ips ?c))          => exact (tfs_spec_ips_eq_dec c)     : typeclass_instances.
#[export] Hint Extern 0 (EqDec (tfs_spec_action ?c))       => exact (tfs_spec_action_eq_dec c)  : typeclass_instances.

#[export] Hint Extern 0 (FiniteType (tfs_states ?s))   => exact (tfs_states_fin s)   : typeclass_instances.
#[export] Hint Extern 0 (FiniteType (tfs_inputs ?s))   => exact (tfs_inputs_fin s)   : typeclass_instances.
#[export] Hint Extern 0 (FiniteType (tfs_outputs ?s))  => exact (tfs_outputs_fin s)  : typeclass_instances.
#[export] Hint Extern 0 (FiniteType (tfs_ips ?s))      => exact (tfs_ips_fin s)      : typeclass_instances.
#[export] Hint Extern 0 (FiniteType (tfs_action ?s))   => exact (tfs_action_fin s)   : typeclass_instances.
#[export] Hint Extern 0 (Show (tfs_states ?s))         => exact (tfs_states_names s)  : typeclass_instances.
#[export] Hint Extern 0 (Show (tfs_inputs ?s))         => exact (tfs_inputs_names s)  : typeclass_instances.
#[export] Hint Extern 0 (Show (tfs_outputs ?s))        => exact (tfs_outputs_names s) : typeclass_instances.
#[export] Hint Extern 0 (Show (tfs_ips ?s))            => exact (tfs_ips_names s)     : typeclass_instances.

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
    (ops: list (@tf_op s_var i_var o_var Empty_set))
    (sys_state: sys_state_t)
    (input: input_t) :=
    List.map (fun op => tf_op_step_updates s_sz i_sz o_sz no_ips op sys_state input) ops.

  Definition tfs_reset_updates
    (states_to_reset: list s_var)
    :=
    List.map (fun v => tf_st_update s_sz o_sz v (tfs_states_init tf_sched_ctx v)) states_to_reset.

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
