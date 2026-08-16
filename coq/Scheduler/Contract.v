Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Export Trustformer.Scheduler.DFG.
Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

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

  tfs_spec_outputs : Type;
  tfs_spec_outputs_eq_dec : EqDec tfs_spec_outputs;
  tfs_spec_outputs_fin : FiniteType tfs_spec_outputs;
  tfs_spec_outputs_names : Show tfs_spec_outputs;
  tfs_spec_outputs_size : tfs_spec_outputs -> nat;

  (* Trusted external functions. [] of them reproduces the pre-externs behaviour. *)
  tfs_spec_externs : Type;
  tfs_spec_externs_eq_dec : EqDec tfs_spec_externs;
  tfs_spec_externs_fin : FiniteType tfs_spec_externs;
  tfs_spec_externs_names : Show tfs_spec_externs;
  tfs_spec_externs_sig : tf_externs tfs_spec_externs;

  tfs_spec_action : Type;
  tfs_spec_action_eq_dec : EqDec tfs_spec_action;
  tfs_spec_action_fin : FiniteType tfs_spec_action;
  tfs_spec_action_ops : tfs_spec_action -> @tf_ops tfs_spec_states tfs_spec_inputs tfs_spec_outputs tfs_spec_externs;

  (* whitebox untainting: [] reproduces the blackbox behaviour *)
  tfs_spec_decls : list (decl_rule tfs_spec_states tfs_spec_inputs tfs_spec_outputs tfs_spec_externs)
}.

Inductive _tfs_ops_t {s_t o_t} :=
  | StOp (s: s_t)
  | OutOp (o: o_t).

Definition tfs_ops_tags {s i o e} (ops: list (@tf_op s i o e)) : list (@_tfs_ops_t s o) :=
  flat_map (fun op =>
    match op with
      | tf_assign dst _ => [StOp dst]
      | tf_output dst _ => [OutOp dst]
      | _ => []
    end) ops.

Definition tfs_ops_no_duplicates {s i o e} (ops: list (@tf_op s i o e)) : Prop :=
  NoDup (flat_map (fun op => 
    match op with 
      | tf_assign dst _ => [StOp dst]  
      | tf_output dst _ => [OutOp dst]
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

  tfs_outputs : Type;
  tfs_outputs_size : tfs_outputs -> nat;
  tfs_outputs_names : Show tfs_outputs;
  tfs_outputs_fin : FiniteType tfs_outputs;

  tfs_action : Type;
  tfs_action_fin : FiniteType tfs_action;

  tfs_map_to: ((ContextEnv (FT:=(tfs_spec_states_fin tfs_ctx))).(env_t) (tf_states_type (tfs_spec_states_size tfs_ctx))) -> ((ContextEnv (FT:=tfs_states_fin)).(env_t) (tf_states_type tfs_states_size));
  tfs_map_from: ((ContextEnv (FT:=tfs_states_fin)).(env_t) (tf_states_type tfs_states_size)) -> ((ContextEnv (FT:=(tfs_spec_states_fin tfs_ctx))).(env_t) (tf_states_type (tfs_spec_states_size tfs_ctx)));

  (* returns the operations that should always run (fst) and the operations that should only run when the done signal is set (snd) *)
  tfs_schedule: tfs_action -> list (@tf_op tfs_states tfs_inputs tfs_outputs (tfs_spec_externs tfs_ctx)) * list (@tf_op tfs_states tfs_inputs tfs_outputs (tfs_spec_externs tfs_ctx));
  (* after the done signal is set, the next cycle the module is ready for new input & the modules output is valid (if the above schedule is respected) *)
  tfs_done_signal: tfs_states;
  (* these states have to be reset to Bits.zero if the done signal is set *)
  tfs_reset_states: list tfs_states;

  (* ---- external calls (campaign extern-calls-mvp, decision D8) ----
     Each trusted external function owns one argument and one result register. The
     call itself is issued by a single rule that runs after every action rule, so the
     design contains exactly one [ExternalCall] per function and therefore one Verilog
     driver per port. The argument is read at P1 (it is the value the action just
     wrote) and the result is written at P0 (so the action reads the *previous*
     cycle's result); Koika admits no ordering in which both hops are P0. *)
  tfs_ext_arg: tfs_spec_externs tfs_ctx -> tfs_states;
  tfs_ext_res: tfs_spec_externs tfs_ctx -> tfs_states;

  (* one result register per function, and no register is both an argument and a
     result: [rule_ext] writes all of them in one rule and reads the arguments at P1,
     which would otherwise observe a sibling's write *)
  tfs_ext_res_inj: forall f g, tfs_ext_res f = tfs_ext_res g -> f = g;
  tfs_ext_res_not_arg: forall f g, tfs_ext_res f <> tfs_ext_arg g;

  (* [rule_ext] writes the result registers at P0, after the action rule ran. A P0
     write is blocked by an earlier read1, write0 or write1, so no result register may
     be the done signal (read at P1 by the done gate), a reset register (written at
     P1) or a target of the scheduled ops (written at P0). *)
  tfs_ext_res_not_done: forall f, tfs_ext_res f <> tfs_done_signal;
  tfs_ext_res_not_reset: forall f, ~ In (tfs_ext_res f) tfs_reset_states;
  tfs_ext_res_not_scheduled: forall a f,
    ~ In (StOp (tfs_ext_res f)) (tfs_ops_tags (fst (tfs_schedule a) ++ snd (tfs_schedule a)));

  (* [rule_ext] reads the argument registers at P1, which a P1 write would block *)
  tfs_ext_arg_not_reset: forall f, ~ In (tfs_ext_arg f) tfs_reset_states;

  tfs_schedule_no_duplicates: forall a,
    tfs_ops_no_duplicates (fst (tfs_schedule a) ++ snd (tfs_schedule a));

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
  (* The scheduled module calls the same external functions as the spec. *)
  Local Notation e_var := (tfs_spec_externs (tfs_ctx tf_sched_ctx)).
  Local Notation e_sig := (tfs_spec_externs_sig (tfs_ctx tf_sched_ctx)).
  
  Local Notation st_env := (ContextEnv.(env_t) (tf_states_type s_sz)).
  Local Notation out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation sys_state_t := (st_env * out_env)%type.
  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).

  Hint Extern 0 (FiniteType s_var) => exact (tfs_states_fin (tf_sched_ctx)) : typeclass_instances.
  Hint Extern 0 (FiniteType i_var) => exact (tfs_inputs_fin (tf_sched_ctx)) : typeclass_instances.
  Hint Extern 0 (FiniteType o_var) => exact (tfs_outputs_fin (tf_sched_ctx)) : typeclass_instances.
  Hint Extern 0 (FiniteType e_var) => exact (tfs_spec_externs_fin (tfs_ctx tf_sched_ctx)) : typeclass_instances.
  Hint Extern 0 (tf_externs e_var) => exact e_sig : typeclass_instances.

  Definition tfs_get_updates
    (ops: list (@tf_op s_var i_var o_var e_var))
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

  (* One update per external function: its result register takes the denotation of the
     function applied to its argument register. Widths are reconciled with [convert],
     mirroring [tf_eval_expr]'s [tf_ext] case and the hardware's [synth_convert]. *)
  Definition tfs_ext_updates (st: st_env) : list (tf_update s_sz o_sz) :=
    List.map
      (fun f => tf_st_update s_sz o_sz (tfs_ext_res tf_sched_ctx f)
                  (convert (tfe_denote f (convert (st.[tfs_ext_arg tf_sched_ctx f])))))
      (finite_elements (T:=e_var)).

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

    (* The external calls run in their own rule *after* the action rule, reading the
       argument registers the action just wrote (D8), so they are evaluated on the
       state the action produced. They only ever write result registers, which the
       action never writes, so putting them first in the list is an override. *)
    let ext_updates := tfs_ext_updates (ContextEnv.(create) (fun x => find_st_val x updates sys_state)) in

    ( 
      ContextEnv.(create) (fun x => find_st_val x (ext_updates ++ updates) sys_state),
      ContextEnv.(create) (fun x => find_out_val x (ext_updates ++ updates) sys_state)
    ).

End SchedulerSpec.
