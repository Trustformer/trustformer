Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Record TFSchedContext := {
  tfs_spec_states : Type;
  tfs_spec_states_fin : FiniteType tfs_spec_states;
  tfs_spec_states_names : Show tfs_spec_states;
  tfs_spec_states_size : tfs_spec_states -> nat;
  tfs_spec_states_init : forall x: tfs_spec_states, tf_states_type tfs_spec_states_size x;

  tfs_spec_inputs : Type;
  tfs_spec_inputs_fin : FiniteType tfs_spec_inputs;
  tfs_spec_inputs_size : tfs_spec_inputs -> nat;

  tfs_spec_outputs : Type;
  tfs_spec_outputs_fin : FiniteType tfs_spec_outputs;
  tfs_spec_outputs_size : tfs_spec_outputs -> nat;

  tfs_spec_action : Type;
  tfs_spec_action_fin : FiniteType tfs_spec_action;
  tfs_spec_action_ops : tfs_spec_action -> @tf_ops tfs_spec_states tfs_spec_inputs tfs_spec_outputs
}.

Section TrustformerScheduler.

  (* 

      Idea:
      - scheduler splits syntax into the per cycle instructions
      - synthesis creates a rule for each one 
      - add two registers to module: command for holding the command over multiple cycles and stage: an integer
        indicating which cycle we are in for a specific command
      - the scheduler here specifies the stage for each ops
      - the guard also checks for the stage
      - the output (only fully fires when stage is final stage), for this a second buffer of output registers is needed
        in the final stage, the output rules, read the current output and (instead of directly putting it on the wire) buffer it
      
      (branching is currently contained within a single cycle)

      In the future the scheduler can store additional metadata (e.g. which branch was taken)
  *)

  Context (tfs_ctx : TFSchedContext).

  Local Notation spec_states := (tfs_spec_states tfs_ctx).
  Local Notation spec_states_fin := (tfs_spec_states_fin tfs_ctx).
  Local Notation spec_states_size := (tfs_spec_states_size tfs_ctx).
  Local Notation spec_states_init := (tfs_spec_states_init tfs_ctx).

  Local Notation spec_inputs := (tfs_spec_inputs tfs_ctx).
  Local Notation spec_inputs_fin := (tfs_spec_inputs_fin tfs_ctx).
  Local Notation spec_inputs_size := (tfs_spec_inputs_size tfs_ctx).

  Local Notation spec_outputs := (tfs_spec_outputs tfs_ctx).
  Local Notation spec_outputs_fin := (tfs_spec_outputs_fin tfs_ctx).
  Local Notation spec_outputs_size := (tfs_spec_outputs_size tfs_ctx).

  Local Notation spec_action := (tfs_spec_action tfs_ctx).
  Local Notation spec_action_fin := (tfs_spec_action_fin tfs_ctx).
  Local Notation spec_action_ops := (tfs_spec_action_ops tfs_ctx).

  Hint Extern 0 (Show spec_states) => exact (tfs_spec_states_names tfs_ctx) : typeclass_instances.

  (* ========= *)

  Local Notation SpecStateEnv := ((ContextEnv (FT:=spec_states_fin)).(env_t) (tf_states_type spec_states_size)).
  Local Notation SpecInputEnv := ((ContextEnv (FT:=spec_inputs_fin)).(env_t) (tf_inputs_type spec_inputs_size)).
  Local Notation SpecOutputEnv := ((ContextEnv (FT:=spec_outputs_fin)).(env_t) (tf_outputs_type spec_outputs_size)).

  Inductive tfs_states :=
    | tfs_fs_st (state: spec_states).

  Definition tfs_states_size (s: tfs_states) : nat :=
    match s with
    | tfs_fs_st st => spec_states_size st
    end.

  Instance tfs_states_fin : FiniteType tfs_states.
  Proof. Admitted.

  Instance show_tfs_states : Show tfs_states :=
    { show := fun s =>
        match s with
        | tfs_fs_st st => String.append "tfs_st_" (show st)
        end
    }.
  
  Local Notation SchedStateEnv := ((ContextEnv (FT:=tfs_states_fin)).(env_t) (tf_states_type tfs_states_size)).

  Definition tfs_map_to: SpecStateEnv -> SchedStateEnv
    . Proof. Admitted.

  Definition tfs_map_from: SchedStateEnv -> SpecStateEnv
    . Proof. Admitted.

  Definition tfs_states_init : forall (s: tfs_states), tf_states_type tfs_states_size s :=
      fun s => (ContextEnv (FT:=tfs_states_fin)).(getenv) (tfs_map_to ((ContextEnv (FT:=spec_states_fin)).(create) spec_states_init)) s.

  Definition tfs_schedule: spec_action -> list (@tf_ops tfs_states spec_inputs spec_outputs)
    . Proof. Admitted.

  Section InterfaceRequirements.

    Definition tfs_run 
      (act: spec_action)
      (sys_state: SpecStateEnv * SpecOutputEnv)
      (input: forall (x : spec_inputs), (type_denote (tf_inputs_type spec_inputs_size x)))
      : SpecStateEnv * SpecOutputEnv :=
      List.fold_right
      (fun ops acc_state =>
          let tfs_sys_state := (tfs_map_to (fst acc_state), snd acc_state) in
          let tfs_sys_state' := tf_ops_run tfs_states_size spec_inputs_size spec_outputs_size ops tfs_sys_state input in
          (tfs_map_from (fst tfs_sys_state'), snd tfs_sys_state')
      ) sys_state (tfs_schedule act).

    Lemma tfs_correct:
      forall (act: spec_action) (sys_state: SpecStateEnv * SpecOutputEnv)
             (input: forall (x : spec_inputs), (type_denote (tf_inputs_type spec_inputs_size x))),
      tf_ops_run spec_states_size spec_inputs_size spec_outputs_size (spec_action_ops act) sys_state input =
      tfs_run act sys_state input.
    Proof. Admitted.

  End InterfaceRequirements.

End TrustformerScheduler.

  (* Definition tfs_blocks: list (@tf_ops tfs_states spec_inputs spec_outputs)
    . Proof. Admitted.

  Definition tfs_schedule: spec_action -> list nat
    . Proof. Admitted.

  Definition tfs_map_to: SpecStateEnv -> SchedStateEnv
    . Proof. Admitted.

  Definition tfs_map_from: SchedStateEnv -> SpecStateEnv
    . Proof. Admitted.

  Section InterfaceRequirements.

    Definition tfs_run 
      (act: spec_action)
      (sys_state: SpecStateEnv * SpecOutputEnv)
      (input: forall (x : spec_inputs), (type_denote (tf_inputs_type spec_inputs_size x)))
      : SpecStateEnv * SpecOutputEnv :=
      List.fold_right
      (fun (idx: nat) acc_state =>
          match nth_error tfs_blocks idx with
          | Some tfs_block =>
              let tfs_sys_state := (tfs_map_to (fst acc_state), snd acc_state) in
              let tfs_sys_state' := tf_ops_run tfs_states_size spec_inputs_size spec_outputs_size tfs_block tfs_sys_state input in
              (tfs_map_from (fst tfs_sys_state'), snd tfs_sys_state')
          | None => acc_state (* should not happen *)
          end
      ) sys_state (tfs_schedule act).

    Lemma tfs_correct:
      forall (act: spec_action) (sys_state: SpecStateEnv * SpecOutputEnv)
             (input: forall (x : spec_inputs), (type_denote (tf_inputs_type spec_inputs_size x))),
      tf_ops_run spec_states_size spec_inputs_size spec_outputs_size (spec_action_ops act) sys_state input =
      tfs_run act sys_state input.
    Proof. Admitted.

  End InterfaceRequirements. *)
