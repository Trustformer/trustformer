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

  tfs_spec_action : Type;
  tfs_spec_action_eq_dec : EqDec tfs_spec_action;
  tfs_spec_action_fin : FiniteType tfs_spec_action;
  tfs_spec_action_ops : tfs_spec_action -> @tf_ops tfs_spec_states tfs_spec_inputs tfs_spec_outputs
}.

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

  (* returns the actions that should always run (fst) and the actions that should only run when the done signal is set (snd) *)
  tfs_schedule: tfs_action -> list (@tf_op tfs_states tfs_inputs tfs_outputs) * list (@tf_op tfs_states tfs_inputs tfs_outputs);
  (* after the done signal is set, the next cycle the module is ready for new input & the modules output is valid (if the above schedule is respected) *)
  tfs_done_signal: tfs_states;
  (* these states have to be reset if the done signal is set *)
  tfs_reset_states: list tfs_states;
}.
