Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.TestDesign3.TrustformerSyntax.
Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Section Semantics.

    (* Given some (finite) variables, each with some HW register type, we define our semantics  *)
    Context (states_var: Type) (states_var_fin : FiniteType states_var) (states_type : states_var -> type).

    (* Given a current state, a variable & an operation, returns the new value for the variable if it is written to *)
    Definition tf_op_step_writes
      (state: ContextEnv.(env_t) states_type)
      (var: states_var)
      (state_op: TrustformerSyntax.tf_ops)
      : option (states_type var) :=
        match state_op with
        | tf_nop => None
        end.

    (* Semantics of a single operation step *)
    Definition tf_op_step_commit
      (state: ContextEnv.(env_t) states_type)
      (state_op: TrustformerSyntax.tf_ops)
      : 
      (ContextEnv.(env_t) states_type) :=
        (ContextEnv.(create)
          (fun k => 
            match tf_op_step_writes state k state_op with
              | Some v => v
              | None => state.[k]
              end)).

    (* TODO: Semantics of a chain of operation steps *)

    Section Properties.
      
      (* This is how I would have done it, but it might be bad *)
      Definition tf_op_var_changed
        (var: states_var)
        (state_op: TrustformerSyntax.tf_ops)
        : bool :=
        match state_op with
        | tf_nop => false
        end.
      Lemma tf_op_var_changed_correct
        (state: ContextEnv.(env_t) states_type)
        (var: states_var)
        (state_op: TrustformerSyntax.tf_ops)
        :
        (tf_op_var_changed var state_op = false -> 
          (tf_op_step_commit state state_op).[var] = state.[var]).
      Proof.
        unfold tf_op_var_changed, tf_op_step_commit, tf_op_step_writes.
        rewrite getenv_create.
        timeout 10 sauto.
      Qed.

      (* This is probably the better way, if it works delete the above *)
      Definition tf_op_var_unchanged
        (var: states_var)
        (state_op: TrustformerSyntax.tf_ops)
        : Prop :=
        forall state,
        (tf_op_step_commit state state_op).[var] = state.[var].
      
      Definition tf_op_var_unchanged_dec
        (var: states_var)
        (state_op: TrustformerSyntax.tf_ops)
        : {tf_op_var_unchanged var state_op} + {~ (tf_op_var_unchanged var state_op)}.
        Proof.
          unfold tf_op_var_unchanged, tf_op_step_commit, tf_op_step_writes.
          destruct state_op.
          - left. intros state. rewrite getenv_create. timeout 10 sauto.
        Qed.
    End Properties.

End Semantics.


