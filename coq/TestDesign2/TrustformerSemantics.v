Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.TestDesign2.TrustformerSyntax.

Section Semantics.

    (* Given some (finite) variables, each with some HW register type, we define our semantics  *)
    Context (states_var: Type) (states_var_fin : FiniteType states_var) (states_type : states_var -> type).
    
    (* Semantics of a single operation step *)
    Definition tf_op_step
      (state: ContextEnv.(env_t) states_type)
      (state_op: TrustformerSyntax.tf_ops)
      : 
      (ContextEnv.(env_t) states_type) :=
        match state_op with
        | tf_nop => state
        end.

    (* TODO: Semantics of a chain of operation steps *)

End Semantics.
