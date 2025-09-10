Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.TestDesign2.TrustformerSyntax.

Section Semantics.

   Context (states_var: Type) (states_var_fin : FiniteType states_var) (states_type : states_var -> type).
    
    Definition tf_op_step
      (state: ContextEnv.(env_t) states_type)
      (state_op: TrustformerSyntax.tf_ops)
      : 
      (ContextEnv.(env_t) states_type) :=
        match state_op with
        | tf_nop => state
        end.

End Semantics.