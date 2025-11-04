Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Section TrustformerSyntax.

    (* Given some variables, inputs and outputs we define our syntax *)
    Context (states_var: Type).
    Context (inputs_var: Type).
    Context (outputs_var: Type).

    (* Atomic operations on variables *)
    Inductive tf_ops :=
        | tf_nop (* No operation *)
        | tf_neg (x : states_var) (* Negate a variable *)
        | tf_input (x : states_var) (y : inputs_var) (* Read input into variable *)
        | tf_output (x : states_var) (y : outputs_var) (* Write variable to output *)
        . 

End TrustformerSyntax.
