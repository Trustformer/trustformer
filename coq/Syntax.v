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

    Inductive tf_unary_ops :=
        | tf_not                                (* Bitwise NOT *)
        (* | tf_sign_extend *)                        (* Sign extend *)
        (* | tf_zero_extend_left *)                   (* Zero extend left *)
        (* | tf_zero_extend_right *)                  (* Zero extend right *)
        (* | tf_slice (offset: nat) (width: nat) *)   (* Slice *)
        .

    Inductive tf_comparison_ops :=
        | tf_eq                                 (* Equal *)
        | tf_neq                                (* Not equal *)
        | tf_lt                                 (* Unsigned Less than *)
        | tf_le                                 (* Unsigned Less than or equal *)
        | tf_gt                                 (* Unsigned Greater than *)
        | tf_ge                                 (* Unsigned Greater than or equal *)
        .

    Inductive tf_binary_ops :=
        | tf_and                                (* Logical and *)
        | tf_or                                 (* Logical or *)
        | tf_xor                                (* Logical xor *)
        | tf_add                                (* Addition *)
        | tf_sub                                (* Subtraction *)
        | tf_mul                                (* Multiplication *)
        | tf_cmp (cmp_op: tf_comparison_ops)    (* Comparison Operations *)
        (* | tf_div *)
        (* | tf_mod *)
        .

    Inductive tf_expr :=
        | tf_const (value: nat)                                             (* Constant value *)
        | tf_var (v: states_var)                                            (* Variable reference *) 
        | tf_op1 (op: tf_unary_ops) (src: tf_expr)                       (* Unary operation *)
        | tf_op2 (op: tf_binary_ops) (src1: tf_expr) (src2: tf_expr)  (* Binary operation *)
        .

    (* Atomic operations on variables *)
    Inductive tf_ops :=
        | tf_nop                                                (* No operation *)
        | tf_assign (dst : states_var) (expr : tf_expr)         (* Unary Operations *)
        
        (* TODO: input & outputs should allow expressions instead of vars *)
        | tf_input (dst : states_var) (src : inputs_var)        (* Read input into variable *)
        | tf_output (dst : outputs_var) (src : states_var)      (* Write variable to output *)
        . 

End TrustformerSyntax.
