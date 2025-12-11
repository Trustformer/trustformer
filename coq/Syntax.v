Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Section TrustformerSyntax.

    (* Given some variables, inputs and outputs we define our syntax *)
    Context {states_var: Type}.
    Context {inputs_var: Type}.
    Context {outputs_var: Type}.

    Inductive tf_unary_ops :=
        | tf_not                                (* Bitwise NOT *)
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
        | tf_cmp (cmp_sz: nat) (cmp_op: tf_comparison_ops)    (* Comparison Operations *)
        .

    Inductive tf_expr :=
        | tf_const (value: nat)                                             (* Constant value *)
        | tf_var (v: states_var)                                            (* Variable reference *) 
        | tf_input (v: inputs_var)                                          (* Input reference *)
        | tf_op1 (op: tf_unary_ops) (src: tf_expr)                          (* Unary operation *)
        | tf_op2 (op: tf_binary_ops) (src1: tf_expr) (src2: tf_expr)        (* Binary operation *)
        .

    (* Atomic operations on variables *)
    Inductive tf_op :=
        | tf_nop                                                (* No operation *)
        | tf_assign (dst : states_var) (expr : tf_expr)         (* Unary Operations *)
        | tf_output (dst : outputs_var) (expr : tf_expr)        (* Write variable to output *)
        . 

    Inductive tf_ops :=
        | tf_ops_base (op: tf_op)                                              (* Single operation *)
        | tf_ops_cons (op: tf_ops) (op2: tf_ops)                               (* Sequence of operations *)
        | tf_ops_if   (cond: tf_expr) (then_ops: tf_ops) (else_ops: tf_ops)    (* Conditional operations *)
        .
End TrustformerSyntax.

(* Notations for Trustformer Syntax *)
(* 
    TODO: This is only temporary, to make some code more readable.
*)

Declare Custom Entry trustformer.
Declare Custom Entry tf_arg.   
Declare Custom Entry tf_const.

Notation "{[ e ]}" := e (e custom trustformer at level 200).

Notation "x" := x (in custom tf_arg at level 0, x constr at level 0).
Notation "n" := n (in custom tf_const at level 0, n constr at level 0).

(* Variables & Constants *)
Notation "'$S' x" := (tf_var x) 
    (in custom trustformer at level 0, x custom tf_arg at level 0).

Notation "'$I' x" := (tf_input x) 
    (in custom trustformer at level 0, x custom tf_arg at level 0).

Notation "'#' n" := (tf_const n) 
    (in custom trustformer at level 0, n custom tf_const at level 0).

(* Grouping *)
Notation "'`' x '`'" := x (in custom trustformer at level 1, x constr at level 0).
Notation "'(' x ')'" := x (in custom trustformer at level 2, x custom trustformer at level 200).

(* Unary Operations *)
Notation "'!' x" := (tf_op1 tf_not x) 
    (in custom trustformer at level 35, right associativity).

(* Binary Operations *)
Notation "x + y" := (tf_op2 tf_add x y) (in custom trustformer at level 50, left associativity).
Notation "x - y" := (tf_op2 tf_sub x y) (in custom trustformer at level 50, left associativity).
Notation "x * y" := (tf_op2 tf_mul x y) (in custom trustformer at level 40, left associativity).
Notation "x & y" := (tf_op2 tf_and x y) (in custom trustformer at level 60, left associativity).
Notation "x | y" := (tf_op2 tf_or x y) (in custom trustformer at level 60, left associativity).
Notation "x ^ y" := (tf_op2 tf_xor x y) (in custom trustformer at level 60, left associativity).

(* Comparisons *)
Notation "x <[ n ] y" := (tf_op2 (tf_cmp n tf_lt) x y) 
    (in custom trustformer at level 70, n custom tf_const at level 0).
Notation "x <=[ n ] y" := (tf_op2 (tf_cmp n tf_le) x y) 
    (in custom trustformer at level 70, n custom tf_const at level 0).
Notation "x >[ n ] y" := (tf_op2 (tf_cmp n tf_gt) x y) 
    (in custom trustformer at level 70, n custom tf_const at level 0).
Notation "x >=[ n ] y" := (tf_op2 (tf_cmp n tf_ge) x y) 
    (in custom trustformer at level 70, n custom tf_const at level 0).
Notation "x ==[ n ] y" := (tf_op2 (tf_cmp n tf_eq) x y) 
    (in custom trustformer at level 70, n custom tf_const at level 0).
Notation "x !=[ n ] y" := (tf_op2 (tf_cmp n tf_neq) x y) 
    (in custom trustformer at level 70, n custom tf_const at level 0).

(* Instructions *)
Notation "'pass'" := (tf_ops_base tf_nop) (in custom trustformer at level 0).

Notation "'let' '$S' x := e" := (tf_ops_base (tf_assign x e)) 
    (in custom trustformer at level 80, x custom tf_arg at level 0).

Notation "'let' '$O' x := e" := (tf_ops_base (tf_output x e)) 
    (in custom trustformer at level 80, x custom tf_arg at level 0).

Notation "s1 ; s2" := (tf_ops_cons s1 s2) 
    (in custom trustformer at level 90, right associativity, format "'[v' s1 ; '/' s2 ']'").

Notation "'if' c 'then' t 'else' f" := (tf_ops_if c t f) 
    (in custom trustformer at level 89, 
    c custom trustformer at level 99, 
    t custom trustformer at level 99, 
    f custom trustformer at level 99,
    format "'[v' 'if'  c  'then' '/' t '/' 'else' '/' f ']'").


Section NotationExamples.
    Context {states_var: Type}.
    Context {inputs_var: Type}.
    Context {outputs_var: Type}.

    Variables (s_a s_b : states_var) (i_x : inputs_var) (o_y : outputs_var).

    Definition t1 : @tf_ops states_var inputs_var outputs_var := {[ 
        let $S s_a := $I i_x ;
        let $S s_b := $I i_x
    ]}.

    Definition t2 : @tf_ops states_var inputs_var outputs_var := {[ 
        if ($I i_x ==[32] $S s_a) 
        then let $O o_y := #1 
        else let $O o_y := #0
    ]}.

    Definition t3 : @tf_ops states_var inputs_var outputs_var := {[ 
        pass ; pass                  
    ]}.

    Definition t4 : @tf_ops states_var inputs_var outputs_var := {[ 
        let $S s_a := $I i_x + #1;                 
        if ($S s_a ==[32] #10) 
        then let $O o_y := $S s_a 
        else pass                           
    ]}.


    Definition t5 : @tf_ops states_var inputs_var outputs_var := {[ 
        let $S s_a := $I (i_x) + `tf_const 1`;           
        if ($S (s_a) ==[32] #10) then pass else pass
    ]}.
End NotationExamples.

