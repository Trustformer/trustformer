Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

(* ===================================================================== *)
(*  An attached IP block                                                 *)
(* ===================================================================== *)
(*
    One record for one concept.  Before this, an IP was encoded as a
    distinguished RESPONSE PORT plus six parallel tables keyed on it
    (tfs_spec_ip_req, _ip_lat, _ip_secret, _no_assign_driven,
    tfs_inputs_is_resp, tfs_drive_reg) -- and [resp] had to impersonate an IP
    name in the syntax because there was nothing else to name.

    Carrying the sizes means [ip_fn] can be typed EXACTLY against the two port
    widths.  While the function lived in the [tf_call] node it could not be:
    a node's type cannot mention [outputs_size req], so it needed size fields
    and a side condition tying them to the ports.  Here that condition holds by
    construction.
*)
Record ip_decl {i o : Type} (isz : i -> nat) (osz : o -> nat) := {
  ip_req  : o;              (* request port, driven mid-action *)
  ip_resp : i;              (* response port, sampled live     *)
  ip_lat  : nat;            (* CYCLES: wait this long after the pulse, then
                               read the answer and pulse again.  Not pipelined. *)
  ip_fn   : bits_t (osz ip_req) -> bits_t (isz ip_resp);
}.
Arguments ip_req {i o isz osz}.
Arguments ip_resp {i o isz osz}.
Arguments ip_lat {i o isz osz}.
Arguments ip_fn {i o isz osz}.

Section TrustformerSyntax.

    (* Given some variables, inputs and outputs we define our syntax *)
    Context {states_var: Type}.
    Context {states_var_eqdec: EqDec states_var}.
    Context {inputs_var: Type}.
    Context {inputs_var_eqdec: EqDec inputs_var}.
    Context {outputs_var: Type}.
    Context {ips_var: Type}.
    Context {outputs_var_eqdec: EqDec outputs_var}.

    Inductive tf_unary_ops :=
        | tf_not                                (* Bitwise NOT *)
        | tf_resize (source_size: nat)          (* Evaluate at source_size, then convert *)
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
        | tf_concat (hi_sz: nat) (lo_sz: nat)   (* Concatenate two values *)
        .

    Inductive tf_expr :=
        | tf_const (value: nat)                                                 (* Constant value *)
        | tf_svar (v: states_var)                                               (* Variable reference *) 
        | tf_ivar (v: inputs_var)                                               (* Input reference *)
        | tf_ovar (v: outputs_var)                                              (* Output reference *)
        | tf_op1 (op: tf_unary_ops) (src: tf_expr)                              (* Unary operation *)
        | tf_op2 (op: tf_binary_ops) (src1: tf_expr) (src2: tf_expr)            (* Binary operation *)
        | tf_expr_if (cond: tf_expr) (then_expr: tf_expr) (else_expr: tf_expr)  (* Conditional expression *)
        .

    (* Atomic operations on variables *)
    Inductive tf_op :=
        | tf_nop                                                (* No operation *)
        | tf_assign (dst : states_var) (expr : tf_expr)         (* Unary Operations *)
        | tf_output (dst : outputs_var) (expr : tf_expr)        (* Write variable to output *)
        (* An external-IP call.  THREE fields, and each is there for a reason
           that survives scrutiny:

             [ip]   WHICH IP -- routing.  Everything about the block (its two
                    ports, its latency, what it computes) lives in the context's
                    [ip_decl], because all of it is a property of the block and
                    not of the call site.
             [dst]  where the answer goes.
             [arg]  the request payload.

           What used to be here and why it left:
             [site] -- nothing ever read it.
             [lat]  -- a property of the IP, not the call.
             [req]  -- derivable: the context pairs it with the response port.
             [resp] -- was impersonating an IP name; [ip] is the name now.
             [f]    -- a property of the IP, and in the record it can be typed
                       exactly against the port widths, which a node cannot do.
                       That also retires the [szA]/[szB] fields and the side
                       condition that tied them to the ports.

           A call is still a STATEMENT, not an expression: a [tf_op] constructor
           never enters [tf_eval_expr], where the tree's most fragile proof lines
           live. *)
        | tf_call (ip: ips_var) (dst: states_var) (arg: tf_expr)
        . 

    Inductive tf_ops :=
        | tf_ops_base (op: tf_op)                                              (* Single operation *)
        | tf_ops_cons (op: tf_ops) (op2: tf_ops)                               (* Sequence of operations *)
        | tf_ops_if   (cond: tf_expr) (then_ops: tf_ops) (else_ops: tf_ops)    (* Conditional operations *)
        .
        
    Instance tf_unary_ops_eqdec: EqDec tf_unary_ops.
    Proof.
        constructor. intros.
        decide equality; apply Nat.eq_dec.
    Qed.

    Instance tf_comparison_ops_eqdec: EqDec tf_comparison_ops.
    Proof.
        constructor. intros.
        decide equality.
    Qed.

    Instance tf_binary_ops_eqdec: EqDec tf_binary_ops.
    Proof.
        constructor. intros.
        decide equality;
        try apply tf_comparison_ops_eqdec;
        try apply Nat.eq_dec.
    Qed.

    Instance tf_expr_eqdec: EqDec tf_expr.
    Proof.
        constructor. intros.
        decide equality;
        try apply Nat.eq_dec;
        try apply states_var_eqdec;
        try apply inputs_var_eqdec;
        try apply outputs_var_eqdec;
        try apply tf_unary_ops_eqdec;
        try apply tf_binary_ops_eqdec.
    Qed.


End TrustformerSyntax.

(* Notations for Trustformer Syntax *)
(* 
    TODO: This is only temporary, to make some code more readable.
*)

Class IsExpr (S I O V : Type) := { 
    as_expr : V -> @tf_expr S I O 
}.

Class IsAssignable (S I O P V : Type) := { 
    do_assign : V -> @tf_expr S I O -> @tf_op S I O P 
}.

Class HasIf (Ret S I O : Type) := {
    make_if : @tf_expr S I O -> Ret -> Ret -> Ret
}.

Arguments as_expr {S I O V} {_} _.
Arguments do_assign {S I O P V} {_} _ _.
Arguments make_if {Ret S I O} {_} _ _ _.

Instance StateIsExpr {S I O : Type} : IsExpr S I O S := {
    as_expr := tf_svar
}.

Instance InputIsExpr {S I O : Type} : IsExpr S I O I := {
    as_expr := tf_ivar
}.

Instance OutputIsExpr {S I O : Type} : IsExpr S I O O := {
    as_expr := tf_ovar
}.

Instance StateIsAssignable {S I O P : Type} : IsAssignable S I O P S := {
    do_assign := tf_assign
}.  

Instance OutputIsAssignable {S I O P : Type} : IsAssignable S I O P O := {
    do_assign := tf_output
}.

Instance IfExpr {S I O : Type} : HasIf (@tf_expr S I O) S I O := {
    make_if := tf_expr_if
}.

Instance IfOps {S I O P : Type} : HasIf (@tf_ops S I O P) S I O := {
    make_if := tf_ops_if
}.

Declare Custom Entry trustformer.
Declare Custom Entry tf_arg.     
Declare Custom Entry tf_const.   

Notation "{[ e ]}" := e (e custom trustformer at level 200).

Notation "x" := x (in custom tf_arg at level 0, x constr at level 0).
Notation "n" := n (in custom tf_const at level 0, n constr at level 0).

(* Variables & Constants *)
Notation "'$' x" := (as_expr x) 
    (in custom trustformer at level 0, x custom tf_arg at level 0, only parsing).
Notation "'$' x" := (tf_svar x) 
    (in custom trustformer at level 0, x custom tf_arg at level 0, format "'$' x", only printing).
Notation "'$' x" := (tf_ivar x) 
    (in custom trustformer at level 0, x custom tf_arg at level 0, format "'$' x", only printing).
Notation "'$' x" := (tf_ovar x) 
    (in custom trustformer at level 0, x custom tf_arg at level 0, format "'$' x", only printing).

Notation "'#' n" := (tf_const n) 
    (in custom trustformer at level 0, format "'#' n", n custom tf_const at level 0).

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
    (in custom trustformer at level 70, n custom tf_const at level 0, format "x  <[ n ]  y").
Notation "x <=[ n ] y" := (tf_op2 (tf_cmp n tf_le) x y) 
    (in custom trustformer at level 70, n custom tf_const at level 0, format "x  <=[ n ]  y").
Notation "x >[ n ] y" := (tf_op2 (tf_cmp n tf_gt) x y) 
    (in custom trustformer at level 70, n custom tf_const at level 0, format "x  >[ n ]  y").
Notation "x >=[ n ] y" := (tf_op2 (tf_cmp n tf_ge) x y) 
    (in custom trustformer at level 70, n custom tf_const at level 0, format "x  >=[ n ]  y").
Notation "x ==[ n ] y" := (tf_op2 (tf_cmp n tf_eq) x y) 
    (in custom trustformer at level 70, n custom tf_const at level 0, format "x  ==[ n ]  y").
Notation "x !=[ n ] y" := (tf_op2 (tf_cmp n tf_neq) x y) 
    (in custom trustformer at level 70, n custom tf_const at level 0, format "x  !=[ n ]  y").

(* Instructions *)
Notation "'pass'" := (tf_ops_base tf_nop) (in custom trustformer at level 0).

Notation "'let' '$' x := e" := (tf_ops_base (do_assign x e))
    (in custom trustformer at level 80, x custom tf_arg at level 0, only parsing).
Notation "'let' '$' x := e" := (tf_ops_base (tf_assign x e)) 
    (in custom trustformer at level 80, x custom tf_arg at level 0, format "'let'  $ x  :=  e", only printing).
Notation "'let' '$' x := e" := (tf_ops_base (tf_output x e)) 
    (in custom trustformer at level 80, x custom tf_arg at level 0, format "'let'  $ x  :=  e", only printing).

Notation "s1 ; s2" := (tf_ops_cons s1 s2) 
    (in custom trustformer at level 90, right associativity, format "'[v' s1 ; '/' s2 ']'").

Notation "'if' c 'then' t 'else' f" := (make_if c t f) 
    (in custom trustformer at level 89, 
    c custom trustformer at level 99, 
    t custom trustformer at level 99, 
    f custom trustformer at level 99,
    only parsing).
Notation "'if' c 'then' t 'else' f" := (tf_ops_if c t f) 
    (in custom trustformer at level 89, 
    c custom trustformer at level 99, 
    t custom trustformer at level 99, 
    f custom trustformer at level 99,
    format "'[v' 'if'  c  'then' '/'   t '/' 'else' '/'   f ']'",
    only printing).
Notation "'if' c 'then' t 'else' f" := (tf_expr_if c t f) 
    (in custom trustformer at level 89, 
    c custom trustformer at level 99, 
    t custom trustformer at level 99, 
    f custom trustformer at level 99,
    only printing).


Section NotationExamples.
    Context {states_var: Type}.
    Context {inputs_var: Type}.
    Context {outputs_var: Type}.
    Context {ips_var: Type}.

    Variables (s_a s_b : states_var) (i_x : inputs_var) (o_y : outputs_var).

    Definition t1 : @tf_ops states_var inputs_var outputs_var ips_var := {[ 
        let $s_a := $i_x + #1;
        let $s_b := $i_x
    ]}.
    Goal True. pose (debug := t1); compute in debug.
    Abort.

    Definition t2 : @tf_ops states_var inputs_var outputs_var ips_var := {[ 
        if ($i_x ==[32] $s_a) 
        then 
            let $o_y := #1;
            pass 
        else let $o_y := #0
    ]}.
    Goal True. pose (debug := t2); compute in debug.
    Abort.

    Definition t3 : @tf_ops states_var inputs_var outputs_var ips_var := {[ 
        pass ; pass                  
    ]}.
    Goal True. pose (debug := t3); compute in debug.
    Abort.

    Definition t4 : @tf_ops states_var inputs_var outputs_var ips_var := {[ 
        let $s_a := $i_x + #1;                 
        if ($s_a ==[32] #10) 
        then let $o_y := $s_a 
        else pass                           
    ]}.
    Goal True. pose (debug := t4); compute in debug.
    Abort.

    Definition t5 : @tf_ops states_var inputs_var outputs_var ips_var := {[ 
        let $s_a := $i_x + `tf_const 1`;           
        if ($s_a ==[32] #10) then pass else pass
    ]}.
    Goal True. pose (debug := t5); compute in debug.
    Abort.

    Definition t6 : @tf_ops states_var inputs_var outputs_var ips_var := {[ 
        let $s_a := if ($i_x ==[32] #0) then #1 else #2 
    ]}.
    Goal True. pose (debug := t6); compute in debug.
    Abort.
End NotationExamples.

