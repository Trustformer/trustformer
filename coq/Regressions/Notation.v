(*! The notation grammar of coq/Syntax.v, exercised.  Each [t] builds a
    [tf_ops] through the `{[ ... ]}` forms and the probe under it computes the
    AST it elaborates to; [t7] and [t8] are the only coverage the `++[hi,lo]`
    and `call` forms have. !*)

Require Import Koika.Frontend.
Require Import Trustformer.Syntax.

Section NotationExamples.
    Context {states_var: Type}.
    Context {inputs_var: Type}.
    Context {outputs_var: Type}.
    Context {ips_var: Type}.

    Variables (s_a s_b : states_var) (i_x : inputs_var) (o_y : outputs_var).
    Variable (p_ip : ips_var).

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

    Definition t7 : @tf_ops states_var inputs_var outputs_var ips_var := {[
        let $s_a := $i_x ++[16,16] #0;
        let $s_b := $i_x ++[8,8] $s_a ++[16,16] #0
    ]}.
    Goal True. pose (debug := t7); compute in debug.
    Abort.

    Definition t8 : @tf_ops states_var inputs_var outputs_var ips_var := {[
        let $s_a := call p_ip ($i_x ++[16,16] #0);
        if ($s_a ==[32] #0) then let $o_y := #1 else let $o_y := $s_a
    ]}.
    Goal True. pose (debug := t8); compute in debug.
    Abort.
End NotationExamples.


