(*!
    Regressions for the diagnostics layer (Scheduler/Show.v, Scheduler/Audit.v).

    These pin the *rendering*, not the analysis -- the analysis itself is pinned
    by LockboxTriesTaint.v, which these examples reuse.  What can silently break
    here is the mapping back from node ids to source: a report that says
    [CR_no_rule 3] is not wrong, it is unusable.
!*)

Require Import Koika.Frontend.

Require Import Trustformer.Scheduler.Audit.
Require Import Trustformer.Examples.LockboxTries.
Require Import Trustformer.Examples.LockboxTriesTaint.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Section Naming.

    Definition dfgA := build_dfg ctxA_blackbox fs_act_test.

    (* The two conditions LockboxTriesTaint.v identifies as nodes 3 and 6 are
       the two the specification is written in terms of. *)
    Example nodes_render_as_source_expressions :
      show_node ctxA_blackbox dfgA 3 = "($fs_st_tries !=[2] #0)"
      /\ show_node ctxA_blackbox dfgA 6 = "($fs_st_pin ==[32] ?fs_in_pin)".
    Proof. split; vm_compute; reflexivity. Qed.

    Example no_rule_says_which_branch_and_why :
      show_crit_reason ctxA_blackbox dfgA (CR_no_rule 3)
      = "branch on ($fs_st_tries !=[2] #0) (node 3) is tainted and no declassification rule targets it".
    Proof. vm_compute. reflexivity. Qed.

    (* The interesting diagnostic: a rule DOES fire, just not on this path.
       [secret_tries_defeats_the_same_rules] is the machine-checked version of
       the same fact in node ids. *)
    Example guard_unmet_says_what_the_path_lacks :
      show_crit_reason ctxA_whitebox (build_dfg ctxA_whitebox fs_act_test)
        (CR_guard_unmet 6 [[(6, true)]; [(3, true)]])
      = "branch on ($fs_st_pin ==[32] ?fs_in_pin) (node 6) is declassified, but not on this path, which would also have to satisfy ($fs_st_pin ==[32] ?fs_in_pin) -- or -- ($fs_st_tries !=[2] #0)".
    Proof. vm_compute. reflexivity. Qed.

    (* [crit_report_all] reports one entry per phi OCCURRENCE, so the report
       groups them: two causes, three occurrences each, not six lines. *)
    Example the_report_groups_occurrences :
      show_crit_report ctxA_blackbox dfgA
      = "  - branch on ($fs_st_tries !=[2] #0) (node 3) is tainted and no declassification rule targets it [3 occurrences]
  - branch on ($fs_st_pin ==[32] ?fs_in_pin) (node 6) is tainted and no declassification rule targets it [3 occurrences]".
    Proof. vm_compute. reflexivity. Qed.

    Example a_clean_design_says_so :
      crit_report_all ctxB_whitebox (build_dfg ctxB_whitebox fs_act_test) = []
      /\ show_crit_report ctxB_whitebox (build_dfg ctxB_whitebox fs_act_test)
         = "no phi is critical".
    Proof. split; vm_compute; reflexivity. Qed.

End Naming.

(*
    Witness paths.  A design that is not constant time leaks; the pair of paths
    is the description of the leak, and is what an [action_bounds] soundness
    proof would have to quantify over.
 *)

Section Witnesses.

    (* [sk_public] branches on an input, so the phi selects and the expensive
       [secret^3] branch is only paid for when the input says so.  Both bounds
       come with the branch that achieves them. *)
    Example public_selector_leaks_along_a_named_path :
      action_bounds_w sk_public 4 (build_dfg sk_public sk_act)
      = ((1, [(3, false)]), (3, [(3, true)])).
    Proof. vm_compute. reflexivity. Qed.

    Example the_leak_reads_back_as_the_condition :
      let a := audit sk_public 4 sk_act in
      show_path sk_public (build_dfg sk_public sk_act) (ta_fast a)
        = "not (?sk_in ==[32] #0)"
      /\ show_path sk_public (build_dfg sk_public sk_act) (ta_slow a)
         = "(?sk_in ==[32] #0)".
    Proof. split; vm_compute; reflexivity. Qed.

    (* Same design, secret selector: the phi is critical, both branches are
       awaited, and there is no pair of paths left to tell apart. *)
    Example secret_selector_has_nothing_to_witness :
      ta_constant_time (audit sk_private 4 sk_act) = true
      /\ ta_cycles_lo (audit sk_private 4 sk_act) = 3
      /\ ta_cycles_hi (audit sk_private 4 sk_act) = 3.
    Proof. repeat split; vm_compute; reflexivity. Qed.

    (* The paper's fig:dfgB5.  Making [tries] public buys a cycle in the common
       case, and the price is a timing channel on the pin check -- which is
       acceptable exactly because with [tries] public the attacker already knows
       the outcome (03_taint_analysis.tex L198). *)
    Example public_tries_leaks_the_pin_check :
      let a := audit ctxB_whitebox 4 fs_act_test in
      ta_constant_time a = false
      /\ ta_fast a = [(6, true); (3, true)]
      /\ ta_slow a = [(3, true); (6, false)].
    Proof. repeat split; vm_compute; reflexivity. Qed.

End Witnesses.

(*
    The audit is one call, and the whole picture is one string.
 *)

Section Report.

    Example the_audit_is_one_call :
      audit_report sk_public 4 sk_act
      = "nodes:         9
buffers:       2
tainted nodes: 3
cycles:        1 .. 3
constant time: NO
  fastest (1) when: not (?sk_in ==[32] #0)
  slowest (3) when: (?sk_in ==[32] #0)
critical phis:
no phi is critical".
    Proof. vm_compute. reflexivity. Qed.

    (* [ta_constant_time] is exactly the bounds collapsing, for every context
       and every action -- not just for the ones tested above. *)
    Example constant_time_is_the_bounds_agreeing :
      forall ctx cost act,
        ta_constant_time (audit ctx cost act) = true
        <-> ta_cycles_lo (audit ctx cost act) = ta_cycles_hi (audit ctx cost act).
    Proof. intros. apply audit_constant_time_iff_bounds_agree. Qed.

End Report.

(*
    The paper draws its DFG figures by hand.  This is the same picture, emitted
    by the compiler that built the graph: tainted nodes yellow, critical phis
    red, buffered nodes boxed, assigned variables double-outlined.
 *)

Section Graphviz.

    Example the_graph_draws_itself :
      audit_dot sk_private 4 sk_act
      = "digraph dfg {
  rankdir=BT;
  node [fontname=""monospace""];
  n0 [label=""0: empty"", shape=ellipse, style=filled, fillcolor=""#ffffff""];
  n1 [label=""1: $sk_secret"", shape=ellipse, style=filled, fillcolor=""#ffe680""];
  n2 [label=""2: #0"", shape=ellipse, style=filled, fillcolor=""#ffffff""];
  n3 [label=""3: ==[32]"", shape=ellipse, style=filled, fillcolor=""#ffe680""];
  n4 [label=""4: *"", shape=box, style=filled, fillcolor=""#ffe680""];
  n5 [label=""5: *"", shape=box, style=filled, fillcolor=""#ffe680""];
  n6 [label=""6: #1"", shape=ellipse, style=filled, fillcolor=""#ffffff""];
  n7 [label=""7: phi"", shape=doubleoctagon, style=filled, fillcolor=""#ff9d9d""];
  n3 -> n1 [label=""l""];
  n3 -> n2 [label=""r""];
  n4 -> n1 [label=""l""];
  n4 -> n1 [label=""r""];
  n5 -> n4 [label=""l""];
  n5 -> n1 [label=""r""];
  n7 -> n3 [label=""c""];
  n7 -> n5 [label=""t""];
  n7 -> n6 [label=""e""];
}".
    Proof. vm_compute. reflexivity. Qed.

End Graphviz.
