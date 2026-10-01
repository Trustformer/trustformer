(*! One entry point for [is this design safe, and what does it cost]: `audit`
    packs `get_tainted`, `crit_report_all`, `action_bounds` and `require_buffer`
    into a record, `audit_report` renders it, `audit_dot` draws it. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Contract.
Require Export Trustformer.Scheduler.Show.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Import ListNotations.

Local Infix "+++" := String.append (at level 60, right associativity).

(* ---------------------------------------------------------------- *)
(* CYCLE BOUNDS.  How long an action takes for a CONCRETE input is   *)
(* [L] in Theorems/IPR.v, which exists for the proofs.  What the     *)
(* circuit gives cheaply is the best and worst case, read off the    *)
(* same cone the compiler walks, each with the branch literals that  *)
(* witness it.                                                      *)
(* ---------------------------------------------------------------- *)

Section Bounds.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation states_var := (tfs_spec_states ctx).
  Local Notation inputs_var := (tfs_spec_inputs ctx).
  Local Notation outputs_var := (tfs_spec_outputs ctx).
  Local Notation ips_var := (tfs_spec_ips ctx).
  Local Notation dfg_state := (@dfg_state_t states_var inputs_var outputs_var ips_var).
  Local Notation get_args := (Build.get_args ctx).
  Local Notation build_dfg := (Build.build_dfg ctx).
  Local Notation calc_backward_cost := (Cost.calc_backward_cost ctx cost_limit).
  Local Notation calc_target_cycle := (Cost.calc_target_cycle cost_limit).
  Local Notation node_op_at := (Taint.node_op_at ctx).
  Local Notation is_source := (Buffers.is_source ctx).
  Local Notation phi_crit := Codegen.phi_crit.
  Local Notation get_tainted := (Taint.get_tainted ctx).
  Local Notation decl_facts := (Taint.decl_facts ctx).

  Definition cycle_of (cycles: list (nid_t * cycle_t)) (n: nid_t) : cycle_t :=
    match BitsToLists.list_assoc cycles n with
    | Some c => c
    | None => 0
    end.

  (* A bound together with the path of branch literals that achieves it.  A
     number alone says the action is not constant time; the path says WHEN it
     is fast and when it is slow, which is the attack. *)
  Definition wcycle := (cycle_t * list lit)%type.

  Definition lit_in (a: lit) (l: list lit) : bool := existsb (lit_eqb a) l.

  Definition wunion (a b: list lit) : list lit :=
    a ++ filter (fun x => negb (lit_in x a)) b.

  (* An UPPER bound is attained as soon as its dominating subterm is, so only
     the winner's branches are required. *)
  Definition wmax (a b: wcycle) : wcycle := if Nat.ltb (fst a) (fst b) then b else a.

  (* Two LOWER bounds must BOTH be attained, so their paths conjoin.  If the two
     disagree on a branch the conjunction is unsatisfiable and the true lower
     bound is higher, so [ta_cycles_lo] stays a bound with an indicative witness. *)
  Definition wmax_lo (a b: wcycle) : wcycle :=
    (Nat.max (fst a) (fst b), wunion (snd a) (snd b)).

  Definition wmin (a b: wcycle) : wcycle := if Nat.ltb (fst b) (fst a) then b else a.

  (* Reaching a deeper stage does not change WHICH branches were taken. *)
  Definition wbump (here: cycle_t) (a: wcycle) : wcycle :=
    if Nat.ltb (fst a) here then (here, snd a) else a.

  (* A critical phi ANDs both branch validities, so it can only be ready when
     the slower branch is; a non-critical one selects, so its best case is the
     faster branch.  That difference is the entire cost of criticality. *)
  Fixpoint node_bounds_w (dfg: dfg_state) (tainted: list nid_t) (dfacts: list gfact)
      (cycles: list (nid_t * cycle_t)) (pi: list lit) (fuel: nat) (n: nid_t)
      : wcycle * wcycle :=
    match fuel with
    | 0 => ((0, pi), (0, pi))
    | S fuel' =>
        (* A source node is never buffered (see [require_buffer]), so it is
           readable in stage 0 no matter how deep its target cycle claims to be. *)
        let here := if is_source dfg n then 0 else cycle_of cycles n in
        let node := nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |} in
        match op node with
        | DFG_Unary _ a =>
            let '(l, u) := node_bounds_w dfg tainted dfacts cycles pi fuel' a in
            (wbump here l, wbump here u)
        | DFG_Resize a =>
            let '(l, u) := node_bounds_w dfg tainted dfacts cycles pi fuel' a in
            (wbump here l, wbump here u)
        | DFG_Binary _ a1 a2 =>
            let '(l1, u1) := node_bounds_w dfg tainted dfacts cycles pi fuel' a1 in
            let '(l2, u2) := node_bounds_w dfg tainted dfacts cycles pi fuel' a2 in
            (wbump here (wmax_lo l1 l2), wbump here (wmax u1 u2))
        (* SPIKE: identity for now.  W-b would add its declared latency to BOTH
           bounds here, which is exactly what keeps the latency derivable. *)
        | DFG_Stall _ a =>
            let '(l, u) := node_bounds_w dfg tainted dfacts cycles pi fuel' a in
            (wbump here l, wbump here u)
        | DFG_Drive _ a _ =>
            let '(l, u) := node_bounds_w dfg tainted dfacts cycles pi fuel' a in
            (wbump here l, wbump here u)
        | DFG_Sample _ t _ =>
            let '(l, u) := node_bounds_w dfg tainted dfacts cycles pi fuel' t in
            (wbump here l, wbump here u)
        (* Like a binary: the ordering join is valid when both arguments are. *)
        | DFG_Join a b =>
            let '(l1, u1) := node_bounds_w dfg tainted dfacts cycles pi fuel' a in
            let '(l2, u2) := node_bounds_w dfg tainted dfacts cycles pi fuel' b in
            (wbump here (wmax_lo l1 l2), wbump here (wmax u1 u2))
        | DFG_Phi c t e =>
            let crit := phi_crit tainted dfacts c pi in
            let '(lc, uc) := node_bounds_w dfg tainted dfacts cycles pi fuel' c in
            let '(lt, ut) := node_bounds_w dfg tainted dfacts cycles (phi_path crit c true pi) fuel' t in
            let '(le, ue) := node_bounds_w dfg tainted dfacts cycles (phi_path crit c false pi) fuel' e in
            (wbump here (wmax_lo lc (if crit then wmax_lo lt le else wmin lt le)),
             wbump here (wmax uc (wmax ut ue)))
        | _ => ((here, pi), (here, pi))
        end
    end.

  Definition node_bounds (dfg: dfg_state) (tainted: list nid_t) (dfacts: list gfact)
      (cycles: list (nid_t * cycle_t)) (pi: list lit) (fuel: nat) (n: nid_t)
      : cycle_t * cycle_t :=
    let '(l, u) := node_bounds_w dfg tainted dfacts cycles pi fuel n in (fst l, fst u).

  (* The action is done when every variable it writes is valid, so the bounds
     are maxima over the roots, counted in CYCLES (combinational is (1, 1)).
     [fst = snd] certifies the action is constant time. *)
  Definition action_bounds_w (dfg: dfg_state) : wcycle * wcycle :=
    let tainted := get_tainted dfg in
    let dfacts := decl_facts dfg in
    let cycles := calc_target_cycle (calc_backward_cost dfg) in
    let '(l, u) :=
      fold_left (fun '(l, u) v =>
                   let '(lv, uv) :=
                     node_bounds_w dfg tainted dfacts cycles [] (List.length (graph dfg)) (snd v) in
                   (wmax_lo l lv, wmax u uv))
                (var_map dfg) ((0, []), (0, [])) in
    ((S (fst l), snd l), (S (fst u), snd u)).

  Definition action_bounds (dfg: dfg_state) : cycle_t * cycle_t :=
    let '(l, u) := action_bounds_w dfg in (fst l, fst u).

  (* Agreeing bounds leave nothing for the two witness paths to distinguish:
     they are then two runs of the same length, which is what makes [fst = snd]
     readable as [constant time]. *)
End Bounds.

(* Node ids, cycle counts and branch literals only, so the verdict is
   independent of the context it was computed in. *)
Record tf_audit := {
  ta_nodes : nat;
  ta_buffers : nat;
  ta_tainted : list nid_t;
  ta_critical : list crit_reason;
  ta_cycles_lo : cycle_t;
  ta_cycles_hi : cycle_t;
  (* the branch literals under which the action hits its lower / upper bound *)
  ta_fast : list lit;
  ta_slow : list lit;
  ta_constant_time : bool;
}.

Section Audit.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation states_var := (tfs_spec_states ctx).
  Local Notation inputs_var := (tfs_spec_inputs ctx).
  Local Notation outputs_var := (tfs_spec_outputs ctx).
  Local Notation spec_action := (tfs_spec_action ctx).
  Local Notation dfg_state := (@dfg_state_t states_var inputs_var outputs_var).

  Definition audit (act: spec_action) : tf_audit :=
    let dfg := build_dfg ctx act in
    let cycles := calc_target_cycle cost_limit (calc_backward_cost ctx cost_limit dfg) in
    let '((lo, pf), (hi, ps)) := action_bounds_w ctx cost_limit dfg in
    {| ta_nodes := List.length (graph dfg);
       ta_buffers := List.length (require_buffer ctx dfg cycles);
       ta_tainted := get_tainted ctx dfg;
       ta_critical := crit_report_all ctx dfg;
       ta_cycles_lo := lo;
       ta_cycles_hi := hi;
       (* the compiler conses as it descends, so reverse into source order *)
       ta_fast := rev pf;
       ta_slow := rev ps;
       ta_constant_time := Nat.eqb lo hi |}.

  (* [ta_constant_time] is not an extra claim: it is exactly the bounds
     collapsing, which is what makes the field readable. *)
  Lemma audit_constant_time_iff_bounds_agree (act: spec_action) :
    ta_constant_time (audit act) = true
    <-> ta_cycles_lo (audit act) = ta_cycles_hi (audit act).
  Proof.
    unfold audit.
    destruct (action_bounds_w ctx cost_limit (build_dfg ctx act)) as [[lo pf] [hi ps]].
    cbn. apply Nat.eqb_eq.
  Qed.

  Definition show_audit (dfg: dfg_state) (a: tf_audit) : string :=
    slines
      ([ "nodes:         " +++ show (ta_nodes a);
         "buffers:       " +++ show (ta_buffers a);
         "tainted nodes: " +++ show (List.length (ta_tainted a));
         "cycles:        " +++
           (if ta_constant_time a
            then show (ta_cycles_lo a)
            else show (ta_cycles_lo a) +++ " .. " +++ show (ta_cycles_hi a));
         "constant time: " +++ (if ta_constant_time a then "yes" else "NO") ]
       ++ (if ta_constant_time a then []
           else [ "  fastest (" +++ show (ta_cycles_lo a) +++ ") when: "
                    +++ show_path ctx dfg (ta_fast a);
                  "  slowest (" +++ show (ta_cycles_hi a) +++ ") when: "
                    +++ show_path ctx dfg (ta_slow a) ])
       ++ [ "critical phis:" ]
       ++ [ show_crit_reasons ctx dfg (ta_critical a) ]).

  Definition audit_report (act: spec_action) : string :=
    show_audit (build_dfg ctx act) (audit act).

  (* The same picture as [dfg_to_dot], plus the buffers the cost limit forced. *)
  Definition audit_dot (act: spec_action) : string :=
    let dfg := build_dfg ctx act in
    let cycles := calc_target_cycle cost_limit (calc_backward_cost ctx cost_limit dfg) in
    dfg_to_dot_annot ctx dfg (get_tainted ctx dfg)
      (map cr_cond (crit_report_all ctx dfg))
      (require_buffer ctx dfg cycles).

End Audit.
