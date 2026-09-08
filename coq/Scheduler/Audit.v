(*! One entry point for [is this design safe, and what does it cost].

    Answering that today means calling `get_tainted`, `crit_report_all`,
    `action_bounds` and `require_buffer` separately and knowing what each
    returns.  `audit` runs all of them on one action and packs the answers into
    a record; `audit_report` renders that record; `audit_dot` draws it.

    Like `Show.v` this is presentation only -- nothing under `coq/Properties/`
    imports it, and it cannot change what the compiler emits.
!*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Scheduler.Contract.
Require Export Trustformer.Scheduler.Show.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Import ListNotations.

Local Infix "+++" := String.append (at level 60, right associativity).

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
    let cycles := calc_target_cycle cost_limit (calc_backward_cost ctx dfg) in
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
    let cycles := calc_target_cycle cost_limit (calc_backward_cost ctx dfg) in
    dfg_to_dot_annot ctx dfg (get_tainted ctx dfg)
      (map cr_cond (crit_report_all ctx dfg))
      (require_buffer ctx dfg cycles).

End Audit.
