(* Small proof moves the scheduler proofs repeat.  Tactics only: they load
   before the lemmas they would name, so a caller passes those in. *)

Require Import Coq.Lists.List.
Require Import Trustformer.Scheduler.Build.

(* Split on a DFG op, naming its fields the same way in every proof, so a new
   node kind adds its branch here rather than at each such split.  A name
   already taken gets a fresh variant, so a discarded branch never clashes. *)
Ltac case_op_names o Hop split_vars :=
  let c := fresh "c" in let v := fresh "v" in let sv := fresh "sv" in
  let ov := fresh "ov" in let op1 := fresh "op1" in let arg := fresh "arg" in
  let arg1 := fresh "arg1" in let arg2 := fresh "arg2" in let cnd := fresh "cnd" in
  let tid := fresh "tid" in let eid := fresh "eid" in let slat := fresh "slat" in
  let sarg := fresh "sarg" in let dip := fresh "dip" in let darg := fresh "darg" in
  let den := fresh "den" in let sip := fresh "sip" in let stok := fresh "stok" in
  let sen := fresh "sen" in let ja := fresh "ja" in let jb := fresh "jb" in
  match split_vars with
  | false =>
      destruct o as [c | v | v | op1 arg | op1 arg1 arg2 | arg | cnd tid eid
                    | slat sarg | dip darg den | sip stok sen | ja jb | ] eqn:Hop
  | true =>
      destruct o as [c | v | [sv | ov] | op1 arg | op1 arg1 arg2 | arg | cnd tid eid
                    | slat sarg | dip darg den | sip stok sen | ja jb | ] eqn:Hop
  end.
Tactic Notation "case_op" constr(o) "as" ident(Hop) := case_op_names o Hop false.
Tactic Notation "case_op" constr(o) :=
  let H := fresh "Hop" in case_op o as H; clear H.
(* The same, a variable read split into a state's [sv] and an output's [ov]. *)
Tactic Notation "case_op_vars" constr(o) "as" ident(Hop) := case_op_names o Hop true.
Tactic Notation "case_op_vars" constr(o) :=
  let H := fresh "Hop" in case_op_vars o as H; clear H.

(* [In x (get_args ctx node)] for an argument [x] of the op [Hop] names (or of
   an op already in the goal), a guard literal's [x] given as [In l en]. *)
Ltac in_args Hop :=
  unfold get_args; try rewrite Hop;
  first [ left; reflexivity | right; left; reflexivity
        | right; right; left; reflexivity | right; apply in_map; assumption ].

(* Read a fact [lem] stated of a builder run at that run, [E: m s = (x, s1)]. *)
Ltac run_fact lem E :=
  let H := fresh "H" in pose proof lem as H; rewrite E in H; exact H.

(* A premise about each node and its register, from a per-register fact [H],
   through the one-node-per-register bridge [lem] (each use marks one). *)
Ltac per_node lem Halign H :=
  let n := fresh "n" in let i := fresh "n_idx" in let Hc := fresh "Hc" in
  intros n i Hc; rewrite <- (lem _ _ i n Halign Hc); apply H.
