(* Small proof moves the scheduler proofs repeat.  Tactics only: they load
   before the lemmas they would name, so a caller passes those in. *)

Require Import Coq.Lists.List.
Require Import Trustformer.Scheduler.Build.

(* Split on a DFG op, naming its fields the same way in every proof. *)
Tactic Notation "case_op" constr(o) "as" ident(Hop) :=
  destruct o as [c | v | v | op1 arg | op1 arg1 arg2 | arg | cnd tid eid
                | slat sa | dov dn den | siv sn sen | ja jb | ] eqn:Hop.

(* [In x (get_args ctx node)] for an argument [x] of the op [Hop] names (or of
   an op already in the goal), a guard literal's [x] given as [In l en]. *)
Ltac in_args Hop :=
  unfold get_args; try rewrite Hop;
  first [ left; reflexivity | right; left; reflexivity
        | right; right; left; reflexivity | right; apply in_map; assumption ].

(* Read a fact [lem] stated of a builder run at that run, [E: m s = (x, s1)]. *)
Ltac run_fact lem E :=
  let H := fresh "H" in pose proof lem as H; rewrite E in H; exact H.
