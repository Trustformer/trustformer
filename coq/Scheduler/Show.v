(*! Human-readable rendering of the scheduler's analysis output.

    The analyses in `VariableScheduler.v` answer in node ids: `get_tainted`
    returns a `list nat`, and `crit_report_all` returns things like
    `[CR_no_rule 3; CR_no_rule 6]`.  That is the right internal representation
    and the wrong thing to show a user, who wrote `$tries != #0`, not `3`.

    This file is pure presentation: `string` in, `string` out, no dependency in
    the other direction.  Nothing under `coq/Properties/` imports it, and
    nothing here may change what the compiler emits.

    Legend used throughout: [$x] state variable, [@x] output variable,
    [?x] input, [#n] constant.
!*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Scheduler.Contract.
Require Export Trustformer.Scheduler.VariableScheduler.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Import ListNotations.

Local Infix "+++" := String.append (at level 60, right associativity).

(* ================================================================= *)
(* String plumbing                                                    *)
(* ================================================================= *)

Definition nl : string := String.String (Ascii.ascii_of_nat 10) String.EmptyString.

Definition sjoin (sep: string) (l: list string) : string :=
  match l with
  | [] => ""
  | x :: rest => fold_left (fun acc y => acc +++ sep +++ y) rest x
  end.

Definition slines (l: list string) : string := sjoin nl l.

Definition sbullets (l: list string) : string :=
  slines (map (fun s => "  - " +++ s) l).

(* ================================================================= *)
(* Operators.  These carry no variables, so they render without a     *)
(* context.                                                           *)
(* ================================================================= *)

Definition show_cmp_op (o: tf_comparison_ops) : string :=
  match o with
  | tf_eq => "==" | tf_neq => "!="
  | tf_lt => "<"  | tf_le => "<="
  | tf_gt => ">"  | tf_ge => ">="
  end.

Definition show_binop (o: tf_binary_ops) : string :=
  match o with
  | tf_and => "&" | tf_or => "|" | tf_xor => "^"
  | tf_add => "+" | tf_sub => "-" | tf_mul => "*"
  | tf_cmp n c => show_cmp_op c +++ "[" +++ show n +++ "]"
  end.

Definition show_unop (o: tf_unary_ops) : string :=
  match o with
  | tf_not => "~"
  | tf_resize n => "resize<" +++ show n +++ ">"
  end.

(* ================================================================= *)
(* Criticality reasons carry only node ids, so grouping them needs no *)
(* context either.  [crit_report_all] reports one entry per phi        *)
(* OCCURRENCE, and the same cause typically shows up several times.    *)
(* ================================================================= *)

Definition cr_cond (r: crit_reason) : nid_t :=
  match r with
  | CR_no_rule c => c
  | CR_sources_unknown c _ => c
  | CR_guard_unmet c _ => c
  end.

Definition lits_eqb (a b: list lit) : bool :=
  Nat.eqb (List.length a) (List.length b)
  && forallb (fun p => lit_eqb (fst p) (snd p)) (combine a b).

Definition crit_reason_eqb (x y: crit_reason) : bool :=
  match x, y with
  | CR_no_rule a, CR_no_rule b => Nat.eqb a b
  | CR_sources_unknown a la, CR_sources_unknown b lb =>
      Nat.eqb a b && Nat.eqb (List.length la) (List.length lb)
      && forallb (fun p => Nat.eqb (fst p) (snd p)) (combine la lb)
  | CR_guard_unmet a ga, CR_guard_unmet b gb =>
      Nat.eqb a b && Nat.eqb (List.length ga) (List.length gb)
      && forallb (fun p => lits_eqb (fst p) (snd p)) (combine ga gb)
  | _, _ => false
  end.

Fixpoint tally_aux {A} (eqb: A -> A -> bool) (l: list A) (acc: list (A * nat))
  : list (A * nat) :=
  match l with
  | [] => acc
  | x :: rest =>
      tally_aux eqb rest
        (if existsb (fun p => eqb (fst p) x) acc
         then map (fun p => if eqb (fst p) x then (fst p, S (snd p)) else p) acc
         else acc ++ [(x, 1)])
  end.

(* Preserves first-occurrence order, which is the order the compiler walks. *)
Definition tally {A} (eqb: A -> A -> bool) (l: list A) : list (A * nat) :=
  tally_aux eqb l [].

Section Rendering.

  Context (ctx: TFSchedContext).

  Local Notation states_var := (tfs_spec_states ctx).
  Local Notation inputs_var := (tfs_spec_inputs ctx).
  Local Notation outputs_var := (tfs_spec_outputs ctx).

  Hint Extern 0 (Show states_var) => exact (tfs_spec_states_names ctx) : typeclass_instances.
  Hint Extern 0 (Show inputs_var) => exact (tfs_spec_inputs_names ctx) : typeclass_instances.
  Hint Extern 0 (Show outputs_var) => exact (tfs_spec_outputs_names ctx) : typeclass_instances.

  Local Notation dfg_node := (@dfg_node_t states_var inputs_var outputs_var).
  Local Notation dfg_state := (@dfg_state_t states_var inputs_var outputs_var).

  Definition empty_node : dfg_node := {| nid := 0; op := DFG_Empty; sz := 0 |}.

  Definition node_of (dfg: dfg_state) (n: nid_t) : dfg_node :=
    nth n (graph dfg) empty_node.

  (* ------------------------------------------------------------- *)
  (* Expressions.  [fuel] is a DEPTH limit, not a termination        *)
  (* argument in disguise: branch conditions are shallow, and a      *)
  (* whole cone printed inline is unreadable, so deeper subterms are *)
  (* abbreviated back to their node id.                              *)
  (* ------------------------------------------------------------- *)

  Fixpoint show_node_aux (dfg: dfg_state) (depth: nat) (n: nid_t) : string :=
    match depth with
    | 0 => "n" +++ show n
    | S d =>
        match op (node_of dfg n) with
        | DFG_Const v => "#" +++ show v
        | DFG_Input v => "?" +++ show v
        | DFG_Var (DFG_SVar v) => "$" +++ show v
        | DFG_Var (DFG_OVar v) => "@" +++ show v
        | DFG_Unary o a => show_unop o +++ "(" +++ show_node_aux dfg d a +++ ")"
        | DFG_Resize a => "resize(" +++ show_node_aux dfg d a +++ ")"
        | DFG_Binary o a1 a2 =>
            "(" +++ show_node_aux dfg d a1 +++ " " +++ show_binop o +++ " "
                +++ show_node_aux dfg d a2 +++ ")"
        | DFG_Phi c t e =>
            "(" +++ show_node_aux dfg d c +++ " ? " +++ show_node_aux dfg d t
                +++ " : " +++ show_node_aux dfg d e +++ ")"
        | DFG_Empty => "<empty>"
        end
    end.

  Definition show_node (dfg: dfg_state) (n: nid_t) : string :=
    show_node_aux dfg 4 n.

  (* [node 3] stays in the output: it is what every other analysis speaks,
     and what the reader needs to cross-reference the graph. *)
  Definition show_node_at (dfg: dfg_state) (n: nid_t) : string :=
    show_node dfg n +++ " (node " +++ show n +++ ")".

  Definition show_lit (dfg: dfg_state) (l: lit) : string :=
    (if snd l then "" else "not ") +++ show_node dfg (fst l).

  Definition show_guard (dfg: dfg_state) (g: list lit) : string :=
    match g with
    | [] => "(nothing)"
    | _ => sjoin " and " (map (show_lit dfg) g)
    end.

  (* ------------------------------------------------------------- *)
  (* Criticality                                                     *)
  (* ------------------------------------------------------------- *)

  Definition show_crit_reason (dfg: dfg_state) (r: crit_reason) : string :=
    match r with
    | CR_no_rule c =>
        "branch on " +++ show_node_at dfg c
        +++ " is tainted and no declassification rule targets it"
    | CR_sources_unknown c ss =>
        "branch on " +++ show_node_at dfg c
        +++ " has a rule, but nothing is derivable for "
        +++ sjoin ", " (map (show_node_at dfg) ss)
    | CR_guard_unmet c gs =>
        "branch on " +++ show_node_at dfg c
        +++ " is declassified, but not on this path, which would also have to satisfy "
        +++ sjoin " -- or -- " (map (show_guard dfg) gs)
    end.

  Definition show_times (n: nat) : string :=
    match n with
    | 1 => ""
    | _ => " [" +++ show n +++ " occurrences]"
    end.

  (* One line per distinct cause, with the number of phi occurrences it
     pessimises.  Empty report = the action is already constant time. *)
  Definition show_crit_reasons (dfg: dfg_state) (rs: list crit_reason) : string :=
    match rs with
    | [] => "no phi is critical"
    | _ =>
        sbullets (map (fun p => show_crit_reason dfg (fst p) +++ show_times (snd p))
                      (tally crit_reason_eqb rs))
    end.

  Definition show_crit_report (dfg: dfg_state) : string :=
    show_crit_reasons dfg (crit_report_all ctx dfg).

  (* A path is a conjunction of branch literals, outermost first (the audit
     reverses the compiler's accumulator before handing it over). *)
  Definition show_path (dfg: dfg_state) (pi: list lit) : string :=
    match pi with
    | [] => "any input"
    | _ => sjoin " and " (map (show_lit dfg) pi)
    end.

  (* ------------------------------------------------------------- *)
  (* Graphviz.  The paper draws its DFG figures by hand; this draws   *)
  (* the one the compiler actually built.                             *)
  (* ------------------------------------------------------------- *)

  Definition dot_label (dfg: dfg_state) (n: nid_t) : string :=
    match op (node_of dfg n) with
    | DFG_Const v => "#" +++ show v
    | DFG_Input v => "?" +++ show v
    | DFG_Var (DFG_SVar v) => "$" +++ show v
    | DFG_Var (DFG_OVar v) => "@" +++ show v
    | DFG_Unary o _ => show_unop o
    | DFG_Resize _ => "resize"
    | DFG_Binary o _ _ => show_binop o
    | DFG_Phi _ _ _ => "phi"
    | DFG_Empty => "empty"
    end.

  Definition dot_edge (src: nid_t) (lbl: string) (dst: nid_t) : string :=
    "  n" +++ show src +++ " -> n" +++ show dst +++ " [label=""" +++ lbl +++ """];".

  Definition dot_edges (nd: dfg_node) : list string :=
    match op nd with
    | DFG_Unary _ a => [dot_edge (nid nd) "" a]
    | DFG_Resize a => [dot_edge (nid nd) "" a]
    | DFG_Binary _ a1 a2 => [dot_edge (nid nd) "l" a1; dot_edge (nid nd) "r" a2]
    | DFG_Phi c t e =>
        [dot_edge (nid nd) "c" c; dot_edge (nid nd) "t" t; dot_edge (nid nd) "e" e]
    | _ => []
    end.

  Definition dot_node (dfg: dfg_state) (tainted crit_conds buffers roots: list nid_t)
      (nd: dfg_node) : string :=
    let n := nid nd in
    let critical := match op nd with
                    | DFG_Phi c _ _ => mem_nid c crit_conds
                    | _ => false
                    end in
    let colour := if critical then "#ff9d9d"
                  else if mem_nid n tainted then "#ffe680"
                  else "#ffffff" in
    let shape := if mem_nid n buffers then "box"
                 else if mem_nid n roots then "doubleoctagon"
                 else "ellipse" in
    "  n" +++ show n +++ " [label=""" +++ show n +++ ": " +++ dot_label dfg n
        +++ """, shape=" +++ shape +++ ", style=filled, fillcolor=""" +++ colour +++ """];".

  (* Explicit annotation lists so a caller that already computed them (the
     audit) does not pay for them twice. *)
  Definition dfg_to_dot_annot (dfg: dfg_state) (tainted crit_conds buffers: list nid_t)
    : string :=
    let roots := map snd (var_map dfg) in
    slines
      (["digraph dfg {";
        "  rankdir=BT;";
        "  node [fontname=""monospace""];"]
       ++ map (dot_node dfg tainted crit_conds buffers roots) (graph dfg)
       ++ flat_map dot_edges (graph dfg)
       ++ ["}"]).

  Definition dfg_to_dot (dfg: dfg_state) : string :=
    dfg_to_dot_annot dfg (get_tainted ctx dfg)
      (map cr_cond (crit_report_all ctx dfg)) [].

End Rendering.
