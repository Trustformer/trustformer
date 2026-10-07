(*! Step 5 of the variable scheduler: which nodes an attacker can already
    compute.  [get_tainted] is the fixed point of "a node is public when it is
    an attacker-visible destination, or a declassification rule recovers it
    from public sources"; [decl_facts] records the path guard each
    declassification needed, so the code generator can check it. !*)

Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Koika.BitsToLists.

Require Import Trustformer.Utils.
Require Import Trustformer.Syntax.
Require Export Trustformer.DFG.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Build.

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.

Import ListNotations.

Section Taint.

  Context (ctx: TFSchedContext).


  Local Notation states_var := (tfs_spec_states ctx).

  Local Notation inputs_var := (tfs_spec_inputs ctx).
  Local Notation inputs_var_class := (tfs_spec_inputs_class ctx).

  Local Notation outputs_var := (tfs_spec_outputs ctx).
  Local Notation outputs_var_class := (tfs_spec_outputs_class ctx).

  Local Notation ips_var := (tfs_spec_ips ctx).

  Local Notation spec_action := (tfs_spec_action ctx).
  Local Notation spec_action_fin := (tfs_spec_action_fin ctx).

  
  Local Notation dfg_op := (@dfg_op_t states_var inputs_var outputs_var ips_var).
  Local Notation dfg_node := (@dfg_node_t states_var inputs_var outputs_var ips_var).
  Local Notation dfg_state := (@dfg_state_t states_var inputs_var outputs_var ips_var).
  Local Notation get_args := (Build.get_args ctx).

  (* ============================== *)
  (* = Step 5: Taint Analysis     = *)
  (* ============================== *)

  (* Declassification sites: the roots of assignments to destinations the
     attacker observes, so [DFG_OVar] filtered on the DECLARED class and
     [DFG_SVar] excluded.  GENERAL_REQUIREMENTS.md 1.1, REVIEW.md 2.3. *)
  Definition public_dsts (dfg: dfg_state) : list (nid_t) :=
    map snd (filter (fun '(v, _) =>
      match v with
      | DFG_OVar o => match outputs_var_class o with
                      | Public => true
                      | Secret => false
                      end
      | DFG_SVar _ => false
      end) (var_map dfg)).

  (* Every declassification instance the user's rules emit for this DFG.
     Instances are generated from the current graph, so node ids can never go
     stale across a re-elaboration. *)
  Definition node_op_at (dfg: dfg_state) (n: nid_t) : dfg_op :=
    op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0; |}).

  (* The round trip's own nodes are plumbing, not values a rule may speak
     about: a stall is a counter, a drive is a message in flight, a join is an
     ordering edge, and a sample's answer is public only as far as [ip_fn] is
     reversible, which no rule states.  A rule naming one of them is dropped.
     It also keeps a rule on the STALL -- trivially sound, since a counter
     carries no value -- from declassifying the answer behind it. *)
  Definition declassifiable (dfg: dfg_state) (n: nid_t) : bool :=
    match node_op_at dfg n with
    | DFG_Stall _ _ | DFG_Drive _ _ _ | DFG_Sample _ _ _ | DFG_Join _ _ => false
    | _ => true
    end.

  Definition decl_instances (dfg: dfg_state) : list decl_instance :=
    filter (fun i => declassifiable dfg (di_target i))
           (flat_map (fun r => dp_rule r dfg) (tfs_spec_decls ctx)).

  (* Only unconditional instances may seed the taint fold: a node that is
     derivable merely on some path is not unconditionally untainted. *)
  Definition uncond_instances (dfg: dfg_state) : list decl_instance :=
    filter (fun i => match di_guard i with [] => true | _ => false end)
           (decl_instances dfg).

  Definition mem_nid (n: nid_t) (l: list nid_t) : bool := existsb (Nat.eqb n) l.

  (* Re-adding a target already in [acc] would let the accumulator grow by
     [|instances|] on every one of the [length (graph dfg)] iterations. *)
  Definition saturate_step (dfg: dfg_state) (acc: list nid_t) : list nid_t :=
    fold_left
      (fun acc i =>
         if forallb (fun s => mem_nid s acc) (di_sources i)
            && negb (mem_nid (di_target i) acc)
         then di_target i :: acc
         else acc)
      (uncond_instances dfg) acc.

  (* [saturate_step] only ever adds nodes, so an unchanged length means the
     fixpoint is reached and the remaining rounds would be idle. *)
  Fixpoint saturate (fuel: nat) (dfg: dfg_state) (acc: list nid_t) : list nid_t :=
    match fuel with
    | 0 => acc
    | S f =>
        let acc' := saturate_step dfg acc in
        if Nat.eqb (length acc') (length acc) then acc else saturate f dfg acc'
    end.

  (* Constants and public inputs agree across any two runs, so they are
     derivable under the empty guard and seed both saturations. *)
  (* Values that enter the graph already known to the attacker: constants, and
     inputs declared [Public].  A [Secret] input comes from inside the trust
     boundary, so it belongs with the taint sources. *)
  Definition trivially_public (dfg: dfg_state) : list nid_t :=
    filter (fun k => match op (nth k (graph dfg)
                                 {| nid := 0; op := DFG_Empty; sz := 0 |}) with
                     | DFG_Const _ => true
                     | DFG_Input v => match inputs_var_class v with
                                      | Public => true
                                      | Secret => false
                                      end
                     | _ => false
                     end)
           (List.seq 1 (length (graph dfg) - 1)).

  (* Every node the attacker can derive a value for. Whitebox untainting is the
     saturation below; it must stay computable without the taint set, since the
     fold below consumes this as a seed. *)
  Definition untainted_roots (dfg: dfg_state) : list (nid_t) :=
    saturate (length (graph dfg)) dfg (public_dsts dfg ++ trivially_public dfg).

  (* ============================== *)
  (* = Guards and their checker   = *)
  (* ============================== *)

  (* A path guard is a conjunction of selector literals: [(c, true)] means the
     then-branch of the phi with condition [c] was taken. *)
  Definition lit := (nid_t * bool)%type.

  Definition lit_eqb (x y: lit) : bool :=
    Nat.eqb (fst x) (fst y) && Bool.eqb (snd x) (snd y).

  Definition guard_incl (g pi: list lit) : bool :=
    forallb (fun a => existsb (lit_eqb a) pi) g.

  Definition get_tainted (dfg: dfg_state) : list (nid_t) :=
    let untainted := untainted_roots dfg in
    let aux (taint_map: list (nid_t)) (node : dfg_node) : list (nid_t) :=
      let args := get_args node in
      (* Only a read of pre-action secret state is a taint source: inputs and reads of
         the pre-action output state are both visible to the attacker. *)
      (* Taint SOURCES, one rule per point a value enters the graph: a constant
         is public, an input and a [DFG_OVar] take their declared class, and a
         [DFG_SVar] is secret -- states ARE the secrets under the attacker model. *)
      let self_tainted := match op node with
        | DFG_Var (DFG_SVar _) => true
        | DFG_Var (DFG_OVar o) => match outputs_var_class o with
                                  | Public => false
                                  | Secret => true
                                  end
        | DFG_Input v => match inputs_var_class v with
                         | Public => false
                         | Secret => true
                         end
        (* A sample is [ip_fn] of its request, so it is exactly as secret as
           that request: its token runs back through the stall to the drive,
           which carries the payload and the guard. *)
        | _ => false
        end in
      (* If node depends on secrets it is tainted *)
      let is_tainted := self_tainted || existsb (fun arg_id =>
        match mem arg_id taint_map with
        | inl m => true
        | inr _ => false
        end) args 
      in
      (* An output node is declassified here. *)
      match mem (nid node) untainted with
        | inl m => taint_map
        | inr _ => if is_tainted then (nid node) :: taint_map else taint_map
      end
    in
    fold_left aux (graph dfg) [].


  (* Transitive constant-time tagging is deliberately absent: only a *derivable*
     latency is required, and a critical phi already waits for both branches.
     See agents/taint-tagging-soundness/PLAN.md issue E. *)

  (* Facts "node [c] is derivable whenever guard [g] holds", seeded from
     [untainted_roots] and saturated by [decl_compose].  DISJUNCTION is several
     entries for one node, hence the Cartesian product below. *)
  Definition gfact := (nid_t * list lit)%type.

  Definition gfacts_of (base: list gfact) (c: nid_t) : list (list lit) :=
    map snd (filter (fun f => Nat.eqb (fst f) c) base).

  Definition declassified_at (base: list gfact) (c: nid_t) (pi: list lit) : bool :=
    existsb (fun g => guard_incl g pi) (gfacts_of base c).

  (* A fact already known under a weaker guard makes the new one redundant. *)
  Definition gsubsumed (base: list gfact) (c: nid_t) (g: list lit) : bool :=
    existsb (fun g0 => guard_incl g0 g) (gfacts_of base c).

  (* Empty when some source has no fact at all. *)
  Fixpoint gcombine (base: list gfact) (ss: list nid_t) : list (list lit) :=
    match ss with
    | [] => [[]]
    | s :: rest =>
        flat_map (fun g => map (fun gr => g ++ gr) (gcombine base rest))
                 (gfacts_of base s)
    end.

  Definition gadd_of (i: decl_instance) (acc: list gfact) (gs: list lit)
    : list gfact :=
    if gsubsumed acc (di_target i) (di_guard i ++ gs) then acc
    else acc ++ [(di_target i, di_guard i ++ gs)].

  Definition gstep1 (acc: list gfact) (i: decl_instance) : list gfact :=
    fold_left (gadd_of i) (gcombine acc (di_sources i)) acc.

  Definition gsaturate_step (dfg: dfg_state) (base: list gfact) : list gfact :=
    fold_left gstep1 (decl_instances dfg) base.

  Fixpoint gsaturate (fuel: nat) (dfg: dfg_state) (base: list gfact) : list gfact :=
    match fuel with
    | 0 => base
    | S f =>
        let base' := gsaturate_step dfg base in
        if Nat.eqb (length base') (length base) then base else gsaturate f dfg base'
    end.

  Definition decl_facts (dfg: dfg_state) : list gfact :=
    gsaturate (length (graph dfg)) dfg
      (map (fun n => (n, [])) (untainted_roots dfg)).

End Taint.
