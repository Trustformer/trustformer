(*! The attacker's clock: the cycle an action finishes on, computed from the
    design and the public view.  [Definitions.L_pub] calls [latency]. !*)

Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Declassification.Recover.

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* [first_true f fuel k] is the least [n >= k] with [f n], or [k + fuel]. *)
Section FirstTrue.
  Variable f : nat -> bool.

  Fixpoint first_true (fuel k: nat) : nat :=
    match fuel with
    | 0 => k
    | S fuel' => if f k then k else first_true fuel' (S k)
    end.
End FirstTrue.

Section Clock.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation sched  := (tfs_schedule ctx cost_limit).
  Local Notation i_var  := (tfs_spec_inputs ctx).
  Local Notation o_var  := (tfs_spec_outputs ctx).
  Local Notation i_sz   := (tfs_spec_inputs_size ctx).
  Local Notation o_sz   := (tfs_spec_outputs_size ctx).
  Local Notation bneeds := (buffer_needs ctx cost_limit).
  Local Notation a_index := (Vect.index (length (buffer_needs ctx cost_limit))).

  Definition node_op (act: tfs_action sched) (n: nid_t) :=
    op (nth n (graph (build_dfg ctx act)) {| nid := 0; op := DFG_Empty; sz := 0 |}).

  Definition stall_lat_of (act: tfs_action sched) (n: nid_t) : option nat :=
    match node_op act n with DFG_Stall l _ => Some l | _ => None end.

  (* SATURATION RANK.  Ranking by node id alone is unsound in V4: a stall makes
     its consumer wait [lat] cycles, not one.  The rank is the id plus the extra
     cycles every stall UP TO AND INCLUDING it costs -- including its own, so a
     stall's rank already covers its wait and everything above it sits past it. *)
  Definition stall_weight (act: tfs_action sched) (n: nid_t) : nat :=
    match stall_lat_of act n with Some l => pred l | None => 0 end.

  Fixpoint node_rank (act: tfs_action sched) (n: nat) : nat :=
    match n with
    | 0 => stall_weight act 0
    | S m => S (node_rank act m) + stall_weight act (S m)
    end.

  (* SETTLE BOUND.  Buffers rank by NODE ID (args_lt_fwd), so a buffer caching
     node [n] settles by cycle [n] and the run is bounded by the graph size.
     The target cycle is NOT a rank: two buffers can share one. *)
  Definition settle_bound (act: tfs_action sched) : nat :=
    node_rank act (length (graph (build_dfg ctx act))).

  (* The attacker's copy of the validity registers, one entry per buffer slot
     in the order [buffer_needs] lists them. *)
  Definition vvec := list bool.

  Definition slot_valid (vv: vvec) (j: nat) : bool := nth j vv false.

  (* A node's validity as the attacker computes it: the buffer slots it reads
     come from [vv], and an untainted phi's selector from [vals].  It mirrors
     [compile_dfg_expr_aux]'s second component. *)
  Fixpoint avalid (act: tfs_action sched) (vals: known (build_dfg ctx act))
      (vv: vvec) (bufs: list (nid_t * (nat * sz_t)))
      (fuel: nat) (pi: list lit) (n: nid_t) : bool :=
    match fuel with
    | 0 => false
    | S f =>
        match BitsToLists.list_assoc bufs n with
        | Some (j, _) => slot_valid vv j
        | None =>
            let rec := avalid act vals vv bufs f in
            match node_op act n with
            | DFG_Const _ => true
            | DFG_Input _ => true
            | DFG_Var _ => true
            | DFG_Unary _ a => rec pi a
            | DFG_Resize a => rec pi a
            | DFG_Binary _ a b => andb (rec pi a) (rec pi b)
            | DFG_Stall _ a => rec pi a
            | DFG_Sample _ tok _ => rec pi tok
            | DFG_Join a b => andb (rec pi a) (rec pi b)
            | DFG_Drive _ a en =>
                fold_right (fun l acc => andb (rec pi (fst l)) acc) (rec pi a) en
            | DFG_Phi c t e =>
                let crit := phi_crit (get_tainted ctx (build_dfg ctx act))
                                     (decl_facts ctx (build_dfg ctx act)) c pi in
                if crit
                then andb (andb (rec (phi_path crit c true pi) t)
                                (rec (phi_path crit c false pi) e))
                          (rec pi c)
                else andb (rec pi c)
                          (match vals c with
                           | Some v =>
                               rec (phi_path crit c (nonzero v) pi)
                                   (if nonzero v then t else e)
                           | None => false
                           end)
            | DFG_Empty => false
            end
        end
    end.

  (* ---- THE SHADOW MACHINE: the registers an attacker can keep ----
     Validity bits and stall counts, one per buffer slot.  No value register
     appears: a validity reads other validities, the counts, and the
     selectors, and nothing else. *)
  Definition sstate := (vvec * list nat)%type.

  (* The table a slot's own gate is compiled against: the action's, minus the
     slot itself, since a buffer recomputes from its sources. *)
  Definition gate_bufs (a_idx: a_index) (n: nid_t)
    : list (nid_t * (nat * sz_t)) :=
    filter (fun '(b, _) => negb (Nat.eqb b n))
           (nth (index_to_nat a_idx) bneeds []).

  Definition slot_gate (act: tfs_action sched) (a_idx: a_index)
      (vals: known (build_dfg ctx act)) (vv: vvec) (n: nid_t) : bool :=
    avalid act vals vv (gate_bufs a_idx n)
      (length (graph (build_dfg ctx act))) [] n.

  (* ONE CYCLE of one slot, read off [compile_dfg_buffers]: a stall's bit rises
     [lat] cycles after its gate and the count advances until it saturates;
     every other slot's bit follows its gate. *)
  Definition slot_step (act: tfs_action sched) (a_idx: a_index)
      (vals: known (build_dfg ctx act)) (st: sstate)
      (e: nid_t * (nat * sz_t)) : bool * nat :=
    let g := slot_gate act a_idx vals (fst st) (fst e) in
    let c := nth (fst (snd e)) (snd st) 0 in
    match stall_lat_of act (fst e) with
    | Some l => (andb g (Nat.eqb c (pred l)),
                 if andb g (negb (Nat.eqb c (pred l))) then S c else c)
    | None => (g, c)
    end.

  Definition sstep (act: tfs_action sched) (a_idx: a_index)
      (vals: known (build_dfg ctx act)) (st: sstate) : sstate :=
    let next := map (slot_step act a_idx vals st)
                    (nth (index_to_nat a_idx) bneeds []) in
    (map fst next, map snd next).

  Definition sstart (a_idx: a_index) : sstate :=
    (repeat false (length (nth (index_to_nat a_idx) bneeds [])),
     repeat 0 (length (nth (index_to_nat a_idx) bneeds []))).

  Fixpoint srun (act: tfs_action sched) (a_idx: a_index)
      (vals: known (build_dfg ctx act)) (k: nat) : sstate :=
    match k with
    | 0 => sstart a_idx
    | S m => sstep act a_idx vals (srun act a_idx vals m)
    end.

  (* The done flag the design assigns: every root of the action has settled. *)
  Definition adone (act: tfs_action sched) (a_idx: a_index)
      (vals: known (build_dfg ctx act)) (vv: vvec) : bool :=
    forallb (fun r => avalid act vals vv (nth (index_to_nat a_idx) bneeds [])
                        (length (graph (build_dfg ctx act))) [] r)
            (nodup Nat.eq_dec (map snd (var_map (build_dfg ctx act)))).

  (* The register takes its value from the cycle before, so cycle 0 is never
     done: it is the start state, whose flag the previous action left. *)
  Definition pdone_test (act: tfs_action sched) (a_idx: a_index)
      (vals: known (build_dfg ctx act)) (k: nat) : bool :=
    match k with
    | 0 => false
    | S m => adone act a_idx vals (fst (srun act a_idx vals m))
    end.

  (* The first cycle at which the attacker's copy of the validity registers
     says every root has settled. *)
  Definition L_pub_at (act: tfs_action sched) (a_idx: a_index)
      (vals: known (build_dfg ctx act)) : nat :=
    first_true (pdone_test act a_idx vals) (S (settle_bound act)) 0.

  (* The node values the attacker's recipe works out from what it sees. *)
  Definition recovered (act: tfs_action sched)
      (sin: forall v: i_var, option (bits_t (i_sz v)))
      (spre spost: forall o: o_var, option (bits_t (o_sz o)))
    : known (build_dfg ctx act) :=
    Recover.recover (p_eq := tfs_spec_ips_eq_dec ctx) (tfs_spec_ip ctx)
      (tfs_spec_decls ctx) (build_dfg ctx act)
      (Recover.seed i_sz o_sz (build_dfg ctx act) sin spre spost)
      (Recover.rounds (tfs_spec_decls ctx) (build_dfg ctx act)).

  Definition latency (act: tfs_action sched)
      (sin: forall v: i_var, option (bits_t (i_sz v)))
      (spre spost: forall o: o_var, option (bits_t (o_sz o))) : nat :=
    match index_of_nat (length bneeds)
            (@finite_index _ (tfs_action_fin sched) act) with
    | Some a_idx => L_pub_at act a_idx (recovered act sin spre spost)
    | None => 0            (* unreachable: the table has a row per action *)
    end.

End Clock.
