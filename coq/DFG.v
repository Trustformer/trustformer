(*! Data-flow graph datatypes for the variable scheduler.  Below `Contract.v`,
    so `TFSchedContext` can carry declassification rules over a `dfg_state_t`;
    these depend only on the three specification variable types. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.

Require Import Coq.Lists.List.
Import ListNotations.

Section SchedulerTypes.

  Context {states_var: Type}.
  Context {inputs_var: Type}.
  Context {outputs_var: Type}.
  Context {ips_var: Type}.

  Definition nid_t := nat.
  Definition sz_t := nat.

  Inductive dfg_vars_t := 
    | DFG_SVar (v: states_var)
    | DFG_OVar (v: outputs_var).

  Inductive dfg_op_t :=
    | DFG_Const (n: nat)
    | DFG_Input (v: inputs_var)
    | DFG_Var (v: dfg_vars_t)
    | DFG_Unary (op: tf_unary_ops) (arg: nid_t)
    | DFG_Binary (op: tf_binary_ops) (arg1: nid_t) (arg2: nid_t)
    | DFG_Resize (arg: nid_t)
    | DFG_Phi (cond: nid_t) (then_id: nid_t) (else_id: nid_t)
    (* [arg]'s value passes through; its validity lags by [lat] CYCLES, counted
       by the buffer this node gets ([compile_dfg_buffers]). *)
    | DFG_Stall (lat: nat) (arg: nid_t)
    (* A round trip: drive the request, stall, sample the answer.  [en] is the
       call's path condition, SYMBOLIC so a guard materialises no nodes, and a
       drive is a conditional SIDE EFFECT with no [var_map] entry. *)
    | DFG_Drive (p: ips_var) (arg: nid_t) (en: list (nid_t * bool))
    | DFG_Sample (p: ips_var) (tok: nid_t) (en: list (nid_t * bool))
    (* An ORDERING constraint and no value: valid when both arguments are, so a
       second call on an IP waits for the first to answer.  It carries no value,
       hence no relation between its width and its arguments. *)
    | DFG_Join (a: nid_t) (b: nid_t)
    | DFG_Empty                
    .

  Record dfg_node_t := {
    nid : nid_t;
    op : dfg_op_t;
    sz : sz_t;
  }.

  Record dfg_state_t := {
    graph : list dfg_node_t;
    var_map : list (dfg_vars_t * nid_t);
  }.

  Context {A} {buffer_needs: list (list A)}.

  Inductive tf_dfg_states_t :=
    | tf_dfg_done
    | tf_dfg_s (state: states_var)
    | tf_dfg_b (a_idx: Vect.index (length buffer_needs)) (n_idx: Vect.index (length (nth (index_to_nat a_idx) buffer_needs [])))
    | tf_dfg_v (a_idx: Vect.index (length buffer_needs)) (n_idx: Vect.index (length (nth (index_to_nat a_idx) buffer_needs [])))
    (* The scheduler's register for an IP request's {strobe, payload}. *)
    | tf_dfg_ov (p: ips_var)
    .
        
End SchedulerTypes.

(* Declassification: the user's claim that [di_target] is recoverable from
   [di_sources] wherever every literal of [di_guard] holds. *)
Record decl_instance := {
  di_target  : nid_t;
  di_sources : list nid_t;
  di_guard   : list (nid_t * bool);
}.

Section Values.
  Context {states_var inputs_var outputs_var ips_var: Type}.
  Local Notation dfg := (@dfg_state_t states_var inputs_var outputs_var ips_var).

  Definition node_at (g: dfg) (n: nid_t) :
      @dfg_node_t states_var inputs_var outputs_var ips_var :=
    nth n (graph g) {| nid := 0; op := DFG_Empty; sz := 0 |}.

  Definition node_sz (g: dfg) (n: nid_t) : nat := sz (node_at g n).

  (* Bits for every node, each at the node's own width. *)
  Definition valuation (g: dfg) := forall n: nid_t, bits_t (node_sz g n).

  (* How a branch reads its condition: all zeros is false. *)
  Definition nonzero {w} (v: bits_t w) : bool := negb (beq_dec v Bits.zero).

  (* [tf_eval_expr]'s clauses, at result width [w] and argument widths [sa], [sb]. *)
  Definition op1_bits (uop: tf_unary_ops) (w sa: nat) (x: bits_t sa) : bits_t w :=
    match uop with
    | tf_not => Bits.neg (convert x)
    | tf_resize s => convert (convert (szB := s) x)
    | tf_slice s o => Bits.slice o w (convert (szB := slice_pad s o w) (convert (szB := s) x))
    end.

  Definition op2_bits (bop: tf_binary_ops) (w sa sb: nat)
      (x: bits_t sa) (y: bits_t sb) : bits_t w :=
    match bop with
    | tf_and => Bits.and (convert x) (convert y)
    | tf_or  => Bits.or  (convert x) (convert y)
    | tf_xor => Bits.xor (convert x) (convert y)
    | tf_add => Bits.plus  (convert x) (convert y)
    | tf_sub => Bits.minus (convert x) (convert y)
    | tf_mul => convert (Bits.mul (convert (szB := w) x) (convert (szB := w) y))
    | tf_cmp szC cop =>
        let u := convert (szB := szC) x in
        let v := convert (szB := szC) y in
        match cop with
        | tf_eq  => if beq_dec u v then convert (Bits.of_nat 1 1) else convert (Bits.of_nat 1 0)
        | tf_neq => if beq_dec u v then convert (Bits.of_nat 1 0) else convert (Bits.of_nat 1 1)
        | tf_lt  => if Bits.unsigned_lt u v then convert (Bits.of_nat 1 1) else convert (Bits.of_nat 1 0)
        | tf_le  => if Bits.unsigned_le u v then convert (Bits.of_nat 1 1) else convert (Bits.of_nat 1 0)
        | tf_gt  => if Bits.unsigned_gt u v then convert (Bits.of_nat 1 1) else convert (Bits.of_nat 1 0)
        | tf_ge  => if Bits.unsigned_ge u v then convert (Bits.of_nat 1 1) else convert (Bits.of_nat 1 0)
        | tf_slt => if Bits.signed_lt u v then convert (Bits.of_nat 1 1) else convert (Bits.of_nat 1 0)
        end
    | tf_concat hz lz =>
        convert (Bits.app (convert (szB := hz) x) (convert (szB := lz) y))
    | tf_lsr => Bits.lsr (Bits.to_nat (convert (szB := w) y)) (convert (szB := w) x)
    | tf_lsl => Bits.lsl (Bits.to_nat (convert (szB := w) y)) (convert (szB := w) x)
    | tf_asr => Bits.asr (Bits.to_nat (convert (szB := w) y)) (convert (szB := w) x)
    | tf_islice s =>
        Bits.slice (Bits.to_nat (convert (szB := Nat.log2_up (islice_pad s w)) (convert (szB := Nat.log2_up s) y))) w
          (convert (szB := islice_pad s w) (convert (szB := s) x))
    end.

  (* Every operation node holds its operation applied to its arguments; inputs,
     variable reads and the round trip's nodes are free. *)
  Definition consistent (g: dfg) (val: valuation g) : Prop :=
    forall n,
      match op (node_at g n) with
      | DFG_Const c => val n = Bits.of_nat _ c
      | DFG_Unary uop a => val n = op1_bits uop _ _ (val a)
      | DFG_Resize a => val n = convert (val a)
      | DFG_Binary bop a b => val n = op2_bits bop _ _ _ (val a) (val b)
      | DFG_Phi c t e => val n = if nonzero (val c) then convert (val t) else convert (val e)
      | _ => True
      end.

  Definition guard_holds (g: dfg) (val: valuation g) (gd: list (nid_t * bool)) : Prop :=
    forall c b, In (c, b) gd -> nonzero (val c) = b.

  (* The widths [build_dfg] produces: each operation's arguments at the widths it reads them. *)
  Definition well_sized (g: dfg) : Prop :=
    forall n,
      match op (node_at g n) with
      | DFG_Unary tf_not a => node_sz g a = node_sz g n
      | DFG_Unary (tf_resize s) a => node_sz g a = s
      | DFG_Unary (tf_slice s _) a => node_sz g a = s
      | DFG_Binary (tf_cmp w _) a b => node_sz g a = w /\ node_sz g b = w
      | DFG_Binary (tf_concat hz lz) a b => node_sz g a = hz /\ node_sz g b = lz
      | DFG_Binary (tf_islice s) a b => node_sz g a = s /\ node_sz g b = Nat.log2_up s
      | DFG_Binary _ a b => node_sz g a = node_sz g n /\ node_sz g b = node_sz g n
      | DFG_Phi c t e =>
          node_sz g c = 1 /\ node_sz g t = node_sz g n /\ node_sz g e = node_sz g n
      | _ => True
      end.
End Values.

(* A rule and its contract: wherever an instance's guard holds, [dp_extract] gives
   the target's value from the sources' values, in every well-sized graph. *)
Record decl_packet (states_var inputs_var outputs_var ips_var: Type) := {
  dp_rule : @dfg_state_t states_var inputs_var outputs_var ips_var -> list decl_instance;
  dp_extract : forall (g: @dfg_state_t states_var inputs_var outputs_var ips_var)
                      (i: decl_instance),
      valuation g -> bits_t (node_sz g (di_target i));
  dp_sound : forall g i (val w: valuation g),
      well_sized g -> In i (dp_rule g) -> consistent g val ->
      guard_holds g val (di_guard i) ->
      (forall s, In s (di_sources i) -> w s = val s) ->
      val (di_target i) = dp_extract g i w;
}.
Arguments dp_rule {_ _ _ _} _ _.
Arguments dp_extract {_ _ _ _} _ _ _ _.
Arguments dp_sound {_ _ _ _} _ _ _ _ _ _ _ _ _ _.
