(*! The vocabulary the guarantees are stated in.  Everything a theorem in
    coq/Theorems/ mentions is defined here or in the compiler it talks about, so
    this file plus the four statement files are the whole proof-layer audit.
    The proofs themselves live under Internal/. !*)

Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Export Trustformer.Scheduler.Schedule.
Require Import Trustformer.Backend.Lowering.
Require Import Trustformer.Declassification.Recover.

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

(* The scheduler record is huge; deprioritise unfolding it during conversion. *)
Strategy 1000 [tfs_schedule].

(* [first_true f fuel k] is the least [n >= k] with [f n], or [k + fuel]. *)
Section FirstTrue.
  Variable f : nat -> bool.

  Fixpoint first_true (fuel k: nat) : nat :=
    match fuel with
    | 0 => k
    | S fuel' => if f k then k else first_true fuel' (S k)
    end.
End FirstTrue.

Section SchedulerWorld.

  (* The variable scheduler is parameterised by a source scheduling context and
     a per-cycle cost limit; every name below is relative to those. *)
  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation sched := (tfs_schedule ctx cost_limit).

  (* ---- Source (spec) world ---- *)
  Local Notation s_var := (tfs_spec_states ctx).
  Local Notation i_var := (tfs_spec_inputs ctx).
  Local Notation o_var := (tfs_spec_outputs ctx).
  Local Notation s_sz  := (tfs_spec_states_size ctx).
  Local Notation i_sz  := (tfs_spec_inputs_size ctx).
  Local Notation o_sz  := (tfs_spec_outputs_size ctx).

  Local Notation src_st_env  := (ContextEnv.(env_t) (tf_states_type s_sz)).
  Local Notation src_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation src_sys_state := (src_st_env * src_out_env)%type.

  (* ---- Scheduled (target) world ---- *)
  Local Notation sched_st_env  := (ContextEnv.(env_t) (tf_states_type (tfs_states_size sched))).
  Local Notation sched_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation sched_sys_state := (sched_st_env * sched_out_env)%type.

  Local Notation p_var  := (tfs_spec_ips ctx).
  Local Notation bneeds := (buffer_needs ctx cost_limit).
  Local Notation si_var := (tfs_inputs sched).
  Local Notation si_sz  := (tfs_inputs_size sched).
  Local Notation ss_sz  := (tfs_states_size sched).
  Local Notation oo_sz  := (tfs_outputs_size sched).

  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).
  Local Notation sched_input_t :=
    (forall x : tfs_inputs sched, type_denote (tf_inputs_type (tfs_inputs_size sched) x)).

  (* What each IP presents on its response channel during one cycle. *)
  Local Notation resp_val :=
    (forall p : tfs_ips sched, bits_t (ip_resp_sz (tfs_ip sched p))).


  (* [tf_dfg_ov p] carries {strobe, payload} with the payload in the low bits,
     and holds a request's payload from its pulse until the next one. *)
  Definition drive_payload (ss: sched_sys_state) (p: tfs_ips sched)
    : bits_t (ip_req_sz (tfs_ip sched p)) :=
    Bits.slice 0 (ip_req_sz (tfs_ip sched p))
      ((fst ss).[tfs_drive_reg sched p]).

  (* The request strobe the IP sees on the port: one cycle per pulse. *)
  Definition port_strobe (ss: sched_sys_state) (p: tfs_ips sched) : bits_t 1 :=
    Bits.slice (ip_req_sz (tfs_ip sched p)) 1
      ((fst ss).[tfs_drive_reg sched p]).

  (* A [DFG_Sample] reads the response channel LIVE, so a cycle's inputs are the
     action's own plus whatever each IP is presenting that cycle. *)
  Definition sched_input (input: input_t) (r: resp_val) : sched_input_t :=
    fun x => match x with
             | inl v => input v
             | inr p => r p
             end.

  (* ---- One scheduled cycle and its bounded iteration ---- *)
  Definition sched_step (act: tfs_action sched) (ss: sched_sys_state) (input: sched_input_t)
    : sched_sys_state :=
    tfs_next_cycle sched act ss input.

  (* [resp k] is what the IPs present during cycle [k]. *)
  Fixpoint run_n (n: nat) (act: tfs_action sched) (input: input_t) (resp: nat -> resp_val) (ss: sched_sys_state) : sched_sys_state :=
    match n with
    | 0 => ss
    | S k => let ss1 := run_n k act input resp ss in
             sched_step act ss1 (sched_input input (resp k))
    end.

  (* THE IP's DATASHEET.  A request strobed on the port and left undisturbed for
     the IP's flight time is answered [ip_lat] cycles after the pulse that sent
     it; at every other cycle the channel promises nothing. *)
  Definition ip_contract (act: tfs_action sched) (input: input_t) (resp: nat -> resp_val) (ss0: sched_sys_state) : Prop :=
    forall (p: tfs_ips sched) (s: nat),
      port_strobe (run_n s act input resp ss0) p = Bits.ones 1 ->
      (forall w, s < w -> w < s + pred (ip_lat (tfs_ip sched p)) ->
         port_strobe (run_n w act input resp ss0) p = Bits.zero) ->
      resp (s + pred (ip_lat (tfs_ip sched p))) p
      = ip_fn (tfs_ip sched p) (drive_payload (run_n s act input resp ss0) p).

  (* The done flag is set when the tf_dfg_done register is non-zero. *)
  Definition done_set (ss: sched_sys_state) : Prop :=
    (fst ss).[tfs_done_signal sched] <> Bits.zero.

  (* done_set is decidable (a size-1 register is zero or all-ones). *)
  Lemma done_set_dec (ss: sched_sys_state) : {done_set ss} + {~ done_set ss}.
  Proof.
    unfold done_set.
    destruct (eq_dec ((fst ss).[tfs_done_signal sched]) Bits.zero) as [H | H].
    - right. intro Hc. apply Hc. exact H.
    - left. exact H.
  Qed.

  (* Registers that must start zeroed: the done flag and every validity bit.
     (Buffer value registers tf_dfg_b may hold arbitrary data, since their
     validity bit is 0.) *)
  (* A stall's buffer is a COUNTER, so its start value is observable: the
     validity it publishes is "counter = lat-1".  The hardware resets it --
     [reset_states] lists [tf_dfg_b] beside [tf_dfg_v] and [maps_to] zeroes it
     -- so saying so here is reading the design, not strengthening it. *)
  Definition zeroed_at_start (x: tfs_states sched) : Prop :=
    match x with
    | tf_dfg_b _ _ => True
    | tf_dfg_v _ _ => True
    | tf_dfg_done  => True
    | _            => False
    end.

  (* Starting relation between a spec state and a scheduled state. *)
  Definition start_rel (sp: src_sys_state) (ss: sched_sys_state) : Prop :=
    snd ss = snd sp                                     (* outputs coincide *)
    /\ maps_from ctx bneeds (fst ss) = fst sp       (* tf_dfg_s slots = spec state *)
    /\ (forall x, zeroed_at_start x -> (fst ss).[x] = Bits.zero).

  Definition node_op (act: tfs_action sched) (n: nid_t) :=
    op (nth n (graph (build_dfg ctx act)) {| nid := 0; op := DFG_Empty; sz := 0 |}).

  Definition stall_lat_of (act: tfs_action sched) (n: nid_t) : option nat :=
    match node_op act n with DFG_Stall l _ => Some l | _ => None end.

  Definition is_sample_of (act: tfs_action sched) (n: nid_t) : bool :=
    match node_op act n with DFG_Sample _ _ _ => true | _ => false end.

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

  (* The buffers a reference expression KEEPS: exactly the sample ones.  This
     is [guard_expr]'s [sbufs] -- "buffers are substituted only for samples,
     every other source is stable across the action".  A sample reads a LIVE
     wire and its buffer LATCHES, so inlining through one would compare a
     latched answer against whatever the port carries now; with two calls on a
     port those differ, and MARS's Quote has eight samples on one. *)
  Definition sample_bufs
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
    : list (nid_t * (nat * sz_t)) :=
    filter (fun '(n, _) => is_sample_of act n)
           (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) []).

  (* Reference expression for DFG node n of act: inlined down to the sample
     buffers, which stand for the answers already received. *)
  Definition node_ref_expr
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (n: nat) : @tf_expr (tfs_states sched) si_var o_var :=
    fst (compile_dfg_expr ctx bneeds
           (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n
           (sample_bufs act a_idx)).

  (* The buffer-free value of forward-graph node [n], demanded at width [szB],
     in scheduler state [ss].  This is what [dfg_action_semantics] talks about. *)
  Definition nval (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (ss: sched_sys_state) (input: sched_input_t) (szB: nat) (n: nid_t) : bits_t szB :=
    tf_eval_expr ss_sz si_sz oo_sz (szB := szB) (node_ref_expr act a_idx n) ss input.

  (* [a_idx] indexes the SAME action as [act]: buffer_needs is built by mapping
     over spec_all_actions, so length (buffer_needs …) = length spec_all_actions
     and act's slot is finite_index act. *)
  Definition act_idx_aligned
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit))) : Prop :=
    index_to_nat a_idx = @finite_index _ (tfs_action_fin sched) act.


  (* ================================================================ *)
  (* The attacker model: what the timing guarantees are stated over.     *)
  (* ================================================================ *)

  (* ---- what the attacker model and the latency function are stated over ---- *)
  Local Notation node_t  := (@dfg_node_t s_var i_var o_var p_var).
  Local Notation a_index := (Vect.index (length (buffer_needs ctx cost_limit))).
  Local Notation o_cls   := (tfs_spec_outputs_class ctx).
  Local Notation ips     := (tfs_spec_ip ctx).
  Local Notation eval1 e ss input :=
    (tf_eval_expr ss_sz si_sz oo_sz (szB := 1) e ss input).
  Local Notation rvalid act a_idx pi n ss input :=
    (eval1 (snd (compile_dfg_expr_at ctx bneeds pi
                   (length (graph (build_dfg ctx act))) a_idx
                   (build_dfg ctx act) n (sample_bufs act a_idx)))
       ss input) (only parsing).
  Local Notation nsz act n :=
    (sz (nth n (graph (build_dfg ctx act))
           {| nid := 0; op := DFG_Empty; sz := 0 |})).
  Local Notation ss_run  := run_n.
  Local Notation ss_done := done_set.
  Local Notation spec_run act sp input :=
    (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act)
       sp input).
  Local Notation sys_state :=
    (ContextEnv.(env_t) (tf_states_type s_sz)
     * ContextEnv.(env_t) (tf_outputs_type o_sz))%type.
  Local Notation run ops sys input :=
    (tf_ops_run s_sz i_sz o_sz ips ops sys input).
  Local Notation ev w e sys input :=
    (tf_eval_expr s_sz i_sz o_sz (szB := w) e sys input).

  Definition is_plumbing (act: tfs_action sched) (n: nid_t) : bool :=
    match node_op act n with
    | DFG_Stall _ _ | DFG_Drive _ _ _ | DFG_Join _ _ => true
    | _ => false
    end.

  (* [decl_instances] drops a rule that names one of these, and the builder
     puts none of them in [var_map], so none is ever declassified. *)
  Definition plumbing_not_root (act: tfs_action sched) : Prop :=
    forall n, is_plumbing act n = true ->
      ~ List.In n (untainted_roots ctx (build_dfg ctx act)).

  (* [dataflow_ops] emits a drive at its IP's request width. *)
  Definition drives_sized (act: tfs_action sched) : Prop :=
    forall n (p: p_var) av en,
      node_op act n = DFG_Drive p av en ->
      sz (nth n (graph (build_dfg ctx act))
           {| nid := 0; op := DFG_Empty; sz := 0 |}) = ip_req_sz (tfs_spec_ip ctx p).

  (* [dataflow_ops] compiles a branch condition at width 1, so every literal a
     drive records for its path condition is a one-bit node. *)
  Definition guards_sized (act: tfs_action sched) : Prop :=
    forall n (p: p_var) av en,
      node_op act n = DFG_Drive p av en ->
      forall l, List.In l en ->
        sz (nth (fst l) (graph (build_dfg ctx act))
             {| nid := 0; op := DFG_Empty; sz := 0 |}) = 1.

  (* A path condition's literals, as the run reads them.  Needed here because
     a sample's latch is gated on its own. *)
  Definition bit_of (b: bool) : bits_t 1 := if b then Bits.ones 1 else Bits.zero.

  Definition pi_holds (act: tfs_action sched) (a_idx: a_index) (input: sched_input_t)
      (pi: list lit) (ss: sched_sys_state) : Prop :=
    forall c b, List.In (c, b) pi ->
      nval act a_idx ss input 1 c = bit_of b.

  (* A node has SETTLED when its reference reads some path's validity as ones:
     every sample buffer it reads has latched, so its bits are a fact about the
     run rather than about a cycle. *)
  Definition settled_at (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t) (n: nid_t) : Prop :=
    exists pi: list lit,
      pi_holds act a_idx input pi ss
      /\ rvalid act a_idx pi n ss input = Bits.ones 1.

  Definition first_done (act: tfs_action sched) (input: input_t)
      (resp: nat -> resp_val) (ss0: sched_sys_state) (N: nat) : Prop :=
    ss_done (ss_run N act input resp ss0)
    /\ forall i, i < N -> ~ ss_done (ss_run i act input resp ss0).

  (* THE ATTACKER'S MODEL OF A RUN, over the two published snapshots and the
     cycle count: the outputs stand at [pre] until cycle [N] and at [post] from
     there.  The arguments are the whole of what it may read. *)
  Definition emulate (pre post: src_out_env) (N k: nat) (ov: o_var) :=
    if Nat.ltb k N then pre.[ov] else post.[ov].

  Definition done_test (act: tfs_action sched) (input: input_t)
      (resp: nat -> resp_val) (ss0: sched_sys_state) (k: nat) : bool :=
    if done_set_dec (ss_run k act input resp ss0) then true else false.

  Definition L (act: tfs_action sched) (input: input_t)
      (resp: nat -> resp_val) (ss0: sched_sys_state) : nat :=
    first_true (done_test act input resp ss0) (S (settle_bound act)) 0.

  (* ================================================================= *)
  (* THE ATTACKER'S CLOCK.  Everything below is computed from public     *)
  (* data: the validity bits and stall counts the attacker keeps, the     *)
  (* selector values the declassification rules recover, and the graph.   *)
  (* ================================================================= *)

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

  (* A path the hardware reads under: each literal is the condition of a phi
     that selects at the rest of the path, valid there. *)
  Fixpoint path_ok (act: tfs_action sched) (a_idx: a_index) (ss: sched_sys_state)
      (input: sched_input_t) (pi: list lit) : Prop :=
    match pi with
    | [] => True
    | (c, _) :: rest =>
        path_ok act a_idx ss input rest
        /\ (exists n t e, node_op act n = DFG_Phi c t e
              /\ phi_crit (get_tainted ctx (build_dfg ctx act))
                          (decl_facts ctx (build_dfg ctx act)) c rest = false)
        /\ pi_holds act a_idx input rest ss
        /\ rvalid act a_idx rest c ss input = Bits.ones 1
    end.

  (* WHAT [avalid] NEEDS OF THE EXTRACTION: a selecting phi reads its condition
     to pick an arm, so the rules must recover that condition -- wherever it has
     settled, which is where the phi reads it. *)
  Definition selectors_extractable (act: tfs_action sched) (a_idx: a_index)
      (vals: known (build_dfg ctx act))
      (ss: sched_sys_state) (input: sched_input_t) : Prop :=
    forall n c t e pi,
      node_op act n = DFG_Phi c t e ->
      phi_crit (get_tainted ctx (build_dfg ctx act))
               (decl_facts ctx (build_dfg ctx act)) c pi = false ->
      pi_holds act a_idx input pi ss ->
      path_ok act a_idx ss input pi ->
      rvalid act a_idx pi c ss input = Bits.ones 1 ->
      exists v, vals c = Some v.

  (* The attacker's vector IS the validity registers, slot by slot. *)
  Definition vv_matches (a_idx: a_index) (vv: vvec) (ss: sched_sys_state)
      (bufs: list (nid_t * (nat * sz_t))) : Prop :=
    forall n j jsz n_idx,
      BitsToLists.list_assoc bufs n = Some (j, jsz) ->
      index_of_nat (length (nth (index_to_nat a_idx) bneeds [])) j = Some n_idx ->
      (slot_valid vv j = true <-> (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1).

  (* The values it brings are the run's values, WHERE THE NODE HAS SETTLED:
     every buffer the node reads has latched. *)
  Definition vals_sound (act: tfs_action sched) (a_idx: a_index)
      (vals: known (build_dfg ctx act))
      (ss: sched_sys_state) (input: sched_input_t) : Prop :=
    forall n v (pi: list lit),
      vals n = Some v ->
      pi_holds act a_idx input pi ss ->
      rvalid act a_idx pi n ss input = Bits.ones 1 ->
      nval act a_idx ss input (nsz act n) n = v.

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
     done: the design resets it. *)
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

  (* WHAT THE ATTACKER SEES: each public input, and each public output before
     and after the action.  A secret port reads [None]. *)
  Record public_view := {
    seen_in   : forall v: i_var, option (type_denote (tf_inputs_type i_sz v));
    seen_pre  : forall o: o_var, option (type_denote (tf_outputs_type o_sz o));
    seen_post : forall o: o_var, option (type_denote (tf_outputs_type o_sz o));
  }.

  Definition observe (input: input_t) (pre post: src_out_env) : public_view := {|
    seen_in v   := match tfs_spec_inputs_class ctx v with
                   | Public => Some (input v) | Secret => None end;
    seen_pre o  := match tfs_spec_outputs_class ctx o with
                   | Public => Some pre.[o] | Secret => None end;
    seen_post o := match tfs_spec_outputs_class ctx o with
                   | Public => Some post.[o] | Secret => None end;
  |}.

  (* The node values the attacker's recipe works out from a view. *)
  Definition recovered (act: tfs_action sched) (view: public_view)
    : known (build_dfg ctx act) :=
    Recover.recover (p_eq := tfs_spec_ips_eq_dec ctx) (tfs_spec_ip ctx)
      (tfs_spec_decls ctx) (build_dfg ctx act)
      (Recover.seed i_sz o_sz (build_dfg ctx act)
         (seen_in view) (seen_pre view) (seen_post view))
      (Recover.rounds (tfs_spec_decls ctx) (build_dfg ctx act)).

  (* THE LATENCY, OVER PUBLIC DATA: a function of the action and the view. *)
  Definition L_pub (act: tfs_action sched) (view: public_view) : nat :=
    match index_of_nat (length bneeds)
            (@finite_index _ (tfs_action_fin sched) act) with
    | Some a_idx => L_pub_at act a_idx (recovered act view)
    | None => 0            (* unreachable: the table has a row per action *)
    end.

  Lemma L_pub_at_slot (act: tfs_action sched) (a_idx: a_index) (view: public_view) :
    act_idx_aligned act a_idx -> L_pub act view = L_pub_at act a_idx (recovered act view).
  Proof.
    unfold L_pub, act_idx_aligned. intro Ha.
    rewrite <- Ha, index_of_nat_to_nat. reflexivity.
  Qed.

  (* ---- the round trip, as a property of one state ---- *)

  (* The DRIVE a sample.s request came from: [sample_req].s walk, stopped one
     node earlier and checked to be on the sample.s own port. *)
  Definition sample_drive_head (act: tfs_action sched) (p: p_var) (h: nid_t)
    : option nid_t :=
    match node_op act h with
    | DFG_Drive p' _ _ => if (tfs_spec_ips_eq_dec ctx).(eq_dec) p' p then Some h else None
    | DFG_Join d _ =>
        match node_op act d with
        | DFG_Drive p' _ _ => if (tfs_spec_ips_eq_dec ctx).(eq_dec) p' p then Some d else None
        | _ => None
        end
    | _ => None
    end.

  Definition sample_drive (act: tfs_action sched) (n: nid_t) : option nid_t :=
    match node_op act n with
    | DFG_Sample p tok _ =>
        match node_op act tok with
        | DFG_Stall _ h => sample_drive_head act p h
        | _ => sample_drive_head act p tok
        end
    | _ => None
    end.

  (* nid of the DFG node cached by validity/value register (a_idx, n_idx). *)
  Definition vreg_nid
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (n_idx : Vect.index (length (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])))
    : nat :=
    fst (nth (index_to_nat n_idx)
             (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])
             (0, (0, 0))).

  (* The validity that goes with [node_ref_expr]: ones exactly when every sample
     buffer the reference reads has already latched. *)
  Definition node_ref_valid
      (act: tfs_action sched)
      (a_idx : Vect.index (length (buffer_needs ctx cost_limit)))
      (n: nat) : @tf_expr (tfs_states sched) si_var o_var :=
    snd (compile_dfg_expr ctx bneeds
           (length (graph (build_dfg ctx act))) a_idx (build_dfg ctx act) n
           (sample_bufs act a_idx)).

  (* THE ROUND TRIP, as a property of one state: a sample that LATCHED UNDER
     ITS GUARD holds [ip_fn] of the request its own drive sent.  [round_trip]
     discharges it at any pre-done cycle, from [ip_contract] and
     [requests_sent]. *)
  Definition samples_answered (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t) : Prop :=
    forall n_idx p tok en d av en',
      node_op act (vreg_nid a_idx n_idx)
        = DFG_Sample p tok en ->
      sample_drive act (vreg_nid a_idx n_idx)
        = Some d ->
      node_op act d = DFG_Drive p av en' ->
      sz (nth d (graph (build_dfg ctx act))
           {| nid := 0; op := DFG_Empty; sz := 0 |}) = ip_req_sz (tfs_spec_ip ctx p) ->
      (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
      pi_holds act a_idx input en ss ->
      (fst ss).[tf_dfg_b a_idx n_idx]
      = convert (ip_fn (tfs_spec_ip ctx p)
          (tf_eval_expr ss_sz si_sz oo_sz
             (szB := ip_req_sz (tfs_spec_ip ctx p))
             (node_ref_expr act a_idx av) ss input)).

  (* The other arm: an arm that was not taken sent no request, so its latch
     enable stayed down and its buffer holds the value it was reset to. *)
  Definition samples_zeroed (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t) : Prop :=
    forall n_idx p tok en,
      node_op act (vreg_nid a_idx n_idx)
        = DFG_Sample p tok en ->
      (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
      ~ pi_holds act a_idx input en ss ->
      (fst ss).[tf_dfg_b a_idx n_idx] = Bits.zero.

  (* Its companion: a latched sample's request carried a SETTLED argument.
     [sample_arg_settled] discharges it at any pre-done cycle. *)
  Definition sample_args_settled (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t) : Prop :=
    forall n_idx p tok en d av en',
      node_op act (vreg_nid a_idx n_idx)
        = DFG_Sample p tok en ->
      sample_drive act (vreg_nid a_idx n_idx)
        = Some d ->
      node_op act d = DFG_Drive p av en' ->
      (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
      eval1 (node_ref_valid act a_idx av) ss input = Bits.ones 1.

  (* And the guard's own sources: a latched sample read its guard from nodes
     that had settled, so whether the guard held is fixed by settled values. *)
  Definition sample_guards_settled (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t) : Prop :=
    forall n_idx p tok en,
      node_op act (vreg_nid a_idx n_idx)
        = DFG_Sample p tok en ->
      (fst ss).[tf_dfg_v a_idx n_idx] = Bits.ones 1 ->
      forall l, List.In l en ->
        eval1 (node_ref_valid act a_idx (fst l)) ss input
        = Bits.ones 1.

  (* What a state owes the round trip, as one hypothesis. *)
  Definition settled (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t) : Prop :=
    samples_answered act a_idx ss input
    /\ samples_zeroed act a_idx ss input
    /\ sample_args_settled act a_idx ss input
    /\ sample_guards_settled act a_idx ss input.

  (* ================================================================ *)
  (* The confidentiality criterion, over the spec alone.                *)
  (* ================================================================ *)

  Definition pub_agree (sys sys': sys_state) : Prop :=
    forall o : o_var, o_cls o = Public -> (snd sys).[o] = (snd sys').[o].

  (* "Secret-free": mentions no secret register and no read of a Secret output.
     Inputs are free at any class, since the theorem shares them between the two
     runs.  The Secret-output clause is REVIEW.md 2.4. *)
  Fixpoint sf_expr (e: @tf_expr s_var i_var o_var) : bool :=
    match e with
    | tf_const _ => true
    | tf_svar _  => false
    | tf_ivar _  => true
    | tf_ovar o  => match o_cls o with Public => true | Secret => false end
    | tf_op1 _ a => sf_expr a
    | tf_op2 _ a b => sf_expr a && sf_expr b
    | tf_expr_if c t f => sf_expr c && (sf_expr t && sf_expr f)
    end.

  (* [g] records a secret-dependent enclosing branch condition.  Under such a
     guard every Public output stays unwritten: assigning even a CONSTANT to one
     inside a branch on [dp] leaks [dp]. *)
  Fixpoint sf_ops (g: bool) (ops: @tf_ops s_var i_var o_var p_var) : bool :=
    match ops with
    | tf_ops_base tf_nop => true
    | tf_ops_base (tf_assign _ _) => true    (* a secret register may hold anything *)
    (* V4 denotes a call as [dst := ip_fn arg], a STATE update: the request port
       is the scheduler's own and is no declared output, so no [o_cls] applies
       and the case coincides with [tf_assign].  The IP bus is outside this
       theorem's attacker view -- see THEOREM-AUDIT.md B5. *)
    | tf_ops_base (tf_call _ _ _) => true
    | tf_ops_base (tf_output o e) =>
        match o_cls o with
        | Secret => true                     (* Secret outputs may be arbitrary *)
        | Public => negb g && sf_expr e
        end
    | tf_ops_cons a b => sf_ops g a && sf_ops g b
    | tf_ops_if c t f =>
        let g' := (g || negb (sf_expr c))%bool in
        sf_ops g' t && sf_ops g' f
    end.

  Definition sf_action (a: tfs_spec_action ctx) : bool :=
    sf_ops false (tfs_spec_action_ops ctx a).

  Fixpoint run_seq (acts: list (tfs_spec_action ctx))
      (sys: sys_state) (input: input_t) : sys_state :=
    match acts with
    | [] => sys
    | a :: rest =>
        run_seq rest (run (tfs_spec_action_ops ctx a) sys input) input
    end.

End SchedulerWorld.


(* ==================================================================== *)
(* The synthesis relations: what it means for the Kôika circuit to      *)
(* implement a scheduled design.                                        *)
(* ==================================================================== *)

Section SynthWorld.

  Context (tf_ctx: TFSynthContext).

  Local Notation sched_ctx := (tf_sched_ctx tf_ctx).
  Local Notation spec_states := (tfs_states sched_ctx).
  Local Notation spec_states_size := (tfs_states_size sched_ctx).
  Local Notation spec_inputs := (tfs_inputs sched_ctx).
  Local Notation spec_inputs_size := (tfs_inputs_size sched_ctx).
  Local Notation spec_outputs := (tfs_outputs sched_ctx).
  Local Notation spec_outputs_size := (tfs_outputs_size sched_ctx).
  Local Notation spec_action := (tfs_action sched_ctx).
  Local Notation spec_states_init := (tfs_states_init sched_ctx).
  Local Notation spec_action_encoding := (tf_action_encoding tf_ctx).
  Local Notation st_env  := (ContextEnv.(env_t) (tf_states_type spec_states_size)).
  Local Notation out_env := (ContextEnv.(env_t) (tf_outputs_type spec_outputs_size)).
  Local Notation sys_state_t := (st_env * out_env)%type.
  Local Notation input_t :=
    (forall x : spec_inputs, type_denote (tf_inputs_type spec_inputs_size x)).
  Local Notation R := (R tf_ctx).
  Local Notation r := (r tf_ctx).
  Local Notation Sigma := (Sigma tf_ctx).
  Local Notation spec_ips := (tfs_ips sched_ctx).
  Local Notation reg_t := (@_reg_t spec_states spec_inputs spec_outputs spec_ips).

  Hint Extern 0 (FiniteType reg_t) => exact (_reg_t_finite tf_ctx) : typeclass_instances.

  Definition state_matches (sys: sys_state_t) (r: ContextEnv.(env_t) R) : Prop :=
    (* State variables map cleanly *)
    (forall (x: spec_states), r.[tf_reg x] = (fst sys).[x]) /\
    (* Output variables map cleanly *)
    (forall (x: spec_outputs), r.[tf_out x] = (snd sys).[x]).

  Definition env_matches (act: spec_action) (input: input_t) (r: ContextEnv.(env_t) R) : Prop :=
    (* action variable maps cleanly *)
    (r.[tf_cmd] = spec_action_encoding act) /\
    (* THE LATCHED inputs map cleanly.  A response port is read live off the
       wire, so its latch holds the value from the dispatch cycle and
       [live_inputs_match] below is what pins it. *)
    (forall (x: spec_inputs),
       tfs_inputs_resp sched_ctx x = None -> r.[tf_in x] = input x).

  Definition state_env_matches (sys: sys_state_t) (act: spec_action) (input: input_t) (r: ContextEnv.(env_t) R) : Prop :=
    state_matches sys r /\
    env_matches act input r.

  Definition input_matches (act: spec_action) (input: input_t) (sigma: forall f, Sig_denote (Sigma f)) : Prop :=
    let cmd_res := sigma ext_in_cmd Ob~1 in      
    (fst cmd_res) = Ob~1 /\ (* TODO: implicit params should be given explicitly once known *)
    (@fst (vect bool (tf_action_reg_size tf_ctx)) unit
      (@snd (vect_cons_t bool (vect_nil_t bool)) (prod (vect bool (tf_action_reg_size tf_ctx)) unit) cmd_res) = spec_action_encoding act) /\
    (forall (x: spec_inputs), sigma (ext_input x) (Ob~1) = input x).

  Definition abstract_init_state (sys: sys_state_t) : Prop :=
    (forall x, (fst sys).[x] = spec_states_init x) /\
    (forall x, (snd sys).[x] = Bits.zero).

  (* A response input is sampled off the wire, so its value comes from [sigma]
     in EVERY cycle -- [env_matches] covers the latched inputs only. *)
  Definition live_inputs_match (input: input_t) (sigma: forall f, Sig_denote (Sigma f)) : Prop :=
    forall v p, tfs_inputs_resp (tf_sched_ctx tf_ctx) v = Some p ->
                sigma (ext_input v) Ob~1 = input v.
End SynthWorld.
