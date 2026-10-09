(*! Definitions the proofs are carried out in: reference values, the round-trip
    predicates, builder side conditions and the hardware's own done cycle. !*)

Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Backend.Lowering.
Require Export Trustformer.Theorems.IPRDefinitions.
Require Export Trustformer.Theorems.Internal.IRDefinitions.
Require Export Trustformer.Theorems.Internal.AttackerClock.
Require Import Trustformer.Declassification.Recover.

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Section ProofWorld.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation sched := (tfs_schedule ctx cost_limit).
  Local Notation i_var := (tfs_spec_inputs ctx).
  Local Notation o_var := (tfs_spec_outputs ctx).
  Local Notation i_sz  := (tfs_spec_inputs_size ctx).
  Local Notation o_sz  := (tfs_spec_outputs_size ctx).
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
  Local Notation resp_val :=
    (forall p : tfs_ips sched, bits_t (ip_resp_sz (tfs_ip sched p))).
  Local Notation a_index := (Vect.index (length (buffer_needs ctx cost_limit))).
  Local Notation eval1 e ss input :=
    (tf_eval_expr ss_sz si_sz oo_sz (szB := 1) e ss input).
  Local Notation nsz act n :=
    (sz (nth n (graph (build_dfg ctx act))
           {| nid := 0; op := DFG_Empty; sz := 0 |})).

  Local Notation done_set := (IRDefinitions.done_set ctx cost_limit).
  Local Notation ss_run   := (IRDefinitions.run_n ctx cost_limit).
  Local Notation L_pub    := (AttackerClock.L_pub ctx cost_limit).
  Local Notation node_op  := (AttackerClock.node_op ctx cost_limit).
  Local Notation settle_bound := (AttackerClock.settle_bound ctx cost_limit).
  Local Notation L_pub_at := (AttackerClock.L_pub_at ctx cost_limit).
  Local Notation recovered := (AttackerClock.recovered ctx cost_limit).

  (* done_set is decidable (a size-1 register is zero or all-ones). *)
  Lemma done_set_dec (ss: sched_sys_state) : {done_set ss} + {~ done_set ss}.
  Proof.
    unfold done_set.
    destruct (eq_dec ((fst ss).[tfs_done_signal sched]) Bits.zero) as [H | H].
    - right. intro Hc. apply Hc. exact H.
    - left. exact H.
  Qed.

  Definition is_sample_of (act: tfs_action sched) (n: nid_t) : bool :=
    match node_op act n with DFG_Sample _ _ _ => true | _ => false end.

  (* The buffers a reference KEEPS: exactly the sample ones, [guard_expr]'s [sbufs].
     A sample LATCHES a live wire, so inlining through it would compare the latched
     answer with the port's current one, which differ once a port takes two calls. *)
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

  Local Notation rvalid act a_idx pi n ss input :=
    (eval1 (snd (compile_dfg_expr_at ctx bneeds pi
                   (length (graph (build_dfg ctx act))) a_idx
                   (build_dfg ctx act) n (sample_bufs act a_idx)))
       ss input) (only parsing).

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

  (* Cycle 0 is the start state, so it never counts, as in [pdone_test]. *)
  Definition done_test (act: tfs_action sched) (input: input_t)
      (resp: nat -> resp_val) (ss0: sched_sys_state) (k: nat) : bool :=
    match k with
    | 0 => false
    | S _ => if done_set_dec (ss_run k act input resp ss0) then true else false
    end.

  Definition L (act: tfs_action sched) (input: input_t)
      (resp: nat -> resp_val) (ss0: sched_sys_state) : nat :=
    first_true (done_test act input resp ss0) (S (settle_bound act)) 0.

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

  Lemma L_pub_at_slot (act: tfs_action sched) (a_idx: a_index) (view: public_view ctx) :
    act_idx_aligned act a_idx ->
    L_pub act view
    = L_pub_at act a_idx
        (recovered act (seen_in ctx view) (seen_pre ctx view) (seen_post ctx view)).
  Proof.
    unfold AttackerClock.L_pub, AttackerClock.latency, act_idx_aligned. intro Ha.
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

  (* THE ROUND TRIP for one state: a sample that LATCHED UNDER ITS GUARD holds
     [ip_fn] of its own drive's request.  [round_trip] discharges it at any
     pre-done cycle, from [ip_contract] and [requests_sent]. *)
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

End ProofWorld.
