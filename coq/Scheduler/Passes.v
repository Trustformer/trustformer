Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.
Require Koika.BitsToLists.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Trustformer.Utils.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Export Trustformer.DFG.
Require Import Trustformer.Scheduler.Build.
Require Import Trustformer.Scheduler.Cost.
Require Import Trustformer.Scheduler.Buffers.
Require Import Trustformer.Scheduler.States.
Require Import Trustformer.Scheduler.Taint.
Require Import Trustformer.Contract.
Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.Program.Wf.

Import ListNotations.


(* Steps 2-6 of the variable scheduler: cost, target cycles, buffer
   allocation, taint and declassification, and the TF lowering.  Build.v holds
   step 1; Schedule.v proves the record obligations on top of all of it. *)

Section Passes.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation states_var := (tfs_spec_states ctx).
  Local Notation states_var_eq_dec := (tfs_spec_states_eq_dec ctx).
  Local Notation states_var_fin := (tfs_spec_states_fin ctx).
  Local Notation states_var_names := (tfs_spec_states_names ctx).
  Local Notation states_var_size := (tfs_spec_states_size ctx).
  Local Notation states_var_init := (tfs_spec_states_init ctx).

  Local Notation inputs_var := (tfs_spec_inputs ctx).
  Local Notation inputs_var_eq_dec := (tfs_spec_inputs_eq_dec ctx).
  Local Notation inputs_var_fin := (tfs_spec_inputs_fin ctx).
  Local Notation inputs_var_size := (tfs_spec_inputs_size ctx).
  Local Notation inputs_var_class := (tfs_spec_inputs_class ctx).

  Local Notation outputs_var := (tfs_spec_outputs ctx).
  Local Notation outputs_var_eq_dec := (tfs_spec_outputs_eq_dec ctx).
  Local Notation outputs_var_fin := (tfs_spec_outputs_fin ctx).
  Local Notation outputs_var_size := (tfs_spec_outputs_size ctx).
  Local Notation outputs_var_class := (tfs_spec_outputs_class ctx).

  Local Notation ips_var := (tfs_spec_ips ctx).
  Local Notation ips_var_eq_dec := (tfs_spec_ips_eq_dec ctx).
  Local Notation ips_var_fin := (tfs_spec_ips_fin ctx).
  Local Notation ip_of := (tfs_spec_ip ctx).

  Local Notation spec_action := (tfs_spec_action ctx).
  Local Notation spec_action_eq_dec := (tfs_spec_action_eq_dec ctx).
  Local Notation spec_action_fin := (tfs_spec_action_fin ctx).
  Local Notation spec_action_ops := (tfs_spec_action_ops ctx).
  Local Notation spec_all_actions := (@finite_elements spec_action spec_action_fin).
  Local Notation spec_action_index := (@finite_index spec_action spec_action_fin).

  Hint Extern 0 (FiniteType states_var) => exact (tfs_spec_states_fin ctx) : typeclass_instances.
  
  Hint Extern 0 (Show states_var) => exact (tfs_spec_states_names ctx) : typeclass_instances.
  Hint Extern 0 (Show inputs_var) => exact (tfs_spec_inputs_names ctx) : typeclass_instances.
  Hint Extern 0 (Show outputs_var) => exact (tfs_spec_outputs_names ctx) : typeclass_instances.
  Hint Extern 0 (Show ips_var) => exact (tfs_spec_ips_names ctx) : typeclass_instances.

  (* --- Step 1, from Build.v --- *)
  Local Notation dfg_vars := (@dfg_vars_t states_var outputs_var).
  Local Notation dfg_op := (@dfg_op_t states_var inputs_var outputs_var ips_var).
  Local Notation dfg_node := (@dfg_node_t states_var inputs_var outputs_var ips_var).
  Local Notation dfg_state := (@dfg_state_t states_var inputs_var outputs_var ips_var).
  Local Notation build_dfg := (Build.build_dfg ctx).
  Local Notation get_args := (Build.get_args ctx).
  Hint Extern 0 (EqDec dfg_vars) => exact (Build.dfg_vars_eq_dec ctx) : typeclass_instances.

  (* --- Steps 2-3, from Cost.v --- *)
  Local Notation cycle_t := Cost.cycle_t.
  Local Notation calc_backward_cost := (Cost.calc_backward_cost ctx cost_limit).
  Local Notation calc_target_cycle := (Cost.calc_target_cycle cost_limit).

  (* --- Step 4, from Buffers.v --- *)
  Local Notation is_source := (Buffers.is_source ctx).
  Local Notation require_buffer := (Buffers.require_buffer ctx).
  Local Notation get_sizes_and_idx := (Buffers.get_sizes_and_idx ctx).
  Local Notation buffer_needs := (Buffers.buffer_needs ctx cost_limit).

  (* The buffer table, computed ONCE by [tfs_schedule] and passed to everything below. *)
  Context (bn : list (list (nid_t * (nat * sz_t)))).

  (* --- the register file, from States.v --- *)
  Local Notation tf_dfg_states := (tf_dfg_states_t (states_var:=states_var) (ips_var:=ips_var) (buffer_needs:=bn)).
  Hint Extern 0 (Show tf_dfg_states) => exact (States.show_tf_dfg_states ctx bn) : typeclass_instances.

  (* --- Step 5, from Taint.v --- *)
  Local Notation lit := Taint.lit.
  Local Notation lit_eqb := Taint.lit_eqb.
  Local Notation guard_incl := Taint.guard_incl.
  Local Notation gfact := Taint.gfact.
  Local Notation gfacts_of := Taint.gfacts_of.
  Local Notation declassified_at := Taint.declassified_at.
  Local Notation mem_nid := Taint.mem_nid.
  Local Notation decl_instances := (Taint.decl_instances ctx).
  Local Notation get_tainted := (Taint.get_tainted ctx).

  Local Notation decl_facts := (Taint.decl_facts ctx).
  (* ============================== *)
  (* = Step 6: TF Compilations    = *)
  (* ============================== *)

  Local Notation expr_t := (@tf_expr tf_dfg_states (inputs_var + ips_var) outputs_var).

  Definition valid_expr_and (expr1: expr_t) (expr2: expr_t) : expr_t :=
    match expr1, expr2 with
    | tf_const 1, e2 => e2
    | e1, tf_const 1 => e1
    | _, _ => tf_op2 tf_and expr1 expr2
    end.

  Definition valid_expr_if (cond: expr_t) (then_expr: expr_t) (else_expr: expr_t) : expr_t :=
    match then_expr, else_expr with
    | tf_const 1, tf_const 1 => tf_const 1
    | _, _ => tf_expr_if cond then_expr else_expr
    end.


  (* First the expression, then the valid signal.  [pi] is the path of selector
     literals this occurrence is compiled under: criticality is per OCCURRENCE,
     since a declassification holds exactly where its guard does. *)

  (* A phi is critical at this occurrence when its condition is tainted and NO
     recorded guard for it is implied by the path. *)
  Definition phi_crit (tainted: list nid_t) (dfacts: list gfact)
      (c: nid_t) (pi: list lit) : bool :=
    mem_nid c tainted && negb (declassified_at dfacts c pi).

  (* A CRITICAL phi reads both branch validities unconditionally, so it compiles
     its branches under the UNEXTENDED path; a selecting phi extends it with the
     selector. *)
  Definition phi_path (crit: bool) (c: nid_t) (b: bool) (pi: list lit) : list lit :=
    if crit then pi else (c, b) :: pi.

  (* ---------------------------------------------------------------- *)
  (* DIAGNOSTICS.  Staying critical is a silent pessimisation, so the   *)
  (* compiler also reports, per phi occurrence, WHY it could not use a  *)
  (* declassification.                                                  *)
  (* ---------------------------------------------------------------- *)

  Inductive crit_reason :=
  (* the condition is tainted and no rule instance targets it *)
  | CR_no_rule (c: nid_t)
  (* an instance targets it, but these of its sources have no fact at all, so
     the composition could not fire *)
  | CR_sources_unknown (c: nid_t) (unknown_sources: list nid_t)
  (* it IS declassified, but no recorded guard is implied by this occurrence's
     path; one entry per recorded guard, listing the literals the path lacks *)
  | CR_guard_unmet (c: nid_t) (missing: list (list lit)).

  Definition guard_missing (g pi: list lit) : list lit :=
    filter (fun a => negb (existsb (lit_eqb a) pi)) g.

  Definition phi_crit_reason (dfg: dfg_state) (tainted: list nid_t) (base: list gfact)
      (c: nid_t) (pi: list lit)
    : option crit_reason :=
    if negb (mem_nid c tainted) then None
    else
      match gfacts_of base c with
      | [] =>
          match find (fun i => Nat.eqb (di_target i) c) (decl_instances dfg) with
          | Some i =>
              Some (CR_sources_unknown c
                      (filter (fun s => match gfacts_of base s with
                                        | [] => true
                                        | _ => false
                                        end)
                              (di_sources i)))
          | None => Some (CR_no_rule c)
          end
      | gs =>
          if declassified_at base c pi then None
          else Some (CR_guard_unmet c (map (fun g => guard_missing g pi) gs))
      end.

  (* The diagnostic never disagrees with the compiler about WHETHER a phi
     occurrence is critical; it only adds the reason. *)
  Lemma phi_crit_reason_none (dfg: dfg_state) (tainted: list nid_t) (base: list gfact)
      (c: nid_t) (pi: list lit) :
    phi_crit_reason dfg tainted base c pi = None
    <-> phi_crit tainted base c pi = false.
  Proof.
    unfold phi_crit_reason, phi_crit, declassified_at. cbv zeta.
    destruct (mem_nid c tainted) eqn:Hm; cbn [negb andb];
      [ | split; intro H; reflexivity ].
    destruct (gfacts_of base c) as [| g0 gs] eqn:Hgs;
      cbn [existsb negb].
    - destruct (find _ (decl_instances dfg)); split; intro H; discriminate.
    - destruct (guard_incl g0 pi || existsb (fun g => guard_incl g pi) gs);
        cbn [negb]; split; intro H; (reflexivity || discriminate).
  Qed.

  (* Walks the same cone [compile_dfg_expr_aux] does, under the same paths.
     [tainted] and [dfacts] are threaded for the same reason they are there. *)
  Fixpoint crit_report_aux (dfg: dfg_state) (tainted: list nid_t) (dfacts: list gfact)
      (pi: list lit) (fuel: nat)
      (n: nid_t) (bufs: list (nid_t * (nat * sz_t))) : list crit_reason :=
    match fuel with
    | 0 => []
    | S fuel' =>
        match BitsToLists.list_assoc bufs n with
        | Some _ => []
        | None =>
            let node := nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |} in
            match op node with
            | DFG_Unary _ a => crit_report_aux dfg tainted dfacts pi fuel' a bufs
            | DFG_Resize a => crit_report_aux dfg tainted dfacts pi fuel' a bufs
            | DFG_Binary _ a1 a2 =>
                crit_report_aux dfg tainted dfacts pi fuel' a1 bufs
                ++ crit_report_aux dfg tainted dfacts pi fuel' a2 bufs
            | DFG_Phi c t e =>
                let crit := phi_crit tainted dfacts c pi in
                (match phi_crit_reason dfg tainted dfacts c pi with Some r => [r] | None => [] end)
                ++ crit_report_aux dfg tainted dfacts pi fuel' c bufs
                ++ crit_report_aux dfg tainted dfacts (phi_path crit c true pi) fuel' t bufs
                ++ crit_report_aux dfg tainted dfacts (phi_path crit c false pi) fuel' e bufs
            (* Explicit, not falling through to [_]: the archive's DEBT-3 was a
               silently under-reporting diagnostic caused by exactly that. *)
            | DFG_Stall _ a => crit_report_aux dfg tainted dfacts pi fuel' a bufs
            | DFG_Drive _ a _ => crit_report_aux dfg tainted dfacts pi fuel' a bufs
            | DFG_Sample _ t _ => crit_report_aux dfg tainted dfacts pi fuel' t bufs
            | DFG_Join a b =>
                crit_report_aux dfg tainted dfacts pi fuel' a bufs
                ++ crit_report_aux dfg tainted dfacts pi fuel' b bufs
            | _ => []
            end
        end
    end.

  (* Entry point mirroring [compile_dfg_expr]: empty path, no buffer cuts. *)
  Definition crit_report (dfg: dfg_state) (n: nid_t) : list crit_reason :=
    crit_report_aux dfg (get_tainted dfg) (decl_facts dfg) [] (length (graph dfg)) n [].

  (* Everything the scheduler compiles for an action, in one list. *)
  Definition crit_report_all (dfg: dfg_state) : list crit_reason :=
    let tainted := get_tainted dfg in
    let dfacts := decl_facts dfg in
    flat_map (fun v => crit_report_aux dfg tainted dfacts [] (length (graph dfg)) (snd v) [])
             (var_map dfg).

  (* ---------------------------------------------------------------- *)
  (* CYCLE BOUNDS.  How long an action takes for a CONCRETE input is    *)
  (* not something to compute (that is [L] in Theorems/IPR.v, which   *)
  (* exists for the proofs).  What the circuit does give cheaply is the *)
  (* best and worst case, read off the same cone the compiler walks.    *)
  (* ---------------------------------------------------------------- *)

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
                     node_bounds_w dfg tainted dfacts cycles [] (length (graph dfg)) (snd v) in
                   (wmax_lo l lv, wmax u uv))
                (var_map dfg) ((0, []), (0, [])) in
    ((S (fst l), snd l), (S (fst u), snd u)).

  Definition action_bounds (dfg: dfg_state) : cycle_t * cycle_t :=
    let '(l, u) := action_bounds_w dfg in (fst l, fst u).

  (* Agreeing bounds leave nothing for the two witness paths to distinguish:
     they are then two runs of the same length, which is what makes [fst = snd]
     readable as [constant time]. *)
  Lemma bounds_agree_witness (dfg: dfg_state) :
    fst (action_bounds dfg) = snd (action_bounds dfg) ->
    fst (fst (action_bounds_w dfg)) = fst (snd (action_bounds_w dfg)).
  Proof.
    unfold action_bounds. destruct (action_bounds_w dfg) as [l u]. cbn. auto.
  Qed.


  Fixpoint compile_dfg_expr_aux (tainted: list nid_t)
    (dfacts: list gfact) (pi: list lit)
    (fuel: nat) (a_idx: Vect.index (length bn)) (dfg: dfg_state) (nid: nid_t) (buffers: list (nid_t * (nat * sz_t))) 
    : (expr_t * expr_t)
    :=
    match fuel with
    | 0 => (tf_const 0, tf_const 0) (* should not happen *)
    | S fuel' =>
        match BitsToLists.list_assoc buffers nid with
        | Some (n_idx, n_sz) => match index_of_nat (length (nth (index_to_nat a_idx) bn [])) n_idx with
                              | Some n_idx' =>
                                  (* a stall's buffer is its COUNTER: the register
                                     is the count, and the stall carries no
                                     value, so only the validity comes back *)
                                  match op (nth nid (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0; |}) with
                                  | DFG_Stall _ _ =>
                                      (tf_const 0, tf_svar (tf_dfg_v a_idx n_idx'))
                                  | _ => (tf_svar (tf_dfg_b a_idx n_idx'), tf_svar (tf_dfg_v a_idx n_idx'))
                                  end
                              | None => (tf_const 0, tf_const 0) (* should not happen *)
                              end
        | None => 
          let node := nth nid (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0; |} in
          match op node with
          | DFG_Const n => (tf_const n, tf_const 1)
          | DFG_Input v => (tf_ivar (inl v), tf_const 1)
          | DFG_Var v => match v with
                        | DFG_SVar s_var => (tf_svar (tf_dfg_s s_var), tf_const 1)
                        | DFG_OVar o_var => (tf_ovar o_var, tf_const 1)
                        end
          | DFG_Unary op arg1 =>
              let '(arg_expr, val_expr) := compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg arg1 buffers in
              (tf_op1 op arg_expr, val_expr)
          | DFG_Binary op arg1 arg2 =>
              let '(arg1_expr, val1_expr) := compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg arg1 buffers in
              let '(arg2_expr, val2_expr) := compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg arg2 buffers in
              (tf_op2 op arg1_expr arg2_expr, valid_expr_and val1_expr val2_expr)
          | DFG_Resize arg1 =>
              let '(arg_expr, val_expr) := compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg arg1 buffers in
              let arg_node := nth arg1 (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0; |} in
              (tf_op1 (tf_resize (sz arg_node)) arg_expr, val_expr)
          | DFG_Phi cond_id then_id else_id =>
              let '(cond_expr, cond_val) := compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg cond_id buffers in
              let '(then_expr, then_val) := compile_dfg_expr_aux tainted dfacts
                (phi_path (phi_crit tainted dfacts cond_id pi) cond_id true pi) fuel' a_idx dfg then_id buffers in
              let '(else_expr, else_val) := compile_dfg_expr_aux tainted dfacts
                (phi_path (phi_crit tainted dfacts cond_id pi) cond_id false pi) fuel' a_idx dfg else_id buffers in
              (
                tf_expr_if cond_expr then_expr else_expr, 
                if phi_crit tainted dfacts cond_id pi then
                  valid_expr_and (valid_expr_and then_val else_val) cond_val
                else
                  valid_expr_and cond_val (valid_expr_if cond_expr then_val else_val)
              )
          (* A stall CARRIES NO VALUE -- it is the counter [compile_dfg_buffers]
             counts out, and the answer arrives on the wire at the sample.  Only
             its validity, which lags its argument's by [lat] cycles, is read. *)
          | DFG_Stall _ arg1 =>
              let '(_, v) := compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg arg1 buffers in
              (tf_const 0, v)
          (* A drive passes its value through: it is the message on its way to
             the port.  A sample's VALUE is the port and its VALIDITY the
             token's, which is where the round trip decouples the two.
             Its validity ALSO waits on the guard, which [get_args] already
             counts as a dependency: a drive fires on the one cycle its stall
             starts, and a path condition read before its sources have settled
             sends the wrong arm's request -- or none.  Regression:
             sim/tb_xport.sv. *)
          | DFG_Drive _ arg1 en =>
              let '(e, v) := compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg arg1 buffers in
              (e, fold_right
                    (fun l acc =>
                       valid_expr_and
                         (snd (compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg
                                 (fst l) buffers))
                         acc)
                    v en)
          | DFG_Sample p tok _ =>
              let '(_, tok_val) := compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg tok buffers in
              (tf_ivar (inr p), tok_val)
          (* ORDERING only: the validity is the AND the sequencing needs, and
             the value is a constant because nothing reads it. *)
          | DFG_Join a b =>
              let '(_, val_a) := compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg a buffers in
              let '(_, val_b) := compile_dfg_expr_aux tainted dfacts pi fuel' a_idx dfg b buffers in
              (tf_const 0, valid_expr_and val_a val_b)
          | DFG_Empty => (tf_const 0, tf_const 0) (* should not happen *)
          end
        end
    end.

  (* The analysis is evaluated once here; compilation starts at the empty path. *)
  Local Notation compile_dfg_expr fuel a_idx dfg n bufs :=
    (compile_dfg_expr_aux (get_tainted dfg) (decl_facts dfg) [] fuel a_idx dfg n bufs).

  (* The path condition: each literal, negated on the else side; empty is [1].
     Compiled for the cycle the drive fires in, so buffers are substituted only
     for samples -- every other source is stable across the action. *)
  Definition guard_expr (tainted: list nid_t) (dfacts: list gfact) (fuel: nat)
    (a_idx: Vect.index (length bn)) (dfg: dfg_state)
    (sbufs: list (nid_t * (nat * sz_t))) (en: list (nid_t * bool)) : expr_t :=
    fold_right (fun (l : nid_t * bool) (acc : expr_t) =>
      let v := fst (compile_dfg_expr_aux tainted dfacts [] fuel a_idx dfg (fst l) sbufs) in
      let lv := if snd l then v else tf_op1 tf_not v in
      tf_op2 tf_and lv acc) (tf_const 1) en.
  Definition compile_dfg_buffers (a_idx: nat) (dfg: dfg_state) (buffers: list (nid_t * (nat * sz_t)))
    : list (@tf_op tf_dfg_states (inputs_var + ips_var) outputs_var Empty_set)
    :=
    (* Bound outside the [flat_map]: inlining these would re-run the whole taint
       and declassification analysis once per buffer. *)
    let tainted := get_tainted dfg in
    let dfacts := decl_facts dfg in
    let fuel := length (graph dfg) in
    (* a guard reads a call result from its LATCH, as a drive's does *)
    let sbufs := filter (fun '(n, _) =>
                           match op (nth n (graph dfg)
                                       {| nid := 0; op := DFG_Empty; sz := 0 |}) with
                           | DFG_Sample _ _ _ => true
                           | _ => false
                           end) buffers in
    match index_of_nat (length bn) a_idx with
    | None => []
    | Some a_idx' =>
      flat_map
        ( fun '(nid, x) => 
          match index_of_nat (length (nth (index_to_nat a_idx') bn [])) (fst x) with
            | Some n_idx' => 
              let buffers' := filter (fun '(b_nid, _) => negb (Nat.eqb b_nid nid)) buffers in
              let '(expr, valid) := compile_dfg_expr_aux tainted dfacts [] fuel a_idx' dfg nid buffers' in
              (* A buffer RECOMPUTES every cycle, sound while its sources are
                 stable across the action.  A [DFG_Sample] reads a LIVE wire, so
                 its buffer LATCHES as its validity RISES and holds thereafter. *)
              let sample_en :=
                match op (nth nid (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}) with
                | DFG_Sample _ _ en => Some en
                | _ => None
                end in
              (* A stall's buffer is a COUNTER: it advances while the argument is
                 valid and saturates at [lat-1], so the validity rises exactly
                 [lat] cycles after the argument's and stays up. *)
              let stall_lat :=
                match op (nth nid (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}) with
                | DFG_Stall l _ => Some l
                | _ => None
                end in
              let cnt := tf_svar (tf_dfg_b a_idx' n_idx') in
              let bexpr :=
                match stall_lat with
                | Some l =>
                    tf_expr_if (tf_op2 tf_and valid
                                  (tf_op1 tf_not (tf_op2 (tf_cmp (snd x) tf_eq) cnt (tf_const (pred l)))))
                      (tf_op2 tf_add cnt (tf_const 1)) cnt
                | None =>
                  match sample_en with
                  (* The GUARD is in the latch enable: an arm that was not taken
                     sent no request, so the channel is carrying another call's
                     cycle and this buffer keeps its reset value.  [vexpr] is
                     untouched, so the count is unchanged. *)
                  | Some en =>
                      tf_expr_if (tf_op2 tf_and
                                    (tf_op2 tf_and valid
                                       (tf_op1 tf_not (tf_svar (tf_dfg_v a_idx' n_idx'))))
                                    (guard_expr tainted dfacts fuel a_idx' dfg sbufs en))
                        expr (tf_svar (tf_dfg_b a_idx' n_idx'))
                  | None => expr
                  end
                end in
              (* The gate is ANDed in, not implied by the count: at [lat = 1]
                 the counter starts at [pred l] and would validate the token
                 before the argument ever did. *)
              let vexpr :=
                match stall_lat with
                | Some l =>
                    tf_op2 tf_and valid
                      (tf_op2 (tf_cmp (snd x) tf_eq) cnt (tf_const (pred l)))
                | None => valid
                end in
              [ tf_assign (tf_dfg_b a_idx' n_idx') bexpr; tf_assign (tf_dfg_v a_idx' n_idx') vexpr ]
            | None => [] (* should not happen *)
            end ) buffers
    end.

  (* ==================================================================== *)
  (* SPIKE 2c: mid-action port drives                                     *)
  (* ==================================================================== *)

  (* The nids of every [DFG_Drive] on [p], LATEST FIRST (the fold conses
     and graph order is program order). *)
  Definition drive_nodes (dfg: dfg_state) (p: ips_var) : list nid_t :=
    fold_left (fun acc nd =>
                 match op nd with
                 | DFG_Drive p' _ _ => if ips_var_eq_dec.(eq_dec) p' p then nid nd :: acc else acc
                 | _ => acc
                 end) (graph dfg) [].

  (* Every IP, not just the ones this action calls: a drive register is live in
     the always half of EVERY action, and one with no call emits a hold. *)
  Definition driven_ports (_: dfg_state) : list ips_var :=
    @finite_elements ips_var ips_var_fin.

  (* [n]'s stall, paired with the node it waits on: the drive itself, or the
     ordering join when the call is SEQUENCED, which is why this looks through
     one binary node. *)
  Definition chain_gate (dfg: dfg_state) (n: nid_t) : option (nid_t * nid_t) :=
    let stall_of := fun (m: nid_t) =>
      match find (fun nd => match op nd with
                            | DFG_Stall _ a => Nat.eqb a m
                            | _ => false
                            end) (graph dfg) with
      | Some nd => Some (nid nd)
      | None => None
      end in
    match stall_of n with
    | Some h => Some (n, h)
    | None =>
        match find (fun nd => match op nd with
                              | DFG_Join a _ => Nat.eqb a n
                              | _ => false
                              end) (graph dfg) with
        | Some j => match stall_of (nid j) with
                    | Some h => Some (nid j, h)
                    | None => None
                    end
        | None => None
        end
    end.

  Definition chain_head (dfg: dfg_state) (n: nid_t) : option nid_t :=
    match chain_gate dfg n with Some (_, h) => Some h | None => None end.

  (* The first cycle of a stall's wait: its counter is still zero. *)
  Definition stall_start (a_idx: Vect.index (length bn)) (dfg: dfg_state)
    (buffers: list (nid_t * (nat * sz_t))) (h: nid_t) : expr_t :=
    match BitsToLists.list_assoc buffers h with
    | Some (n_idx, n_sz) =>
        match index_of_nat (length (nth (index_to_nat a_idx) bn [])) n_idx with
        | Some n_idx' =>
            tf_op2 (tf_cmp n_sz tf_eq) (tf_svar (tf_dfg_b a_idx n_idx')) (tf_const 0)
        | None => tf_const 0
        end
    | None => tf_const 0
    end.

  (* A drive is an ALWAYS-op, so the request is on the wire during the action.
     The port HOLDS its old value until the drive's validity fires, and validity
     is monotone, so it stays stable from there to the response. *)

  Definition compile_dfg_drives (a_idx: nat) (dfg: dfg_state)
    (buffers: list (nid_t * (nat * sz_t)))
    : list (@tf_op tf_dfg_states (inputs_var + ips_var) outputs_var Empty_set) :=
    let tainted := get_tainted dfg in
    let dfacts := decl_facts dfg in
    let fuel := length (graph dfg) in
    (* the only buffers a guard keeps -- see [guard_expr] *)
    let sbufs := filter (fun '(n, _) =>
                           match op (nth n (graph dfg)
                                       {| nid := 0; op := DFG_Empty; sz := 0 |}) with
                           | DFG_Sample _ _ _ => true
                           | _ => false
                           end) buffers in
    match index_of_nat (length bn) a_idx with
    | None => []
    | Some a_idx' =>
        (* ONE scheduler register per driven port, holding {strobe, payload}.
           BOTH halves select on the PULSE: pulses are one cycle and disjoint,
           so request k's payload is taken at its own cycle and then HELD. *)
        map (fun p =>
               tf_assign (tf_dfg_ov p)
                 (tf_op2 (tf_concat 1 (ip_req_sz (ip_of p)))
                    (fold_right
                       (fun n acc =>
                          let '(_, v) := compile_dfg_expr_aux tainted dfacts [] fuel a_idx' dfg n buffers in
                          (* the path condition the call sits under: a drive in
                             an untaken branch must not reach the wire *)
                          let en_val :=
                            match op (nth n (graph dfg)
                                        {| nid := 0; op := DFG_Empty; sz := 0 |}) with
                            | DFG_Drive _ _ en => guard_expr tainted dfacts fuel a_idx' dfg sbufs en
                            | _ => tf_const 1
                            end in
                          let '(vgate, vfirst) :=
                            match chain_gate dfg n with
                            | Some (g, h) =>
                                (snd (compile_dfg_expr_aux tainted dfacts [] fuel a_idx' dfg g buffers),
                                 stall_start a_idx' dfg buffers h)
                            | None => (v, tf_const 1)
                            end in
                          tf_expr_if (tf_op2 tf_and en_val (tf_op2 tf_and vgate vfirst))
                            (tf_const 1) acc)
                       (tf_const 0) (drive_nodes dfg p))
                    (fold_right
                       (fun n acc =>
                          let '(e, v) := compile_dfg_expr_aux tainted dfacts [] fuel a_idx' dfg n buffers in
                          (* the path condition the call sits under: a drive in
                             an untaken branch must not reach the wire *)
                          let en_val :=
                            match op (nth n (graph dfg)
                                        {| nid := 0; op := DFG_Empty; sz := 0 |}) with
                            | DFG_Drive _ _ en => guard_expr tainted dfacts fuel a_idx' dfg sbufs en
                            | _ => tf_const 1
                            end in
                          let '(vgate, vfirst) :=
                            match chain_gate dfg n with
                            | Some (g, h) =>
                                (snd (compile_dfg_expr_aux tainted dfacts [] fuel a_idx' dfg g buffers),
                                 stall_start a_idx' dfg buffers h)
                            | None => (v, tf_const 1)
                            end in
                          tf_expr_if (tf_op2 tf_and en_val (tf_op2 tf_and vgate vfirst))
                            e acc)
                       (tf_svar (tf_dfg_ov p)) (drive_nodes dfg p))))
            (driven_ports dfg)
    end.

  Fixpoint combine_valid_exprs (exprs: list (@tf_expr tf_dfg_states (inputs_var + ips_var) outputs_var)) : @tf_expr tf_dfg_states (inputs_var + ips_var) outputs_var :=
    match exprs with
    | [] => tf_const 1
    | [e] => e
    | e :: rest => valid_expr_and e (combine_valid_exprs rest)
    end. 

  Definition compile_dfg_aux (a_idx: nat) (dfg: dfg_state) (buffers: list (nid_t * (nat * sz_t)))
    : list (@tf_op tf_dfg_states (inputs_var + ips_var) outputs_var Empty_set) :=
    let tainted := get_tainted dfg in
    let dfacts := decl_facts dfg in
    let fuel := length (graph dfg) in
    match index_of_nat (length bn) a_idx with
      | None => []
      | Some a_idx' => 
        map 
          ( fun '(var, nid) => 
            let '(expr, valid) := compile_dfg_expr_aux tainted dfacts [] fuel a_idx' dfg nid buffers in
            match var with
            | DFG_SVar sv =>
              tf_assign (tf_dfg_s sv) expr
            | DFG_OVar ov => 
              tf_output ov expr
            end
            ) (var_map dfg)
      end.

  Definition compile_dfg_valid (a_idx: nat) (dfg: dfg_state) (buffers: list (nid_t * (nat * sz_t)))
    : @tf_op tf_dfg_states (inputs_var + ips_var) outputs_var Empty_set :=
    let tainted := get_tainted dfg in
    let dfacts := decl_facts dfg in
    let fuel := length (graph dfg) in
    let nids := nodup Nat.eq_dec (map snd (var_map dfg)) in
    let exprs := match index_of_nat (length bn) a_idx with
      | None => []
      | Some a_idx' => map ( fun nid => snd (compile_dfg_expr_aux tainted dfacts [] fuel a_idx' dfg nid buffers)) nids
    end in
    tf_assign tf_dfg_done (combine_valid_exprs exprs).

  Definition schedule (act: spec_action)
    (* : list (list (@tf_ops tf_dfg_states inputs_var outputs_var)) := *)
    :=
    let idx := spec_action_index act in
    (* Determine the DFG of each operation *)
    let dfgs := map build_dfg spec_all_actions in
    (* Calculate the cost maps for each DFG *)
    let cost_maps := map calc_backward_cost dfgs in
    (* Calculate the target cycles for each node *)
    let cycle_maps := map calc_target_cycle cost_maps in
    (* Determine the required buffers across all actions *)
    let buffers := map (fun '(dfg, cycle_map) => get_sizes_and_idx dfg (require_buffer dfg cycle_map)) (combine dfgs cycle_maps) in

    let final_ops := compile_dfg_aux idx (nth idx dfgs {| graph := []; var_map := [] |}) (nth idx buffers []) in
    let done_signal := compile_dfg_valid idx (nth idx dfgs {| graph := []; var_map := [] |}) (nth idx buffers []) in
    
    ( 
      done_signal :: compile_dfg_buffers idx (nth idx dfgs {| graph := []; var_map := [] |}) (nth idx buffers [])
                  ++ compile_dfg_drives idx (nth idx dfgs {| graph := []; var_map := [] |}) (nth idx buffers []),
      final_ops
    ).

End Passes.
