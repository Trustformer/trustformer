(*! Step 6 of the variable scheduler: the DFG becomes [tf_ops] over the
    scheduled register file.  Each buffered node gets an assignment guarded by
    its validity bit, each IP drive a request pulse, and [schedule] packs the
    per-action always-half and done-half the [TFSchedule] record carries. !*)

Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.
Require Koika.BitsToLists.

Require Import Trustformer.Utils.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Export Trustformer.DFG.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Build.
Require Import Trustformer.Scheduler.Cost.
Require Import Trustformer.Scheduler.Buffers.
Require Import Trustformer.Scheduler.States.
Require Import Trustformer.Scheduler.Taint.

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.

Import ListNotations.

Section Codegen.

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

End Codegen.
