(*! Steps 2 and 3 of the variable scheduler: what each node costs, and which
    cycle it lands in.  [calc_backward_cost] accumulates the cost of the
    longest path from a node to the action's roots; dividing by the per-cycle
    budget [clim] turns that into a target cycle. !*)

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
Require Import Coq.micromega.Lia.

Import ListNotations.

Section Cost.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation states_var := (tfs_spec_states ctx).

  Local Notation inputs_var := (tfs_spec_inputs ctx).

  Local Notation outputs_var := (tfs_spec_outputs ctx).

  Local Notation ips_var := (tfs_spec_ips ctx).

  Local Notation spec_action := (tfs_spec_action ctx).
  Local Notation spec_action_fin := (tfs_spec_action_fin ctx).

  

  Local Notation dfg_op := (@dfg_op_t states_var inputs_var outputs_var ips_var).
  Local Notation dfg_node := (@dfg_node_t states_var inputs_var outputs_var ips_var).
  Local Notation dfg_state := (@dfg_state_t states_var inputs_var outputs_var ips_var).
  Local Notation get_args := (Build.get_args ctx).

  (* A cycle holds at least one unit of work.  At [cost_limit = 0] every target
     cycle collapses to 0, so no stall crosses a cycle boundary, no stall is
     buffered, and [stall_start] leaves every drive's pulse at zero. *)
  Definition clim : nat := Nat.max 1 cost_limit.

  Lemma clim_pos : 0 < clim.
  Proof. unfold clim. apply Nat.lt_le_trans with (m := 1); [ lia | apply Nat.le_max_l ]. Qed.
  (* ============================ *)
  (* = Step 2: Cost Calculation = *)
  (* ============================ *)

  Definition cost_t := nat.

  Definition cost_fn (d: dfg_op) (sz: nat) : cost_t :=
    match d with
    | DFG_Const _ => 0
    | DFG_Input _ => 0
    | DFG_Var _ => 0
    | DFG_Unary op _ => match op with
                        | tf_not => 1
                        | tf_resize _ => 0
                      end
    | DFG_Binary op _ _ => match op with
                        | tf_and => 1
                        | tf_or => 1
                        | tf_xor => 1
                        | tf_add => 2
                        | tf_sub => 2
                        | tf_mul => 5
                        | tf_cmp _ _ => 1
                        (* SPIKE: concatenation is pure wiring. *)
                        | tf_concat _ _ => 0
                        end
    | DFG_Resize _ => 0
    | DFG_Phi _ _ _ => 1
    (* SPIKE: a stall is a register, not combinational logic.  The real W-b
       design needs a separate [must_buffer] predicate rather than an inflated
       cost -- see the archive's DEBT-2. *)
    (* [ip_lat] is in CYCLES, so scale by [cost_limit]: a whole multiple shifts
       [calc_target_cycle]'s quotient by exactly that many cycles, whatever the
       remainder.  Regressions: Regressions/StallLatency.v [sep_pad_r0..r5], [sep_lat_0..6]. *)
    | DFG_Stall lat _ => lat * clim
    (* SPIKE 2b: a drive and a sample are wiring, not logic. *)
    | DFG_Drive _ _ _ => 0
    | DFG_Sample _ _ _ => 0
    (* Same as the [DFG_Binary tf_or] it replaces, so the schedule is unmoved:
       its validity is a real AND gate even though it carries no value. *)
    | DFG_Join _ _ => 1
    | DFG_Empty => 0
    end.

  Definition list_assoc_set_all_max {K: Type} {eq: EqDec K} (l: list (K * nat)) (k: list K) (v: nat)
    : list (K * nat) :=
    fold_left (fun acc key => 
      if Nat.leb (match BitsToLists.list_assoc acc key with
              | Some existing => existing
              | None => 0
              end) v then
        BitsToLists.list_assoc_set acc key v
      else
        acc
    ) k l.

  Definition calc_backward_cost (dfg : dfg_state) : list (nid_t * cost_t) :=
    let aux (cost_map: list (nid_t * cost_t)) (node : dfg_node) : list (nid_t * cost_t) :=
      let cost := match BitsToLists.list_assoc cost_map (nid node) with
                  | Some c => c
                  | None => 0
                  end in
      list_assoc_set_all_max cost_map ((nid node) :: get_args node) (cost + cost_fn (op node) (sz node))
    in
    fold_left aux (List.rev (graph dfg)) [].

  (* Steps 3-6 stay simple: performant HLS is out of scope here. *)

  (* ============================== *)
  (* = Step 3: Distance Splitting = *)
  (* ============================== *)

  Definition cycle_t := nat.

  Definition calc_target_cycle (cost_map: list (nid_t * cost_t)) : list (nid_t * cycle_t) :=
    map (fun '(nid, c) => (nid, c / clim)) cost_map.

End Cost.
