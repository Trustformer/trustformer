(*! Step 4 of the variable scheduler: which nodes need a buffer register.  A
    node whose value is read in a later cycle than the one it settles in gets a
    slot; [buffer_needs] is that table for every action, and the scheduled
    state type is indexed by it. !*)

Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Koika.BitsToLists.

Require Import Trustformer.Utils.
Require Import Trustformer.Syntax.
Require Export Trustformer.DFG.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Build.
Require Import Trustformer.Scheduler.Cost.

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.

Import ListNotations.

Section Buffers.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation states_var := (tfs_spec_states ctx).

  Local Notation inputs_var := (tfs_spec_inputs ctx).

  Local Notation outputs_var := (tfs_spec_outputs ctx).

  Local Notation ips_var := (tfs_spec_ips ctx).

  Local Notation spec_action := (tfs_spec_action ctx).
  Local Notation spec_action_fin := (tfs_spec_action_fin ctx).
  Local Notation spec_all_actions := (@finite_elements spec_action spec_action_fin).

  

  Local Notation dfg_op := (@dfg_op_t states_var inputs_var outputs_var ips_var).
  Local Notation dfg_node := (@dfg_node_t states_var inputs_var outputs_var ips_var).
  Local Notation dfg_state := (@dfg_state_t states_var inputs_var outputs_var ips_var).
  Local Notation build_dfg := (Build.build_dfg ctx).
  Local Notation get_args := (Build.get_args ctx).
  Local Notation cycle_t := Cost.cycle_t.
  Local Notation calc_backward_cost := (Cost.calc_backward_cost ctx cost_limit).
  Local Notation calc_target_cycle := (Cost.calc_target_cycle cost_limit).

  (* A source op holds one value for the whole action -- constants are literals,
     inputs are latched at action start, state is written at done -- so it is
     re-read in any later stage and stays buffer-free. *)
  Definition source_op (o : dfg_op) : bool :=
    match o with
    | DFG_Const _ | DFG_Input _ | DFG_Var _ => true
    | _ => false
    end.

  Definition is_source (dfg : dfg_state) (n : nid_t) : bool :=
    source_op (op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0; |})).

  (* A sample reads a LIVE wire and a later call on the same port moves it, so
     its answer is latched whatever the schedule does with it.  Leaving that to
     the cycle-crossing test reads the wire again in a later cycle. *)
  Definition sample_nodes (dfg: dfg_state) : list nid_t :=
    map nid (filter (fun nd => match op nd with
                               | DFG_Sample _ _ _ => true
                               | _ => false
                               end) (graph dfg)).

  Definition require_buffer (dfg : dfg_state) (cycle_costs : list (nid_t * cycle_t)) : list (nid_t) :=
    let aux (cost_map: list (nid_t)) (node : dfg_node) : list (nid_t) :=
      let n_cycle := match BitsToLists.list_assoc cycle_costs (nid node) with
                      | Some c => c
                      | None => 0 (* should not happen *)
                      end in
      filter (fun x => if is_source dfg x then false else
                      match BitsToLists.list_assoc cycle_costs x with
                      | Some c => negb (Nat.eqb c n_cycle)
                      | None => false (* should not happen *)
                      end ) (get_args node) ++ cost_map
    in
    nodup Nat.eq_dec (fold_left aux (graph dfg) []
                        ++ filter (fun x => if is_source dfg x then false else
                                          match BitsToLists.list_assoc cycle_costs x with
                                          | Some 0 => false
                                          | _ => true
                                          end ) (map snd (var_map dfg))
                        ++ sample_nodes dfg).

  Definition get_sizes_and_idx (dfg : dfg_state) (nodes: list nid_t) : list (nid_t * (nat * sz_t)) :=
    rev (fst (
      fold_left (fun '(acc, idx) nid =>
        let node := nth nid (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0; |} in
        ((nid, (idx, sz node)) :: acc, S idx)
      ) nodes ([], 0))).

  Definition buffer_needs 
    :=
    (* Determine the DFG of each operation *)
    let dfgs := map build_dfg spec_all_actions in
    (* Calculate the cost maps for each DFG *)
    let cost_maps := map calc_backward_cost dfgs in
    (* Calculate the target cycles for each node *)
    let cycle_maps := map calc_target_cycle cost_maps in
    (* Determine the required buffers across all actions *)
    let buffers := map (fun '(dfg, cycle_map) => get_sizes_and_idx dfg (require_buffer dfg cycle_map)) (combine dfgs cycle_maps) in
    
    buffers.
End Buffers.
