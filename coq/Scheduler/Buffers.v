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

(* Buffers SHARE value registers across actions: one action runs at a time and
   every buffer is cleared when it finishes.  An entry's slot is keyed by its
   width and its rank among its action's entries of that width. *)
Section Slots.

  Context (bn : list (list (nid_t * (nat * sz_t)))).

  Definition key_eq_dec (x y: sz_t * nat) : {x = y} + {x <> y}.
  Proof. decide equality; apply Nat.eq_dec. Defined.

  Fixpoint rank_keys (seen: list sz_t) (ws: list sz_t) : list (sz_t * nat) :=
    match ws with
    | [] => []
    | w :: ws' => (w, count_occ Nat.eq_dec seen w) :: rank_keys (w :: seen) ws'
    end.

  Definition action_keys (entries: list (nid_t * (nat * sz_t))) : list (sz_t * nat) :=
    rank_keys [] (map (fun e => snd (snd e)) entries).

  Definition slot_keys : list (sz_t * nat) := nodup key_eq_dec (flat_map action_keys bn).

  Fixpoint position (k: sz_t * nat) (l: list (sz_t * nat)) : nat :=
    match l with
    | [] => 0
    | x :: l' => if key_eq_dec x k then 0 else S (position k l')
    end.

  Definition slot_of (a m: nat) : nat :=
    position (nth m (action_keys (nth a bn [])) (0, 0)) slot_keys.

  Lemma rank_keys_fst seen ws : map fst (rank_keys seen ws) = ws.
  Proof.
    revert seen; induction ws as [| w ws IH]; intro seen; cbn; [ reflexivity | ].
    rewrite IH. reflexivity.
  Qed.

  Lemma rank_keys_ge seen ws w c :
    In (w, c) (rank_keys seen ws) -> count_occ Nat.eq_dec seen w <= c.
  Proof.
    revert seen; induction ws as [| w0 ws IH]; intros seen Hin; cbn in Hin; [ contradiction | ].
    destruct Hin as [Heq | Hin].
    - injection Heq as -> ->. reflexivity.
    - specialize (IH (w0 :: seen) Hin). cbn in IH.
      destruct (Nat.eq_dec w0 w); lia.
  Qed.

  Lemma rank_keys_nodup seen ws : NoDup (rank_keys seen ws).
  Proof.
    revert seen; induction ws as [| w ws IH]; intro seen; cbn; constructor; [ | apply IH ].
    intro Hin. apply rank_keys_ge in Hin. cbn in Hin.
    destruct (Nat.eq_dec w w); [ lia | congruence ].
  Qed.

  Lemma action_keys_length entries : length (action_keys entries) = length entries.
  Proof.
    unfold action_keys. rewrite <- (map_length fst), rank_keys_fst, map_length. reflexivity.
  Qed.

  Lemma action_keys_width entries m :
    m < length entries ->
    fst (nth m (action_keys entries) (0, 0)) = snd (snd (nth m entries (0, (0, 0)))).
  Proof.
    intro Hm. unfold action_keys.
    rewrite <- (map_nth fst _ (0, 0)), rank_keys_fst.
    rewrite (nth_indep _ _ (snd (snd (0, (0, 0))))) by (rewrite map_length; exact Hm).
    apply (map_nth (fun e => snd (snd e))).
  Qed.

  Lemma position_spec k l : In k l -> position k l < length l /\ nth (position k l) l (0, 0) = k.
  Proof.
    induction l as [| x l IH]; intro Hin; cbn in Hin |- *; [ contradiction | ].
    destruct (key_eq_dec x k) as [-> | Hne]; [ split; [ lia | reflexivity ] | ].
    destruct Hin as [-> | Hin]; [ congruence | ].
    destruct (IH Hin). split; [ lia | assumption ].
  Qed.

  Lemma slot_key_in a m :
    a < length bn -> m < length (nth a bn []) ->
    In (nth m (action_keys (nth a bn [])) (0, 0)) slot_keys.
  Proof.
    intros Ha Hm. unfold slot_keys. apply nodup_In, in_flat_map.
    exists (nth a bn []). split; [ apply nth_In, Ha | ].
    apply nth_In. rewrite action_keys_length. exact Hm.
  Qed.

  Lemma slot_of_bound a m :
    a < length bn -> m < length (nth a bn []) -> slot_of a m < length slot_keys.
  Proof. intros Ha Hm. exact (proj1 (position_spec _ _ (slot_key_in a m Ha Hm))). Qed.

  Lemma slot_of_width a m :
    a < length bn -> m < length (nth a bn []) ->
    fst (nth (slot_of a m) slot_keys (0, 0)) = snd (snd (nth m (nth a bn []) (0, (0, 0)))).
  Proof.
    intros Ha Hm. unfold slot_of. rewrite (proj2 (position_spec _ _ (slot_key_in a m Ha Hm))).
    exact (action_keys_width _ m Hm).
  Qed.

  Lemma slot_of_inj a m1 m2 :
    a < length bn -> m1 < length (nth a bn []) -> m2 < length (nth a bn []) ->
    slot_of a m1 = slot_of a m2 -> m1 = m2.
  Proof.
    intros Ha H1 H2 Heq. unfold slot_of in Heq.
    pose proof (proj2 (position_spec _ _ (slot_key_in a m1 Ha H1))) as E1.
    pose proof (proj2 (position_spec _ _ (slot_key_in a m2 Ha H2))) as E2.
    rewrite Heq, E2 in E1.
    pose proof (rank_keys_nodup [] (map (fun e => snd (snd e)) (nth a bn []))) as Hnd.
    fold (action_keys (nth a bn [])) in Hnd.
    apply (proj1 (NoDup_nth _ (0, 0)) Hnd);
      [ rewrite action_keys_length; assumption
      | rewrite action_keys_length; assumption
      | symmetry; exact E1 ].
  Qed.

  (* Which of action [a]'s entries holds slot [k]. *)
  Definition slot_owner (a k: nat) : nat :=
    match find (fun m => Nat.eqb (slot_of a m) k) (List.seq 0 (length (nth a bn []))) with
    | Some m => m
    | None => 0
    end.

  Lemma slot_owner_of a m :
    a < length bn -> m < length (nth a bn []) -> slot_owner a (slot_of a m) = m.
  Proof.
    intros Ha Hm. unfold slot_owner.
    destruct (find _ _) as [m' |] eqn:Hf.
    - apply find_some in Hf. destruct Hf as [Hin Heq].
      apply in_seq in Hin. apply Nat.eqb_eq in Heq.
      exact (slot_of_inj a m' m Ha ltac:(lia) Hm Heq).
    - exfalso. assert (Hn : In m (List.seq 0 (length (nth a bn [])))) by (apply in_seq; lia).
      apply (find_none _ _ Hf) in Hn. rewrite Nat.eqb_refl in Hn. discriminate.
  Qed.

  (* The index [k] of [Vect.index n], from its bound. *)
  Fixpoint index_lt (n k: nat) {struct n} : k < n -> Vect.index n :=
    match n return k < n -> Vect.index n with
    | 0 => fun H => False_rect _ (Nat.nlt_0_r k H)
    | S n' => match k return k < S n' -> Vect.index (S n') with
              | 0 => fun _ => thisone
              | S k' => fun H => anotherone (index_lt n' k' (proj2 (Nat.succ_lt_mono k' n') H))
              end
    end.

  Lemma index_lt_to_nat n k H : index_to_nat (index_lt n k H) = k.
  Proof.
    revert k H; induction n as [| n IH]; intros k H; [ lia | ].
    destruct k; cbn; [ reflexivity | rewrite IH; reflexivity ].
  Qed.

  Definition slot_width (k: Vect.index (length slot_keys)) : nat :=
    fst (nth (index_to_nat k) slot_keys (0, 0)).

  (* The register of an action's buffer. *)
  Definition slot_idx (a_idx: Vect.index (length bn))
      (n_idx: Vect.index (length (nth (index_to_nat a_idx) bn []))) : Vect.index (length slot_keys) :=
    index_lt _ (slot_of (index_to_nat a_idx) (index_to_nat n_idx))
      (slot_of_bound _ _ (index_to_nat_bounded a_idx) (index_to_nat_bounded n_idx)).

  Lemma slot_idx_to_nat a_idx n_idx :
    index_to_nat (slot_idx a_idx n_idx) = slot_of (index_to_nat a_idx) (index_to_nat n_idx).
  Proof. apply index_lt_to_nat. Qed.

  Lemma slot_idx_inj a_idx n1 n2 : slot_idx a_idx n1 = slot_idx a_idx n2 -> n1 = n2.
  Proof.
    intro Heq. apply index_to_nat_injective.
    apply (f_equal index_to_nat) in Heq. rewrite !slot_idx_to_nat in Heq.
    exact (slot_of_inj _ _ _ (index_to_nat_bounded a_idx) (index_to_nat_bounded n1)
             (index_to_nat_bounded n2) Heq).
  Qed.

  Lemma slot_idx_width a_idx n_idx :
    slot_width (slot_idx a_idx n_idx)
    = snd (snd (nth (index_to_nat n_idx) (nth (index_to_nat a_idx) bn []) (0, (0, 0)))).
  Proof.
    unfold slot_width. rewrite slot_idx_to_nat.
    exact (slot_of_width _ _ (index_to_nat_bounded a_idx) (index_to_nat_bounded n_idx)).
  Qed.

End Slots.
