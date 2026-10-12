Require Import Koika.Frontend.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

Require Import Trustformer.Examples.Knox.Fifo.Spec.

(* The FIFO's actions agree with Knox's spec.rkt for all 32-bit data and every
   sequence of calls. *)

Section Universal.

  Definition BW := bits_t W.
  Definition Z1 : bits_t 1 := Bits.of_nat 1 0.
  Definition O1 : bits_t 1 := Bits.of_nat 1 1.
  Definition ZW : BW := Bits.of_nat W 0.

  Definition portsB := (bits_t 1 * bits_t 1 * bits_t 1 * BW)%type.

  Definition mkB (c: bits_t CNT_SZ) (d0 d1 d2: BW) (o: portsB) : sysst W :=
    let '(f, e, pv, pd) := o in
    (ContextEnv.(create) (fun k => match k return tf_states_type (fs_states_size W) k with
        | st_cnt => c | st_slot S0 => d0 | st_slot S1 => d1 | st_slot S2 => d2 end),
     ContextEnv.(create) (fun k => match k return tf_outputs_type (fs_outputs_size W) k with
        | out_full => f | out_empty => e | out_peek_valid => pv | out_peek_data => pd end)).

  Definition repB (q: list BW) (o: portsB) : sysst W :=
    mkB (Bits.of_nat CNT_SZ (length q)) (nth 0 q ZW) (nth 1 q ZW) (nth 2 q ZW) o.

  Definition knoxB (a: fs_action) (v: BW) (q: list BW) : portsB * list BW :=
    match a with
    | act_full  => ((if Nat.eqb (length q) 3 then O1 else Z1, Z1, Z1, ZW), q)
    | act_empty => ((Z1, match q with [] => O1 | _ => Z1 end, Z1, ZW), q)
    | act_push  => ((Z1, Z1, Z1, ZW), if Nat.eqb (length q) 3 then q else q ++ [v])
    | act_peek  => (match q with [] => (Z1, Z1, Z1, ZW) | x :: _ => (Z1, Z1, O1, x) end, q)
    | act_pop   => ((Z1, Z1, Z1, ZW), match q with [] => [] | _ :: r => r end)
    end.

  Definition inpB (v: BW) : forall i : fs_inputs, bits_t (fs_inputs_size W i) :=
    fun i => match i return bits_t (fs_inputs_size W i) with in_v => v end.

  Definition runB (a: fs_action) (v: BW) (st: sysst W) : sysst W :=
    tf_ops_run (fs_states_size W) (fs_inputs_size W) (fs_outputs_size W) no_ips
               (fs_ops a) st (inpB v).

  Theorem fifo_universal_canonical :
    forall (a: fs_action) (q: list BW) (v: BW) (stale: portsB),
      length q <= 3 ->
      runB a v (repB q stale) = repB (snd (knoxB a v q)) (fst (knoxB a v q)).
  Proof.
    intros a q v [[[f e] pv] pd] Hl.
    destruct q as [|x0 [|x1 [|x2 [|x3 q]]]]; [ | | | | simpl in Hl; lia ];
      destruct a; vm_compute; reflexivity.
  Qed.

  Definition outsB (st: sysst W) : portsB :=
    (ContextEnv.(getenv) (snd st) out_full, ContextEnv.(getenv) (snd st) out_empty,
     ContextEnv.(getenv) (snd st) out_peek_valid, ContextEnv.(getenv) (snd st) out_peek_data).
  Definition absB (st: sysst W) : list BW :=
    firstn (Bits.to_nat (ContextEnv.(getenv) (fst st) st_cnt))
      [ContextEnv.(getenv) (fst st) (st_slot S0); ContextEnv.(getenv) (fst st) (st_slot S1);
       ContextEnv.(getenv) (fst st) (st_slot S2)].

  Theorem fifo_universal_garbage :
    forall (a: fs_action) (n: nat) (d0 d1 d2 v: BW) (stale: portsB),
      n <= 3 ->
      let q := firstn n [d0; d1; d2] in
      let st' := runB a v (mkB (Bits.of_nat CNT_SZ n) d0 d1 d2 stale) in
      absB st' = snd (knoxB a v q) /\ outsB st' = fst (knoxB a v q).
  Proof.
    intros a n d0 d1 d2 v [[[f e] pv] pd] Hn.
    destruct n as [|[|[|[|n]]]]; [ | | | | lia ];
      destruct a; vm_compute; split; reflexivity.
  Qed.

End Universal.

Section Trace.

  Definition zports : portsB := (Z1, Z1, Z1, ZW).

  Fixpoint knox_trace (tr: list (fs_action * BW)) (q: list BW) (r: portsB) : portsB * list BW :=
    match tr with
    | [] => (r, q)
    | (a, v) :: tr' => knox_trace tr' (snd (knoxB a v q)) (fst (knoxB a v q))
    end.

  Fixpoint run_trace (tr: list (fs_action * BW)) (st: sysst W) : sysst W :=
    match tr with
    | [] => st
    | (a, v) :: tr' => run_trace tr' (runB a v st)
    end.

  Lemma knoxB_len : forall a v q, length q <= 3 -> length (snd (knoxB a v q)) <= 3.
  Proof.
    intros a v q H; destruct a; cbn [knoxB snd]; auto.
    - match goal with |- context [if ?c then _ else _] => destruct c eqn:E end; [exact H|].
      apply Nat.eqb_neq in E. rewrite app_length. cbn [length]. lia.
    - destruct q; cbn [length] in *; lia.
  Qed.

  Theorem fifo_trace :
    forall tr q r, length q <= 3 ->
      run_trace tr (repB q r) = repB (snd (knox_trace tr q r)) (fst (knox_trace tr q r)).
  Proof.
    induction tr as [|[a v] tr IH]; intros q r Hl; simpl; [reflexivity|].
    rewrite fifo_universal_canonical by exact Hl.
    apply IH, knoxB_len, Hl.
  Qed.

  Lemma initial_is_repB : initial = repB [] zports.
  Proof. vm_compute. reflexivity. Qed.

  Corollary fifo_from_reset :
    forall tr, run_trace tr initial
               = repB (snd (knox_trace tr [] zports)) (fst (knox_trace tr [] zports)).
  Proof. intros tr. rewrite initial_is_repB. apply fifo_trace. simpl; lia. Qed.

  Lemma zero_tuple_collisions :
    fst (knoxB act_push ZW []) = zports /\ fst (knoxB act_pop ZW []) = zports /\
    fst (knoxB act_peek ZW []) = zports /\ fst (knoxB act_full ZW []) = zports.
  Proof. vm_compute. repeat split. Qed.

End Trace.
