Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.

Require Import Trustformer.Syntax.
Require Import Trustformer.Contract.
Require Import Trustformer.Backend.Lowering.

(* Gallina macros that emit Trustformer syntax, and [mk_synth_ctx], which derives
   the action encoding.  Macros run in extracted OCaml, where nat and N are 63-bit
   ints, so none computes a number larger than its arguments. *)

Section DerivedEncoding.
  Context {A: Type} {FT: FiniteType A}.

  Definition auto_enc_sz : nat :=
    S (Nat.log2 (List.length (@finite_elements A FT))).

  Definition auto_enc (a: A) : bits_t auto_enc_sz :=
    Bits.of_nat auto_enc_sz (finite_index a).

  Lemma auto_enc_index_lt :
    forall a, finite_index a < List.length (@finite_elements A FT).
  Proof.
    intros a. apply nth_error_Some. rewrite finite_surjective. discriminate.
  Qed.

  Lemma auto_enc_index_lt_pow2 : forall a, finite_index a < pow2 auto_enc_sz.
  Proof.
    intros a. rewrite pow2_correct. unfold auto_enc_sz.
    pose proof (auto_enc_index_lt a) as Hlt.
    destruct (Nat.log2_spec (List.length (@finite_elements A FT))) as [_ Hhi]; [ lia | ].
    lia.
  Qed.

  Lemma auto_enc_inj : forall a1 a2, auto_enc a1 = auto_enc a2 -> a1 = a2.
  Proof.
    intros a1 a2 H. apply finite_index_injective.
    apply (f_equal Bits.to_nat) in H. unfold auto_enc in H.
    rewrite !Bits.to_nat_of_nat in H by apply auto_enc_index_lt_pow2.
    exact H.
  Qed.
End DerivedEncoding.

Definition mk_synth_ctx (s: TFSchedule) {names: Show (tfs_action s)} : TFSynthContext := {|
  tf_sched_ctx := s;
  tf_action_reg_size := @auto_enc_sz (tfs_action s) (tfs_action_fin s);
  tf_action_encoding := @auto_enc (tfs_action s) (tfs_action_fin s);
  tf_action_encoding_inj := @auto_enc_inj (tfs_action s) (tfs_action_fin s);
  tf_action_names := names;
|}.

Section Macros.
  Context {state_t input_t output_t ip_t: Type}.

  Local Notation E := (@tf_expr state_t input_t output_t).
  Local Notation OPS := (@tf_ops state_t input_t output_t ip_t).

  Fixpoint mk_seq (l: list OPS) : OPS :=
    match l with
    | [] => tf_ops_base tf_nop
    | [o] => o
    | o :: rest => tf_ops_cons o (mk_seq rest)
    end.

  Context {K: Type} {K_fin: FiniteType K}.

  Definition mk_index_is (w: nat) (idx: E) (k: K) : E :=
    tf_op2 (tf_cmp w tf_eq) idx (tf_const (finite_index k)).

  (* Arrays are state families indexed by a finite type: cell [k] has index
     [finite_index k], compared at width [w]; an index naming no cell selects
     [default]. *)
  Definition mk_switch (w: nat) (idx: E) (body: K -> OPS) (default: OPS) : OPS :=
    List.fold_right (fun k acc => tf_ops_if (mk_index_is w idx k) (body k) acc)
      default (@finite_elements K K_fin).

  Definition mk_arr_read (w: nat) (idx: E) (cell: K -> E) (default: E) : E :=
    List.fold_right (fun k acc => tf_expr_if (mk_index_is w idx k) (cell k) acc)
      default (@finite_elements K K_fin).

  Definition mk_arr_write (w: nat) (idx: E) (cell: K -> state_t) (v: E) : OPS :=
    mk_switch w idx (fun k => tf_ops_base (tf_assign (cell k) v)) (tf_ops_base tf_nop).

  Definition mk_forall (body: K -> OPS) : OPS :=
    mk_seq (List.map body (@finite_elements K K_fin)).

  Context {O_fin: FiniteType output_t}.

  Definition mk_clear_outputs : OPS :=
    mk_seq (List.map (fun o => tf_ops_base (tf_output o (tf_const 0)))
                     (@finite_elements output_t O_fin)).

  Definition mk_zext (from to: nat) (e: E) : E :=
    match to - from with
    | 0 => e
    | d => tf_op2 (tf_concat d from) (tf_const 0) e
    end.

  Definition mk_pow2 (k: nat) : E :=
    match k with
    | 0 => tf_const 1
    | _ => tf_op2 (tf_concat 1 k) (tf_const 1) (tf_const 0)
    end.

  Definition mk_bit (k: nat) (e: E) : E :=
    tf_op2 (tf_cmp (S k) tf_ge) e (mk_pow2 k).

  Fixpoint mk_slice_aux (n lo: nat) (e: E) : E :=
    match n with
    | 0 => tf_const 0
    | 1 => mk_bit lo e
    | S n' => tf_op2 (tf_concat 1 n') (mk_bit (lo + n') e) (mk_slice_aux n' lo e)
    end.

  Definition mk_slice (hi lo: nat) (e: E) : E :=
    mk_slice_aux (S hi - lo) lo e.

  Fixpoint mk_chunks (l: list (nat * nat)) : E * nat :=
    match l with
    | [] => (tf_const 0, 0)
    | [(w, v)] => (tf_const v, w)
    | (w, v) :: rest =>
        let (e, wr) := mk_chunks rest in
        (tf_op2 (tf_concat w wr) (tf_const v) e, w + wr)
    end.

  Definition mk_bytes (l: list nat) : E :=
    fst (mk_chunks (List.map (fun b => (8, b)) l)).

  Definition mk_rep (nb c: nat) : E :=
    mk_bytes (List.repeat c nb).

  Fixpoint N_bytes_le (nb: nat) (n: N) : list nat * N :=
    match nb with
    | 0 => ([], n)
    | S nb' =>
        let (bs, rest) := N_bytes_le nb' (N.div n 256) in
        (N.to_nat (N.modulo n 256) :: bs, rest)
    end.

  Definition N_chunks (w: nat) (n: N) : list (nat * nat) :=
    let (bs, rest) := N_bytes_le (w / 8) n in
    let top := match w mod 8 with
               | 0 => []
               | r => [(r, N.to_nat (N.modulo rest (2 ^ N.of_nat r)))]
               end in
    top ++ List.rev (List.map (fun b => (8, b)) bs).

  Definition mk_N (w: nat) (n: N) : E :=
    fst (mk_chunks (N_chunks w n)).

  Definition hex_digit (c: ascii) : nat :=
    let n := nat_of_ascii c in
    if Nat.leb 48 n && Nat.leb n 57 then n - 48
    else if Nat.leb 97 n && Nat.leb n 102 then n - 87
    else if Nat.leb 65 n && Nat.leb n 70 then n - 55
    else 0.

  Fixpoint hex_digits (s: string) : list nat :=
    match s with
    | EmptyString => []
    | String c rest =>
        if Ascii.eqb c "_"%char then hex_digits rest
        else hex_digit c :: hex_digits rest
    end.

  Fixpoint hex_bytes (ds: list nat) : list (nat * nat) :=
    match ds with
    | a :: b :: rest => (8, 16 * a + b) :: hex_bytes rest
    | [a] => [(4, a)]
    | [] => []
    end.

  Definition mk_hex (s: string) : E :=
    let ds := hex_digits s in
    fst (mk_chunks
      (if Nat.odd (List.length ds)
       then match ds with d :: rest => (4, d) :: hex_bytes rest | [] => [] end
       else hex_bytes ds)).

  (* x := x mod m for a state x of width w and 1 <= m < 2^62: restoring division
     by the constants m * 2^i, so the latency does not depend on x. *)
  Definition mk_urem_const (x: state_t) (w: nat) (m: N) : OPS :=
    let bl := N.size_nat m in
    let c (i: nat) : E :=
      mk_zext (bl + i) w
        (match i with
         | 0 => mk_N bl m
         | _ => tf_op2 (tf_concat bl i) (mk_N bl m) (tf_const 0)
         end) in
    let step (i: nat) : OPS :=
      tf_ops_if (tf_op2 (tf_cmp w tf_ge) (tf_svar x) (c i))
        (tf_ops_base (tf_assign x (tf_op2 tf_sub (tf_svar x) (c i))))
        (tf_ops_base tf_nop) in
    if N.eqb m 0 || Nat.ltb w bl then tf_ops_base tf_nop
    else mk_seq (List.map step (List.rev (List.seq 0 (S (w - bl))))).

End Macros.
