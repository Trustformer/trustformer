Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
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

Definition mk_ip (req resp lat: nat) (fn: bits_t req -> bits_t resp) : ip_decl := {|
  ip_req_sz := req;
  ip_resp_sz := resp;
  ip_lat := Nat.max 1 lat;
  ip_lat_pos := Nat.le_max_l 1 lat;
  ip_fn := fn;
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

  Definition mk_for (n: nat) (body: nat -> OPS) : OPS :=
    mk_seq (List.map body (List.seq 0 n)).

  (* A skipped copy changes nothing, so once [cond] is false it stays false: a while loop
     of at most [n] rounds.  A public [cond] lets the action finish early; a secret one
     always waits for all [n] rounds. *)
  Definition mk_while (n: nat) (cond: E) (body: nat -> OPS) : OPS :=
    mk_for n (fun i => tf_ops_if cond (body i) (tf_ops_base tf_nop)).

  Definition mk_fold (n: nat) (f: nat -> E -> E) (init: E) : E :=
    List.fold_left (fun acc i => f i acc) (List.seq 0 n) init.

  Fixpoint mk_concat_aux (l: list (nat * E)) : E * nat :=
    match l with
    | [] => (tf_const 0, 0)
    | [(w, e)] => (tf_op1 (tf_resize w) e, w)
    | (w, e) :: rest =>
        let (r, wr) := mk_concat_aux rest in
        (tf_op2 (tf_concat w wr) e r, w + wr)
    end.

  Definition mk_concat (l: list (nat * E)) : E :=
    fst (mk_concat_aux l).

  Fixpoint mk_select_from (w i: nat) (idx: E) (l: list E) (default: E) : E :=
    match l with
    | [] => default
    | e :: rest =>
        tf_expr_if (tf_op2 (tf_cmp w tf_eq) idx (tf_const i)) e (mk_select_from w (S i) idx rest default)
    end.

  Definition mk_select (w: nat) (idx: E) (l: list E) (default: E) : E :=
    mk_select_from w 0 idx l default.

  Context {K: Type} {K_fin: FiniteType K}.

  Definition mk_index_is (w: nat) (idx: E) (k: K) : E :=
    tf_op2 (tf_cmp w tf_eq) idx (tf_const (finite_index k)).

  Definition mk_first (p: K -> E) (body: K -> OPS) (none: OPS) : OPS :=
    List.fold_right (fun k acc => tf_ops_if (p k) (body k) acc)
      none (@finite_elements K K_fin).

  (* Arrays are state families indexed by a finite type: cell [k] has index
     [finite_index k], compared at width [w]; an index naming no cell selects
     [default]. *)
  Definition mk_switch (w: nat) (idx: E) (body: K -> OPS) (default: OPS) : OPS :=
    mk_first (mk_index_is w idx) body default.

  Definition mk_arr_read (w: nat) (idx: E) (cell: K -> E) (default: E) : E :=
    List.fold_right (fun k acc => tf_expr_if (mk_index_is w idx k) (cell k) acc)
      default (@finite_elements K K_fin).

  Definition mk_arr_write (w: nat) (idx: E) (cell: K -> state_t) (v: E) : OPS :=
    mk_switch w idx (fun k => tf_ops_base (tf_assign (cell k) v)) (tf_ops_base tf_nop).

  Definition mk_forall (body: K -> OPS) : OPS :=
    mk_seq (List.map body (@finite_elements K K_fin)).

  Definition mk_any (p: K -> E) : E :=
    List.fold_right (fun k acc => tf_op2 tf_or (p k) acc) (tf_const 0) (@finite_elements K K_fin).

  Definition mk_all (p: K -> E) : E :=
    List.fold_right (fun k acc => tf_op2 tf_and (p k) acc) (tf_op1 tf_not (tf_const 0))
      (@finite_elements K K_fin).

  Definition mk_next (k: K) : option K :=
    List.nth_error (@finite_elements K K_fin) (S (finite_index k)).

  Definition mk_shift_down (cell: K -> state_t) (fill: E) : OPS :=
    mk_forall (fun k => match mk_next k with
                        | Some k' => tf_ops_base (tf_assign (cell k) (tf_svar (cell k')))
                        | None => tf_ops_base (tf_assign (cell k) fill)
                        end).

  Context {O_fin: FiniteType output_t}.

  Definition mk_clear_outputs : OPS :=
    mk_seq (List.map (fun o => tf_ops_base (tf_output o (tf_const 0)))
                     (@finite_elements output_t O_fin)).

  Definition mk_zext (from to: nat) (e: E) : E :=
    match to - from with
    | 0 => if Nat.eqb to from then tf_op1 (tf_resize from) e
           else tf_op1 (tf_resize to) (tf_op1 (tf_resize from) e)
    | d => tf_op2 (tf_concat d from) (tf_const 0) e
    end.

  Definition mk_pow2 (k: nat) : E :=
    match k with
    | 0 => tf_const 1
    | _ => tf_op2 (tf_concat 1 k) (tf_const 1) (tf_const 0)
    end.

  Definition mk_slice (hi lo: nat) (e: E) : E :=
    tf_op1 (tf_resize (S hi - lo)) (tf_op1 (tf_slice (S hi) lo) e).

  Definition mk_bit (k: nat) (e: E) : E :=
    mk_slice k k e.

  Definition mk_sext (s t: nat) (e: E) : E :=
    match s with
    | 0 => tf_const 0
    | S s' =>
        if Nat.leb t s then tf_op1 (tf_resize t) (tf_op1 (tf_resize s) e)
        else let m := mk_zext s t (mk_pow2 s') in
             tf_op1 (tf_resize t) (tf_op2 tf_sub (tf_op2 tf_xor (mk_zext s t (tf_op1 (tf_resize s) e)) m) m)
    end.

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

  Definition packed_all_valid (wd w iw: nat) : bool :=
    Nat.leb iw (Nat.log2 (wd / w)).

  Definition packed_in_range (wd w iw: nat) (i: E) : E :=
    tf_op2 (tf_cmp iw tf_lt) i (tf_const (wd / w)).

  Definition mk_packed_get (wd w iw: nat) (x i: E) : E :=
    let read := tf_op1 (tf_resize w) (tf_op2 (tf_islice wd) x (tf_op2 tf_mul i (tf_const w))) in
    if packed_all_valid wd w iw then read
    else tf_expr_if (packed_in_range wd w iw i) read (tf_const 0).

  Definition mk_packed_set (x: state_t) (wd w iw: nat) (i v: E) : OPS :=
    let off := tf_op2 tf_mul i (tf_const w) in
    let mask := mk_zext w wd (tf_op1 (tf_resize w) (tf_op1 tf_not (tf_const 0))) in
    let write := tf_ops_base (tf_assign x
      (tf_op2 tf_or
         (tf_op2 tf_and (tf_svar x) (tf_op1 tf_not (tf_op2 tf_lsl mask off)))
         (tf_op2 tf_lsl (mk_zext w wd (tf_op1 (tf_resize w) v)) off))) in
    if packed_all_valid wd w iw then write
    else tf_ops_if (packed_in_range wd w iw i) write (tf_ops_base tf_nop).

  Definition mk_case (w: nat) (e: E) (arms: list (N * OPS)) (default: OPS) : OPS :=
    List.fold_right
      (fun arm acc => tf_ops_if (tf_op2 (tf_cmp w tf_eq) e (mk_N w (fst arm))) (snd arm) acc)
      default (List.filter (fun arm => Nat.leb (N.size_nat (fst arm)) w) arms).

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

Notation "'for' i '<' n 'do' b 'end'" := (mk_for n (fun i => b))
  (in custom trustformer at level 89, i name, n constr at level 0, b custom trustformer at level 99).
Notation "'for' i '<' n 'while' c 'do' b 'end'" := (mk_while n c (fun i => b))
  (in custom trustformer at level 89, i name, n constr at level 0, c custom trustformer at level 99,
   b custom trustformer at level 99).
Notation "x [ hi : lo ]" := (mk_slice hi lo x)
  (in custom trustformer at level 3, left associativity, hi custom tf_const at level 0,
   lo custom tf_const at level 0, format "x [ hi : lo ]").

Section Harness.
  Context (ctx: TFSchedContext).

  Local Instance sim_states_fin : FiniteType (tfs_spec_states ctx) := tfs_spec_states_fin ctx.
  Local Instance sim_outputs_fin : FiniteType (tfs_spec_outputs ctx) := tfs_spec_outputs_fin ctx.
  Local Instance sim_inputs_fin : FiniteType (tfs_spec_inputs ctx) := tfs_spec_inputs_fin ctx.

  Definition sim_state :=
    (ContextEnv.(env_t) (tf_states_type (tfs_spec_states_size ctx))
     * ContextEnv.(env_t) (tf_outputs_type (tfs_spec_outputs_size ctx)))%type.

  Definition sim_init : sim_state :=
    (ContextEnv.(create) (tfs_spec_states_init ctx), ContextEnv.(create) (fun _ => Bits.zero)).

  Definition sim_inputs (f: tfs_spec_inputs ctx -> N) (x: tfs_spec_inputs ctx)
    : bits_t (tfs_spec_inputs_size ctx x) :=
    Bits.of_N _ (f x).

  Definition sim_step (a: tfs_spec_action ctx) (f: tfs_spec_inputs ctx -> N) (s: sim_state) : sim_state :=
    tf_ops_run (tfs_spec_states_size ctx) (tfs_spec_inputs_size ctx) (tfs_spec_outputs_size ctx)
      (tfs_spec_ip ctx) (tfs_spec_action_ops ctx a) s (sim_inputs f).

  Definition sim_steps (l: list (tfs_spec_action ctx * (tfs_spec_inputs ctx -> N))) (s: sim_state) : sim_state :=
    List.fold_left (fun s c => sim_step (fst c) (snd c) s) l s.

  Definition sim_out (s: sim_state) (o: tfs_spec_outputs ctx) : N :=
    Bits.to_N (ContextEnv.(getenv) (snd s) o).

  Definition sim_reg (s: sim_state) (x: tfs_spec_states ctx) : N :=
    Bits.to_N (ContextEnv.(getenv) (fst s) x).
End Harness.

(* Width lint: implicit truncations (operands, values, constants, shift amounts),
   signed operations on narrower zero-extended operands, and if-conditions wider
   than one bit, of which only bit 0 is tested. *)
Inductive lint_issue :=
  | lint_concat (annotated operand: nat)
  | lint_compare (width operand: nat)
  | lint_assign (dst value: nat)
  | lint_call (req arg: nat)
  | lint_const (width value: nat)
  | lint_condition (operand: nat)
  | lint_index (width operand: nat)
  | lint_shift (width amount: nat)
  | lint_signed (width operand: nat).

Section Lint.
  Context {state_t input_t output_t ip_t: Type}.
  Context (s_sz: state_t -> nat) (i_sz: input_t -> nat) (o_sz: output_t -> nat) (ips: ip_t -> ip_decl).

  Local Notation E := (@tf_expr state_t input_t output_t).
  Local Notation OPS := (@tf_ops state_t input_t output_t ip_t).

  Fixpoint natural_width (e: E) : option nat :=
    match e with
    | tf_const _ => None
    | tf_svar v => Some (s_sz v)
    | tf_ivar v => Some (i_sz v)
    | tf_ovar v => Some (o_sz v)
    | tf_op1 tf_not _ => None
    | tf_op1 (tf_resize s) _ => Some s
    | tf_op1 (tf_slice _ _) _ => None
    | tf_op2 tf_lsr a _ | tf_op2 tf_asr a _ => natural_width a
    | tf_op2 tf_lsl _ _ => None
    | tf_op2 (tf_islice _) _ _ => None
    | tf_op2 (tf_cmp _ _) _ _ => Some 1
    | tf_op2 (tf_concat hi lo) _ _ => Some (hi + lo)
    | tf_op2 _ a b | tf_expr_if _ a b =>
        match natural_width a, natural_width b with
        | Some x, Some y => Some (Nat.max x y)
        | _, _ => None
        end
    end.

  Definition narrower (w: nat) (e: E) (issue: nat -> nat -> lint_issue) : list lint_issue :=
    match natural_width e with
    | Some k => if Nat.ltb w k then [issue w k] else []
    | None => []
    end.

  Definition wider (w: nat) (e: E) : list lint_issue :=
    match natural_width e with
    | Some k => if Nat.ltb k w then [lint_signed w k] else []
    | None => []
    end.

  Definition condition (c: E) : list lint_issue :=
    match natural_width c with
    | Some k => if Nat.ltb 1 k then [lint_condition k] else []
    | None => []
    end.

  Fixpoint lint_expr (w: nat) (e: E) : list lint_issue :=
    match e with
    | tf_const v => if Nat.leb w (Nat.log2 v) then [lint_const w v] else []
    | tf_svar _ | tf_ivar _ | tf_ovar _ => []
    | tf_op1 tf_not a => lint_expr w a
    | tf_op1 (tf_resize s) a => lint_expr s a
    | tf_op1 (tf_slice s _) a => lint_expr s a
    | tf_op2 (tf_islice s) a b =>
        narrower (Nat.log2_up s) b lint_index ++ lint_expr s a ++ lint_expr (Nat.log2_up s) b
    | tf_op2 (tf_cmp n tf_slt) a b =>
        narrower n a lint_compare ++ narrower n b lint_compare ++ wider n a ++ wider n b
        ++ lint_expr n a ++ lint_expr n b
    | tf_op2 (tf_cmp n _) a b =>
        narrower n a lint_compare ++ narrower n b lint_compare ++ lint_expr n a ++ lint_expr n b
    | tf_op2 tf_asr a b => wider w a ++ narrower w b lint_shift ++ lint_expr w a ++ lint_expr w b
    | tf_op2 tf_lsr a b | tf_op2 tf_lsl a b => narrower w b lint_shift ++ lint_expr w a ++ lint_expr w b
    | tf_op2 (tf_concat hi lo) a b =>
        narrower hi a lint_concat ++ narrower lo b lint_concat ++ lint_expr hi a ++ lint_expr lo b
    | tf_op2 _ a b => lint_expr w a ++ lint_expr w b
    | tf_expr_if c a b => condition c ++ lint_expr 1 c ++ lint_expr w a ++ lint_expr w b
    end.

  Fixpoint lint_ops (o: OPS) : list lint_issue :=
    match o with
    | tf_ops_base tf_nop => []
    | tf_ops_base (tf_assign x e) => narrower (s_sz x) e lint_assign ++ lint_expr (s_sz x) e
    | tf_ops_base (tf_output x e) => narrower (o_sz x) e lint_assign ++ lint_expr (o_sz x) e
    | tf_ops_base (tf_call p d a) =>
        narrower (ip_req_sz (ips p)) a lint_call ++ lint_expr (ip_req_sz (ips p)) a
        ++ (if Nat.ltb (s_sz d) (ip_resp_sz (ips p)) then [lint_assign (s_sz d) (ip_resp_sz (ips p))] else [])
    | tf_ops_cons a b => lint_ops a ++ lint_ops b
    | tf_ops_if c a b => condition c ++ lint_expr 1 c ++ lint_ops a ++ lint_ops b
    end.
End Lint.

Definition tf_lint (ctx: TFSchedContext) : list (tfs_spec_action ctx * lint_issue) :=
  List.flat_map
    (fun a => List.map (fun i => (a, i))
       (lint_ops (tfs_spec_states_size ctx) (tfs_spec_inputs_size ctx) (tfs_spec_outputs_size ctx)
          (tfs_spec_ip ctx) (tfs_spec_action_ops ctx a)))
    (@finite_elements _ (tfs_spec_action_fin ctx)).
