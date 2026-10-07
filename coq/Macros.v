Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.

Require Import Trustformer.Syntax.
Require Import Trustformer.Contract.
Require Import Trustformer.Backend.Lowering.

(* Macros: Gallina functions that write Trustformer syntax for things the DSL
   has no construct for (arrays, bit slices, wide constants, modulo by a
   constant), plus [mk_synth_ctx], which derives the action encoding so that a
   spec writes no proof at all.

   A macro needs no proof.  The headline theorems hold for every [tf_ops] and
   put no well-formedness condition on actions, so whatever a macro emits is
   covered.  A wrong macro yields a design that is still secure but does not
   do what was meant: check the generated design against the spec with
   vm_compute Examples (Regressions/MacroLib.v does this for every macro here).

   Two rules every macro below follows:
   - Exact widths.  A concat or compare used in a wider context is widened by
     [synth_convert] (Backend/Lowering.v), a Koika Slice wider than its operand
     that cuttlec prints as an out-of-range part-select.  Each macro states the
     width of its result; use it there, or widen it with [mk_zext].
   - No big numbers.  Macros run in the extracted program, where Koika maps
     nat, N and Z to OCaml's 63-bit int (Koika/Extraction/ExtractionSetup.v).
     Nothing here computes a value larger than its arguments, and wide
     constants are built from byte literals.  A macro that computes 2^62 or
     more passes every vm_compute Example and still emits wrong Verilog. *)

(* ---------------------------------------------------------------- Encoding *)

(* [tf_action_encoding_inj] used to be the one proof each spec wrote.  The
   action type already has a [FiniteType] instance, and its index is an
   injective encoding.  Action [a] gets command code [finite_index a], i.e.
   its position in the declaration for a derived instance. *)

Section DerivedEncoding.
  Context {A: Type} {FT: FiniteType A}.

  (* Wide enough for every index: n < 2^(S (log2 n)). *)
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

(* The synthesis context for a schedule, with everything else derived:
     Definition tf_ctx := mk_synth_ctx (tfs_schedule tfs_ctx 10). *)
Definition mk_synth_ctx (s: TFSchedule) {names: Show (tfs_action s)} : TFSynthContext := {|
  tf_sched_ctx := s;
  tf_action_reg_size := @auto_enc_sz (tfs_action s) (tfs_action_fin s);
  tf_action_encoding := @auto_enc (tfs_action s) (tfs_action_fin s);
  tf_action_encoding_inj := @auto_enc_inj (tfs_action s) (tfs_action_fin s);
  tf_action_names := names;
|}.

(* ------------------------------------------------------------ Syntax macros *)

Section Macros.
  Context {state_t input_t output_t ip_t: Type}.

  Local Notation E := (@tf_expr state_t input_t output_t).
  Local Notation OPS := (@tf_ops state_t input_t output_t ip_t).

  (* -- Sequencing -- *)

  (* [o1; ...; on]; the empty list is [pass] *)
  Fixpoint mk_seq (l: list OPS) : OPS :=
    match l with
    | [] => tf_ops_base tf_nop
    | [o] => o
    | o :: rest => tf_ops_cons o (mk_seq rest)
    end.

  (* -- Arrays --

     The DSL has no arrays.  An array is a family of state variables indexed by
     a finite type, one register per cell:
       Inductive slot := S0 | S1 | S2 | S3.
       Inductive states := st_pin (s: slot) | st_data (s: slot).
     Cell [k] has index [finite_index k], its position in the declaration.  The
     index expression is compared at width [w], so [K] may have at most 2^w
     cells; an index that names no cell selects the default.  Each access
     unrolls into one compare per cell; with a secret index every arm is padded
     to the same latency. *)

  Context {K: Type} {K_fin: FiniteType K}.

  (* 1 bit: [idx] names cell [k] *)
  Definition mk_index_is (w: nat) (idx: E) (k: K) : E :=
    tf_op2 (tf_cmp w tf_eq) idx (tf_const (finite_index k)).

  (* [body k] for the cell [idx] names, [default] if it names none *)
  Definition mk_switch (w: nat) (idx: E) (body: K -> OPS) (default: OPS) : OPS :=
    List.fold_right (fun k acc => tf_ops_if (mk_index_is w idx k) (body k) acc)
      default (@finite_elements K K_fin).

  (* the cell [idx] names, [default] if it names none; at the context width *)
  Definition mk_arr_read (w: nat) (idx: E) (cell: K -> E) (default: E) : E :=
    List.fold_right (fun k acc => tf_expr_if (mk_index_is w idx k) (cell k) acc)
      default (@finite_elements K K_fin).

  (* [cell idx := v]; nothing is written if [idx] names no cell *)
  Definition mk_arr_write (w: nat) (idx: E) (cell: K -> state_t) (v: E) : OPS :=
    mk_switch w idx (fun k => tf_ops_base (tf_assign (cell k) v)) (tf_ops_base tf_nop).

  (* [body k] for every cell, in index order *)
  Definition mk_forall (body: K -> OPS) : OPS :=
    mk_seq (List.map body (@finite_elements K K_fin)).

  (* -- Outputs -- *)

  Context {O_fin: FiniteType output_t}.

  (* 0 to every output.  Outputs keep their value between actions, so an
     action that starts with this shows nothing from an earlier one (the
     clear_results idiom of Examples/Mars). *)
  Definition mk_clear_outputs : OPS :=
    mk_seq (List.map (fun o => tf_ops_base (tf_output o (tf_const 0)))
                     (@finite_elements output_t O_fin)).

  (* -- Bits -- *)

  (* e, evaluated at width [from], zero-extended to width [to] by an explicit
     concat (no-op if [to <= from]) *)
  Definition mk_zext (from to: nat) (e: E) : E :=
    match to - from with
    | 0 => e
    | d => tf_op2 (tf_concat d from) (tf_const 0) e
    end.

  (* 2^k at width k+1, with no large literal *)
  Definition mk_pow2 (k: nat) : E :=
    match k with
    | 0 => tf_const 1
    | _ => tf_op2 (tf_concat 1 k) (tf_const 1) (tf_const 0)
    end.

  (* bit k of e, 1 bit wide.  The compare reads the low k+1 bits of e, and
     those are >= 2^k exactly when bit k is set.  The DSL keeps only low bits
     (resize truncates, there is no shift right), so this is the way up. *)
  Definition mk_bit (k: nat) (e: E) : E :=
    tf_op2 (tf_cmp (S k) tf_ge) e (mk_pow2 k).

  Fixpoint mk_slice_aux (n lo: nat) (e: E) : E :=
    match n with
    | 0 => tf_const 0
    | 1 => mk_bit lo e
    | S n' => tf_op2 (tf_concat 1 n') (mk_bit (lo + n') e) (mk_slice_aux n' lo e)
    end.

  (* e[hi:lo] for hi >= lo, hi-lo+1 bits wide: one compare per bit *)
  Definition mk_slice (hi lo: nat) (e: E) : E :=
    mk_slice_aux (S hi - lo) lo e.

  (* -- Constants --

     [tf_const] carries a unary nat: cuttlec overflows its stack at about 1e6,
     and vm_compute slows down well before that.  Wider constants are
     concatenations of small literals. *)

  (* big-endian (width, value) chunks, concatenated, with the total width;
     each value must be < 2^width *)
  Fixpoint mk_chunks (l: list (nat * nat)) : E * nat :=
    match l with
    | [] => (tf_const 0, 0)
    | [(w, v)] => (tf_const v, w)
    | (w, v) :: rest =>
        let (e, wr) := mk_chunks rest in
        (tf_op2 (tf_concat w wr) (tf_const v) e, w + wr)
    end.

  (* big-endian bytes, 8 * length bits wide *)
  Definition mk_bytes (l: list nat) : E :=
    fst (mk_chunks (List.map (fun b => (8, b)) l)).

  (* byte [c] repeated [nb] times (e.g. HMAC's ipad), 8 * nb bits wide *)
  Definition mk_rep (nb c: nat) : E :=
    mk_bytes (List.repeat c nb).

  (* the [nb] low bytes of n, least significant first, and what is left *)
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

  (* n mod 2^w at exactly width w.  n itself must be < 2^62 (an OCaml int
     once extracted); write wider constants with [mk_hex]. *)
  Definition mk_N (w: nat) (n: N) : E :=
    fst (mk_chunks (N_chunks w n)).

  Definition hex_digit (c: ascii) : nat :=
    let n := nat_of_ascii c in
    if Nat.leb 48 n && Nat.leb n 57 then n - 48          (* 0-9 *)
    else if Nat.leb 97 n && Nat.leb n 102 then n - 87    (* a-f *)
    else if Nat.leb 65 n && Nat.leb n 70 then n - 55     (* A-F *)
    else 0.

  (* hex digits, skipping the separator '_' *)
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

  (* a constant written in hex, 4 bits per digit; '_' separates groups and
     any other non-hex character counts as 0.  For any width:
       mk_hex "6a09e667_bb67ae85" *)
  Definition mk_hex (s: string) : E :=
    let ds := hex_digits s in
    fst (mk_chunks
      (if Nat.odd (List.length ds)
       then match ds with d :: rest => (4, d) :: hex_bytes rest | [] => [] end
       else hex_bytes ds)).

  (* -- Arithmetic -- *)

  (* x := x mod m in place, for a state [x] of width [w] and 1 <= m < 2^62.
     Restoring division by the constant: for i = k .. 0, with c_i = m * 2^i,
       if x >=[w] c_i then x := x - c_i
     where k is the largest i with c_i < 2^w, so every w-bit x is reduced.  It
     is a fixed sequence of compares and subtracts, so its latency does not
     depend on x, and c_i is built by concat, so no number exceeds m. *)
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
