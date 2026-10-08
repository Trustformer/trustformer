Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Coq.NArith.NArith.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Backend.Lowering.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Macros.
Require Trustformer.Theorems.Definitions.
Require Trustformer.Theorems.IPR.
Require Trustformer.Theorems.Synthesis.
Require Trustformer.Theorems.SchedulerSimulation.

Require Import Coq.Lists.List.
Import ListNotations.

(* Knox's two-row lockbox: multi-lockbox-pad, and multi-lockbox-leak with its
   #:leak dropped (knox-hsm). *)

Section FunctionalSpecification.

    Definition TW := 16.
    Definition W := 128.

    Inductive fs_action := act_store | act_get.

    Inductive row := r0 | r1.

    Inductive fs_states :=
    | st_valid (r: row) | st_tag (r: row) | st_secret (r: row) | st_password (r: row).
    Inductive fs_inputs := in_tag | in_secret | in_password.
    Inductive fs_outputs := out_ok | out_ret.

    Definition fs_states_size (tw w: nat) (x: fs_states) : nat :=
      match x with
      | st_valid _ => 1
      | st_tag _ => tw
      | st_secret _ | st_password _ => w
      end.
    Definition fs_inputs_size (tw w: nat) (x: fs_inputs) : nat :=
      match x with
      | in_tag => tw
      | in_secret | in_password => w
      end.
    Definition fs_outputs_size (w: nat) (x: fs_outputs) : nat :=
      match x with
      | out_ok => 1
      | out_ret => w
      end.

    Definition fs_states_init (x: fs_states) : tf_states_type (fs_states_size TW W) x :=
      Bits.zero.

    Local Notation E := (@tf_expr fs_states fs_inputs fs_outputs).
    Local Notation OPS := (@tf_ops fs_states fs_inputs fs_outputs Empty_set).

    Definition matches (tw: nat) (r: row) : E :=
      {[ ($(st_valid r) ==[1] #1) & ($(st_tag r) ==[tw] $in_tag) ]}.
    Definition free (r: row) : E := {[ $(st_valid r) ==[1] #0 ]}.

    Definition at_row (r: row) : E := tf_const (finite_index r).
    Definition NONE : E := tf_const 2.
    Definition IDX := 2.

    Definition store_row (tw: nat) : E :=
      {[ if `matches tw r0` then `at_row r0`
         else if `matches tw r1` then `at_row r1`
         else if `free r0` then `at_row r0`
         else if `free r1` then `at_row r1`
         else `NONE` ]}.

    Definition get_row (tw: nat) : E :=
      {[ if `matches tw r0` then `at_row r0`
         else if `matches tw r1` then `at_row r1`
         else `NONE` ]}.

    Definition write_row (r: row) : OPS :=
      {[ let $(st_valid r) := #1;
         let $(st_tag r) := $in_tag;
         let $(st_secret r) := $in_secret;
         let $(st_password r) := $in_password;
         let $out_ok := #1 ]}.

    Definition open_row (w: nat) (r: row) : OPS :=
      {[ let $out_ret := (if ($(st_password r) ==[w] $in_password) then $(st_secret r) else #0);
         let $(st_valid r) := #0;
         let $(st_tag r) := #0;
         let $(st_secret r) := #0;
         let $(st_password r) := #0 ]}.

    Definition fs_ops (tw w: nat) (a: fs_action) : OPS :=
      match a with
      | act_store =>
          {[ `mk_clear_outputs`;
             `mk_switch IDX (store_row tw) write_row {[ pass ]}` ]}
      | act_get =>
          {[ `mk_clear_outputs`;
             `mk_switch IDX (get_row tw) (open_row w) {[ pass ]}` ]}
      end.

End FunctionalSpecification.

Section Checks.

    Local Notation OPS := (@tf_ops fs_states fs_inputs fs_outputs Empty_set).

    Example store_unfolds : fs_ops TW W act_store =
      {[ (let $out_ok := #0; let $out_ret := #0);
         if (`store_row TW` ==[2] #0) then `write_row r0`
         else if (`store_row TW` ==[2] #1) then `write_row r1`
         else pass ]}.
    Proof. reflexivity. Qed.

    Example get_unfolds : fs_ops TW W act_get =
      {[ (let $out_ok := #0; let $out_ret := #0);
         if (`get_row TW` ==[2] #0) then `open_row W r0`
         else if (`get_row TW` ==[2] #1) then `open_row W r1`
         else pass ]}.
    Proof. reflexivity. Qed.

    Record krow := KR { kv: bool; kt: N; ks: N; kp: N }.
    Definition row_empty : krow := KR false 0 0 0.
    Definition kstate := (krow * krow)%type.
    Definition s0 : kstate := (row_empty, row_empty).

    Definition kmatch (r: krow) (t: N) : bool := kv r && N.eqb (kt r) t.

    Definition knox_store (t x p: N) (s: kstate) : bool * kstate :=
      let '(a, b) := s in
      let nr := KR true t x p in
      if kmatch a t then (true, (nr, b))
      else if kmatch b t then (true, (a, nr))
      else if negb (kv a) then (true, (nr, b))
      else if negb (kv b) then (true, (a, nr))
      else (false, s).

    Definition knox_get (t g: N) (s: kstate) : N * kstate :=
      let '(a, b) := s in
      if kmatch a t then ((if N.eqb (kp a) g then ks a else 0%N), (row_empty, b))
      else if kmatch b t then ((if N.eqb (kp b) g then ks b else 0%N), (a, row_empty))
      else (0%N, s).

    Inductive kcall := c_store (t x p: N) | c_get (t g: N).
    Inductive kret := r_bool (b: bool) | r_bv (v: N).

    Definition knox_step (c: kcall) (s: kstate) : kret * kstate :=
      match c with
      | c_store t x p => let '(b, s') := knox_store t x p s in (r_bool b, s')
      | c_get t g => let '(v, s') := knox_get t g s in (r_bv v, s')
      end.

    Definition enc (r: kret) : N * N :=
      match r with
      | r_bool b => ((if b then 1 else 0), 0)%N
      | r_bv v => (0%N, v)
      end.

    Definition pair_eqb (a b: N * N) : bool := N.eqb (fst a) (fst b) && N.eqb (snd a) (snd b).

    Definition sysst (tw w: nat) :=
      (ContextEnv.(env_t) (tf_states_type (fs_states_size tw w))
       * ContextEnv.(env_t) (tf_outputs_type (fs_outputs_size w)))%type.

    Definition fld (r: krow) (k: fs_states) : N :=
      match k with
      | st_valid _ => if kv r then 1%N else 0%N
      | st_tag _ => kt r
      | st_secret _ => ks r
      | st_password _ => kp r
      end.

    Definition rowsel (s: kstate) (k: fs_states) : krow :=
      match k with
      | st_valid r0 | st_tag r0 | st_secret r0 | st_password r0 => fst s
      | _ => snd s
      end.

    Definition mk (tw w: nat) (s: kstate) (ok ret: N) : sysst tw w :=
      (ContextEnv.(create) (fun k => Bits.of_N (fs_states_size tw w k) (fld (rowsel s k) k)),
       ContextEnv.(create) (fun x => match x return tf_outputs_type (fs_outputs_size w) x with
                                     | out_ok => Bits.of_N 1 ok
                                     | out_ret => Bits.of_N w ret
                                     end)).

    Definition rd {tw w} (st: sysst tw w) (k: fs_states) : N :=
      Bits.to_N (ContextEnv.(getenv) (fst st) k).
    Definition ports {tw w} (st: sysst tw w) : N * N :=
      (Bits.to_N (ContextEnv.(getenv) (snd st) out_ok),
       Bits.to_N (ContextEnv.(getenv) (snd st) out_ret)).

    Definition all_fields : list fs_states :=
      [st_valid r0; st_tag r0; st_secret r0; st_password r0;
       st_valid r1; st_tag r1; st_secret r1; st_password r1].

    Definition same_state {tw w} (st: sysst tw w) (s: kstate) : bool :=
      forallb (fun k => N.eqb (rd st k) (fld (rowsel s k) k)) all_fields.
    Definition state_eqb (x y: kstate) : bool :=
      forallb (fun k => N.eqb (fld (rowsel x k) k) (fld (rowsel y k) k)) all_fields.

    Definition inp (tw w: nat) (t x p: N) (i: fs_inputs) : bits_t (fs_inputs_size tw w i) :=
      match i with
      | in_tag => Bits.of_N tw t
      | in_secret => Bits.of_N w x
      | in_password => Bits.of_N w p
      end.

    Definition run (tw w: nat) (a: fs_action) (t x p: N) (st: sysst tw w) : sysst tw w :=
      tf_ops_run (fs_states_size tw w) (fs_inputs_size tw w) (fs_outputs_size w) no_ips
                 (fs_ops tw w a) st (inp tw w t x p).

    Definition do_call (tw w: nat) (j: N) (c: kcall) (st: sysst tw w) : sysst tw w :=
      match c with
      | c_store t x p => run tw w act_store t x p st
      | c_get t g => run tw w act_get t j g st
      end.

    Definition nums (n: nat) : list N := map N.of_nat (seq 0 n).
    Definition rows (tw w: nat) : list krow :=
      flat_map (fun v => flat_map (fun t => flat_map (fun x => map (fun p => KR v t x p)
        (nums (2 ^ w))) (nums (2 ^ w))) (nums (2 ^ tw))) [false; true].
    Definition states (tw w: nat) : list kstate :=
      flat_map (fun a => map (fun b => (a, b)) (rows tw w)) (rows tw w).

    Definition agree_step (tw w: nat) (c: kcall) (s: kstate) : bool :=
      let r := do_call tw w 1 c (mk tw w s 1 1) in
      let '(ret, s') := knox_step c s in
      pair_eqb (ports r) (enc ret) && same_state r s'.

    Definition check_store (tw w: nat) : bool :=
      forallb (fun s => forallb (fun t => forallb (fun x => forallb (fun p =>
        agree_step tw w (c_store t x p) s)
        (nums (2 ^ w))) (nums (2 ^ w))) (nums (2 ^ tw))) (states tw w).

    Definition check_get (tw w: nat) : bool :=
      forallb (fun s => forallb (fun t => forallb (fun g =>
        agree_step tw w (c_get t g) s)
        (nums (2 ^ w))) (nums (2 ^ tw))) (states tw w).

    Example states_count : length (states 2 1) = 1024.
    Proof. vm_compute. reflexivity. Qed.
    Example exhaustive_store_tw2_w1 : check_store 2 1 = true.
    Proof. vm_compute. reflexivity. Qed.
    Example exhaustive_get_tw2_w1 : check_get 2 1 = true.
    Proof. vm_compute. reflexivity. Qed.

    Definition ALL : N := N.ones 128.
    Definition HI : N := N.shiftl 1 127.
    Definition TALL : N := N.ones 16.
    Definition S1 : N := 0x0123456789abcdef_fedcba9876543210.
    Definition P1 : N := 0xa5a5a5a5c3c3c3c3_0f0f0f0f99999999.
    Definition S2 : N := 0xdeadbeefcafebabe_0000000000000001.
    Definition P2 : N := 0x00000000ffffffff.
    Definition S3 : N := 0x77777777777777777777777777777777.
    Definition P3 : N := 0x8000000000000000000000000000beef.

    Definition initial : sysst TW W :=
      (ContextEnv.(create) fs_states_init, ContextEnv.(create) (fun _ => Bits.zero)).

    Fixpoint tf_session (j: N) (cs: list kcall) (st: sysst TW W) : list (N * N) * sysst TW W :=
      match cs with
      | [] => ([], st)
      | c :: cs' => let st' := do_call TW W j c st in
                    let '(os, fin) := tf_session j cs' st' in (ports st' :: os, fin)
      end.

    Fixpoint knox_session (cs: list kcall) (s: kstate) : list (N * N) * kstate :=
      match cs with
      | [] => ([], s)
      | c :: cs' => let '(r, s') := knox_step c s in
                    let '(os, fin) := knox_session cs' s' in (enc r :: os, fin)
      end.

    Definition agree (j: N) (cs: list kcall) (s: kstate) (ok ret: N) : bool :=
      let '(o1, f1) := tf_session j cs (mk TW W s ok ret) in
      let '(o2, f2) := knox_session cs s in
      forallb (fun '(a, b) => pair_eqb a b) (combine o1 o2)
      && Nat.eqb (length o1) (length o2) && same_state f1 f2.

    Definition T : N * N := (1, 0)%N.
    Definition F : N * N := (0, 0)%N.
    Definition V (v: N) : N * N := (0%N, v).

    Definition sessions : list (list kcall) :=
      [
        [c_get 0 0; c_store 0 0 0; c_get 0 0];
        [c_store 34 1337 1234; c_get 34 0; c_get 34 1234];
        [c_store 34 1337 1234; c_get 34 1234; c_get 34 1234];
        [c_store 1 S1 P1; c_store 2 S2 P2; c_store 3 S3 P3; c_get 3 P3; c_get 2 P2; c_get 1 P1];
        [c_store 1 S1 P1; c_store 2 S2 P2; c_get 1 0; c_store 2 S3 P3; c_get 2 P2;
         c_store 1 S1 P1; c_get 1 P1];
        [c_store 1 S1 P1; c_store 2 S2 P2; c_get 1 0; c_store 2 S3 P3; c_store 9 S1 P1;
         c_get 2 P3; c_get 9 P1];
        [c_store TALL S1 P1; c_get TALL (N.lxor P1 HI); c_get TALL P1;
         c_store TALL S2 P2; c_get TALL (N.lxor P2 1); c_get TALL P2];
        [c_store 0 ALL ALL; c_get 5 ALL; c_get 0 ALL; c_get 0 ALL];
        [c_store 7 S1 P1; c_store 7 S2 P2; c_get 7 P1; c_store 7 S1 P1; c_store 7 S2 P2; c_get 7 P2];
        [c_store 7 S1 P1; c_get 7 P1; c_store 8 S2 P2; c_get 8 0; c_store 7 0 0; c_get 7 0] ].

    Example session_values :
      map (fun cs => fst (tf_session S2 cs initial)) sessions =
      [ [V 0; T; V 0];
        [T; V 0; V 0];
        [T; V 1337; V 0];
        [T; T; F; V 0; V S2; V S1];
        [T; T; V 0; T; V 0; T; V S1];
        [T; T; V 0; T; T; V S3; V S1];
        [T; V 0; V 0; T; V 0; V 0];
        [T; V 0; V ALL; V 0];
        [T; T; V 0; T; T; V S2];
        [T; V S1; T; V 0; T; V 0] ].
    Proof. vm_compute. reflexivity. Qed.

    Example sessions_agree_from_reset :
      forallb (fun cs => agree S2 cs s0 0 0) sessions = true.
    Proof. vm_compute. reflexivity. Qed.

    Example sessions_agree_any_state :
      forallb (fun s => forallb (fun cs => agree ALL cs s 1 S3) sessions)
        [ (KR true 1 S2 P2, row_empty);
          (row_empty, KR true 2 S2 P2);
          (KR true 1 S2 P2, KR true 1 S3 P3);
          (KR false 34 S3 1234, KR false 1 S2 P2);
          (KR true 3 S3 P3, KR true 4 S2 P2) ] = true.
    Proof. vm_compute. reflexivity. Qed.

    Definition dup : kstate := (KR true 1 S2 P2, KR true 1 S3 P3).
    Example duplicate_tag_row0_wins :
      (fst (tf_session 0 [c_get 1 P3; c_get 1 P3] (mk TW W dup 0 0)),
       fst (tf_session 0 [c_store 1 S1 P1; c_get 1 P3; c_get 1 P3] (mk TW W dup 0 0)))
      = ([V 0; V S3], [T; V 0; V S3]).
    Proof. vm_compute. reflexivity. Qed.

    Definition s1 : sysst TW W := do_call TW W 0 (c_store 34 1337 1234) initial.
    Definition bad2 : sysst TW W := do_call TW W 0 (c_get 34 0) s1.
    Example rackunit_basic :
      [ports s1; ports bad2; ports (do_call TW W 0 (c_get 34 1234) bad2);
       ports (do_call TW W 0 (c_get 34 1234) s1)]
      = [T; V 0; V 0; V 1337].
    Proof. vm_compute. reflexivity. Qed.

    Example init_is_s0 : same_state initial s0 && pair_eqb (ports initial) (0, 0)%N = true.
    Proof. vm_compute. reflexivity. Qed.

    Definition st1 : sysst TW W := mk TW W (KR true 0x8001 S1 P1, row_empty) 0 0.
    Example full_width_compare :
      map (fun '(t, g) => ports (do_call TW W 0 (c_get t g) st1))
        [(0x8001, P1); (0x8001, N.lxor P1 HI); (0x8001, N.lxor P1 1); (0x0001, P1); (0x8000, P1)]%N
      = [V S1; V 0; V 0; V 0; V 0].
    Proof. vm_compute. reflexivity. Qed.

    Example get_ignores_in_secret :
      map (fun '(t, g) => run TW W act_get t 0 g st1) [(0x8001, P1); (0x8001, 0); (5, P1)]%N
      = map (fun '(t, g) => run TW W act_get t ALL g st1) [(0x8001, P1); (0x8001, 0); (5, P1)]%N.
    Proof. vm_compute. reflexivity. Qed.

    Definition wipe (st: sysst TW W) : sysst TW W := (fst st, snd initial).
    Definition full_st : sysst TW W := mk TW W (KR true 1 S1 P1, KR true 2 S2 P2) 1 ALL.
    Definition prev : list (sysst TW W) :=
      [do_call TW W 0 (c_get 1 P1) full_st; full_st; s1; bad2; initial].
    Definition next : list (sysst TW W -> sysst TW W) :=
      [do_call TW W 0 (c_store 3 S3 P3); do_call TW W 0 (c_store 1 S3 P3);
       do_call TW W 0 (c_get 2 P2); do_call TW W 0 (c_get 2 0); do_call TW W 0 (c_get 9 0)].
    Example no_stale_outputs :
      map (fun st => map (fun f => ports (f st)) next) prev
      = map (fun st => map (fun f => ports (f (wipe st))) next) prev.
    Proof. vm_compute. reflexivity. Qed.

    Definition is_empty (r: krow) : bool :=
      negb (kv r) && N.eqb (kt r) 0 && N.eqb (ks r) 0 && N.eqb (kp r) 0.
    Definition knox_R (s: kstate) : bool :=
      let '(a, b) := s in
      negb (kv a && kv b && N.eqb (kt a) (kt b))
      && (kv a || is_empty a) && (kv b || is_empty b).

    Definition check_clear (tw w: nat) : bool :=
      forallb (fun s => forallb (fun t => forallb (fun g =>
        let r1 := do_call tw w 1 (c_get t g) (mk tw w s 1 1) in
        let r2 := do_call tw w 1 (c_get t 0) r1 in
        let '(e1, s1') := knox_step (c_get t g) s in
        let '(e2, s2') := knox_step (c_get t 0) s1' in
        pair_eqb (ports r1) (enc e1) && same_state r1 s1'
        && pair_eqb (ports r2) (0, 0)%N && same_state r2 s1'
        && pair_eqb (enc e2) (0, 0)%N && state_eqb s2' s1')
        (nums (2 ^ w))) (nums (2 ^ tw))) (filter knox_R (states tw w)).

    Example R_states_count : length (filter knox_R (states 2 1)) = 225.
    Proof. vm_compute. reflexivity. Qed.
    Example host_clear_tw2_w1 : check_clear 2 1 = true.
    Proof. vm_compute. reflexivity. Qed.

    Example host_clear :
      fst (tf_session 0 [c_store 7 S1 P1; c_get 7 P1; c_get 7 0] initial) = [T; V S1; V 0].
    Proof. vm_compute. reflexivity. Qed.

    Example clear_outside_R :
      let '(_, s1') := knox_step (c_get 1 P2) dup in
      let '(_, s2') := knox_step (c_get 1 0) s1' in
      state_eqb s2' s1' = false.
    Proof. vm_compute. reflexivity. Qed.

    Definition knox_leak (s: kstate) : bool * N * bool * N :=
      let '(a, b) := s in
      (kv a, (if kv a then kt a else 0%N), kv b, (if kv b then kt b else 0%N)).

    Definition after (cs: list kcall) : kstate := snd (knox_session cs s0).

    Definition LA : kstate := after [c_store 1 S1 P1; c_store 2 S2 P2; c_get 1 0].
    Definition LB : kstate := after [c_store 2 S2 P2].

    Definition followups : list (list kcall) :=
      [ [c_store 2 S3 P3; c_get 2 P3];
        [c_store 5 S1 P1; c_store 6 S3 P3; c_get 5 P1; c_get 6 0];
        [c_get 2 P2; c_get 2 P2];
        [c_get 2 0; c_store 2 S1 P1; c_get 2 P1];
        [c_get 9 P2; c_store 9 S1 P1; c_store 8 S3 P3] ].

    Definition tf_outs (cs: list kcall) (s: kstate) : list (N * N) :=
      fst (tf_session 1 cs (mk TW W s 0 0)).

    Example leak_layouts :
      (knox_leak LA, knox_leak LB,
       forallb (fun cs => knox_R LA && knox_R LB && agree 1 cs LA 0 0 && agree 1 cs LB 0 0) followups,
       map (fun cs => tf_outs cs LA) followups, map (fun cs => tf_outs cs LB) followups)
      = ((false, 0, true, 2), (true, 2, false, 0), true,
         [[T; V S3]; [T; F; V S1; V 0]; [V S2; V 0]; [V 0; T; V S1]; [V 0; T; F]],
         [[T; V S3]; [T; F; V S1; V 0]; [V S2; V 0]; [V 0; T; V S1]; [V 0; T; F]])%N.
    Proof. vm_compute. reflexivity. Qed.

End Checks.

Section Instance.

    Definition tfs_ctx : TFSchedContext := {|
        tfs_spec_states := fs_states;
        tfs_spec_states_fin := _;
        tfs_spec_states_size := fs_states_size TW W;
        tfs_spec_states_init := fs_states_init;

        tfs_spec_inputs := fs_inputs;
        tfs_spec_inputs_fin := _;
        tfs_spec_inputs_size := fs_inputs_size TW W;
        tfs_spec_inputs_class := fun _ => Public;
        tfs_spec_outputs := fs_outputs;
        tfs_spec_outputs_fin := _;
        tfs_spec_outputs_size := fs_outputs_size W;
        tfs_spec_outputs_class := fun _ => Public;
        tfs_spec_action := fs_action;
        tfs_spec_action_fin := _;
        tfs_spec_action_ops := fs_ops TW W;
        tfs_spec_ips := Empty_set;
        tfs_spec_ip := no_ips;
        tfs_spec_decls := []
    |}.

    Definition CL := 10.

    Definition tf_ctx : TFSynthContext := mk_synth_ctx (tfs_schedule tfs_ctx CL).

    Example cmd_codes :
      tf_action_reg_size tf_ctx = 2
      /\ map (fun a => Bits.to_nat (tf_action_encoding tf_ctx a)) [act_store; act_get] = [0; 1].
    Proof. vm_compute. split; reflexivity. Qed.

    Example sf_both_false :
      (Definitions.sf_action tfs_ctx act_store, Definitions.sf_action tfs_ctx act_get) = (false, false).
    Proof. vm_compute. reflexivity. Qed.

    Definition ipr_here := IPR.emulator_correct tfs_ctx CL.
    Definition sched_here := SchedulerSimulation.variable_scheduler_correct tfs_ctx CL.
    Definition synth_here := Synthesis.synthesis_correct tf_ctx.
    Definition init_here := Synthesis.initial_state_matches tf_ctx.

    Definition package := Lowering.package tf_ctx "Knox_MultiLockbox".

End Instance.

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Knox_MultiLockbox.ml" prog.
