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

Require Import Coq.Lists.List.
Import ListNotations.

(* Knox's three-element FIFO (knox-hsm fifo). *)

Section FunctionalSpecification.

    Definition W := 32.
    Definition CNT_SZ := 2.

    Inductive slot := S0 | S1 | S2.

    Inductive fs_action := act_full | act_empty | act_push | act_peek | act_pop.

    Inductive fs_states := st_cnt | st_slot (k: slot).
    Inductive fs_inputs := in_v.
    Inductive fs_outputs := out_full | out_empty | out_peek_valid | out_peek_data.

    Definition fs_states_size (w: nat) (x: fs_states) : nat :=
      match x with st_cnt => CNT_SZ | st_slot _ => w end.
    Definition fs_inputs_size (w: nat) (_: fs_inputs) : nat := w.
    Definition fs_outputs_size (w: nat) (x: fs_outputs) : nat :=
      match x with out_peek_data => w | _ => 1 end.

    Definition fs_states_init (x: fs_states) : tf_states_type (fs_states_size W) x :=
      Bits.zero.

    Local Notation E := (@tf_expr fs_states fs_inputs fs_outputs).
    Local Notation OPS := (@tf_ops fs_states fs_inputs fs_outputs Empty_set).

    Definition shifted (k: slot) : E :=
      match k with
      | S0 => tf_svar (st_slot S1)
      | S1 => tf_svar (st_slot S2)
      | S2 => tf_const 0
      end.

    Definition fs_ops (a: fs_action) : OPS :=
      match a with
      | act_full =>
          {[ `mk_clear_outputs`;
             let $out_full := ($st_cnt ==[CNT_SZ] #3) ]}
      | act_empty =>
          {[ `mk_clear_outputs`;
             let $out_empty := ($st_cnt ==[CNT_SZ] #0) ]}
      | act_push =>
          {[ `mk_clear_outputs`;
             `mk_switch CNT_SZ (tf_svar st_cnt)
                (fun k => {[ let $(st_slot k) := $in_v;
                             let $st_cnt := $st_cnt + #1 ]})
                {[ pass ]}` ]}
      | act_peek =>
          {[ `mk_clear_outputs`;
             let $out_peek_valid := ($st_cnt !=[CNT_SZ] #0);
             let $out_peek_data := (if ($st_cnt ==[CNT_SZ] #0) then #0 else $(st_slot S0)) ]}
      | act_pop =>
          {[ `mk_clear_outputs`;
             if ($st_cnt !=[CNT_SZ] #0) then
               (`mk_forall (fun k => {[ let $(st_slot k) := `shifted k` ]})`;
                let $st_cnt := $st_cnt - #1)
             else pass ]}
      end.

End FunctionalSpecification.

Section Checks.

    Local Notation OPS := (@tf_ops fs_states fs_inputs fs_outputs Empty_set).

    Definition native_push : OPS := {[
      `mk_clear_outputs`;
      if ($st_cnt ==[CNT_SZ] #0) then
        (let $(st_slot S0) := $in_v; let $st_cnt := $st_cnt + #1)
      else if ($st_cnt ==[CNT_SZ] #1) then
        (let $(st_slot S1) := $in_v; let $st_cnt := $st_cnt + #1)
      else if ($st_cnt ==[CNT_SZ] #2) then
        (let $(st_slot S2) := $in_v; let $st_cnt := $st_cnt + #1)
      else pass ]}.
    Example push_unfolds : fs_ops act_push = native_push.
    Proof. reflexivity. Qed.

    Definition native_pop : OPS := {[
      `mk_clear_outputs`;
      if ($st_cnt !=[CNT_SZ] #0) then
        ((let $(st_slot S0) := $(st_slot S1);
          let $(st_slot S1) := $(st_slot S2);
          let $(st_slot S2) := #0);
         let $st_cnt := $st_cnt - #1)
      else pass ]}.
    Example pop_unfolds : fs_ops act_pop = native_pop.
    Proof. reflexivity. Qed.

    Definition sysst (w: nat) :=
      (ContextEnv.(env_t) (tf_states_type (fs_states_size w))
       * ContextEnv.(env_t) (tf_outputs_type (fs_outputs_size w)))%type.

    Definition ports4 := (N * N * N * N)%type.

    Definition mk (w: nat) (c d0 d1 d2: N) (o: ports4) : sysst w :=
      let '(f, e, pv, pd) := o in
      (ContextEnv.(create) (fun x => match x return tf_states_type (fs_states_size w) x with
                                     | st_cnt => Bits.of_N CNT_SZ c
                                     | st_slot S0 => Bits.of_N w d0
                                     | st_slot S1 => Bits.of_N w d1
                                     | st_slot S2 => Bits.of_N w d2
                                     end),
       ContextEnv.(create) (fun x => match x return tf_outputs_type (fs_outputs_size w) x with
                                     | out_full => Bits.of_N 1 f
                                     | out_empty => Bits.of_N 1 e
                                     | out_peek_valid => Bits.of_N 1 pv
                                     | out_peek_data => Bits.of_N w pd
                                     end)).

    Definition rep (w: nat) (q: list N) (o: ports4) : sysst w :=
      mk w (N.of_nat (length q)) (nth 0 q 0%N) (nth 1 q 0%N) (nth 2 q 0%N) o.
    Definition rep_garbage (w: nat) (g: N) (q: list N) (o: ports4) : sysst w :=
      mk w (N.of_nat (length q)) (nth 0 q g) (nth 1 q g) (nth 2 q g) o.

    Definition inp (w: nat) (x: N) (i: fs_inputs) : bits_t (fs_inputs_size w i) :=
      match i with in_v => Bits.of_N w x end.

    Definition run (w: nat) (a: fs_action) (x: N) (st: sysst w) : sysst w :=
      tf_ops_run (fs_states_size w) (fs_inputs_size w) (fs_outputs_size w) no_ips
                 (fs_ops a) st (inp w x).
    Definition op32 (a: fs_action) (x: N) : sysst W -> sysst W := run W a x.

    Definition gs {w} (st: sysst w) k : N := Bits.to_N (ContextEnv.(getenv) (fst st) k).
    Definition go {w} (st: sysst w) k : N := Bits.to_N (ContextEnv.(getenv) (snd st) k).

    Definition ports {w} (st: sysst w) : ports4 :=
      (go st out_full, go st out_empty, go st out_peek_valid, go st out_peek_data).
    Definition regs {w} (st: sysst w) : list N :=
      [gs st st_cnt; gs st (st_slot S0); gs st (st_slot S1); gs st (st_slot S2)].
    Definition abs {w} (st: sysst w) : list N :=
      firstn (N.to_nat (gs st st_cnt)) [gs st (st_slot S0); gs st (st_slot S1); gs st (st_slot S2)].

    Definition CAPACITY := 3.

    Inductive kret := r_full (b: bool) | r_empty (b: bool) | r_void | r_peek (o: option N).

    Definition knox_step (a: fs_action) (v: N) (q: list N) : kret * list N :=
      match a with
      | act_full  => (r_full (Nat.eqb (length q) CAPACITY), q)
      | act_empty => (r_empty (match q with [] => true | _ => false end), q)
      | act_push  => (r_void, if Nat.eqb (length q) CAPACITY then q else q ++ [v])
      | act_peek  => (r_peek (match q with [] => None | x :: _ => Some x end), q)
      | act_pop   => (r_void, match q with [] => q | _ :: r => r end)
      end.

    Definition b2n (b: bool) : N := if b then 1%N else 0%N.
    Definition enc (r: kret) : ports4 :=
      match r with
      | r_full b => (b2n b, 0, 0, 0)
      | r_empty b => (0, b2n b, 0, 0)
      | r_void => (0, 0, 0, 0)
      | r_peek None => (0, 0, 0, 0)
      | r_peek (Some d) => (0, 0, 1, d)
      end%N.

    Definition p4_eqb (p q: ports4) : bool :=
      let '(a, b, c, d) := p in let '(a', b', c', d') := q in
      N.eqb a a' && N.eqb b b' && N.eqb c c' && N.eqb d d'.
    Fixpoint leqb (a b: list N) : bool :=
      match a, b with
      | [], [] => true
      | x :: a', y :: b' => N.eqb x y && leqb a' b'
      | _, _ => false
      end.

    Definition acts : list fs_action := [act_full; act_empty; act_push; act_peek; act_pop].

    Fixpoint queues (n: nat) (D: list N) : list (list N) :=
      match n with
      | 0 => [[]]
      | S n' => [] :: flat_map (fun x => map (cons x) (queues n' D)) D
      end.

    Definition check_canon (w: nat) (D: list N) (stale: list ports4) : bool :=
      forallb (fun q => forallb (fun a => forallb (fun v => forallb (fun o =>
        let '(r, q') := knox_step a v q in
        let st := run w a v (rep w q o) in
        leqb (regs st) (regs (rep w q' (enc r))) && p4_eqb (ports st) (enc r)) stale) D) acts)
        (queues CAPACITY D).

    Definition check_garbage (w: nat) (D: list N) (g: N) (stale: list ports4) : bool :=
      forallb (fun q => forallb (fun a => forallb (fun v => forallb (fun o =>
        let '(r, q') := knox_step a v q in
        let st := run w a v (rep_garbage w g q o) in
        leqb (abs st) q' && p4_eqb (ports st) (enc r)) stale) D) acts) (queues CAPACITY D).

    Definition D2 : list N := [0; 1; 2; 3]%N.
    Definition stale2 : list ports4 := [(0, 0, 0, 0); (1, 1, 1, 2)]%N.

    Example queues_count : length (queues CAPACITY D2) = 85.
    Proof. reflexivity. Qed.
    Example exhaustive_canon_w2 : check_canon 2 D2 stale2 = true.
    Proof. vm_compute. reflexivity. Qed.
    Example exhaustive_garbage_w2 :
      forallb (fun g => check_garbage 2 D2 g stale2) D2 = true.
    Proof. vm_compute. reflexivity. Qed.

    Definition MAX : N := 4294967295.
    Definition HALF : N := 2147483648.
    Definition DEAD : N := 3735928559.
    Definition D32 : list N := [0; 1; HALF; MAX]%N.
    Definition stale32 : list ports4 := [(0, 0, 0, 0); (1, 1, 1, DEAD)]%N.

    Example boundary_canon_w32 : check_canon W D32 stale32 = true.
    Proof. vm_compute. reflexivity. Qed.
    Example boundary_garbage_w32 : check_garbage W D32 DEAD stale32 = true.
    Proof. vm_compute. reflexivity. Qed.

    Definition initial : sysst W :=
      (ContextEnv.(create) fs_states_init, ContextEnv.(create) (fun _ => Bits.zero)).

    Example init_is_s0 : (regs initial, ports initial) = ([0; 0; 0; 0], (0, 0, 0, 0))%N.
    Proof. vm_compute. reflexivity. Qed.

    Fixpoint tf_session (cs: list (fs_action * N)) (st: sysst W) : list ports4 * list N :=
      match cs with
      | [] => ([], abs st)
      | (a, x) :: cs' => let st' := op32 a x st in
                         let '(os, fin) := tf_session cs' st' in (ports st' :: os, fin)
      end.

    Fixpoint knox_session (cs: list (fs_action * N)) (q: list N) : list ports4 * list N :=
      match cs with
      | [] => ([], q)
      | (a, x) :: cs' => let '(r, q') := knox_step a x q in
                         let '(os, fin) := knox_session cs' q' in (enc r :: os, fin)
      end.

    Definition agree (cs: list (fs_action * N)) (st: sysst W) : bool :=
      let '(o1, f1) := tf_session cs st in
      let '(o2, f2) := knox_session cs (abs st) in
      forallb (fun '(a, b) => p4_eqb a b) (combine o1 o2)
      && Nat.eqb (length o1) (length o2) && leqb f1 f2.

    Example reset_queries :
      map (fun a => ports (op32 a 0 initial)) [act_empty; act_full; act_peek]
      = [(0, 1, 0, 0); (0, 0, 0, 0); (0, 0, 0, 0)]%N.
    Proof. vm_compute. reflexivity. Qed.

    Example peek_zero_is_valid : ports (op32 act_peek 0 (op32 act_push 0 initial)) = (0, 0, 1, 0)%N.
    Proof. vm_compute. reflexivity. Qed.

    Definition fill : list (fs_action * N) :=
      [(act_push, 1); (act_push, 2); (act_push, 3); (act_full, 0); (act_push, 4);
       (act_peek, 0); (act_pop, 0); (act_peek, 0); (act_pop, 0); (act_pop, 0);
       (act_peek, 0); (act_pop, 0); (act_empty, 0)]%N.
    Example session_fill :
      tf_session fill initial =
      ([(0, 0, 0, 0); (0, 0, 0, 0); (0, 0, 0, 0); (1, 0, 0, 0); (0, 0, 0, 0);
        (0, 0, 1, 1); (0, 0, 0, 0); (0, 0, 1, 2); (0, 0, 0, 0); (0, 0, 0, 0);
        (0, 0, 0, 0); (0, 0, 0, 0); (0, 1, 0, 0)], [])%N.
    Proof. vm_compute. reflexivity. Qed.
    Example fill_drops_fourth : abs (fold_left (fun st '(a, x) => op32 a x st) (firstn 5 fill) initial)
                                = [1; 2; 3]%N.
    Proof. vm_compute. reflexivity. Qed.
    Example drained_is_s0 : regs (fold_left (fun st '(a, x) => op32 a x st) fill initial) = [0; 0; 0; 0]%N.
    Proof. vm_compute. reflexivity. Qed.

    Definition A : N := 2882400001.
    Definition B : N := 305419896.
    Example refill_order :
      let st := fold_left (fun st '(a, x) => op32 a x st)
                  [(act_push, A); (act_push, B); (act_push, MAX); (act_pop, 0); (act_push, HALF)]%N initial in
      (abs st, ports (op32 act_peek 0 st), ports (op32 act_full 0 st),
       ports (op32 act_peek 0 (op32 act_pop 0 (op32 act_pop 0 st))))
      = ([B; MAX; HALF], (0, 0, 1, B), (1, 0, 0, 0), (0, 0, 1, HALF))%N.
    Proof. vm_compute. reflexivity. Qed.

    Example dropped_push_keeps_order :
      let st := fold_left (fun st '(a, x) => op32 a x st)
                  [(act_push, A); (act_push, B); (act_push, MAX); (act_push, HALF);
                   (act_pop, 0); (act_pop, 0)]%N initial in
      (abs st, ports (op32 act_peek 0 st)) = ([MAX], (0, 0, 1, MAX))%N.
    Proof. vm_compute. reflexivity. Qed.

    Definition sessions : list (list (fs_action * N)) :=
      [ fill;
        [(act_push, A); (act_push, B); (act_push, MAX); (act_pop, 0); (act_push, HALF);
         (act_peek, 0); (act_full, 0); (act_pop, 0); (act_pop, 0); (act_peek, 0)];
        [(act_peek, 0); (act_pop, 0); (act_empty, 0); (act_push, 0); (act_peek, 0);
         (act_empty, 0); (act_full, 0); (act_push, DEAD); (act_push, 0); (act_full, 0);
         (act_push, 7); (act_peek, 0); (act_pop, 0); (act_peek, 0); (act_pop, 0); (act_peek, 0)];
        [(act_push, 1); (act_pop, 0); (act_push, 2); (act_push, 3); (act_pop, 0);
         (act_push, 4); (act_push, 5); (act_full, 0); (act_peek, 0); (act_pop, 0);
         (act_peek, 0); (act_pop, 0); (act_peek, 0); (act_pop, 0); (act_empty, 0)] ]%N.

    Example sessions_agree_from_reset : forallb (fun cs => agree cs initial) sessions = true.
    Proof. vm_compute. reflexivity. Qed.

    Example sessions_agree_any_state :
      forallb (fun st => forallb (fun cs => agree cs st) sessions)
        [rep W [DEAD] (1, 1, 1, MAX); rep W [MAX; 0] (0, 0, 1, 7);
         rep W [1; HALF; MAX] (0, 1, 0, 0); rep_garbage W DEAD [] (0, 0, 1, DEAD);
         rep_garbage W MAX [A; B] (1, 0, 0, 0)]%N = true.
    Proof. vm_compute. reflexivity. Qed.

    Example peek_empty_garbage :
      ports (op32 act_peek 0 (mk W 0 DEAD DEAD DEAD (0, 0, 0, 0)%N)) = (0, 0, 0, 0)%N.
    Proof. vm_compute. reflexivity. Qed.

    Definition wipe (st: sysst W) : sysst W := (fst st, snd initial).
    Definition prev : list (sysst W) :=
      [op32 act_peek 0 (rep W [DEAD] (0, 0, 0, 0)); op32 act_full 0 (rep W [1; 2; 3] (0, 0, 0, 0));
       op32 act_empty 0 initial; rep W [HALF; MAX] (1, 1, 1, MAX)]%N.
    Definition next : list (sysst W -> sysst W) :=
      [op32 act_full 0; op32 act_empty 0; op32 act_push MAX; op32 act_peek 0; op32 act_pop 0].
    Example no_stale_outputs :
      map (fun st => map (fun f => ports (f st)) next) prev
      = map (fun st => map (fun f => ports (f (wipe st))) next) prev.
    Proof. vm_compute. reflexivity. Qed.

    Example pop_clears_peek_port :
      let st := op32 act_peek 0 (rep W [DEAD] (0, 0, 0, 0)%N) in
      (ports st, ports (op32 act_pop 0 st)) = ((0, 0, 1, DEAD), (0, 0, 0, 0))%N.
    Proof. vm_compute. reflexivity. Qed.

    Example in_v_ignored :
      forallb (fun st => forallb (fun a =>
        leqb (regs (op32 a 0 st)) (regs (op32 a MAX st))
        && p4_eqb (ports (op32 a 0 st)) (ports (op32 a MAX st)))
        [act_full; act_empty; act_peek; act_pop])
        [initial; rep W [DEAD] (0, 0, 0, 0); rep W [1; 2; 3] (0, 0, 0, 0)]%N = true.
    Proof. vm_compute. reflexivity. Qed.

    Example host_clear_w2 :
      forallb (fun q => forallb (fun x =>
        let st := run 2 act_peek 0 (rep 2 q (0, 0, 0, 0)%N) in
        let s1 := run 2 act_empty x st in
        let s2 := run 2 act_full x st in
        N.eqb (go s1 out_peek_data) 0 && N.eqb (go s1 out_peek_valid) 0
        && N.eqb (go s2 out_peek_data) 0 && N.eqb (go s2 out_peek_valid) 0
        && leqb (regs s1) (regs st) && leqb (regs s2) (regs st)) D2) (queues CAPACITY D2) = true.
    Proof. vm_compute. reflexivity. Qed.

    Example host_clear_w32 :
      let st := op32 act_peek 0 (rep W [DEAD; A] (0, 0, 0, 0)%N) in
      (ports st, ports (op32 act_empty 0 st), abs (op32 act_empty 0 st))
      = ((0, 0, 1, DEAD), (0, 0, 0, 0), [DEAD; A])%N.
    Proof. vm_compute. reflexivity. Qed.

End Checks.

Section Instance.

    Definition tfs_ctx : TFSchedContext := {|
        tfs_spec_states := fs_states;
        tfs_spec_states_fin := _;
        tfs_spec_states_size := fs_states_size W;
        tfs_spec_states_init := fs_states_init;

        tfs_spec_inputs := fs_inputs;
        tfs_spec_inputs_fin := _;
        tfs_spec_inputs_size := fs_inputs_size W;
        tfs_spec_inputs_class := fun _ => Public;
        tfs_spec_outputs := fs_outputs;
        tfs_spec_outputs_fin := _;
        tfs_spec_outputs_size := fs_outputs_size W;
        tfs_spec_outputs_class := fun _ => Public;
        tfs_spec_action := fs_action;
        tfs_spec_action_fin := _;
        tfs_spec_action_ops := fs_ops;
        tfs_spec_ips := Empty_set;
        tfs_spec_ip := no_ips;
        tfs_spec_decls := []
    |}.

    Definition CL := 10.

    Definition tf_ctx : TFSynthContext := mk_synth_ctx (tfs_schedule tfs_ctx CL).

    Example cmd_width : tf_action_reg_size tf_ctx = 3.
    Proof. reflexivity. Qed.
    Example cmd_codes :
      map (fun a => Bits.to_nat (tf_action_encoding tf_ctx a)) acts = [0; 1; 2; 3; 4].
    Proof. vm_compute. reflexivity. Qed.

    Example sf_flags :
      map (Definitions.sf_action tfs_ctx) acts = [false; false; true; false; true].
    Proof. vm_compute. reflexivity. Qed.

    Definition ipr_here := IPR.ipr tfs_ctx CL _ _
      (tf_action_encoding_inj tf_ctx) (tf_action_names tf_ctx).

    Definition package := Lowering.package tf_ctx "Knox_Fifo".

End Instance.

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Knox_Fifo.ml" prog.
