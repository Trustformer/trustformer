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

(* Knox's one-element FIFO (knox-hsm fifo1). *)

Section FunctionalSpecification.

    Definition W := 32.

    Inductive fs_action := act_full | act_empty | act_push | act_pop.

    Inductive fs_states := st_valid | st_data.
    Inductive fs_inputs := in_v.
    Inductive fs_outputs := out_full | out_empty | out_pop_valid | out_pop_data.

    Definition fs_states_size (w: nat) (x: fs_states) : nat :=
      match x with st_valid => 1 | st_data => w end.
    Definition fs_inputs_size (w: nat) (_: fs_inputs) : nat := w.
    Definition fs_outputs_size (w: nat) (x: fs_outputs) : nat :=
      match x with out_pop_data => w | _ => 1 end.

    Definition fs_states_init (x: fs_states) : tf_states_type (fs_states_size W) x :=
      Bits.zero.

    Local Notation OPS := (@tf_ops fs_states fs_inputs fs_outputs Empty_set).

    Definition fs_ops (a: fs_action) : OPS :=
      match a with
      | act_full =>
          {[ `mk_clear_outputs`;
             let $out_full := ($st_valid ==[1] #1) ]}
      | act_empty =>
          {[ `mk_clear_outputs`;
             let $out_empty := ($st_valid ==[1] #0) ]}
      | act_push =>
          {[ `mk_clear_outputs`;
             if ($st_valid ==[1] #0) then
               (let $st_data := $in_v; let $st_valid := #1)
             else pass ]}
      | act_pop =>
          {[ `mk_clear_outputs`;
             let $out_pop_valid := ($st_valid ==[1] #1);
             let $out_pop_data := (if ($st_valid ==[1] #1) then $st_data else #0);
             let $st_valid := #0 ]}
      end.

End FunctionalSpecification.

Section Checks.

    Local Notation OPS := (@tf_ops fs_states fs_inputs fs_outputs Empty_set).

    Definition sysst (w: nat) :=
      (ContextEnv.(env_t) (tf_states_type (fs_states_size w))
       * ContextEnv.(env_t) (tf_outputs_type (fs_outputs_size w)))%type.

    Definition ports4 := (N * N * N * N)%type.

    Definition mk (w: nat) (vb d: N) (o: ports4) : sysst w :=
      let '(f, e, pv, pd) := o in
      (ContextEnv.(create) (fun x => match x return tf_states_type (fs_states_size w) x with
                                     | st_valid => Bits.of_N 1 vb
                                     | st_data => Bits.of_N w d
                                     end),
       ContextEnv.(create) (fun x => match x return tf_outputs_type (fs_outputs_size w) x with
                                     | out_full => Bits.of_N 1 f
                                     | out_empty => Bits.of_N 1 e
                                     | out_pop_valid => Bits.of_N 1 pv
                                     | out_pop_data => Bits.of_N w pd
                                     end)).

    Definition inp (w: nat) (x: N) (i: fs_inputs) : bits_t (fs_inputs_size w i) :=
      match i with in_v => Bits.of_N w x end.

    Definition run_with (ops: fs_action -> OPS) (w: nat) (a: fs_action) (x: N)
        (st: sysst w) : sysst w :=
      tf_ops_run (fs_states_size w) (fs_inputs_size w) (fs_outputs_size w) no_ips
                 (ops a) st (inp w x).
    Definition run (w: nat) := run_with fs_ops w.
    Definition op32 (a: fs_action) (x: N) : sysst W -> sysst W := run W a x.

    Definition valid_of {w} (st: sysst w) : N := Bits.to_N (ContextEnv.(getenv) (fst st) st_valid).
    Definition data_of {w} (st: sysst w) : N := Bits.to_N (ContextEnv.(getenv) (fst st) st_data).
    Definition ports {w} (st: sysst w) : ports4 :=
      (Bits.to_N (ContextEnv.(getenv) (snd st) out_full),
       Bits.to_N (ContextEnv.(getenv) (snd st) out_empty),
       Bits.to_N (ContextEnv.(getenv) (snd st) out_pop_valid),
       Bits.to_N (ContextEnv.(getenv) (snd st) out_pop_data)).

    Definition abs {w} (st: sysst w) : option N :=
      if N.eqb (valid_of st) 0 then None else Some (data_of st).

    Inductive kret := r_full (b: bool) | r_empty (b: bool) | r_void | r_pop (o: option N).

    Definition knox_step (a: fs_action) (v: N) (s: option N) : kret * option N :=
      match a with
      | act_full  => (r_full (match s with Some _ => true | None => false end), s)
      | act_empty => (r_empty (match s with Some _ => false | None => true end), s)
      | act_push  => (r_void, match s with Some _ => s | None => Some v end)
      | act_pop   => (r_pop s, None)
      end.

    Definition b2n (b: bool) : N := if b then 1%N else 0%N.
    Definition enc (r: kret) : ports4 :=
      match r with
      | r_full b => (b2n b, 0, 0, 0)
      | r_empty b => (0, b2n b, 0, 0)
      | r_void => (0, 0, 0, 0)
      | r_pop None => (0, 0, 0, 0)
      | r_pop (Some d) => (0, 0, 1, d)
      end%N.

    Definition p4_eqb (p q: ports4) : bool :=
      let '(a, b, c, d) := p in let '(a', b', c', d') := q in
      N.eqb a a' && N.eqb b b' && N.eqb c c' && N.eqb d d'.
    Definition opt_eqb (p q: option N) : bool :=
      match p, q with
      | None, None => true
      | Some a, Some b => N.eqb a b
      | _, _ => false
      end.

    Definition step_ok (ops: fs_action -> OPS) (w: nat) (a: fs_action) (x: N) (st: sysst w) : bool :=
      let '(r, s') := knox_step a x (abs st) in
      let st' := run_with ops w a x st in
      opt_eqb (abs st') s' && p4_eqb (ports st') (enc r).

    Definition acts : list fs_action := [act_full; act_empty; act_push; act_pop].

    Definition vals (w: nat) : list N := map N.of_nat (seq 0 (2 ^ w)).
    Definition stale (w: nat) : list ports4 := [(0, 0, 0, 0); (1, 1, 1, N.ones (N.of_nat w)); (0, 1, 1, 5)]%N.

    Definition check_all (ops: fs_action -> OPS) (w: nat) : bool :=
      forallb (fun vb => forallb (fun d => forallb (fun x => forallb (fun a => forallb (fun o =>
        step_ok ops w a x (mk w vb d o)) (stale w)) acts) (vals w)) (vals w)) [0; 1]%N.

    Example exhaustive_w4 : check_all fs_ops 4 = true.
    Proof. vm_compute. reflexivity. Qed.

    Definition nomask_ops (a: fs_action) : OPS :=
      match a with
      | act_pop =>
          {[ `mk_clear_outputs`;
             let $out_pop_valid := ($st_valid ==[1] #1);
             let $out_pop_data := $st_data;
             let $st_valid := #0 ]}
      | _ => fs_ops a
      end.
    Example mutant_rejected : check_all nomask_ops 4 = false.
    Proof. vm_compute. reflexivity. Qed.

    Definition MAX : N := 4294967295.
    Definition HALF : N := 2147483648.
    Definition DEAD : N := 3735928559.
    Definition vals32 : list N := [0; 1; HALF; DEAD; MAX]%N.

    Example boundary_w32 :
      forallb (fun vb => forallb (fun d => forallb (fun x => forallb (fun a => forallb (fun o =>
        step_ok fs_ops W a x (mk W vb d o)) [(0, 0, 0, 0); (1, 1, 1, MAX)]%N) acts) vals32) vals32)
        [0; 1]%N = true.
    Proof. vm_compute. reflexivity. Qed.

    Definition initial : sysst W :=
      (ContextEnv.(create) fs_states_init, ContextEnv.(create) (fun _ => Bits.zero)).

    Example init_is_s0 : (valid_of initial, data_of initial, ports initial) = (0, 0, (0, 0, 0, 0))%N.
    Proof. vm_compute. reflexivity. Qed.

    Fixpoint tf_session (ops: fs_action -> OPS) (cs: list (fs_action * N)) (st: sysst W)
      : list ports4 * option N :=
      match cs with
      | [] => ([], abs st)
      | (a, x) :: cs' => let st' := run_with ops W a x st in
                         let '(os, fin) := tf_session ops cs' st' in (ports st' :: os, fin)
      end.

    Fixpoint knox_session (cs: list (fs_action * N)) (s: option N) : list ports4 * option N :=
      match cs with
      | [] => ([], s)
      | (a, x) :: cs' => let '(r, s') := knox_step a x s in
                         let '(os, fin) := knox_session cs' s' in (enc r :: os, fin)
      end.

    Definition agree (cs: list (fs_action * N)) (st: sysst W) : bool :=
      let '(o1, f1) := tf_session fs_ops cs st in
      let '(o2, f2) := knox_session cs (abs st) in
      forallb (fun '(a, b) => p4_eqb a b) (combine o1 o2)
      && Nat.eqb (length o1) (length o2) && opt_eqb f1 f2.

    Definition demo : list (fs_action * N) :=
      [(act_empty, 0); (act_push, 0); (act_full, 0); (act_push, 7); (act_pop, 0);
       (act_pop, 0); (act_full, 0); (act_push, MAX); (act_pop, 0); (act_empty, 0)]%N.
    Example session_demo :
      fst (tf_session fs_ops demo initial) =
      [(0, 1, 0, 0); (0, 0, 0, 0); (1, 0, 0, 0); (0, 0, 0, 0); (0, 0, 1, 0);
       (0, 0, 0, 0); (0, 0, 0, 0); (0, 0, 0, 0); (0, 0, 1, MAX); (0, 1, 0, 0)]%N.
    Proof. vm_compute. reflexivity. Qed.

    Example push_on_full_keeps_old :
      fst (tf_session fs_ops [(act_push, 5); (act_push, 9); (act_pop, 0)]%N initial)
      = [(0, 0, 0, 0); (0, 0, 0, 0); (0, 0, 1, 5)]%N.
    Proof. vm_compute. reflexivity. Qed.

    Definition stale_pop : list (fs_action * N) := [(act_push, 42); (act_pop, 0); (act_pop, 0)]%N.
    Example pop_on_empty_masks :
      (fst (tf_session fs_ops stale_pop initial), data_of (op32 act_pop 0 (op32 act_pop 0 (op32 act_push 42 initial))))
      = ([(0, 0, 0, 0); (0, 0, 1, 42); (0, 0, 0, 0)], 42)%N.
    Proof. vm_compute. reflexivity. Qed.
    Example mutant_leaks :
      last (fst (tf_session nomask_ops stale_pop initial)) (0, 0, 0, 0)%N = (0, 0, 0, 42)%N.
    Proof. vm_compute. reflexivity. Qed.

    Definition sessions : list (list (fs_action * N)) :=
      [ demo;
        [(act_push, 5); (act_push, 9); (act_pop, 0)];
        stale_pop;
        [(act_pop, 0); (act_full, 0); (act_empty, 0); (act_push, DEAD); (act_full, 0);
         (act_empty, 0); (act_push, 0); (act_pop, 0); (act_push, HALF); (act_pop, 0); (act_pop, 0)];
        [(act_push, 1); (act_pop, 0); (act_push, 2); (act_pop, 0); (act_push, 3); (act_full, 0)] ]%N.

    Example sessions_agree_from_reset : forallb (fun cs => agree cs initial) sessions = true.
    Proof. vm_compute. reflexivity. Qed.

    Example sessions_agree_any_state :
      forallb (fun st => forallb (fun cs => agree cs st) sessions)
        [mk W 0 DEAD (1, 1, 1, MAX); mk W 1 0 (0, 0, 1, 7); mk W 1 MAX (0, 1, 0, 0);
         mk W 0 0 (0, 0, 1, DEAD)]%N = true.
    Proof. vm_compute. reflexivity. Qed.

    Definition wipe (st: sysst W) : sysst W := (fst st, snd initial).
    Definition prev : list (sysst W) :=
      [op32 act_pop 0 (op32 act_push DEAD initial); op32 act_full 0 (op32 act_push 1 initial);
       op32 act_empty 0 initial; mk W 0 HALF (1, 1, 1, MAX)]%N.
    Definition next : list (sysst W -> sysst W) :=
      [op32 act_full 0; op32 act_empty 0; op32 act_push MAX; op32 act_pop 0].
    Example no_stale_outputs :
      map (fun st => map (fun f => ports (f st)) next) prev
      = map (fun st => map (fun f => ports (f (wipe st))) next) prev.
    Proof. vm_compute. reflexivity. Qed.

    Example in_v_ignored :
      forallb (fun st => forallb (fun a =>
        let s1 := op32 a 0 st in let s2 := op32 a MAX st in
        p4_eqb (ports s1) (ports s2) && opt_eqb (abs s1) (abs s2)
        && N.eqb (data_of s1) (data_of s2))
        [act_full; act_empty; act_pop]) [initial; mk W 1 DEAD (0, 0, 0, 0)]%N = true.
    Proof. vm_compute. reflexivity. Qed.

    Example host_clear_w4 :
      forallb (fun d => forallb (fun x =>
        let st := run 4 act_pop 0 (run 4 act_push d (mk 4 0 0 (0, 0, 0, 0)%N)) in
        p4_eqb (ports st) (0, 0, 1, d)%N
        && p4_eqb (ports (run 4 act_full x st)) (0, 0, 0, 0)%N
        && p4_eqb (ports (run 4 act_empty x st)) (0, 1, 0, 0)%N) (vals 4)) (vals 4) = true.
    Proof. vm_compute. reflexivity. Qed.

    Definition C0FFEE42 : N := 3237997122.
    Example host_clear_w32 :
      let st := op32 act_pop 0 (op32 act_push C0FFEE42 initial) in
      (ports st, ports (op32 act_full 0 st), ports (op32 act_empty 0 st),
       abs (op32 act_empty 0 st), knox_step act_empty 0 None)
      = ((0, 0, 1, C0FFEE42), (0, 0, 0, 0), (0, 1, 0, 0), None, (r_empty true, None))%N.
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
      map (fun a => Bits.to_nat (tf_action_encoding tf_ctx a)) acts = [0; 1; 2; 3].
    Proof. vm_compute. reflexivity. Qed.

    Example sf_flags :
      map (Definitions.sf_action tfs_ctx) acts = [false; false; true; false].
    Proof. vm_compute. reflexivity. Qed.

    Definition ipr_here := IPR.circuit_emulated tfs_ctx CL _ _
      (tf_action_encoding_inj tf_ctx) (tf_action_names tf_ctx).

    Definition package := Lowering.package tf_ctx "Knox_Fifo1".

End Instance.

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Knox_Fifo1.ml" prog.
