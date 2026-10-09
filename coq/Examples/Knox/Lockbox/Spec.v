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

(* Knox's lockbox (knox-hsm lockbox): get returns the secret for the right
   password and always empties the box. *)

Section FunctionalSpecification.

    Definition W := 128.

    Inductive fs_action := act_store | act_get.

    Inductive fs_states := st_secret | st_password.
    Inductive fs_inputs := in_secret | in_password.
    Inductive fs_outputs := out_ok | out_ret.

    Definition fs_states_size (w: nat) (_: fs_states) : nat := w.
    Definition fs_inputs_size (w: nat) (_: fs_inputs) : nat := w.
    Definition fs_outputs_size (w: nat) (x: fs_outputs) : nat :=
      match x with
      | out_ok => 1
      | out_ret => w
      end.

    Definition fs_states_init (x: fs_states) : tf_states_type (fs_states_size W) x :=
      Bits.zero.

    Local Notation OPS := (@tf_ops fs_states fs_inputs fs_outputs Empty_set).

    Definition fs_ops (w: nat) (a: fs_action) : OPS :=
      match a with
      | act_store =>
          {[ `mk_clear_outputs`;
             let $out_ok := #1;
             let $st_secret := $in_secret;
             let $st_password := $in_password ]}
      | act_get =>
          {[ `mk_clear_outputs`;
             let $out_ret := (if ($in_password ==[w] $st_password) then $st_secret else #0);
             let $st_secret := #0;
             let $st_password := #0 ]}
      end.

End FunctionalSpecification.

Section Checks.

    Definition sysst (w: nat) :=
      (ContextEnv.(env_t) (tf_states_type (fs_states_size w))
       * ContextEnv.(env_t) (tf_outputs_type (fs_outputs_size w)))%type.

    Definition mk (w: nat) (s p ok ret: N) : sysst w :=
      (ContextEnv.(create) (fun x => match x return tf_states_type (fs_states_size w) x with
                                     | st_secret => Bits.of_N w s
                                     | st_password => Bits.of_N w p
                                     end),
       ContextEnv.(create) (fun x => match x return tf_outputs_type (fs_outputs_size w) x with
                                     | out_ok => Bits.of_N 1 ok
                                     | out_ret => Bits.of_N w ret
                                     end)).

    Definition inp (w: nat) (x y: N) (i: fs_inputs) : bits_t (fs_inputs_size w i) :=
      match i with
      | in_secret => Bits.of_N w x
      | in_password => Bits.of_N w y
      end.

    Definition run (w: nat) (a: fs_action) (x y: N) (st: sysst w) : sysst w :=
      tf_ops_run (fs_states_size w) (fs_inputs_size w) (fs_outputs_size w) no_ips
                 (fs_ops w a) st (inp w x y).

    Definition sec_of {w} (st: sysst w) : N := Bits.to_N (ContextEnv.(getenv) (fst st) st_secret).
    Definition pw_of {w} (st: sysst w) : N := Bits.to_N (ContextEnv.(getenv) (fst st) st_password).
    Definition ok_of {w} (st: sysst w) : N := Bits.to_N (ContextEnv.(getenv) (snd st) out_ok).
    Definition ret_of {w} (st: sysst w) : N := Bits.to_N (ContextEnv.(getenv) (snd st) out_ret).
    Definition ports {w} (st: sysst w) : N * N := (ok_of st, ret_of st).
    Definition st_pair {w} (st: sysst w) : N * N := (sec_of st, pw_of st).

    Inductive kcall := c_store (secret password: N) | c_get (guess: N).
    Inductive kret := r_true | r_bv (v: N).

    Definition knox_step (c: kcall) (s: N * N) : kret * (N * N) :=
      match c with
      | c_store x y => (r_true, (x, y))
      | c_get g => (r_bv (if N.eqb g (snd s) then fst s else 0%N), (0%N, 0%N))
      end.

    Definition enc (r: kret) : N * N :=
      match r with
      | r_true => (1%N, 0%N)
      | r_bv v => (0%N, v)
      end.

    Definition pair_eqb (a b: N * N) : bool := N.eqb (fst a) (fst b) && N.eqb (snd a) (snd b).

    Definition vals (w: nat) : list N := map N.of_nat (seq 0 (2 ^ w)).
    Definition stale : list (N * N) := [(0, 0); (1, 0); (0, 7)]%N.
    Definition junk : list N := [0; 5; 7]%N.

    Definition check_get (w: nat) : bool :=
      forallb (fun s => forallb (fun p => forallb (fun g => forallb (fun '(ok, o) => forallb (fun j =>
        let r := run w act_get j g (mk w s p ok o) in
        let '(ret, st') := knox_step (c_get g) (s, p) in
        pair_eqb (ports r) (enc ret) && pair_eqb (st_pair r) st')
        junk) stale) (vals w)) (vals w)) (vals w).

    Definition check_store (w: nat) : bool :=
      forallb (fun s => forallb (fun p => forallb (fun x => forallb (fun y => forallb (fun '(ok, o) =>
        let r := run w act_store x y (mk w s p ok o) in
        let '(ret, st') := knox_step (c_store x y) (s, p) in
        pair_eqb (ports r) (enc ret) && pair_eqb (st_pair r) st')
        stale) (vals w)) (vals w)) (vals w)) (vals w).

    Definition check_clear (w: nat) : bool :=
      forallb (fun s => forallb (fun p => forallb (fun g => forallb (fun '(ok, o) =>
        let r1 := run w act_get 5 g (mk w s p ok o) in
        let r2 := run w act_get 7 0 r1 in
        let '(ret1, st1) := knox_step (c_get g) (s, p) in
        let '(ret2, st2) := knox_step (c_get 0) st1 in
        pair_eqb (ports r1) (enc ret1)
        && pair_eqb (ports r2) (0, 0)%N && pair_eqb (st_pair r2) (0, 0)%N
        && pair_eqb (enc ret2) (0, 0)%N && pair_eqb st2 st1 && pair_eqb st1 (0, 0)%N)
        stale) (vals w)) (vals w)) (vals w).

    Example exhaustive_get_w3 : check_get 3 = true.
    Proof. vm_compute. reflexivity. Qed.
    Example exhaustive_store_w3 : check_store 3 = true.
    Proof. vm_compute. reflexivity. Qed.
    Example exhaustive_clear_w3 : check_clear 3 = true.
    Proof. vm_compute. reflexivity. Qed.

    Definition ALL : N := N.ones 128.
    Definition HI : N := N.shiftl 1 127.
    Definition S1 : N := 0x0123456789abcdef_fedcba9876543210.
    Definition P1 : N := 0xa5a5a5a5c3c3c3c3_0f0f0f0f99999999.
    Definition S2 : N := 0xdeadbeefcafebabe_0000000000000001.
    Definition P2 : N := 0x00000000ffffffff.

    Definition initial : sysst W :=
      (ContextEnv.(create) fs_states_init, ContextEnv.(create) (fun _ => Bits.zero)).

    Definition store (x y: N) : sysst W -> sysst W := run W act_store x y.
    Definition get (g: N) : sysst W -> sysst W := run W act_get S2 g.

    Definition do_call (c: kcall) : sysst W -> sysst W :=
      match c with c_store x y => store x y | c_get g => get g end.

    Fixpoint tf_session (cs: list kcall) (st: sysst W) : list (N * N) * (N * N) :=
      match cs with
      | [] => ([], st_pair st)
      | c :: cs' => let st' := do_call c st in
                    let '(os, fin) := tf_session cs' st' in (ports st' :: os, fin)
      end.

    Fixpoint knox_session (cs: list kcall) (s: N * N) : list (N * N) * (N * N) :=
      match cs with
      | [] => ([], s)
      | c :: cs' => let '(r, s') := knox_step c s in
                    let '(os, fin) := knox_session cs' s' in (enc r :: os, fin)
      end.

    Definition agree (cs: list kcall) (st: sysst W) : bool :=
      let '(o1, f1) := tf_session cs st in
      let '(o2, f2) := knox_session cs (st_pair st) in
      forallb (fun '(a, b) => pair_eqb a b) (combine o1 o2)
      && Nat.eqb (length o1) (length o2) && pair_eqb f1 f2.

    Definition T : N * N := (1, 0)%N.
    Definition V (v: N) : N * N := (0%N, v).

    Definition sessions : list (list kcall) :=
      [
        [c_get 0; c_store S1 P1; c_get P1; c_get 0; c_get P1];
        [c_store S1 P1; c_get (N.lxor P1 HI); c_get P1];
        [c_store S1 P1; c_get (N.lxor P1 1); c_get P1];
        [c_store S1 P1; c_store S2 P2; c_get P1];
        [c_store S1 P1; c_store S2 P2; c_get P2; c_get P2];
        [c_store ALL ALL; c_get ALL; c_get ALL];
        [c_store 0 P1; c_get P1; c_get 0];
        [c_store S1 0; c_get 0; c_get 0];
        [c_store S1 P1; c_get P1; c_store S2 P2; c_get 0; c_store 0 0; c_get 0] ].

    Example session_values :
      map (fun cs => fst (tf_session cs initial)) sessions =
      [ [V 0; T; V S1; V 0; V 0];
        [T; V 0; V 0];
        [T; V 0; V 0];
        [T; T; V 0];
        [T; T; V S2; V 0];
        [T; V ALL; V 0];
        [T; V 0; V 0];
        [T; V S1; V 0];
        [T; V S1; T; V 0; T; V 0] ].
    Proof. vm_compute. reflexivity. Qed.

    Example sessions_agree_from_reset : forallb (fun cs => agree cs initial) sessions = true.
    Proof. vm_compute. reflexivity. Qed.

    Example sessions_agree_any_state :
      forallb (fun st => forallb (fun cs => agree cs st) sessions)
        [mk W 0 P1 0 S2; mk W S1 0 1 0; mk W S1 P1 0 S1; mk W ALL HI 0 ALL] = true.
    Proof. vm_compute. reflexivity. Qed.

    Example init_is_s0 : (st_pair initial, ports initial) = ((0, 0), (0, 0))%N.
    Proof. vm_compute. reflexivity. Qed.

    Definition s1 := store S1 P1 initial.
    Example store_ports_state : (ports s1, st_pair s1) = (T, (S1, P1)).
    Proof. vm_compute. reflexivity. Qed.
    Example full_width_compare :
      map (fun g => ports (get g s1)) [P1; N.lxor P1 HI; N.lxor P1 1; N.lxor P1 ALL; 0]%N
      = [V S1; V 0; V 0; V 0; V 0].
    Proof. vm_compute. reflexivity. Qed.

    Example get_always_wipes :
      map (fun g => st_pair (get g s1)) [P1; N.lxor P1 1; 0]%N = [(0, 0); (0, 0); (0, 0)]%N.
    Proof. vm_compute. reflexivity. Qed.

    Example get_ignores_in_secret :
      map (fun '(st, g) => run W act_get 0 g st) [(s1, P1); (s1, 0%N); (initial, 0%N)]
      = map (fun '(st, g) => run W act_get ALL g st) [(s1, P1); (s1, 0%N); (initial, 0%N)].
    Proof. vm_compute. reflexivity. Qed.

    Definition wipe (st: sysst W) : sysst W := (fst st, snd initial).
    Definition prev : list (sysst W) := [get P1 s1; get 0 s1; s1; initial; mk W S1 P1 1 ALL].
    Definition next : list (sysst W -> sysst W) := [store S2 P2; get P1; get 0; get ALL].
    Example no_stale_outputs :
      map (fun st => map (fun f => ports (f st)) next) prev
      = map (fun st => map (fun f => ports (f (wipe st))) next) prev.
    Proof. vm_compute. reflexivity. Qed.

    Example host_clear :
      let r := get P1 s1 in
      (ports r, ports (get 0 r), st_pair (get 0 r), knox_step (c_get 0) (0, 0)%N)
      = (V S1, V 0, (0, 0)%N, (r_bv 0, (0, 0)%N)).
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
        tfs_spec_action_ops := fs_ops W;
        tfs_spec_ips := Empty_set;
        tfs_spec_ip := no_ips;
        tfs_spec_decls := []
    |}.

    Definition CL := 10.

    Definition tf_ctx : TFSynthContext := mk_synth_ctx (tfs_schedule tfs_ctx CL).

    Example cmd_width : tf_action_reg_size tf_ctx = 2.
    Proof. reflexivity. Qed.
    Example cmd_codes :
      map (fun a => Bits.to_nat (tf_action_encoding tf_ctx a)) [act_store; act_get] = [0; 1].
    Proof. vm_compute. reflexivity. Qed.

    Example sf_store : Definitions.sf_action tfs_ctx act_store = true.
    Proof. vm_compute. reflexivity. Qed.
    Example sf_get : Definitions.sf_action tfs_ctx act_get = false.
    Proof. vm_compute. reflexivity. Qed.

    Definition ipr_here := IPR.ipr tfs_ctx CL _ _
      (tf_action_encoding_inj tf_ctx) (tf_action_names tf_ctx).

    Definition package := Lowering.package tf_ctx "Knox_Lockbox".

End Instance.

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Knox_Lockbox.ml" prog.
