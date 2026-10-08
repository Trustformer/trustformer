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

(* Knox's saturating counter (knox-hsm counter; counter-picorv32 has the same
   spec). *)

Section FunctionalSpecification.

    Definition W := 32.

    Inductive fs_action := act_add | act_get.

    Inductive fs_states := st_s.
    Inductive fs_inputs := in_x.
    Inductive fs_outputs := out_val.

    Definition fs_states_size (w: nat) (_: fs_states) : nat := w.
    Definition fs_inputs_size (w: nat) (_: fs_inputs) : nat := w.
    Definition fs_outputs_size (w: nat) (_: fs_outputs) : nat := w.

    Definition fs_states_init (w: nat) (x: fs_states) : tf_states_type (fs_states_size w) x :=
      Bits.zero.

    Local Notation OPS := (@tf_ops fs_states fs_inputs fs_outputs Empty_set).

    Definition sat_bound (w: nat) : @tf_expr fs_states fs_inputs fs_outputs :=
      mk_N (S w) (N.ones (N.of_nat w)).

    Definition fs_ops (w: nat) (a: fs_action) : OPS :=
      match a with
      | act_add =>
          {[ `mk_clear_outputs`;
             if ((`mk_zext w (S w) (tf_ivar in_x)` + `mk_zext w (S w) (tf_svar st_s)`)
                   <=[(S w)] `sat_bound w`) then
               let $st_s := $in_x + $st_s
             else
               let $st_s := ! #0 ]}
      | act_get =>
          {[ `mk_clear_outputs`;
             let $out_val := $st_s ]}
      end.

End FunctionalSpecification.

Section Checks.

    Definition sysst (w: nat) :=
      (ContextEnv.(env_t) (tf_states_type (fs_states_size w))
       * ContextEnv.(env_t) (tf_outputs_type (fs_outputs_size w)))%type.

    Definition mk (w: nat) (s o: N) : sysst w :=
      (ContextEnv.(create) (fun k => match k return tf_states_type (fs_states_size w) k with
                                     | st_s => Bits.of_N w s end),
       ContextEnv.(create) (fun k => match k return tf_outputs_type (fs_outputs_size w) k with
                                     | out_val => Bits.of_N w o end)).

    Definition initial : sysst W :=
      (ContextEnv.(create) (fs_states_init W), ContextEnv.(create) (fun _ => Bits.zero)).

    Definition inp (w: nat) (x: N) : forall i : fs_inputs, bits_t (fs_inputs_size w i) :=
      fun i => match i return bits_t (fs_inputs_size w i) with in_x => Bits.of_N w x end.

    Definition run_ops (w: nat) (ops: @tf_ops fs_states fs_inputs fs_outputs Empty_set)
               (x: N) (st: sysst w) : sysst w :=
      tf_ops_run (fs_states_size w) (fs_inputs_size w) (fs_outputs_size w) no_ips ops st (inp w x).

    Definition run (w: nat) (a: fs_action) (x: N) (st: sysst w) : sysst w :=
      run_ops w (fs_ops w a) x st.

    Definition add (x: N) : sysst W -> sysst W := run W act_add x.
    Definition get : sysst W -> sysst W := run W act_get 0xDEAD.

    Definition s_of {w} (st: sysst w) : N := Bits.to_N (ContextEnv.(getenv) (fst st) st_s).
    Definition o_of {w} (st: sysst w) : N := Bits.to_N (ContextEnv.(getenv) (snd st) out_val).

    Definition sat_ref (w: nat) (x s: N) : N := N.min (s + x) (N.ones (N.of_nat w)).

    Definition z1 : bits_t 1 := Bits.zero.
    Definition knox_spec (x s: bits_t 32) : bits_t 32 :=
      if Bits.unsigned_le (Bits.plus (Bits.app z1 x) (Bits.app z1 s)) (Bits.app z1 (Bits.ones 32))
      then Bits.plus x s else Bits.ones 32.
    Definition knox_impl (x s: bits_t 32) : bits_t 32 :=
      if Bits.unsigned_lt (Bits.plus s x) s then Bits.ones 32 else Bits.plus s x.

    Definition add_ops_carry (w: nat) : @tf_ops fs_states fs_inputs fs_outputs Empty_set :=
      {[ `mk_clear_outputs`;
         if (($in_x + $st_s) <[w] $st_s) then let $st_s := ! #0
         else let $st_s := $in_x + $st_s ]}.

    Definition check_all (w: nat) : bool :=
      let vals := List.map N.of_nat (List.seq 0 (2 ^ w)) in
      forallb (fun s => forallb (fun x => forallb (fun o =>
          let a := run w act_add x (mk w s o) in
          let c := run_ops w (add_ops_carry w) x (mk w s o) in
          let g := run w act_get x (mk w s o) in
          N.eqb (s_of a) (sat_ref w x s) && N.eqb (o_of a) 0
          && N.eqb (s_of a) (s_of c) && N.eqb (o_of a) (o_of c)
          && N.eqb (s_of g) s && N.eqb (o_of g) s) [0; 5]%N) vals) vals.
    Example exhaustive_w4 : check_all 4 = true.
    Proof. vm_compute. reflexivity. Qed.

    Definition MAX := 4294967295%N.
    Definition HALF := 2147483648%N.
    Definition cases32 : list (N * N) :=
      [ (0, 0); (0, 5); (7, 9); (MAX - 1, 1); (MAX - 1, 2); (MAX, 0); (MAX, 1); (MAX, MAX);
        (HALF, HALF); (HALF - 1, HALF); (HALF, HALF - 1); (1, MAX); (0, MAX);
        (MAX - 1000, 999); (MAX - 1000, 1000); (MAX - 1000, 1001);
        (123456789, 987654321); (3000000000, 1294967295); (3000000000, 1294967296) ]%N.
    Definition check32 : bool :=
      forallb (fun '(s, x) =>
        let a := add x (mk W s 77) in
        let g := get a in
        let bx := Bits.of_N 32 x in let bs := Bits.of_N 32 s in
        N.eqb (s_of a) (sat_ref W x s)
        && N.eqb (s_of a) (Bits.to_N (knox_spec bx bs))
        && N.eqb (s_of a) (Bits.to_N (knox_impl bx bs))
        && N.eqb (o_of a) 0 && N.eqb (o_of g) (s_of a) && N.eqb (s_of g) (s_of a)) cases32.
    Example boundary_32 : check32 = true.
    Proof. vm_compute. reflexivity. Qed.

    Example fresh_get : o_of (get initial) = 0%N.
    Proof. vm_compute. reflexivity. Qed.
    Example no_wrap : s_of (add HALF (mk W HALF 0)) = MAX.
    Proof. vm_compute. reflexivity. Qed.
    Example exact_boundary : s_of (add 1 (mk W (MAX - 1) 0)) = MAX.
    Proof. vm_compute. reflexivity. Qed.
    Example one_over_boundary : s_of (add 2 (mk W (MAX - 1) 0)) = MAX.
    Proof. vm_compute. reflexivity. Qed.
    Example sticky_max :
      List.map (fun x => s_of (add x (mk W MAX 0))) [0; 1; HALF; MAX]%N = [MAX; MAX; MAX; MAX].
    Proof. vm_compute. reflexivity. Qed.
    Example add_zero_noop :
      List.map (fun s => s_of (add 0 (mk W s 0))) [0; 1; HALF; MAX]%N = [0; 1; HALF; MAX]%N.
    Proof. vm_compute. reflexivity. Qed.
    Example get_ignores_input :
      List.map (fun x => run W act_get x (mk W 42 0)) [0; 12345; MAX]%N
      = [mk W 42 42; mk W 42 42; mk W 42 42].
    Proof. vm_compute. reflexivity. Qed.

    Definition session : list N :=
      let s1 := add 3000000000 initial in
      let g1 := get s1 in
      let s2 := add 1294967295 g1 in
      let g2 := get s2 in
      let s3 := add 2000000000 g2 in
      let g3 := get s3 in
      let s4 := add 0 g3 in
      let g4 := get s4 in
      List.map o_of [s1; g1; s2; g2; s3; g3; s4; g4].
    Example session_ports : session = [0; 3000000000; 0; MAX; 0; MAX; 0; MAX]%N.
    Proof. vm_compute. reflexivity. Qed.

    Example add_clears_port : o_of (add 1 (mk W 42 42)) = 0%N.
    Proof. vm_compute. reflexivity. Qed.
    Definition prev_states : list (sysst W) :=
      [get (mk W 42 0); get (mk W MAX 0); mk W 7 MAX; mk W HALF 1234; initial].
    Definition wipe (st: sysst W) : sysst W := (fst st, snd initial).
    Definition next_calls : list (sysst W -> sysst W) := [add 5; add MAX; get].
    Example no_stale_outputs :
      List.map (fun st => List.map (fun f => o_of (f st)) next_calls) prev_states
      = List.map (fun st => List.map (fun f => o_of (f (wipe st))) next_calls) prev_states.
    Proof. vm_compute. reflexivity. Qed.

    Example host_wipe :
      List.map (fun st => add 0 (get st)) [initial; mk W 42 0; mk W (MAX - 1) 7; mk W MAX 0]
      = List.map (fun st => wipe (get st)) [initial; mk W 42 0; mk W (MAX - 1) 7; mk W MAX 0].
    Proof. vm_compute. reflexivity. Qed.

End Checks.

Section Instance.

    Definition tfs_ctx : TFSchedContext := {|
        tfs_spec_states := fs_states;
        tfs_spec_states_fin := _;
        tfs_spec_states_size := fs_states_size W;
        tfs_spec_states_init := fs_states_init W;

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
      List.map (fun a => Bits.to_nat (tf_action_encoding tf_ctx a)) [act_add; act_get] = [0; 1].
    Proof. vm_compute. reflexivity. Qed.

    Example sf_add : Definitions.sf_action tfs_ctx act_add = true.
    Proof. vm_compute. reflexivity. Qed.
    Example sf_get : Definitions.sf_action tfs_ctx act_get = false.
    Proof. vm_compute. reflexivity. Qed.

    Definition ipr_here := IPR.emulator_correct tfs_ctx CL.
    Definition sched_here := SchedulerSimulation.variable_scheduler_correct tfs_ctx CL.
    Definition synth_here := Synthesis.synthesis_correct tf_ctx.
    Definition init_here := Synthesis.initial_state_matches tf_ctx.

    Definition package := Lowering.package tf_ctx "Knox_Counter".

End Instance.

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Knox_Counter.ml" prog.
