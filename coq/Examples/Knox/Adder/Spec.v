Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Coq.NArith.NArith.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Backend.Lowering.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Macros.
Require Trustformer.Theorems.ConfidentialityDefinitions.
Require Trustformer.Theorems.IPR.

Require Import Coq.Lists.List.
Import ListNotations.

(* Knox's adder (knox-hsm adder); both operands arrive in one command. *)

Section FunctionalSpecification.

    Definition W := 32.

    Inductive fs_action := act_add.

    Definition fs_states := Empty_set.
    Inductive fs_inputs := in_x | in_y.
    Inductive fs_outputs := out_sum.

    Definition fs_states_size (w: nat) (x: fs_states) : nat := match x with end.
    Definition fs_inputs_size (w: nat) (_: fs_inputs) : nat := w.
    Definition fs_outputs_size (w: nat) (_: fs_outputs) : nat := w.

    Definition fs_states_init (w: nat) (x: fs_states) : tf_states_type (fs_states_size w) x :=
      match x with end.

    Local Notation OPS := (@tf_ops fs_states fs_inputs fs_outputs Empty_set).

    Definition fs_ops (w: nat) (a: fs_action) : OPS :=
      match a with
      | act_add =>
          {[ `mk_clear_outputs`;
             let $out_sum := $in_x + $in_y ]}
      end.

End FunctionalSpecification.

Section Checks.

    Definition sysst (w: nat) :=
      (ContextEnv.(env_t) (tf_states_type (fs_states_size w))
       * ContextEnv.(env_t) (tf_outputs_type (fs_outputs_size w)))%type.

    Definition mk (w: nat) (o: N) : sysst w :=
      (ContextEnv.(create) (fs_states_init w),
       ContextEnv.(create) (fun k => match k return tf_outputs_type (fs_outputs_size w) k with
                                     | out_sum => Bits.of_N w o end)).

    Definition initial : sysst W :=
      (ContextEnv.(create) (fs_states_init W), ContextEnv.(create) (fun _ => Bits.zero)).

    Definition inp (w: nat) (x y: N) : forall i : fs_inputs, bits_t (fs_inputs_size w i) :=
      fun i => match i return bits_t (fs_inputs_size w i) with
               | in_x => Bits.of_N w x
               | in_y => Bits.of_N w y
               end.

    Definition run (w: nat) (x y: N) (st: sysst w) : sysst w :=
      tf_ops_run (fs_states_size w) (fs_inputs_size w) (fs_outputs_size w) no_ips
                 (fs_ops w act_add) st (inp w x y).

    Definition add (x y: N) : sysst W -> sysst W := run W x y.

    Definition o_of {w} (st: sysst w) : N := Bits.to_N (ContextEnv.(getenv) (snd st) out_sum).

    Definition bvadd_ref (w: nat) (x y: N) : N := N.modulo (x + y) (2 ^ N.of_nat w).

    Definition check_all (w: nat) (stale: list N) : bool :=
      let vals := List.map N.of_nat (List.seq 0 (2 ^ w)) in
      forallb (fun x => forallb (fun y => forallb (fun o =>
          N.eqb (o_of (run w x y (mk w o))) (bvadd_ref w x y)) stale) vals) vals.
    Example exhaustive_w4 : check_all 4 [0; 5; 15]%N = true.
    Proof. vm_compute. reflexivity. Qed.
    Example exhaustive_w8 : check_all 8 [255]%N = true.
    Proof. vm_compute. reflexivity. Qed.

    Definition MAX := 4294967295%N.
    Definition HALF := 2147483648%N.
    Definition knox_vectors : list (N * N * N) :=
      [ (0, 0, 0); (7, 9, 16);
        (MAX, 1, 0); (1, MAX, 0);
        (MAX, MAX, MAX - 1);
        (HALF, HALF, 0); (HALF - 1, HALF, MAX);
        (3000000000, 1294967295, MAX); (3000000000, 1294967296, 0);
        (0xDEADBEEF, 0xCAFEBABE, 2846652845);
        (123456789, 987654321, 1111111110) ]%N.

    Example knox_vectors_32 :
      forallb (fun '(x, y, e) =>
         forallb (fun o => N.eqb (o_of (add x y (mk W o))) e && N.eqb (bvadd_ref W x y) e)
                 [0; 77; MAX]%N) knox_vectors = true.
    Proof. vm_compute. reflexivity. Qed.

    Example commutes :
      forallb (fun '(x, y, _) => N.eqb (o_of (add x y initial)) (o_of (add y x (mk W MAX))))
              knox_vectors = true.
    Proof. vm_compute. reflexivity. Qed.

    Example history_independent :
      o_of (add 5 6 (add MAX MAX (add HALF 3 initial))) = 11%N.
    Proof. vm_compute. reflexivity. Qed.

    Example fresh_port : o_of initial = 0%N.
    Proof. vm_compute. reflexivity. Qed.

    Example add_zero_is_reset :
      List.map (add 0 0) [initial; add 7 9 initial; add MAX MAX initial; mk W HALF]
      = [initial; initial; initial; initial].
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

    Example cmd_width : tf_action_reg_size tf_ctx = 1.
    Proof. reflexivity. Qed.
    Example cmd_codes :
      List.map (fun a => Bits.to_nat (tf_action_encoding tf_ctx a)) [act_add] = [0].
    Proof. vm_compute. reflexivity. Qed.

    Example sf_add : ConfidentialityDefinitions.sf_action tfs_ctx act_add = true.
    Proof. vm_compute. reflexivity. Qed.

    Definition ipr_here := IPR.ipr tfs_ctx CL _ _
      (tf_action_encoding_inj tf_ctx) (tf_action_names tf_ctx).

    Definition package := Lowering.package tf_ctx "Knox_Adder".

End Instance.

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Knox_Adder.ml" prog.
