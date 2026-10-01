(* ===================================================================== *)
(*  SPIKE: a branch on a call result, where the branch's calls are on a   *)
(*  DIFFERENT port from the call the condition reads.                    *)
(* ===================================================================== *)
(*
    [Regression_GuardCall] is the same program with every call on ONE port,
    and it passes: [last_sample] finds the first call's sample -- its guard is
    not disjoint from either arm's -- so both arms' drives are sequenced behind
    it and cannot fire until the answer is latched.

    Move the condition's call to another port and that ordering join is gone:
    [last_sample] searches the ARM's port, where nothing precedes.  A drive's
    compiled validity is its ARGUMENT's, not its guard's, so the arm's stall
    starts counting immediately, and the arm's drive gets its one pulse window
    while the condition's answer is still in flight and its latch still reads
    zero.
*)

Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.DFG.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.

Require Import Coq.Lists.List.
Import ListNotations.

Section XPortGuard.

  Definition xw := 256.
  Definition xlat := 3.
  Definition xclimit := 5.

  Inductive xp_action := act_x.
  Inductive xp_states := st_c | st_r.
  Inductive xp_inputs := in_msg.
  Definition xp_outputs := Empty_set.

  Definition xp_states_size  (_: xp_states)  : nat := xw.
  Definition xp_inputs_size  (_: xp_inputs)  : nat := xw.
  Definition xp_outputs_size (_: xp_outputs) : nat := xw.

  Definition xp_states_init (x: xp_states) : tf_states_type xp_states_size x :=
    match x with st_c => Bits.zero | st_r => Bits.zero end.

  Definition xp_f (v: bits_t xw) : bits_t xw := v.
  Definition xp_in_class  (_: xp_inputs)  : port_class := Public.
  Definition xp_out_class (_: xp_outputs) : port_class := Secret.

  (* TWO ports: the condition's call and the arms' calls do not share one. *)
  Inductive xp_ips := xp_cond | xp_arm.
  Definition xp_ip (_: xp_ips) : ip_decl :=
    {| ip_req_sz := xw; ip_resp_sz := xw; ip_lat := xlat;
       ip_lat_pos := ltac:(unfold xlat; lia); ip_fn := xp_f |}.

  (* st_c := cond(in_msg);
     if st_c = 0 then st_r := arm(7) else st_r := arm(9) *)
  Definition xp_ops : @tf_ops xp_states xp_inputs xp_outputs xp_ips :=
    tf_ops_cons
      (tf_ops_base (tf_call xp_cond st_c (tf_ivar in_msg)))
      (tf_ops_if (tf_op2 (tf_cmp xw tf_eq) (tf_svar st_c) (tf_const 0))
        (tf_ops_base (tf_call xp_arm st_r (tf_const 7)))
        (tf_ops_base (tf_call xp_arm st_r (tf_const 9)))).

  Definition xp_ctx : TFSchedContext := {|
      tfs_spec_states := xp_states;   tfs_spec_states_fin := _;
      tfs_spec_states_size := xp_states_size;
      tfs_spec_states_init := xp_states_init;
      tfs_spec_inputs := xp_inputs;   tfs_spec_inputs_fin := _;
      tfs_spec_inputs_size := xp_inputs_size;
      tfs_spec_inputs_class := xp_in_class;
      tfs_spec_outputs := xp_outputs; tfs_spec_outputs_fin := _;
      tfs_spec_outputs_size := xp_outputs_size;
      tfs_spec_outputs_class := xp_out_class;
      tfs_spec_action := xp_action;   tfs_spec_action_fin := _;
      tfs_spec_action_ops := fun _ => xp_ops;
      tfs_spec_ips := xp_ips;         tfs_spec_ips_fin := _;
      tfs_spec_ip := xp_ip;
      tfs_spec_decls := []
  |}.

  Definition xp_dfg := build_dfg xp_ctx act_x.

  (* one call on the condition's port, one per arm on the other *)
  Example xp_cond_one_drive :
    List.length (drive_nodes xp_ctx xp_dfg xp_cond) = 1.
  Proof. vm_compute. reflexivity. Qed.

  Example xp_arm_two_drives :
    List.length (drive_nodes xp_ctx xp_dfg xp_arm) = 2.
  Proof. vm_compute. reflexivity. Qed.

  (* NEITHER arm's drive is sequenced behind a sample: [chain_gate] returns the
     drive itself, so the only thing holding it is its own guard. *)
  Definition xp_gate_is_join (d: nid_t) : bool :=
    match chain_gate xp_ctx xp_dfg d with
    | Some (g, _) =>
        match op (nth g (graph xp_dfg)
                    (hd {| nid := 0; op := DFG_Empty; sz := 0 |} (graph xp_dfg))) with
        | DFG_Join _ _ => true
        | _ => false
        end
    | None => false
    end.

  Example xp_arms_have_no_join :
    forallb (fun d => negb (xp_gate_is_join d))
            (drive_nodes xp_ctx xp_dfg xp_arm) = true.
  Proof. vm_compute. reflexivity. Qed.

End XPortGuard.

Require Import Trustformer.Backend.Lowering.

Section XPortGuardSynthesis.

  Definition xp_action_encoding (a: xp_action) : bits_t 16 :=
    match a with act_x => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1 end.

  Lemma xp_action_encoding_inj :
    forall a1 a2, xp_action_encoding a1 = xp_action_encoding a2 -> a1 = a2.
  Proof. intros a1 a2 _. destruct a1; destruct a2; reflexivity. Qed.

  Definition xp_schedule := tfs_schedule xp_ctx xclimit.

  Definition xp_tf_ctx : TFSynthContext := {|
    tf_sched_ctx := xp_schedule;
    tf_action_encoding := xp_action_encoding;
    tf_action_encoding_inj := xp_action_encoding_inj;
  |}.
  Definition xp_package := Lowering.package xp_tf_ctx "Regression_XPortGuard".

End XPortGuardSynthesis.

Definition xp_prog := Interop.Backends.register xp_package.
Set Extraction Output Directory "build".
Extraction "Regression_XPortGuard.ml" xp_prog.
