(* ===================================================================== *)
(*  SPIKE: a call AFTER an [if] whose arms both call the same IP.        *)
(* ===================================================================== *)
(*
    The third call has to wait for whichever arm ran.  It is sequenced behind
    the pending calls on the port, and BOTH arms are pending -- an untaken
    arm's stall counts out regardless, so waiting on only the most recent one
    lets it wave this call through while the taken arm is still in flight.
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

Section ArmsSeq.

  Definition aw := 32.
  Definition alat := 3.
  Definition aclimit := 5.

  Inductive as_action := act_a.
  Inductive as_states := st_t | st_e | st_z.
  Inductive as_inputs := in_sel | in_x | in_y.
  Definition as_outputs := Empty_set.

  Definition as_ss (_: as_states) : nat := aw.
  Definition as_is (_: as_inputs) : nat := aw.
  Definition as_os (_: as_outputs) : nat := aw.
  Definition as_init (v: as_states) : tf_states_type as_ss v :=
    match v with st_t => Bits.zero | st_e => Bits.zero | st_z => Bits.zero end.

  Definition as_f (v: bits_t aw) : bits_t aw := v.
  Definition as_inc (_: as_inputs) : port_class := Public.
  Definition as_outc (_: as_outputs) : port_class := Secret.

  Inductive as_ips := as_ip.
  Definition as_ip_decl (_: as_ips) : ip_decl :=
    {| ip_req_sz := aw; ip_resp_sz := aw; ip_lat := alat;
       ip_lat_pos := ltac:(unfold alat; lia); ip_fn := as_f |}.

  (* the taken arm's argument is several cycles deeper than the other's *)
  Definition deep : @tf_expr as_states as_inputs as_outputs :=
    tf_op2 tf_mul (tf_ivar in_x)
      (tf_op2 tf_mul (tf_ivar in_x)
         (tf_op2 tf_mul (tf_ivar in_x) (tf_ivar in_x))).

  (* if sel = 0 then st_t := ip(x*x*x*x) else st_e := ip(y);
     st_z := ip(1)  *)
  Definition as_ops : @tf_ops as_states as_inputs as_outputs as_ips :=
    tf_ops_cons
      (tf_ops_if (tf_op2 (tf_cmp aw tf_eq) (tf_ivar in_sel) (tf_const 0))
         (tf_ops_base (tf_call as_ip st_t deep))
         (tf_ops_base (tf_call as_ip st_e (tf_ivar in_y))))
      (tf_ops_base (tf_call as_ip st_z (tf_const 1))).

  Definition as_ctx : TFSchedContext := {|
      tfs_spec_states := as_states;   tfs_spec_states_fin := _;
      tfs_spec_states_size := as_ss;  tfs_spec_states_init := as_init;
      tfs_spec_inputs := as_inputs;   tfs_spec_inputs_fin := _;
      tfs_spec_inputs_size := as_is;  tfs_spec_inputs_class := as_inc;
      tfs_spec_outputs := as_outputs; tfs_spec_outputs_fin := _;
      tfs_spec_outputs_size := as_os; tfs_spec_outputs_class := as_outc;
      tfs_spec_action := as_action;   tfs_spec_action_fin := _;
      tfs_spec_action_ops := fun _ => as_ops;
      tfs_spec_ips := as_ips;         tfs_spec_ips_fin := _;
      tfs_spec_ip := as_ip_decl;
      tfs_spec_decls := []
  |}.

  Definition as_dfg := build_dfg as_ctx act_a.

  (* one per arm, plus the one after the [if] *)
  Example arms_three_drives :
    List.length (drive_nodes as_ctx as_dfg as_ip) = 3.
  Proof. vm_compute. reflexivity. Qed.

  (* the third call is sequenced behind BOTH arms: two joins, not one *)
  Example arms_two_joins :
    List.length (filter (fun nd => match op nd with
                                   | DFG_Join _ _ => true | _ => false end)
                        (graph as_dfg)) = 2.
  Proof. vm_compute. reflexivity. Qed.

End ArmsSeq.

Require Import Trustformer.Backend.Lowering.

Section ArmsSeqSynthesis.

  Definition as_action_encoding (a: as_action) : bits_t 16 :=
    match a with act_a => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1 end.

  Lemma as_action_encoding_inj :
    forall a1 a2, as_action_encoding a1 = as_action_encoding a2 -> a1 = a2.
  Proof. intros a1 a2 _. destruct a1; destruct a2; reflexivity. Qed.

  Definition as_schedule := tfs_schedule as_ctx aclimit.

  Definition as_tf_ctx : TFSynthContext := {|
    tf_sched_ctx := as_schedule;
    tf_action_encoding := as_action_encoding;
    tf_action_encoding_inj := as_action_encoding_inj;
  |}.
  Definition as_package := Lowering.package as_tf_ctx "Regression_ArmsSeq".

End ArmsSeqSynthesis.

Definition as_prog := Interop.Backends.register as_package.
Set Extraction Output Directory "build".
Extraction "Regression_ArmsSeq.ml" as_prog.
