Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.
Require Export Koika.Primitives.

Require Koika.Properties.SemanticProperties.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Utils.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.TypedSynthesis.
Require Trustformer.Properties.Common.
From Koika.Utils Require Import Tactics.
Require Import Koika.IRR.Tactics.

Require Import Streams.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Init.Tactics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Program.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.

Require Import Coq.Logic.ProofIrrelevance.

Require Import Hammer.Plugin.Hammer.
Set Hammer ATPLimit 5.
Set Hammer GSMode 63.

Section SynthesisCorrectness.

  Context (tf_ctx: TFSynthContext).

  (* ====== Abbreviations ====== *)
  Local Notation sched_ctx := (tf_sched_ctx tf_ctx).
  
  Local Notation spec_states := (tfs_states (tf_sched_ctx tf_ctx)).
  Local Notation spec_states_fin := (tfs_states_fin (tf_sched_ctx tf_ctx)).
  Local Notation spec_states_size := (tfs_states_size (tf_sched_ctx tf_ctx)).
  Local Notation spec_states_t := (tf_states_type spec_states_size).
  Local Notation spec_states_init := (tfs_states_init (tf_sched_ctx tf_ctx)).
  Local Notation spec_all_states := (@finite_elements spec_states spec_states_fin).
  Local Notation spec_state_index := (@finite_index spec_states spec_states_fin).
  Local Notation spec_state_num := (Datatypes.length spec_all_states).

  Local Notation spec_inputs := (tfs_inputs (tf_sched_ctx tf_ctx)).
  Local Notation spec_inputs_fin := (tfs_inputs_fin (tf_sched_ctx tf_ctx)).
  Local Notation spec_inputs_size := (tfs_inputs_size (tf_sched_ctx tf_ctx)).
  Local Notation spec_inputs_t := (tf_inputs_type spec_inputs_size).
  Local Notation spec_all_inputs := (@finite_elements spec_inputs spec_inputs_fin).
  Local Notation spec_input_index := (@finite_index spec_inputs spec_inputs_fin).
  Local Notation spec_input_num := (Datatypes.length spec_all_inputs).

  Local Notation spec_outputs := (tfs_outputs (tf_sched_ctx tf_ctx)).
  Local Notation spec_outputs_fin := (tfs_outputs_fin (tf_sched_ctx tf_ctx)).
  Local Notation spec_outputs_size := (tfs_outputs_size (tf_sched_ctx tf_ctx)).
  Local Notation spec_outputs_t := (tf_outputs_type spec_outputs_size).
  Local Notation spec_all_outputs := (@finite_elements spec_outputs spec_outputs_fin).
  Local Notation spec_output_index := (@finite_index spec_outputs spec_outputs_fin).
  Local Notation spec_output_num := (Datatypes.length spec_all_outputs).

  Local Notation spec_action := (tfs_action (tf_sched_ctx tf_ctx)).
  Local Notation spec_action_fin := (tfs_action_fin (tf_sched_ctx tf_ctx)).
  Local Notation spec_all_actions := (@finite_elements spec_action spec_action_fin).
  Local Notation spec_action_index := (@finite_index spec_action spec_action_fin).
  Local Notation spec_action_num := (Datatypes.length spec_all_actions).

  Local Notation spec_action_reg_size := (tf_action_reg_size tf_ctx).
  Local Notation spec_action_encoding := (tf_action_encoding tf_ctx).
  Local Notation spec_action_encoding_inj := (tf_action_encoding_inj tf_ctx).

  Local Notation spec_schedule := (tfs_schedule (tf_sched_ctx tf_ctx)).
  Local Notation spec_done_state := (tfs_done_signal (tf_sched_ctx tf_ctx)).
  Local Notation spec_reset_states := (tfs_reset_states (tf_sched_ctx tf_ctx)).

  Local Definition spec_schedule_ops_nodup := (tfs_schedule_no_duplicates (tf_sched_ctx tf_ctx)).

  Local Notation reg_t := (@_reg_t spec_states spec_inputs spec_outputs).
  Local Notation reg_t_finite := (@_reg_t_finite tf_ctx).
  Local Notation ext_fn_t := (@_ext_fn_t spec_inputs spec_outputs).

  Local Notation st_env := (ContextEnv.(env_t) (tf_states_type spec_states_size)).
  Local Notation out_env := (ContextEnv.(env_t) (tf_outputs_type spec_outputs_size)).
  Local Notation sys_state_t := (st_env * out_env)%type.
  Local Notation input_t := (forall x : spec_inputs, type_denote (tf_inputs_type spec_inputs_size x)).

  Local Notation R := (R tf_ctx).
  Local Notation r := (r tf_ctx).
  Local Notation Sigma := (Sigma tf_ctx).
  Local Notation rules := (rules tf_ctx).
  Local Notation system_schedule := (system_schedule tf_ctx).
  Local Notation REnv := (@ContextEnv reg_t (_reg_t_finite tf_ctx)).

  Hint Extern 0 (FiniteType spec_states) => exact (tfs_states_fin (tf_sched_ctx tf_ctx)) : typeclass_instances.
  Hint Extern 0 (FiniteType spec_inputs) => exact (tfs_inputs_fin (tf_sched_ctx tf_ctx)) : typeclass_instances.
  Hint Extern 0 (FiniteType spec_outputs) => exact (tfs_outputs_fin (tf_sched_ctx tf_ctx)) : typeclass_instances.
  Hint Extern 0 (FiniteType spec_action) => exact (tfs_action_fin (tf_sched_ctx tf_ctx)) : typeclass_instances.

  Hint Extern 0 (FiniteType reg_t) => exact (_reg_t_finite tf_ctx) : typeclass_instances.

  Ltac match_eq :=
  match goal with
  | [ |- (match ?L with _ => _ end) = (match ?R with _ => _ end) ] =>
    let LM := fresh "LM" in
    let RM := fresh "RM" in
    let HeqL := fresh "HeqLM" in
    let HeqR := fresh "HeqRM" in
    remember L as LM eqn:HeqL;
    remember R as RM eqn:HeqR;
    let H := fresh "H" in
    assert (H : LM = RM); [ 
      (* First subgoal: prove the scrutinees are equal *)
      subst LM RM 
    | (* Second subgoal: use the equality to close the original goal *)
      rewrite H; reflexivity 
    ]
  end.

  Ltac extract_match_term :=
  match goal with
  | |- context [match ?X with _ => _ end] =>
      match X with
      | context [match _ with _ => _ end] => 
          fail 1
      | _ => 
          let MT := fresh "MT" in
          let HeqMT := fresh "HeqMT" in
          remember X as MT eqn:HeqMT
      end
  end.

  Ltac in_match_term tac :=
  match goal with
  | |- context [match ?X with _ => _ end] =>
      match X with
      | context [match _ with _ => _ end] => 
          fail 1
      | _ => 
          let MT := fresh "MT" in
          let HeqMT := fresh "HeqMT" in
          remember X as MT eqn:HeqMT;
          tac HeqMT;
          subst MT
      end
  end.

  (* ====== Input Helper Lemmas ====== *)

  Lemma nodup_spec_all_states : NoDup spec_all_states.
  Proof. apply NoDup_map_inv with (f:=(finite_index (FiniteType:=spec_states_fin))). apply finite_injective. Qed.

  Lemma nodup_spec_all_inputs : NoDup spec_all_inputs.
  Proof. apply NoDup_map_inv with (f:=(finite_index (FiniteType:=spec_inputs_fin))). apply finite_injective. Qed.

  Lemma nodup_spec_all_outputs : NoDup spec_all_outputs.
  Proof. apply NoDup_map_inv with (f:=(finite_index (FiniteType:=spec_outputs_fin))). apply finite_injective. Qed.

  Lemma nodup_spec_all_actions : NoDup spec_all_actions.
  Proof. apply NoDup_map_inv with (f:=(finite_index (FiniteType:=spec_action_fin))). apply finite_injective. Qed.

  Lemma in_spec_all_states : forall x, In x spec_all_states.
  Proof. 
    intros x. generalize (finite_surjective x (FiniteType:=spec_states_fin)). 
    intros H1. apply nth_error_In with (finite_index x (FiniteType:=spec_states_fin)). exact H1. 
  Qed.

  Lemma in_spec_all_inputs : forall x, In x spec_all_inputs.
  Proof. 
    intros x. generalize (finite_surjective x (FiniteType:=spec_inputs_fin)). 
    intros H1. apply nth_error_In with (finite_index x (FiniteType:=spec_inputs_fin)). exact H1. 
  Qed.

  Lemma in_spec_all_outputs : forall x, In x spec_all_outputs.
  Proof. 
    intros x. generalize (finite_surjective x (FiniteType:=spec_outputs_fin)). 
    intros H1. apply nth_error_In with (finite_index x (FiniteType:=spec_outputs_fin)). exact H1. 
  Qed.

  Lemma in_spec_all_actions : forall x, In x spec_all_actions.
  Proof. 
    intros x. generalize (finite_surjective x (FiniteType:=spec_action_fin)). 
    intros H1. apply nth_error_In with (finite_index x (FiniteType:=spec_action_fin)). exact H1. 
  Qed.

  Lemma not_in_reg_ready_all_states:
    ~ In (tf_ready (states_var:=spec_states) (inputs_var:=spec_inputs) (outputs_var:=spec_outputs)) (map tf_reg spec_all_states).
  Proof.
    intro. rewrite in_map_iff in H. destruct H as [x [Heq Hin]]. congruence.
  Qed.

  Lemma not_in_reg_ready_all_outputs:
    ~ In (tf_ready (states_var:=spec_states) (inputs_var:=spec_inputs) (outputs_var:=spec_outputs)) (map tf_out spec_all_outputs).
  Proof.
    intro. rewrite in_map_iff in H. destruct H as [x [Heq Hin]]. congruence.
  Qed.  

  Lemma not_in_reg_cmd_all_states:
    ~ In (tf_cmd (states_var:=spec_states) (inputs_var:=spec_inputs) (outputs_var:=spec_outputs)) (map tf_reg spec_all_states).
  Proof.
    intro. rewrite in_map_iff in H. destruct H as [x [Heq Hin]]. congruence.
  Qed.

  Lemma not_in_reg_cmd_all_outputs:
    ~ In (tf_cmd (states_var:=spec_states) (inputs_var:=spec_inputs) (outputs_var:=spec_outputs)) (map tf_out spec_all_outputs).
  Proof.
    intro. rewrite in_map_iff in H. destruct H as [x [Heq Hin]]. congruence.
  Qed.

  Lemma not_in_reg_reg_all_inputs:
    forall x, ~ In (tf_reg (states_var:=spec_states) (inputs_var:=spec_inputs) (outputs_var:=spec_outputs) x) (map tf_in spec_all_inputs).
  Proof.
    intro. intro. rewrite in_map_iff in H. destruct H as [x0 [Heq Hin]]. subst. congruence.
  Qed.

  Lemma not_in_reg_out_all_inputs:
    forall x, ~ In (tf_out (states_var:=spec_states) (inputs_var:=spec_inputs) (outputs_var:=spec_outputs) x) (map tf_in spec_all_inputs).
  Proof.
    intro. intro. rewrite in_map_iff in H. destruct H as [x0 [Heq Hin]]. subst. congruence.
  Qed.

  Lemma not_in_reg_ready_all_inputs:
    ~ In (tf_ready (states_var:=spec_states) (inputs_var:=spec_inputs) (outputs_var:=spec_outputs)) (map tf_in spec_all_inputs).
  Proof.
    intro. rewrite in_map_iff in H. destruct H as [x [Heq Hin]]. congruence.
  Qed.

  Section Encoding.

    Lemma spec_action_encoding_inj' :
      forall (a1 a2 : spec_action),
      a1 <> a2 -> spec_action_encoding a1 <> spec_action_encoding a2.
    Proof.
      intros a1 a2 H_neq. intros H_eq.
      apply spec_action_encoding_inj in H_eq.
      contradiction.
    Qed.    

    Lemma reg_name_inj :
      forall r1 r2,
        (_reg_name tf_ctx r1) = (_reg_name tf_ctx r2) -> r1 = r2.
    Proof.
      intros. unfold _reg_name in H.
      timeout 10 simpl in H. 
      injection H. intros.
      apply string_id_of_nat_inj in H0.
      apply finite_index_injective in H0.
      exact H0.
    Qed.

    Lemma reg_name_inj' :
      forall r1 r2,
        (_reg_name tf_ctx r1) <> (_reg_name tf_ctx r2) -> r1 <> r2.
    Proof.
      intros. unfold _reg_name in H.
      timeout 10 simpl in H.
      unfold not in *. intros. subst r2.
      apply H. reflexivity.
    Qed.

    Lemma out_name_inj :
      forall o1 o2,
        (_out_name tf_ctx o1) = (_out_name tf_ctx o2) -> o1 = o2.
    Proof.
      intros. unfold _out_name in H.
      timeout 10 simpl in H.
      injection H. intros.
      apply string_id_of_nat_inj in H0.
      apply finite_index_injective in H0.
      exact H0.
    Qed.

    Lemma out_name_inj' :
      forall o1 o2,
        (_out_name tf_ctx o1) <> (_out_name tf_ctx o2) -> o1 <> o2.
    Proof.
      intros. unfold _out_name in H.
      timeout 10 simpl in H. 
      unfold not in *. intros. subst o2.
      apply H. reflexivity.
    Qed.

    Lemma reg_ready_or_not (r: ContextEnv.(env_t) R) :
      { r.[tf_ready] = Ob~1 } + { r.[tf_ready] = Ob~0 }.
    Proof.
      destruct (eq_dec r.[tf_ready] (Ob~1)) as [Hready | Hnotready'].
      - left. assumption.
      - right.
        destruct r.[tf_ready] eqn:Hready_val; try discriminate.
        vm_compute Bits.of_nat in *. destruct vtl; try discriminate.
        destruct vhd; try reflexivity. contradiction.
    Qed.

  End Encoding. 

  Opaque _register_var_name.

  (* ====== State and Environment Relations ====== *)

  Definition state_matches (sys: sys_state_t) (r: ContextEnv.(env_t) R) : Prop :=
    (* State variables map cleanly *)
    (forall (x: spec_states), r.[tf_reg x] = (fst sys).[x]) /\
    (* Output variables map cleanly *)
    (forall (x: spec_outputs), r.[tf_out x] = (snd sys).[x]).

  Definition state_equal (r1 r2: ContextEnv.(env_t) R): Prop :=
    (forall (x: spec_states), r1.[tf_reg x] = r2.[tf_reg x]) /\
    (forall (x: spec_outputs), r1.[tf_out x] = r2.[tf_out x]).

  Definition env_matches (act: spec_action) (input: input_t) (r: ContextEnv.(env_t) R) : Prop :=
    (* action variable maps cleanly *)
    (r.[tf_cmd] = spec_action_encoding act) /\
    (* input variables map cleanly *)
    (forall (x: spec_inputs), r.[tf_in x] = input x).

  Definition env_equal (r1 r2: ContextEnv.(env_t) R): Prop :=
    (r1.[tf_cmd] = r2.[tf_cmd]) /\
    (forall (x: spec_inputs), r1.[tf_in x] = r2.[tf_in x]).

  Definition state_env_matches (sys: sys_state_t) (act: spec_action) (input: input_t) (r: ContextEnv.(env_t) R) : Prop :=
    state_matches sys r /\
    env_matches act input r.

  Definition input_matches (act: spec_action) (input: input_t) (sigma: forall f, Sig_denote (Sigma f)) : Prop :=
    let cmd_res := sigma ext_in_cmd Ob~1 in      
    (fst cmd_res) = Ob~1 /\ (* TODO: implicit params should be given explicitly once known *)
    (@fst (vect bool (tf_action_reg_size tf_ctx)) unit
      (@snd (vect_cons_t bool (vect_nil_t bool)) (prod (vect bool (tf_action_reg_size tf_ctx)) unit) cmd_res) = spec_action_encoding act) /\
    (forall (x: spec_inputs), sigma (ext_input x) (Ob~1) = input x).

  (* Lemma state_env_matches_comp :
    forall sys act input r1 r2,
      state_equal r1 r2 ->
      env_equal r1 r2 ->
      state_env_matches sys act input r1 = state_env_matches sys act input r2.
  Proof.
    intros. 
    unfold state_equal in H. destruct H as [Hstate_eq Hout_eq].
    unfold env_equal in H0. destruct H0 as [Hcmd_eq Hin_eq].
    unfold state_env_matches, state_matches, env_matches. f_equal; [f_equal | f_equal].
    (* - apply prop_ext.  *) (* Not provable without function extensionality *)

  Admitted.  *)

  (* ====== Initial State Correctness ====== *)

  Definition abstract_init_state (sys: sys_state_t) : Prop :=
    (forall x, (fst sys).[x] = spec_states_init x) /\
    (forall x, (snd sys).[x] = Bits.zero).

  Theorem initial_state_matches :
    forall (sys: sys_state_t),
      abstract_init_state sys ->
      state_matches sys ((ContextEnv).(create) r).
  Proof.
    intros sys Hinit.
    unfold state_matches, abstract_init_state in *.
    destruct Hinit as [Hstate Houtput].
    split; intros x.
    - rewrite getenv_create. simpl. symmetry. apply Hstate.
    - rewrite getenv_create. simpl. symmetry. apply Houtput.
  Qed.

  (* ====== Translation Validation ====== *)

  Arguments log_empty : simpl never.
  Arguments log_cons : simpl never.

  Section MayReadWrite.

    Local Notation may_read := (may_read (R:=R) (REnv:=REnv) (reg_t:=reg_t)).
    Local Notation may_write := (may_write (R:=R) (REnv:=REnv) (reg_t:=reg_t)).

    Lemma may_read0_implies_may_read1 :
      forall log_r idx,
        may_read log_r P0 idx = true -> may_read log_r P1 idx = true.
    Proof.
      intros log_r idx H. unfold may_read in *. apply andb_prop in H. destruct H as [H_is_write0 H_is_write1]. exact H_is_write1.
    (* Time Qed. *)
    Admitted. (* SPEEDUP *)
    (* 15 seconds *)

    Lemma may_write0_implies_may_write1 :
      forall log_r log_a idx,
        may_write log_r log_a P0 idx = true -> may_write log_r log_a P1 idx = true.
    Proof.
      intros log_r log_a idx H. unfold may_write in *. apply andb_prop in H. destruct H as [H_cons H_is_write1].
      exact H_is_write1.
    (* Time Qed. *)
    Admitted. (* SPEEDUP *)
    (* ??? seconds *)

    Definition may_read_all log_r port regs :=
      forallb (may_read log_r port) regs.

    Definition may_write_all log_r log_a port regs :=
      forallb (may_write log_r log_a port) regs.

    Lemma may_read_all0_implies_may_read_all1 :
      forall log_r regs,
        may_read_all log_r P0 regs = true -> may_read_all log_r P1 regs = true.
    Proof.
      intros log_r regs H. unfold may_read_all in *. rewrite forallb_forall in H. apply forallb_forall. intros x Hin.
      apply H in Hin. apply may_read0_implies_may_read1. exact Hin.
    Qed.

    Lemma may_write_log_cons_neq :
      forall log_r log_a port
             idx1 idx2 entry,
        idx2 <> idx1 ->
        may_write log_r (log_cons idx1 entry log_a) port idx2
        = may_write log_r log_a port idx2.
    Proof.
      intros log_r log_a port idx1 idx2 entry Hneq. destruct entry, kind.
      + unfold may_write. rewrite !SemanticProperties.log_existsb_app.
        rewrite !(SemanticProperties.log_existsb_log_cons_neq log_a idx2 idx1); try assumption; reflexivity.
      + unfold may_write. rewrite !SemanticProperties.log_existsb_app.
        rewrite !(SemanticProperties.log_existsb_log_cons_neq log_a idx2 idx1); try assumption; reflexivity.
    Qed.

    Lemma may_write_log_cons_eq :
      forall log_r log_a prt
             idx entry,
        may_write log_r (log_cons idx entry log_a) prt idx
        = may_write log_r log_a prt idx && 
          match prt with
          | P0 =>
            negb (is_read1 (kind entry) (port entry)) 
            && negb (is_write0 (kind entry) (port entry))
            && negb (is_write1 (kind entry) (port entry))
          | P1 => negb (is_write1 (kind entry) (port entry))
          end.
    Proof.
      intros log_r log_a prt idx entry. destruct entry, kind.
      - unfold may_write. rewrite !SemanticProperties.log_existsb_app.
        rewrite !(SemanticProperties.log_existsb_log_cons_eq log_a idx).
        destruct prt; simpl.
        + destruct port; simpl; [ rewrite andb_true_r | rewrite andb_false_r ]; reflexivity.
        + rewrite andb_true_r; reflexivity.
      - unfold may_write. rewrite !SemanticProperties.log_existsb_app.
        rewrite !(SemanticProperties.log_existsb_log_cons_eq log_a idx).
        destruct prt; simpl.
        + destruct port; simpl; rewrite !andb_false_r; reflexivity.
        + destruct port; simpl; [ rewrite andb_true_r | rewrite andb_false_r ]; reflexivity.
    Qed.

    Lemma may_write_all_log_cons_neq :
      forall log_r log_a port regs
             idx entry,
        ~ In idx regs ->
        may_write_all log_r (log_cons idx entry log_a) port regs
        = may_write_all log_r log_a port regs.
    Proof.
      intros log_r log_a port regs idx entry Hnotin.
      unfold may_write_all. apply forallb_pointwise. intros.
      assert (x <> idx) as Hx_neq.
      { intros Heq. subst x. contradiction. }
      rewrite may_write_log_cons_neq; try assumption. reflexivity.
    Qed.

    Lemma may_write_all_log_cons :
      forall log_r log_a prt regs
             idx entry,
        In idx regs ->
        may_write_all log_r (log_cons idx entry log_a) prt regs
        = may_write_all log_r log_a prt regs && 
          match prt with
          | P0 =>
            negb (is_read1 (kind entry) (port entry)) 
            && negb (is_write0 (kind entry) (port entry))
            && negb (is_write1 (kind entry) (port entry))
          | P1 => negb (is_write1 (kind entry) (port entry))
          end.
    Proof.
      intros log_r log_a prt regs idx entry Hin.

      induction regs as [| r regs H0 ]; simpl in *; try contradiction.
      destruct Hin as [Heq | Hin]; subst.
      - destruct (Common.in_dec idx regs).
        + rewrite (H0 i). rewrite may_write_log_cons_eq.
          destruct prt; simpl.
          * remember ((negb _) && (negb _) && (negb _)) as cond.
            destruct cond; [ rewrite !andb_true_r | rewrite !andb_false_r ]; reflexivity.
          * destruct negb; [ rewrite !andb_true_r | rewrite !andb_false_r ]; reflexivity.
        + rewrite may_write_all_log_cons_neq by assumption. rewrite may_write_log_cons_eq.
          rewrite <- !andb_assoc. rewrite (andb_comm (may_write_all _ _ _ _)). reflexivity.
      - rewrite (H0 Hin); clear H0 Hin.
        destruct (eq_dec r idx) as [Heq | Hneq]; subst.
        + rewrite may_write_log_cons_eq. 
          destruct prt; simpl.
          * remember ((negb _) && (negb _) && (negb _)) as cond.
            destruct cond; [ rewrite !andb_true_r | rewrite !andb_false_r ]; reflexivity.
          * destruct negb; [ rewrite !andb_true_r | rewrite !andb_false_r ]; reflexivity.
        + rewrite may_write_log_cons_neq by assumption. rewrite andb_assoc. reflexivity.
    Qed.

    Lemma may_write_all_cons :
      forall log1 log2 P0 r regs,
      may_write_all log1 log2 P0 (r :: regs) = true ->
      may_write log1 log2 P0 r = true /\ may_write_all log1 log2 P0 regs = true.
    Proof.
      intros log1 log2 P0 r regs H.
      unfold may_write_all in H. simpl in H.
      apply andb_prop in H. destruct H as [H_r H_regs].
      split; assumption.
    Qed.

    Lemma may_read_all_cons :
      forall log1 P0 r regs,
      may_read_all log1 P0 (r :: regs) = true ->
      may_read log1 P0 r = true /\ may_read_all log1 P0 regs = true.
    Proof.
      intros log1 P0 r regs H.
      unfold may_read_all in H. simpl in H.
      apply andb_prop in H. destruct H as [H_r H_regs].
      split; assumption.
    Qed.

  End MayReadWrite.

  Arguments may_read : simpl never.
  Arguments may_write : simpl never.
  Arguments may_write_all : simpl never.
  Arguments may_read_all : simpl never.

  Local Notation Write0 x := ({| kind := LogWrite; port := P0; val := x |}).
  Local Notation Write1 x := ({| kind := LogWrite; port := P1; val := x |}).
  Local Notation Read0 := ({| kind := LogRead; port := P0; val := tt |}).
  Local Notation Read1 := ({| kind := LogRead; port := P1; val := tt |}).

  Section Interpreting.

    (* Goal: Write stepper lemmas for simplifying the interp_rule below *)

    Local Notation interp_action := (interp_action (reg_t:=reg_t) (pos_t:=pos_t) (var_t:=var_t) (fn_name_t:=fn_name_t) (R:=R) (Sigma:=Sigma) (REnv:=REnv)).

    Lemma interp_action_seq :
      forall r sigma sig (ctx: tcontext sig) log_r log_a a1 a2,
        interp_action (tau:=unit_t) r sigma ctx log_r log_a (Seq a1 a2) = 
          let/opt3 log_a, _, Gamma := interp_action r sigma ctx log_r log_a a1 
          in interp_action r sigma Gamma log_r log_a a2.
    Proof. reflexivity. Qed.

    Lemma interp_action_if :
      forall r sigma sig (ctx: tcontext sig) log_r log_a cond tbranch fbranch,
        interp_action (tau:=unit_t) r sigma ctx log_r log_a (If cond tbranch fbranch) = 
          let/opt3 log_a, cond0, Gamma := interp_action r sigma ctx log_r log_a cond
          in (if Bits.single cond0 
              then interp_action r sigma Gamma log_r log_a tbranch 
              else interp_action r sigma Gamma log_r log_a fbranch).
    Proof. reflexivity. Qed.

    Lemma interp_action_read0 :
      forall r sigma sig (ctx: tcontext sig) log_r log_a idx,
        may_read log_r P0 idx = true ->
        interp_action (tau:=R idx) r sigma ctx log_r log_a (Read P0 idx) = 
        Some (log_cons idx {| kind := LogRead; port := P0; val := tt |} log_a, r.[idx], ctx).
    Proof. intros; simpl. rewrite H; try auto. Qed.

    Lemma interp_action_buffer_inputs_cons :
      forall r_env sigma log1 log2 i inputs rest,
        may_write log1 log2 P0 (tf_in i) = true ->
        interp_action (tau:=unit_t) r_env sigma CtxEmpty log1 log2 (rule_buffer_inputs tf_ctx (i :: inputs) rest) =
        interp_action r_env sigma CtxEmpty log1
            (log_cons (tf_in i) (Write0 (sigma (ext_input i) Ob~1)) log2)
            (rule_buffer_inputs tf_ctx inputs rest)
        .
    Proof.
      intros. simpl. rewrite H. reflexivity.
    Time Qed.

  End Interpreting.

  Lemma interp_action_buffer_inputs :
    forall (r: ContextEnv.(env_t) R) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log1 log2 rest,
      (forall x : spec_inputs, sigma (ext_input x) Ob~1 = input x) ->
      may_write_all log1 log2 P0 (map tf_in spec_all_inputs) = true ->

      interp_action (tau:=unit_t) r sigma CtxEmpty log1 log2 (rule_buffer_inputs tf_ctx spec_all_inputs rest) = 
      let log_n := fold_left (fun log x => log_cons (tf_in x) (Write0 (sigma (ext_input x) Ob~1)) log) spec_all_inputs log2 in
      interp_action r sigma CtxEmpty log1 log_n rest.
  Proof.
    intros r input sigma log1 log2 rest Hinput Hwr0_in.

    pose proof (nodup_spec_all_inputs) as H_nodup_inputs.
    generalize dependent log2. generalize rest.

    induction spec_all_inputs as [| i inputs H0 ]; intros.
    - reflexivity.
    - cbn [map] in Hwr0_in. apply may_write_all_cons in Hwr0_in; destruct Hwr0_in as [Hwr0_i Hwr0_inputs].
      rewrite interp_action_buffer_inputs_cons; try assumption.
      cbn [fold_left]. apply (H0); clear H0.
      + abstract ( inversion H_nodup_inputs; subst; assumption ).
      + rewrite may_write_all_log_cons_neq; try assumption.
        apply Common.not_in_map; try assumption.
        * abstract ( inversion H_nodup_inputs; subst; assumption ).
        * abstract ( intros; inversion H; reflexivity ).
  (* Timeout 600 Time Qed.  *)
  Admitted. (* SPEEDUP *)
  (* 12 seconds *)    

  Lemma may_write_fold_cons_w0_inputs :
    forall log log2 prt x (sigma: forall f, Sig_denote (Sigma f)),
    ~ In x (map tf_in spec_all_inputs) ->
    may_write log (fold_left (fun log x => log_cons (tf_in x) (Write0 (sigma (ext_input x) Ob~1)) log) spec_all_inputs log2) prt x
    = may_write (R:=R) (REnv:=REnv) log log2 prt x.
  Proof.
    intros log log2 prt x sigma Hnotin.

    assert (NoDup (map (tf_in (states_var:=spec_states) (inputs_var:=spec_inputs) (outputs_var:=spec_outputs)) (rev spec_all_inputs))) as Hnodup.
    { 
      rewrite map_rev. apply NoDup_rev. apply FinFun.Injective_map_NoDup. 
      + unfold FinFun.Injective. intros. (* hammer *) timeout 10 sfirstorder.
      + apply nodup_spec_all_inputs.
    }

    rewrite in_rev in *. rewrite <- map_rev in *.
    rewrite <- fold_left_rev_right. 
    
    induction (rev spec_all_inputs) as [| i inputs H0 ]; simpl in *.
    - reflexivity.
    - apply Decidable.not_or in Hnotin. destruct Hnotin as [Hnotin_i Hnotin_inputs].
      rewrite may_write_log_cons_neq; try (symmetry; assumption). apply H0; clear H0; try assumption.
      inversion Hnodup. subst. exact H2.
  Qed.

  Lemma may_write_all_fold_cons_w0_inputs :
    forall log log2 prt (sigma: forall f, Sig_denote (Sigma f)) l,
    (forall x, In x l -> ~ In x (map tf_in spec_all_inputs)) ->
    may_write_all log (fold_left (fun log x => log_cons (tf_in x) (Write0 (sigma (ext_input x) Ob~1)) log) spec_all_inputs log2) prt l
    = may_write_all log log2 prt l.
  Proof.
    intros log log2 prt sigma l Hnot_in.

    unfold may_write_all. apply forallb_pointwise. intros.
    rewrite may_write_fold_cons_w0_inputs; try assumption.
    - reflexivity.
    - apply (Hnot_in x H).
  Qed.

  Definition log_after_cmd_guard_rdy (act: spec_action) (sigma: forall f, Sig_denote (Sigma f)) :=
    log_cons (R:=R) (REnv:=REnv) tf_ready (Write0 Ob~0)
      (log_cons tf_cmd (Write0 (spec_action_encoding act))
        (fold_left
          (fun log0 x => log_cons (tf_in x) (Write0 (sigma (ext_input x) Ob~1)) log0) 
            spec_all_inputs (log_cons tf_ready Read0 (log_cons tf_ready Read0 (log_cons tf_ready Read0 log_empty))))).

  Lemma interp_action_cmd_guard :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log,
      state_matches sys r ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      may_write_all log log_empty P0 (map tf_in spec_all_inputs) = true ->
      may_read log P0 (tf_ready) = true ->
      may_write log log_empty P0 (tf_ready) = true ->
      may_read log P0 (tf_cmd) = true ->
      may_write log log_empty P0 (tf_cmd) = true ->
      interp_action r sigma CtxEmpty log log_empty (rule_cmd_guard tf_ctx act) = 
      Some ( 
        if Bits.single r.[tf_ready] then log_after_cmd_guard_rdy act sigma else log_cons tf_cmd Read0 (log_cons tf_ready Read0 log_empty),
        Ob,
        CtxEmpty
      ).
  Proof.
    intros sys r act input sigma log Hstate Hinput_rdy Hinput_nrdy.
    intros Hwr0_in Hrd0_rdy Hwr0_ready Hrd0_cmd Hwr0_cmd.

    unfold rule_cmd_guard. rewrite interp_action_if. 
    (* Set Printing Implicit. *) change (bits_t 1) with (R tf_ready) at 2. rewrite interp_action_read0; try assumption.
    unfold opt_bind.
    
    destruct (reg_ready_or_not r) as [Hready | Hnotready].
    - (* Ready case *)
      in_match_term ltac:(fun H => rewrite Hready in H; cbn in H).

      rewrite interp_action_seq. unfold Guard. rewrite interp_action_if.
      unfold opt_bind. extract_match_term. cbn in HeqMT. rewrite Hrd0_rdy in HeqMT. cbn in HeqMT.
      subst MT. 
      
      unfold input_matches in Hinput_rdy. destruct Hinput_rdy as [Hval [Hcmd Hinput]]; try assumption.
      rewrite Hready. extract_match_term. setoid_rewrite Hval in HeqMT. cbn in HeqMT. subst MT.

      in_match_term ltac:(fun H => cbn in H).
      rewrite interp_action_seq. rewrite interp_action_if. unfold opt_bind.

      extract_match_term. cbn in HeqMT. rewrite Hrd0_rdy in HeqMT. rewrite Hready in HeqMT. cbn in HeqMT. 
      unfold BitFuns._eq in HeqMT. rewrite Hcmd in HeqMT. rewrite beq_dec_refl in HeqMT.
      subst MT.

      in_match_term ltac:(fun H => cbn in H).
      in_match_term ltac:(fun H => cbn in H).
      rewrite (interp_action_buffer_inputs r input sigma).
      + rewrite interp_action_seq. 
        unfold opt_bind. in_match_term ltac:(fun H => cbn in H).
      
        rewrite may_write_fold_cons_w0_inputs.
        2: { intro. rewrite in_map_iff in H. destruct H as [x [Heq Hin]]. congruence. }

        set (MW := may_write _ _ P0 tf_cmd). assert (MW = true) as HMW.
        { subst MW. rewrite !may_write_log_cons_neq; try assumption. all: (* hammer *) timeout 10 sauto. } rewrite HMW. clear HMW MW.
        cbn.

        set (MW := may_write _ _ P0 tf_ready). assert (MW = true) as HMW.
        { 
          subst MW. rewrite !may_write_log_cons_neq; [|(* hammer *) timeout 10 sauto]. rewrite may_write_fold_cons_w0_inputs. 
          2: { intro. rewrite in_map_iff in H. destruct H as [x [Heq Hin]]. congruence. }
          rewrite !may_write_log_cons_eq. rewrite Hwr0_ready. ring. 
        } rewrite HMW. clear HMW MW.
        unfold log_after_cmd_guard_rdy. reflexivity.
      + exact Hinput.
      + rewrite !may_write_all_log_cons_neq. exact Hwr0_in.
        all: abstract (intro; rewrite in_map_iff in H; destruct H as [x [Heq Hin]]; subst; congruence).
    - (* Not ready case *)
      in_match_term ltac:(fun H => rewrite Hnotready in H; cbn in H).
      unfold Guard. rewrite interp_action_if. unfold opt_bind. 
      in_match_term ltac:(fun H => cbn in H; rewrite Hrd0_cmd in H; cbn in H).

      unfold env_matches in Hinput_rdy. destruct Hinput_nrdy as [Hcmd Hin]; try assumption.
      extract_match_term. rewrite Hcmd in HeqMT. cbn in HeqMT. rewrite beq_dec_refl in HeqMT. subst MT.
      reflexivity.
  (* Timeout 600 Time Qed.  *)
  Admitted. (* SPEEDUP *)
  (* 188 seconds *)

  Program Fixpoint CtxReadVars (r: ContextEnv.(env_t) R) (regs: list reg_t) (sig: tsig var_t) (acc: tcontext sig) : 
    tcontext (rev (map (fun r => (_register_var_name tf_ctx r, R r)) regs) ++ sig) :=
    match regs with
    | [] => acc
    | reg :: rs => 
        let k_tau := (_register_var_name tf_ctx reg, R reg) in
        CtxReadVars r rs (k_tau :: sig) (CtxCons k_tau (r.[reg]) acc)
    end.
  Next Obligation.
    rewrite <- List.app_assoc.
    reflexivity.
  Qed.

  Arguments _Log : simpl never.


  Lemma interp_action_read_vars_states:
    forall r sigma tau sig
      (rest : action R Sigma (rev (map (fun r => (_register_var_name tf_ctx r, R r)) (map tf_reg spec_all_states)) ++ sig) tau)
      log_r log_a (ctx: tcontext (var_t:=var_t) sig),
      may_read_all log_r P0 (map tf_reg spec_all_states) = true ->
        match 
          interp_action r sigma 
            ctx 
            log_r log_a 
            (rule_read_vars tf_ctx (_register_var_name tf_ctx) (map tf_reg spec_all_states) rest)
        return option (Log R REnv) with
        | Some (l, _, _) => Some (l)
        | None => None
        end =
        match 
          interp_action r sigma 
            (CtxReadVars r (map tf_reg spec_all_states) sig ctx) log_r 
            (fold_left (fun log s => log_cons (tf_reg s) (LE LogRead P0 tt) log) spec_all_states log_a) rest
        return option (Log R REnv) with
        | Some (l, _, _) => Some (l)
        | None => None
        end.
  Proof.
    intros r sigma tau sig rest log_r log_a ctx Hrd0_st.


    (* pose proof (nodup_spec_all_states) as H_nodup_all_states. *)
    generalize dependent log_a. generalize dependent rest. generalize dependent tau. generalize dependent ctx. generalize dependent sig.

    induction spec_all_states as [| s states H0 ]; intros.
    - reflexivity.
    - cbn in Hrd0_st. apply may_read_all_cons in Hrd0_st; destruct Hrd0_st as [Hrd0_s Hrd0_states].
      specialize (H0 Hrd0_states). 
      cbn. rewrite Hrd0_s. cbn. unfold opt_bind.
      rewrite Common.bind_match.

      rewrite H0; clear H0. clear.
      admit. (* Dependent Type Hell *)
      
      (* set (e := TypedSynthesis.rule_read_vars_obligation_1 _ _ _ _ _).
      set (e0 := CtxReadVars_obligation_1 _ _ _).
      clearbody e e0. cbv zeta in e, e0.

      dependent destruction e. dependent destruction e0.  *)
   
  Admitted.

  Lemma interp_action_read_vars_outputs:
    forall r sigma tau sig
      (rest : action R Sigma (rev (map (fun r => (_register_var_name tf_ctx r, R r)) (map tf_out spec_all_outputs)) ++ sig) tau)
      log_r log_a (ctx: tcontext (var_t:=var_t) sig),
      may_read_all log_r P0 (map tf_out spec_all_outputs) = true ->
        match interp_action r sigma ctx log_r log_a 
          (rule_read_vars tf_ctx (_register_var_name tf_ctx) (map tf_out spec_all_outputs) rest)
        return option (Log R REnv) with
        | Some (l, _, _) => Some (l)
        | None => None
        end =
        match 
          interp_action r sigma (CtxReadVars r (map tf_out spec_all_outputs) sig ctx) log_r 
            (fold_left (fun log s => log_cons (tf_out s) (LE LogRead P0 tt) log) spec_all_outputs log_a) rest
        return option (Log R REnv) with
        | Some (l, _, _) => Some (l)
        | None => None
        end.
  Proof.
    intros r sigma tau sig rest log_r log_a ctx Hrd0_out.

    generalize dependent log_a. generalize dependent rest. generalize dependent tau. generalize dependent ctx. generalize dependent sig.

    induction spec_all_outputs as [| s outputs H0 ]; intros.
    - reflexivity.
    - cbn in Hrd0_out. apply may_read_all_cons in Hrd0_out; destruct Hrd0_out as [Hrd0_s Hrd0_outputs].
      specialize (H0 Hrd0_outputs). 
      cbn. rewrite Hrd0_s. cbn. unfold opt_bind.
      rewrite Common.bind_match.

      rewrite H0; clear H0. clear.
      admit. (* Dependent Type Hell *)
  Admitted.

  Fixpoint eval_expr_aux {szB}
      (expr: tf_expr) log
      (sys_state: sys_state_t)
      (input: input_t)
      : (bits_t szB * list reg_t) :=
        match expr with
        | tf_const value =>
            (Bits.of_nat szB value, log)
        | tf_svar v =>
            (convert (fst sys_state).[v], tf_reg v :: log)
        | tf_ivar v =>
            (convert (input v), tf_in v :: log)
        | tf_ovar v =>
            (convert (snd sys_state).[v], tf_out v :: log)
        | tf_op1 op src =>
            let (val_src, log_src) := (eval_expr_aux src log sys_state input) in
            (
              match op with
              | tf_not => Bits.neg val_src
              end,
              log_src
            )
        | tf_op2 op src1 src2 =>
            let (val_src1, log_src1) := (eval_expr_aux src1 log sys_state input) in
            let (val_src2, log_src2) := (eval_expr_aux src2 log_src1 sys_state input) in
            match op with
            | tf_and => (Bits.and val_src1 val_src2, log_src2)
            | tf_or => (Bits.or val_src1 val_src2, log_src2)
            | tf_xor => (Bits.xor val_src1 val_src2, log_src2)
            | tf_add => (Bits.plus val_src1 val_src2, log_src2)
            | tf_sub => (Bits.minus val_src1 val_src2, log_src2)
            | tf_mul => (convert (Bits.mul val_src1 val_src2), log_src2)
            | tf_cmp szC cmp_op =>
                let (val_cmp_src1, log_cmp_src1) := (eval_expr_aux (szB:=szC) src1 log_src2 sys_state input) in
                let (val_cmp_src2, log_cmp_src2) := (eval_expr_aux (szB:=szC) src2 log_cmp_src1 sys_state input) in
                (
                  match cmp_op with
                  | tf_eq =>
                      if beq_dec val_cmp_src1 val_cmp_src2 then Bits.of_nat szB 1 else Bits.of_nat szB 0
                  | tf_neq =>
                      if beq_dec val_cmp_src1 val_cmp_src2 then Bits.of_nat szB 0 else Bits.of_nat szB 1
                  | tf_lt =>
                      if Bits.unsigned_lt val_cmp_src1 val_cmp_src2 then Bits.of_nat szB 1 else Bits.of_nat szB 0
                  | tf_le =>
                      if Bits.unsigned_le val_cmp_src1 val_cmp_src2 then Bits.of_nat szB 1 else Bits.of_nat szB 0
                  | tf_gt =>
                      if Bits.unsigned_gt val_cmp_src1 val_cmp_src2 then Bits.of_nat szB 1 else Bits.of_nat szB 0
                  | tf_ge =>
                      if Bits.unsigned_ge val_cmp_src1 val_cmp_src2 then Bits.of_nat szB 1 else Bits.of_nat szB 0
                  end,
                  log_cmp_src2
                )
            end
        | tf_expr_if cond then_expr else_expr =>
            let (val_cond, log_cond) := (eval_expr_aux (szB:=1) cond log sys_state input) in
            if beq_dec val_cond Bits.zero then (* Note: we check for false i.e. all bits are zero, thus the bodies here are switched *)
              eval_expr_aux else_expr log_cond sys_state input 
            else
              eval_expr_aux then_expr log_cond sys_state input
        end.

  Definition expr_log (expr: tf_expr) (szB: nat) (sys_state: sys_state_t) (input: input_t) log :=
    fold_left (fun acc reg => log_cons (R:=R) (REnv:=REnv) reg {| kind := LogRead; port := match reg with
                                                   | tf_in v => P1
                                                   | _ => P0
                                                   end; val := tt |} acc ) (snd (eval_expr_aux (szB:=szB) expr [] sys_state input)) log.

  (* 
  TODO: here
  
  Lemma interp_synth_convert :
    forall r sigma log_r log_a szA ctx sig szB (expr : action R Sigma sig (bits_t szA)),
      interp_action (R:=R) (REnv:=REnv) r sigma ctx log_r log_a (synth_convert (in_var_size := szA) tf_ctx szB expr) = 
      match interp_action (R:=R) (REnv:=REnv) r sigma ctx log_r log_a expr 
      return option (Log R REnv * bits_t szB * sig) with
      | Some (l, v, g) => Some (l, convert (szB:=szB) v, g)
      | None => None
      end.
  Proof.
    intros r sigma log_r log_a szB szA expr.

    unfold synth_convert. 
    generalize dependent expr.
    (* Dependent Type Hell *)
    (* destruct (lt_eq_lt_dec szA szB) as [[Hlt | Hlt] | Hgt]; intros. *)
    admit.
  Admitted. *)

  Lemma interp_action_expr :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log_r log_a expr dst,
      state_matches sys r ->
      env_matches act input r ->
      interp_action r sigma
        (CtxReadVars r (map tf_out spec_all_outputs) (rev (map (fun r0 : reg_t => (_register_var_name tf_ctx r0, R r0)) (map tf_reg spec_all_states)) ++ [])
        (CtxReadVars r (map tf_reg spec_all_states) [] CtxEmpty)) log_r log_a (expr_to_action tf_ctx expr (spec_states_size dst))
      = Some (
          expr_log expr (spec_states_size dst) sys input log_a, 
          tf_eval_expr (szB:=spec_states_size dst) spec_states_size spec_inputs_size spec_outputs_size expr sys input, 
          CtxReadVars r (map tf_out spec_all_outputs) (rev (map (fun r0 : reg_t => (_register_var_name tf_ctx r0, R r0)) (map tf_reg spec_all_states)) ++ [])
          (CtxReadVars r (map tf_reg spec_all_states) [] CtxEmpty)
        ).
  Proof.
    intros sys r act input sigma log_r log_a expr dst.
    intros Hstate Hinput_rdy.

    induction expr.
    + (* Const *)
      reflexivity.
    + (* Var *)
      cbn. rewrite interp_synth_convert. reflexivity.
      
      admit. 

  Definition affected_regs (ops: list (@tf_op spec_states spec_inputs spec_outputs)) : list reg_t :=
    fold_right (fun op acc => match op with
                             | tf_assign dst _ => tf_reg dst :: acc
                             | tf_output dst _ => tf_out dst :: acc
                             | _ => acc
                             end) [] ops.

  Lemma interp_action_aux :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log_r log_a ops rest,
      state_matches sys r ->
      env_matches act input r ->
      may_read_all log_r P1 (map tf_in spec_all_inputs) = true ->
      NoDup (affected_regs ops) ->
      may_write_all log_r log_a P0 (affected_regs ops) = true ->
      match interp_action (tau:=unit_t) r sigma (CtxReadVars r (map tf_out spec_all_outputs) (rev (map (fun r0 : reg_t => (_register_var_name tf_ctx r0, R r0)) (map tf_reg spec_all_states)) ++ [])
                                    (CtxReadVars r (map tf_reg spec_all_states) [] CtxEmpty))
              log_r log_a (rule_aux tf_ctx ops rest)
      return option (Log R REnv) with
      | Some (l, _, _) => Some (l)
      | None => None
      end =
      None.
  Proof.
    intros r sigma log_r log_a ops rest.
    intros Hrd1_in HNoDup_aff Hwr0_aff.

    generalize dependent log_a. generalize dependent rest.
    induction ops as [| op ops H0 ]; intros.
    - admit.
    - destruct op.
      + cbn. apply H0; [ exact HNoDup_aff | exact Hwr0_aff ].
      + cbn. cbn in Hwr0_aff. apply may_write_all_cons in Hwr0_aff. destruct Hwr0_aff as [Hwr0_dst Hwr0_rest].
        admit.
        (* rewrite Hwr0_dst. apply H0; [| exact Hwr0_rest]. *)
  Admitted.

  Definition construct_log (sys: sys_state_t) (act: spec_action) (input: input_t) ready (log_a: Log R ContextEnv): Log R ContextEnv :=
    let updates := if 
                    beq_dec (find_st_val sched_ctx spec_done_state (tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input) sys) Bits.zero
                  then 
                    tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input
                  else 
                    tfs_reset_updates sched_ctx spec_reset_states 
                    ++ tfs_get_updates sched_ctx (snd (spec_schedule act)) sys input 
                    ++ tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input in
    match eq_dec ready Ob~1 with
    | left Hready => log_a (* TODO: update while working on the proof below *)
    | right Hnotready => log_a (* TODO: update while working on the proof below *)
    end.

  Lemma interp_action_cmd :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log_r log_a,
      state_matches sys r ->
      env_matches act input r ->
      may_read_all log_r P0 (map tf_reg spec_all_states) = true ->
      may_write_all log_r log_a P0 (map tf_reg spec_all_states) = true ->
      may_read_all log_r P1 (map tf_in spec_all_inputs) = true ->
      may_read_all log_r P0 (map tf_out spec_all_outputs) = true ->
      may_write_all log_r log_a P0 (map tf_out spec_all_outputs) = true ->
      may_write log_r log_a P1 (tf_ready) = true ->
      match interp_action r sigma CtxEmpty log_r log_a (_rule_cmd tf_ctx act) with
      | Some (l, v, _) => Some (l)
      | None => None
      end =
      Some ( construct_log sys act input r.[tf_ready] log_a ).
  Proof.
    intros sys r act input sigma log_r log_a Hstate Hinput_rdy Hinput_nrdy.
    intros Hrd0_st Hwr0_st Hrd1_in Hrd0_out Hwr0_out Hwr1_ready.
    
    unfold _rule_cmd. rewrite interp_action_read_vars_states; try assumption.
    rewrite interp_action_read_vars_outputs; try assumption.
    admit.
  Admitted.

  Lemma interp_rule_correct :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log,
      state_matches sys r ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      may_read_all log P0 (map tf_reg spec_all_states) = true ->
      may_write_all log log_empty P0 (map tf_reg spec_all_states) = true ->
      may_read_all log P0 (map tf_in spec_all_inputs) = true ->
      may_write_all log log_empty P0 (map tf_in spec_all_inputs) = true ->
      may_read_all log P0 (map tf_out spec_all_outputs) = true ->
      may_write_all log log_empty P0 (map tf_out spec_all_outputs) = true ->
      may_read log P0 (tf_ready) = true ->
      may_write log log_empty P0 (tf_ready) = true ->
      may_read log P0 (tf_cmd) = true ->
      may_write log log_empty P0 (tf_cmd) = true ->
      let guard_log := if Bits.single r.[tf_ready] then log_after_cmd_guard_rdy act sigma else log_cons tf_cmd Read0 (log_cons tf_ready Read0 log_empty) in
      interp_rule r sigma log (rules (rule_cmd act)) = Some (construct_log sys act input r.[tf_ready] guard_log).
  Proof.
    intros sys r act input sigma log Hstate Hinput_rdy Hinput_nrdy.
    intros Hrd0_st Hwr0_st Hrd0_in Hwr0_in Hrd0_out Hwr0_out Hrd0_rdy Hwr0_ready Hrd0_cmd Hwr0_cmd.
    unfold interp_rule, rules.

    rewrite interp_action_seq. unfold opt_bind.
    rewrite (interp_action_cmd_guard sys r act input sigma log); try assumption.

    setoid_rewrite (interp_action_cmd sys r act input sigma log 
              (if Bits.single r.[tf_ready] 
                then log_after_cmd_guard_rdy act sigma 
                else log_cons tf_cmd Read0 (log_cons tf_ready Read0 log_empty))).
    - reflexivity.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - destruct (reg_ready_or_not r) as [Hready | Hnotready].
      + rewrite Hready. cbn. unfold log_after_cmd_guard_rdy. 
        rewrite !may_write_all_log_cons_neq. rewrite may_write_all_fold_cons_w0_inputs. rewrite !may_write_all_log_cons_neq. assumption.
        all: (try exact not_in_reg_ready_all_states); (try exact not_in_reg_cmd_all_states).
        intros. rewrite in_map_iff in H. destruct H as [x0 [Heq Hin]]. subst. exact (not_in_reg_reg_all_inputs x0).
      + rewrite Hnotready. cbn. rewrite !may_write_all_log_cons_neq. assumption.
        all: (try exact not_in_reg_ready_all_states); (try exact not_in_reg_cmd_all_states).
    - apply may_read_all0_implies_may_read_all1. assumption.  
    - assumption.
    - destruct (reg_ready_or_not r) as [Hready | Hnotready].
      + rewrite Hready. cbn. unfold log_after_cmd_guard_rdy. 
        rewrite !may_write_all_log_cons_neq. rewrite may_write_all_fold_cons_w0_inputs. rewrite !may_write_all_log_cons_neq. assumption.
        all: (try exact not_in_reg_ready_all_outputs); (try exact not_in_reg_cmd_all_outputs).
        intros. rewrite in_map_iff in H. destruct H as [x0 [Heq Hin]]. subst. exact (not_in_reg_out_all_inputs x0).
      + rewrite Hnotready. cbn. rewrite !may_write_all_log_cons_neq. assumption.
        all: (try exact not_in_reg_ready_all_outputs); (try exact not_in_reg_cmd_all_outputs).
    - destruct (reg_ready_or_not r) as [Hready | Hnotready].
      + rewrite Hready. cbn. unfold log_after_cmd_guard_rdy.
        rewrite may_write_log_cons_eq. rewrite may_write_log_cons_neq. 
        rewrite may_write_fold_cons_w0_inputs. rewrite !may_write_log_cons_eq. simpl. rewrite !andb_true_r.
        * apply may_write0_implies_may_write1. assumption. 
        * exact not_in_reg_ready_all_inputs. 
        * intro. congruence.
      + rewrite Hnotready. cbn. rewrite may_write_log_cons_neq. rewrite may_write_log_cons_eq. simpl. rewrite !andb_true_r.
        * apply may_write0_implies_may_write1. assumption.
        * intro. congruence.
  (* Time Qed. *)
  Admitted. (* SPEEDUP *)
  (* ??? seconds *)

  (* 
    Once we can substitue the expensive HW interpretation with a contructed log, we should be able to work on the lemmas below
    until then we do not wish to proceed past this point
  *)
Abort.

  Lemma latest_write_cmd_rdy :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log,
      state_matches sys r ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      good_log log ->
      r.[tf_ready] = Ob~1 ->
      latest_write match interp_rule r sigma log (rules (rule_cmd act)) with
        | Some l => log_app l log
        | None => log
        end tf_cmd = Some (spec_action_encoding act).
  Proof.
  Admitted.

  Lemma latest_write_cmd_nrdy :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log,
      state_matches sys r ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      good_log log ->
      r.[tf_ready] = Ob~0 ->
      latest_write match interp_rule r sigma log (rules (rule_cmd act)) with
        | Some l => log_app l log
        | None => log
        end tf_cmd = None.
  Proof.
  Admitted.

  Lemma latest_write_input_rdy :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log x,
      state_matches sys r ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      good_log log ->
      r.[tf_ready] = Ob~1 ->
      latest_write match interp_rule r sigma log (rules (rule_cmd act)) with
        | Some l => log_app l log
        | None => log
        end (tf_in x) = Some (input x).
  Proof.
  Admitted.

  Lemma latest_write_input_nrdy :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log x,
      state_matches sys r ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      good_log log ->
      r.[tf_ready] = Ob~0 ->
      latest_write match interp_rule r sigma log (rules (rule_cmd act)) with
        | Some l => log_app l log
        | None => log
        end (tf_in x) = None.
  Proof.
  Admitted.

  Lemma latest_write_reg :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log x,
      state_matches sys r ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      good_log log ->
      latest_write match interp_rule r sigma log (rules (rule_cmd act)) with
        | Some l => log_app l log
        | None => log
        end (tf_reg x) =
        find_st_update sched_ctx x
          (if 
            beq_dec (find_st_val sched_ctx spec_done_state (tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input) sys) Bits.zero
          then 
            tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input
          else 
            tfs_reset_updates sched_ctx spec_reset_states 
            ++ tfs_get_updates sched_ctx (snd (spec_schedule act)) sys input 
            ++ tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input).
  Proof.
  Admitted.

  Lemma latest_write_out :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log x,
      state_matches sys r ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      good_log log ->
      latest_write match interp_rule r sigma log (rules (rule_cmd act)) with
        | Some l => log_app l log
        | None => log
        end (tf_out x) =
        find_out_update sched_ctx x
          (if 
            beq_dec (find_st_val sched_ctx spec_done_state (tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input) sys) Bits.zero
          then 
            tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input
          else 
            tfs_reset_updates sched_ctx spec_reset_states 
            ++ tfs_get_updates sched_ctx (snd (spec_schedule act)) sys input 
            ++ tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input).
  Proof.
  Admitted.

  Lemma synthesis_correct_aux3 :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log,
      state_matches sys r ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      good_log log ->
      state_env_matches (tfs_next_cycle sched_ctx act sys input) act input (commit_update r match interp_rule r sigma log (rules (rule_cmd act)) with
        | Some l => log_app l log
        | None => log
        end).
  Proof.
    intros sys r act input sigma log Hstate Hin_rdy Hin_nrdy Hlog.
    unfold state_env_matches; split.
    - unfold state_matches; split; intros.
      + unfold commit_update, tfs_next_cycle. cbn [fst snd].
        rewrite !getenv_create. unfold find_st_val at 1.
        assert (r.[tf_reg x] = (fst sys).[x]) as Hreg. { apply Hstate. } rewrite Hreg. clear Hreg.
        match_eq. apply latest_write_reg; try assumption.
      + unfold commit_update, tfs_next_cycle. cbn [fst snd].
        rewrite !getenv_create. unfold find_out_val at 1.
        assert (r.[tf_out x] = (snd sys).[x]) as Hreg. { apply Hstate. } rewrite Hreg. clear Hreg.
        match_eq. apply latest_write_out; try assumption.
    - unfold env_matches; split; intros.
      + unfold commit_update. rewrite getenv_create.
        destruct (reg_ready_or_not r) as [Hready | Hnotready].
        * rewrite (latest_write_cmd_rdy sys r act input sigma log); try assumption; reflexivity.
        * rewrite (latest_write_cmd_nrdy sys r act input sigma log); try assumption. apply (Hin_nrdy Hnotready). auto.
      + unfold commit_update. rewrite getenv_create.
        destruct (reg_ready_or_not r) as [Hready | Hnotready].
        * rewrite (latest_write_input_rdy sys r act input sigma log x); try assumption; reflexivity.
        * rewrite (latest_write_input_nrdy sys r act input sigma log x); try assumption. apply (Hin_nrdy Hnotready). 
  Qed.

  Lemma interp_rule_cmd_wrong :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log a,
      state_matches sys r ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      act <> a ->
      interp_rule r sigma log (rules (rule_cmd a)) = None.
  Proof.
    intros sys r act input sigma log a Hstate Hin_rdy Hin_nrdy Hact_neq_a.
    unfold interp_rule, rules, rule_cmd_guard. simpl_eq. (* Takes a while, but otherwise qed stalls *)
    destruct may_read; try reflexivity. timeout 10 cbn. 
    destruct (reg_ready_or_not r) as [Hready | Hnotready].
    - specialize (Hin_rdy Hready) as H_in. rewrite Hready. timeout 10 cbn.
      destruct Bits.single; try reflexivity. timeout 10 cbn. destruct beq_dec eqn:Hbeq; try reflexivity.
      apply beq_dec_iff in Hbeq. contradict Hbeq.
      unfold input_matches in H_in. destruct H_in as [H_v [H_act_enc H_input]].
      rewrite H_act_enc. apply spec_action_encoding_inj'. assumption.
    - specialize (Hin_nrdy Hnotready) as H_in. rewrite Hnotready. timeout 10 cbn.
      destruct may_read; try reflexivity. timeout 10 cbn. destruct beq_dec eqn:Hbeq; try reflexivity.
      apply beq_dec_iff in Hbeq. contradict Hbeq.
      unfold env_matches in H_in. destruct H_in as [H_cmd _]. rewrite H_cmd; try auto.
      apply spec_action_encoding_inj'. assumption.
  Qed.  

  Lemma latest_write_schedule_outputs :
    forall (r: ContextEnv.(env_t) R) (sigma: forall f, Sig_denote (Sigma f)) log x,
      match x with | tf_out_ack _ => False | _ => True end ->
      latest_write (interp_scheduler' r sigma rules log (system_schedule_outputs tf_ctx)) x = latest_write log x.
  Proof.
    intros r sigma log x Hx. unfold system_schedule_outputs.

    assert (forall t, tf_out_ack t <> x). { intros t. (* hammer *) sfirstorder. } clear Hx.
    
    generalize dependent log.
    induction (spec_all_outputs) as [|o outputs IH]; intros log.
    - cbn [fold_right interp_scheduler']. destruct x; reflexivity.
    - cbn [fold_right interp_scheduler' rules]. unfold interp_rule. cbn [interp_action].
      unfold opt_bind. destruct may_read; [|apply IH]. destruct may_write; [rewrite IH|apply IH]. 
      clear IH. rewrite SemanticProperties.latest_write_app. 
      rewrite SemanticProperties.latest_write_cons_neq; [|symmetry; exact (H o)].
      rewrite Common.latest_write_log_cons_read; [|auto].
      rewrite SemanticProperties.latest_write_empty. reflexivity.
  Qed.

  Lemma synthesis_correct_aux2 :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log (actions: list spec_action),
      state_matches sys r ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      good_log log ->
      ~ In act actions ->
      state_env_matches (tfs_next_cycle sched_ctx act sys input) act input
        (commit_update r
          match interp_rule r sigma log (rules (rule_cmd act)) with
          | Some l => interp_scheduler' r sigma rules (log_app l log) (fold_right (fun (t : spec_action) (acc : scheduler) => rule_cmd t |> acc) (system_schedule_outputs tf_ctx) actions)
          | None => interp_scheduler' r sigma rules log (fold_right (fun (t : spec_action) (acc : scheduler) => rule_cmd t |> acc) (system_schedule_outputs tf_ctx) actions)
          end)
      =
      state_env_matches (tfs_next_cycle sched_ctx act sys input) act input (commit_update r
          match interp_rule r sigma log (rules (rule_cmd act)) with
          | Some l => (log_app l log)
          | None => log
          end).
  Proof.
    intros sys r act input sigma log actions Hstate Hin_rdy Hin_nrdy Hlog H_notin_actions.

    induction actions as [|a actions IH].
    - cbn [fold_right]. 
      apply state_env_matches_comp;
        (* All: *) unfold state_equal, env_equal; split;
          (* All: *) intros x; unfold commit_update; rewrite !getenv_create; match_eq; destruct interp_rule; apply latest_write_schedule_outputs; reflexivity.
    - apply not_in_cons in H_notin_actions. destruct H_notin_actions as [Hneq Hnotin].

      cbn [fold_right interp_scheduler'].
      destruct (interp_rule r sigma log (rules (rule_cmd act))) as [l | ] eqn:H_interp_cmd.
      + rewrite (interp_rule_cmd_wrong sys r act input sigma (log_app l log) a Hstate Hin_rdy Hin_nrdy); try assumption.
        apply IH; try assumption.
      + rewrite (interp_rule_cmd_wrong sys r act input sigma log a Hstate Hin_rdy Hin_nrdy); try assumption.
        apply IH; try assumption.
  Qed.


  Lemma synthesis_correct_aux :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log,
      state_matches sys r ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      good_log log ->
      state_env_matches (tfs_next_cycle sched_ctx act sys input) act input (commit_update r (interp_scheduler' r sigma rules log (system_schedule_actions tf_ctx))).
  Proof.
    intros sys r act input sigma log Hstate Hin_rdy Hin_nrdy Hlog.
    unfold system_schedule_actions.

    pose proof (nodup_spec_all_actions) as H_nodup_actions.
    pose proof (in_spec_all_actions act) as H_in_actions.

    generalize dependent log.
    induction (spec_all_actions) as [|a actions IH] ; [inversion H_in_actions | ]. intros log Hlog.
    
    apply NoDup_cons_iff in H_nodup_actions. destruct H_nodup_actions as [H_a_notin H_nodup_actions].
    destruct H_in_actions as [H_act_eq | H_in_actions]; subst.

    - (* current action is the requested action *)
      cbn [fold_right interp_scheduler'].

      rewrite synthesis_correct_aux2; try assumption.
      apply (synthesis_correct_aux3 sys r act input sigma log Hstate Hin_rdy Hin_nrdy Hlog).

    - (* current action is not the requested action *)
      assert (H_act_neq_a: act <> a). { intro H. subst. contradiction. }
      cbn [fold_right interp_scheduler'].

      rewrite (interp_rule_cmd_wrong sys r act input sigma log a Hstate Hin_rdy Hin_nrdy H_act_neq_a).
      apply IH; try assumption.
  Qed.

  Lemma interp_rule_busy_ready : 
    forall (r: ContextEnv.(env_t) R) sigma,
      r.[tf_ready] = Ob~1 ->
      interp_rule r sigma log_empty (rules rule_busy) = None.
  Proof.
    intros r sigma Hready. unfold rules, interp_rule. unfold interp_action. 
    rewrite Hready. destruct may_read; sauto.
  Qed.

  Lemma interp_rule_busy_not_ready : 
    forall (r: ContextEnv.(env_t) R) sigma,
      r.[tf_ready] = Ob~0 ->
      interp_rule r sigma log_empty (rules rule_busy) = Some (
        log_cons tf_cmd_ack {| kind := LogWrite; port := P0; val := fst (sigma ext_in_cmd (getenv ContextEnv r tf_ready)) |}
          (log_cons tf_ready {| kind := LogRead; port := P0; val := tt |} 
            (log_cons tf_ready {| kind := LogRead; port := P0; val := tt |} 
              log_empty)
          )
        ).
  Proof.
    intros r sigma Hready. unfold rules, interp_rule, interp_action. 
    rewrite Hready. simpl_eq.

    (* prove we may read *)
    set (mr := may_read _ _ _). assert (mr = true). 
    { subst mr. unfold may_read. rewrite !SemanticProperties.log_existsb_empty. sauto. }
    rewrite H. clear H mr.
    
    unfold opt_bind.
    set (cond := Bits.single _). cbn in cond. subst cond. cbv iota.
    
    (* prove we may write *)
    set (mw := may_write _ _ _ _). assert (mw = true). 
    { 
      subst mw. unfold may_write. rewrite !SemanticProperties.log_existsb_app. rewrite !Common.log_existsb_cons. rewrite !SemanticProperties.log_existsb_empty.
      (* hammer *) timeout 10 hauto.
    }
    rewrite H, Hready. reflexivity.
  Qed.
 
  Theorem synthesis_correct :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f)),
      state_matches sys r ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      state_env_matches (tfs_next_cycle sched_ctx act sys input) act input (interp_cycle sigma rules system_schedule r).
  Proof.
    intros sys r act input sigma Hstate Hin_rdy Hin_nrdy.
    
    unfold interp_cycle, interp_scheduler, system_schedule in *.
    cbn [interp_scheduler'].

    (* case destinction on whether hardware is ready or not *)
    destruct (reg_ready_or_not r) as [Hready | Hnotready].
    - specialize (Hin_rdy Hready) as H_in.
      
      (* simplify the busy rule *)
      specialize (interp_rule_busy_ready r sigma Hready) as H_busy_ready. 
      rewrite H_busy_ready. clear H_busy_ready.

      apply synthesis_correct_aux; try assumption.
      (* Show that the log is good *)
      exact log_empty_good_log.

    - specialize (Hin_nrdy Hnotready) as H_in.

      (* simplify the busy rule *)
      specialize (interp_rule_busy_not_ready r sigma Hnotready) as H_busy_not_ready.
      rewrite H_busy_not_ready. clear H_busy_not_ready.

      apply synthesis_correct_aux; try assumption.
      (* Show that the log is good *)
      apply good_log_app; try exact log_empty_good_log.
      apply good_log_cons. apply good_log_cons. apply good_log_cons.
      all: try exact log_empty_good_log; try timeout 10 sauto.
  Qed.

End SynthesisCorrectness.
