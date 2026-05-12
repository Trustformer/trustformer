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
  Opaque tf_sched_ctx.
  
  Local Notation spec_states := (tfs_states (tf_sched_ctx tf_ctx)).
  Opaque tfs_states.
  Local Notation spec_states_fin := (tfs_states_fin (tf_sched_ctx tf_ctx)).
  Opaque tfs_states_fin.
  Local Notation spec_states_size := (tfs_states_size (tf_sched_ctx tf_ctx)).
  Opaque tfs_states_size.
  Local Notation spec_states_t := (tf_states_type spec_states_size).
  Opaque tf_states_type.
  Local Notation spec_states_init := (tfs_states_init (tf_sched_ctx tf_ctx)).
  Opaque tfs_states_init.
  Local Notation spec_all_states := (@finite_elements spec_states spec_states_fin).
  Opaque finite_elements.
  Local Notation spec_state_index := (@finite_index spec_states spec_states_fin).
  Opaque finite_index.
  Local Notation spec_state_num := (Datatypes.length spec_all_states).

  Local Notation spec_inputs := (tfs_inputs (tf_sched_ctx tf_ctx)).
  Opaque tfs_inputs.
  Local Notation spec_inputs_fin := (tfs_inputs_fin (tf_sched_ctx tf_ctx)).
  Opaque tfs_inputs_fin.
  Local Notation spec_inputs_size := (tfs_inputs_size (tf_sched_ctx tf_ctx)).
  Opaque tfs_inputs_size.
  Local Notation spec_inputs_t := (tf_inputs_type spec_inputs_size).
  Opaque tf_inputs_type.
  Local Notation spec_all_inputs := (@finite_elements spec_inputs spec_inputs_fin).
  Opaque finite_elements.
  Local Notation spec_input_index := (@finite_index spec_inputs spec_inputs_fin).
  Opaque finite_index.
  Local Notation spec_input_num := (Datatypes.length spec_all_inputs).

  Local Notation spec_outputs := (tfs_outputs (tf_sched_ctx tf_ctx)).
  Opaque tfs_outputs.
  Local Notation spec_outputs_fin := (tfs_outputs_fin (tf_sched_ctx tf_ctx)).
  Opaque tfs_outputs_fin.
  Local Notation spec_outputs_size := (tfs_outputs_size (tf_sched_ctx tf_ctx)).
  Opaque tfs_outputs_size.
  Local Notation spec_outputs_t := (tf_outputs_type spec_outputs_size).
  Opaque tf_outputs_type.
  Local Notation spec_all_outputs := (@finite_elements spec_outputs spec_outputs_fin).
  Opaque finite_elements.
  Local Notation spec_output_index := (@finite_index spec_outputs spec_outputs_fin).
  Opaque finite_index.
  Local Notation spec_output_num := (Datatypes.length spec_all_outputs).

  Local Notation spec_action := (tfs_action (tf_sched_ctx tf_ctx)).
  Opaque tfs_action.
  Local Notation spec_action_fin := (tfs_action_fin (tf_sched_ctx tf_ctx)).
  Opaque tfs_action_fin.
  Local Notation spec_all_actions := (@finite_elements spec_action spec_action_fin).
  Opaque finite_elements.
  Local Notation spec_action_index := (@finite_index spec_action spec_action_fin).
  Opaque finite_index.
  Local Notation spec_action_num := (Datatypes.length spec_all_actions).

  Local Notation spec_action_reg_size := (tf_action_reg_size tf_ctx).
  Local Notation spec_action_encoding := (tf_action_encoding tf_ctx).
  Opaque tf_action_encoding.
  Local Notation spec_action_encoding_inj := (tf_action_encoding_inj tf_ctx).
  Opaque tf_action_encoding_inj.

  Local Notation spec_schedule := (tfs_schedule (tf_sched_ctx tf_ctx)).
  Local Notation spec_done_state := (tfs_done_signal (tf_sched_ctx tf_ctx)).
  Local Notation spec_reset_states := (tfs_reset_states (tf_sched_ctx tf_ctx)).

  Local Definition spec_schedule_ops_nodup := (tfs_schedule_no_duplicates (tf_sched_ctx tf_ctx)).

  Local Notation reg_t := (@_reg_t spec_states spec_inputs spec_outputs).
  Local Notation reg_t_finite := (@_reg_t_finite tf_ctx).
  Opaque _reg_t_finite.
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

  Ltac extract_match_term_lhs :=
  match goal with
  | |- ?LHS = _ => 
      match LHS with
      | context [match ?X with _ => _ end] =>
          match X with
          | context [match _ with _ => _ end] => 
              fail 1
          | _ => 
              let MT := fresh "MT" in
              let HeqMT := fresh "HeqMT" in
              remember X as MT eqn:HeqMT
          end
      end
  end.

  Ltac extract_match_term_rhs :=
  match goal with
  | |- _ = ?RHS => 
      match RHS with
      | context [match ?X with _ => _ end] =>
          match X with
          | context [match _ with _ => _ end] => 
              fail 1
          | _ => 
              let MT := fresh "MT" in
              let HeqMT := fresh "HeqMT" in
              remember X as MT eqn:HeqMT
          end
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

  Ltac let_to_projs :=
  repeat match goal with
  | |- context [ match ?p with (x, y) => _ end ] =>
      rewrite (surjective_pairing p); simpl
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

  Lemma not_in_reg_cmd_all_states:
    ~ In (tf_cmd (states_var:=spec_states) (inputs_var:=spec_inputs) (outputs_var:=spec_outputs)) (map tf_reg spec_all_states).
  Proof.
    intro. rewrite in_map_iff in H. destruct H as [x [Heq Hin]]. congruence.
  Qed.

  Lemma not_in_reg_cmd_ack_all_states:
    ~ In (tf_cmd_ack (states_var:=spec_states) (inputs_var:=spec_inputs) (outputs_var:=spec_outputs)) (map tf_reg spec_all_states).
  Proof.
    intro. rewrite in_map_iff in H. destruct H as [x [Heq Hin]]. congruence.
  Qed.

  Lemma not_in_reg_ready_all_outputs:
    ~ In (tf_ready (states_var:=spec_states) (inputs_var:=spec_inputs) (outputs_var:=spec_outputs)) (map tf_out spec_all_outputs).
  Proof.
    intro. rewrite in_map_iff in H. destruct H as [x [Heq Hin]]. congruence.
  Qed. 

  Lemma not_in_reg_cmd_all_outputs:
    ~ In (tf_cmd (states_var:=spec_states) (inputs_var:=spec_inputs) (outputs_var:=spec_outputs)) (map tf_out spec_all_outputs).
  Proof.
    intro. rewrite in_map_iff in H. destruct H as [x [Heq Hin]]. congruence.
  Qed.

  Lemma not_in_reg_cmd_ack_all_outputs:
    ~ In (tf_cmd_ack (states_var:=spec_states) (inputs_var:=spec_inputs) (outputs_var:=spec_outputs)) (map tf_out spec_all_outputs).
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

  Lemma not_in_reg_cmd_all_inputs:
    ~ In (tf_cmd (states_var:=spec_states) (inputs_var:=spec_inputs) (outputs_var:=spec_outputs)) (map tf_in spec_all_inputs).
  Proof.
    intro. rewrite in_map_iff in H. destruct H as [x [Heq Hin]]. congruence.
  Qed.

  Lemma not_in_reg_cmd_ack_all_inputs:
    ~ In (tf_cmd_ack (states_var:=spec_states) (inputs_var:=spec_inputs) (outputs_var:=spec_outputs)) (map tf_in spec_all_inputs).
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

  Lemma state_env_matches_comp :
    forall sys act input r1 r2,
      state_equal r1 r2 ->
      env_equal r1 r2 ->
      state_env_matches sys act input r1 <-> state_env_matches sys act input r2.
  Proof.
    intros. 
    unfold state_equal in H. destruct H as [H1 H2].
    unfold env_equal in H0. destruct H0 as [H3 H4].
    unfold state_env_matches, state_matches, env_matches.
    repeat split; sauto.
  Qed.

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

  (* Arguments log_empty : simpl never.
  Arguments log_cons : simpl never. *)
  Opaque log_empty.
  Opaque log_cons.
  Opaque finite_elements.
  Opaque finite_index.

  Section MayReadWrite.

    Local Notation may_read := (may_read (R:=R) (REnv:=REnv) (reg_t:=reg_t)).
    Local Notation may_write := (may_write (R:=R) (REnv:=REnv) (reg_t:=reg_t)).


    Lemma may_read0_implies_may_read1 :
      forall log_r idx,
        may_read log_r P0 idx = true -> may_read log_r P1 idx = true.
    Proof.
      intros log_r idx H. unfold may_read in *. apply andb_prop in H. destruct H as [H_is_write0 H_is_write1]. exact H_is_write1.
    Qed.

    Lemma may_write0_implies_may_write1 :
      forall log_r log_a idx,
        may_write log_r log_a P0 idx = true -> may_write log_r log_a P1 idx = true.
    Proof.
      intros log_r log_a idx H. unfold may_write in *. apply andb_prop in H. destruct H as [H_cons H_is_write1].
      exact H_is_write1.
    Qed.
    
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

    Lemma may_read_log1_cons_neq :
      forall log_r port
             idx1 idx2 entry,
        idx2 <> idx1 ->
        may_read (log_cons idx1 entry log_r) port idx2
        = may_read log_r port idx2.
    Proof.
      intros log_r port idx1 idx2 entry Hneq. destruct entry, kind.
      - unfold may_read. rewrite !(SemanticProperties.log_existsb_log_cons_neq log_r idx2 idx1); try assumption; reflexivity.
      - unfold may_read. rewrite !(SemanticProperties.log_existsb_log_cons_neq log_r idx2 idx1); try assumption; reflexivity.
    Qed.

    Lemma may_read_log1_cons_eq :
      forall log_r prt
             idx entry,
        may_read (log_cons idx entry log_r) prt idx
        = may_read log_r prt idx && 
          match prt with
          | P0 =>
            negb (is_write0 (kind entry) (port entry))
            && negb (is_write1 (kind entry) (port entry))
          | P1 => negb (is_write1 (kind entry) (port entry))
          end.
    Proof.
      intros log_r prt idx entry. destruct entry, kind.
      - unfold may_read. rewrite !(SemanticProperties.log_existsb_log_cons_eq log_r idx).
        destruct prt; simpl; rewrite andb_true_r; reflexivity.
      - unfold may_read. rewrite !(SemanticProperties.log_existsb_log_cons_eq log_r idx).
        destruct prt; simpl.
        + destruct port; simpl; rewrite !andb_false_r; reflexivity.
        + destruct port; simpl; [ rewrite andb_true_r | rewrite andb_false_r ]; reflexivity.
    Qed.

    Lemma may_read_all_log1_cons_neq :
      forall log_r port regs idx entry,
        ~ In idx regs ->
        may_read_all (log_cons idx entry log_r) port regs
        = may_read_all log_r port regs.
    Proof.
      intros log_r port regs idx entry Hnotin.
      unfold may_read_all. apply forallb_pointwise. intros. 
      assert (x <> idx) as Hx_neq.
      { intros Heq. subst x. contradiction. }
      rewrite may_read_log1_cons_neq; try assumption. reflexivity.
    Qed.

    Lemma may_write_log1_cons_neq :
      forall log_r log_a port
             idx1 idx2 entry,
        idx2 <> idx1 ->
        may_write (log_cons idx1 entry log_r) log_a port idx2
        = may_write log_r log_a port idx2.
    Proof.
      intros log_r log_a port idx1 idx2 entry Hneq. destruct entry, kind.
      + unfold may_write. rewrite !SemanticProperties.log_existsb_app.
        rewrite !(SemanticProperties.log_existsb_log_cons_neq log_r idx2 idx1); try assumption; reflexivity.
      + unfold may_write. rewrite !SemanticProperties.log_existsb_app.
        rewrite !(SemanticProperties.log_existsb_log_cons_neq log_r idx2 idx1); try assumption; reflexivity.
    Qed.

    Lemma may_write_log1_cons_eq :
      forall log_r log_a prt
             idx entry,
        may_write (log_cons idx entry log_r) log_a prt idx
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
        rewrite !(SemanticProperties.log_existsb_log_cons_eq log_r idx).
        destruct prt; simpl.
        + destruct port; simpl; [ rewrite andb_true_r | rewrite orb_true_r; rewrite andb_false_r ]; reflexivity.
        + rewrite andb_true_r; reflexivity.
      - unfold may_write. rewrite !SemanticProperties.log_existsb_app.
        rewrite !(SemanticProperties.log_existsb_log_cons_eq log_r idx).
        destruct prt; simpl.
        + destruct port; simpl; rewrite !andb_false_r; rewrite orb_true_r; ring.
        + destruct port; simpl; [ rewrite andb_true_r | rewrite orb_true_r; rewrite andb_false_r ]; reflexivity.
    Qed.

    Lemma may_write_all_log1_cons_neq :
      forall log_r log_a port regs
             idx entry,
        ~ In idx regs ->
        may_write_all (log_cons idx entry log_r) log_a port regs
        = may_write_all log_r log_a port regs.
    Proof.
      intros log_r log_a port regs idx entry Hnotin.
      unfold may_write_all. apply forallb_pointwise. intros.
      assert (x <> idx) as Hx_neq.
      { intros Heq. subst x. contradiction. }
      rewrite may_write_log1_cons_neq; try assumption. reflexivity.
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

    Section MayReadWriteLogEmpty.

      Lemma may_read_log_empty :
        forall port idx,
          may_read log_empty port idx = true.
      Proof. intros. unfold may_read. rewrite !SemanticProperties.log_existsb_empty. sauto. Qed.

      Lemma may_write_log_empty :
        forall port idx,
          may_write log_empty log_empty port idx = true.
      Proof. intros. unfold may_write. rewrite !SemanticProperties.log_existsb_app. rewrite !SemanticProperties.log_existsb_empty. sauto. Qed.

      Lemma may_read_all_log_empty :
        forall port regs,
          may_read_all log_empty port regs = true.
      Proof. intros. unfold may_read_all. rewrite forallb_forall. intros. apply may_read_log_empty. Qed.

      Lemma may_write_all_log_empty :
        forall port regs,
          may_write_all log_empty log_empty port regs = true.
      Proof. intros. unfold may_write_all. rewrite forallb_forall. intros. apply may_write_log_empty. Qed.

    End MayReadWriteLogEmpty.

    Section MayReadWriteOne.

      Lemma may_read_all_one_state :
        forall log port r,
          may_read_all log port (map tf_reg spec_all_states) = true ->
          may_read log port (tf_reg r) = true.
      Proof.
        intros log port r H. unfold may_read_all in H. rewrite forallb_forall in H. apply H. apply in_map. apply in_spec_all_states.
      Qed.

      Lemma may_read_all_one_output :
        forall log port o,
          may_read_all log port (map tf_out spec_all_outputs) = true ->
          may_read log port (tf_out o) = true.
      Proof.
        intros log port o H. unfold may_read_all in H. rewrite forallb_forall in H. apply H. apply in_map. apply in_spec_all_outputs.
      Qed.

      Lemma may_read_all_one_input :
        forall log port i,
          may_read_all log port (map tf_in spec_all_inputs) = true ->
          may_read log port (tf_in i) = true.
      Proof.
        intros log port i H. unfold may_read_all in H. rewrite forallb_forall in H. apply H. apply in_map. apply in_spec_all_inputs.
      Qed.
      
      Lemma may_write_all_one_state :
        forall log1 log2 port r,
          may_write_all log1 log2 port (map tf_reg spec_all_states) = true ->
          may_write log1 log2 port (tf_reg r) = true.
      Proof.
        intros log1 log2 port r H. unfold may_write_all in H. rewrite forallb_forall in H. apply H. apply in_map. apply in_spec_all_states.
      Qed.

      Lemma may_write_all_one_output :
        forall log1 log2 port o,
          may_write_all log1 log2 port (map tf_out spec_all_outputs) = true ->
          may_write log1 log2 port (tf_out o) = true.
      Proof.
        intros log1 log2 port o H. unfold may_write_all in H. rewrite forallb_forall in H. apply H. apply in_map. apply in_spec_all_outputs.
      Qed.

      Lemma may_write_all_one_input :
        forall log1 log2 port i,
          may_write_all log1 log2 port (map tf_in spec_all_inputs) = true ->
          may_write log1 log2 port (tf_in i) = true.
      Proof.
        intros log1 log2 port i H. unfold may_write_all in H. rewrite forallb_forall in H. apply H. apply in_map. apply in_spec_all_inputs.
      Qed.

    End MayReadWriteOne.

  End MayReadWrite.

  Opaque may_read.
  Opaque may_write.
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
    Qed.

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

  Definition inputs_are_buffered (input: input_t) (r: ContextEnv.(env_t) R) log :=
    forall v, 
      latest_write0 (REnv:=REnv) (R:=R) log (tf_in v) = Some (input v) 
      \/ 
      latest_write0 (REnv:=REnv) (R:=R) log (tf_in v) = None /\ r.[tf_in v] = input v.

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
                let (val_cmp_src1, log_cmp_src1) := (eval_expr_aux (szB:=szC) src1 log sys_state input) in
                let (val_cmp_src2, log_cmp_src2) := (eval_expr_aux (szB:=szC) src2 log_cmp_src1 sys_state input) in
                (
                  match cmp_op with
                  | tf_eq =>
                      if beq_dec val_cmp_src1 val_cmp_src2 then convert (Bits.of_nat 1 1) else convert (Bits.of_nat 1 0)
                  | tf_neq =>
                      if beq_dec val_cmp_src1 val_cmp_src2 then convert (Bits.of_nat 1 0) else convert (Bits.of_nat 1 1)
                  | tf_lt =>
                      if Bits.unsigned_lt val_cmp_src1 val_cmp_src2 then convert (Bits.of_nat 1 1) else convert (Bits.of_nat 1 0)
                  | tf_le =>
                      if Bits.unsigned_le val_cmp_src1 val_cmp_src2 then convert (Bits.of_nat 1 1) else convert (Bits.of_nat 1 0)
                  | tf_gt =>
                      if Bits.unsigned_gt val_cmp_src1 val_cmp_src2 then convert (Bits.of_nat 1 1) else convert (Bits.of_nat 1 0)
                  | tf_ge =>
                      if Bits.unsigned_ge val_cmp_src1 val_cmp_src2 then convert (Bits.of_nat 1 1) else convert (Bits.of_nat 1 0)
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

  Lemma fst_eval_expr_aux_eq_tf_eval_expr:
    forall expr log1 sys input szB,
      fst (eval_expr_aux (szB:=szB) expr log1 sys input) = tf_eval_expr (szB:=szB) spec_states_size spec_inputs_size spec_outputs_size expr sys input.
  Proof.
    intros expr log1 sys input szB.

    generalize dependent szB.
    generalize dependent log1.
    induction expr; intros log1 szB; try reflexivity.
    - cbn. destruct op. rewrite Common.fst_let_repackage. f_equal.
      apply IHexpr.
    - cbn. destruct op.
      + let_to_projs. f_equal. f_equal. 
        * apply IHexpr1.
        * apply IHexpr2.
      + let_to_projs. f_equal. f_equal. 
        * apply IHexpr1.
        * apply IHexpr2.
      + let_to_projs. f_equal. f_equal. 
        * apply IHexpr1.
        * apply IHexpr2.
      + let_to_projs. f_equal. f_equal. 
        * apply IHexpr1.
        * apply IHexpr2.
      + let_to_projs. f_equal. f_equal.
        * apply IHexpr1.
        * apply IHexpr2.
      + let_to_projs. f_equal. f_equal.
        * apply IHexpr1.
        * apply IHexpr2.
      + let_to_projs. destr; match_eq; f_equal; try apply IHexpr1; try apply IHexpr2.
    - cbn. let_to_projs. extract_match_term_lhs. extract_match_term_rhs.
      assert (MT = MT0). 2: { rewrite H. subst. destr; try apply IHexpr2; try apply IHexpr3. }
      subst. f_equal. apply (IHexpr1 log1 1).
  Qed.

  Lemma snd_eval_expr_aux_log_irrelevant:
    forall expr log1 log2 sys input szB,
      fst (eval_expr_aux (szB:=szB) expr log1 sys input) = fst (eval_expr_aux (szB:=szB) expr log2 sys input).
  Proof.
    intros expr log1 log2 sys input szB.

    generalize dependent szB.
    generalize dependent log2.
    generalize dependent log1.
    induction expr; intros log1 log2 szB; try reflexivity.
    - cbn.
      pose proof (IHexpr log1 log2 szB). 
      destruct (eval_expr_aux expr log1 sys input).
      destruct (eval_expr_aux expr log2 sys input).
      cbn in *. subst. reflexivity.
    - destruct op.
      + cbn.
        pose proof (IHexpr1 log1 log2 szB).
        destruct (eval_expr_aux expr1 log1 sys input). cbn in *. subst.
        destruct (eval_expr_aux expr1 log2 sys input). cbn in *. subst.
        pose proof (IHexpr2 l l0 szB).
        destruct (eval_expr_aux expr2 l sys input). cbn in *. subst.
        destruct (eval_expr_aux expr2 l0 sys input). cbn in *. subst. reflexivity.
      + cbn.
        pose proof (IHexpr1 log1 log2 szB).
        destruct (eval_expr_aux expr1 log1 sys input). cbn in *. subst.
        destruct (eval_expr_aux expr1 log2 sys input). cbn in *. subst.
        pose proof (IHexpr2 l l0 szB).
        destruct (eval_expr_aux expr2 l sys input). cbn in *. subst.
        destruct (eval_expr_aux expr2 l0 sys input). cbn in *. subst. reflexivity.
      + cbn.
        pose proof (IHexpr1 log1 log2 szB).
        destruct (eval_expr_aux expr1 log1 sys input). cbn in *. subst.
        destruct (eval_expr_aux expr1 log2 sys input). cbn in *. subst.
        pose proof (IHexpr2 l l0 szB).
        destruct (eval_expr_aux expr2 l sys input). cbn in *. subst.
        destruct (eval_expr_aux expr2 l0 sys input). cbn in *. subst. reflexivity.
      + cbn.
        pose proof (IHexpr1 log1 log2 szB).
        destruct (eval_expr_aux expr1 log1 sys input). cbn in *. subst.
        destruct (eval_expr_aux expr1 log2 sys input). cbn in *. subst.
        pose proof (IHexpr2 l l0 szB).
        destruct (eval_expr_aux expr2 l sys input). cbn in *. subst.
        destruct (eval_expr_aux expr2 l0 sys input). cbn in *. subst. reflexivity.
      + cbn.
        pose proof (IHexpr1 log1 log2 szB).
        destruct (eval_expr_aux expr1 log1 sys input). cbn in *. subst.
        destruct (eval_expr_aux expr1 log2 sys input). cbn in *. subst.
        pose proof (IHexpr2 l l0 szB).
        destruct (eval_expr_aux expr2 l sys input). cbn in *. subst.
        destruct (eval_expr_aux expr2 l0 sys input). cbn in *. subst. reflexivity.
      + cbn.
        pose proof (IHexpr1 log1 log2 szB).
        destruct (eval_expr_aux expr1 log1 sys input). cbn in *. subst.
        destruct (eval_expr_aux expr1 log2 sys input). cbn in *. subst.
        pose proof (IHexpr2 l l0 szB).
        destruct (eval_expr_aux expr2 l sys input). cbn in *. subst.
        destruct (eval_expr_aux expr2 l0 sys input). cbn in *. subst. reflexivity.
      + cbn.
        pose proof (IHexpr1 log1 log2 szB).
        destruct (eval_expr_aux expr1 log1 sys input). cbn in *. subst.
        destruct (eval_expr_aux expr1 log2 sys input). cbn in *. subst.
        pose proof (IHexpr2 l l0 szB).
        destruct (eval_expr_aux expr2 l sys input). cbn in *. subst.
        destruct (eval_expr_aux expr2 l0 sys input). cbn in *. subst.
        pose proof (IHexpr1 log1 log2 cmp_sz).
        destruct (eval_expr_aux expr1 log1 sys input). cbn in *. subst.
        destruct (eval_expr_aux expr1 log2 sys input). cbn in *. subst.
        pose proof (IHexpr2 l3 l4 cmp_sz).
        destruct (eval_expr_aux expr2 l3 sys input). cbn in *. subst.
        destruct (eval_expr_aux expr2 l4 sys input). cbn in *. subst. reflexivity.
    - cbn.
      pose proof (IHexpr1 log1 log2 1).
      destruct (eval_expr_aux expr1 log1 sys input). cbn in *. subst.
      destruct (eval_expr_aux expr1 log2 sys input). cbn in *. subst.
      destr. 
      + apply IHexpr3.
      + apply IHexpr2.
  Qed.

  Lemma snd_eval_expr_aux_app_log:
    forall expr log1 log2 sys input szB,
      snd (eval_expr_aux (szB:=szB) expr log1 sys input) ++ log2 = snd (eval_expr_aux (szB:=szB) expr (log1 ++ log2) sys input).
  Proof.
    intros expr log1 log2 sys input szB.

    generalize dependent szB.
    generalize dependent log2.
    generalize dependent log1.
    induction expr; intros log1 log2 szB; try reflexivity.
    - cbn.
      pose proof (IHexpr log1 log2 szB). 
      destruct (eval_expr_aux expr log1 sys input).
      destruct (eval_expr_aux expr (log1 ++ log2) sys input).
      cbn in *. subst. reflexivity.
    - destruct op.
      + cbn.
        pose proof (IHexpr1 log1 log2 szB).
        destruct (eval_expr_aux expr1 (log1 ++ log2) sys input). cbn in *. subst.
        destruct (eval_expr_aux expr1 log1 sys input). cbn in *. subst.
        pose proof (IHexpr2 l log2 szB).
        destruct (eval_expr_aux expr2 (l ++ log2) sys input). cbn in *. subst.
        destruct (eval_expr_aux expr2 l sys input). cbn in *. reflexivity.
      + cbn.
        pose proof (IHexpr1 log1 log2 szB).
        destruct (eval_expr_aux expr1 (log1 ++ log2) sys input). cbn in *. subst.
        destruct (eval_expr_aux expr1 log1 sys input). cbn in *. subst.
        pose proof (IHexpr2 l log2 szB).
        destruct (eval_expr_aux expr2 (l ++ log2) sys input). cbn in *. subst.
        destruct (eval_expr_aux expr2 l sys input). cbn in *. reflexivity.
      + cbn.
        pose proof (IHexpr1 log1 log2 szB).
        destruct (eval_expr_aux expr1 (log1 ++ log2) sys input). cbn in *. subst.
        destruct (eval_expr_aux expr1 log1 sys input). cbn in *. subst.
        pose proof (IHexpr2 l log2 szB).
        destruct (eval_expr_aux expr2 (l ++ log2) sys input). cbn in *. subst.
        destruct (eval_expr_aux expr2 l sys input). cbn in *. reflexivity.
      + cbn.
        pose proof (IHexpr1 log1 log2 szB).
        destruct (eval_expr_aux expr1 (log1 ++ log2) sys input). cbn in *. subst.
        destruct (eval_expr_aux expr1 log1 sys input). cbn in *. subst.
        pose proof (IHexpr2 l log2 szB).
        destruct (eval_expr_aux expr2 (l ++ log2) sys input). cbn in *. subst.
        destruct (eval_expr_aux expr2 l sys input). cbn in *. reflexivity.
      + cbn.
        pose proof (IHexpr1 log1 log2 szB).
        destruct (eval_expr_aux expr1 (log1 ++ log2) sys input). cbn in *. subst.
        destruct (eval_expr_aux expr1 log1 sys input). cbn in *. subst.
        pose proof (IHexpr2 l log2 szB).
        destruct (eval_expr_aux expr2 (l ++ log2) sys input). cbn in *. subst.
        destruct (eval_expr_aux expr2 l sys input). cbn in *. reflexivity.
      + cbn.
        pose proof (IHexpr1 log1 log2 szB).
        destruct (eval_expr_aux expr1 (log1 ++ log2) sys input). cbn in *. subst.
        destruct (eval_expr_aux expr1 log1 sys input). cbn in *. subst.
        pose proof (IHexpr2 l log2 szB).
        destruct (eval_expr_aux expr2 (l ++ log2) sys input). cbn in *. subst.
        destruct (eval_expr_aux expr2 l sys input). cbn in *. reflexivity.
      + cbn.
        pose proof (IHexpr1 log1 log2 szB).
        destruct (eval_expr_aux expr1 (log1 ++ log2) sys input). cbn in *. subst.
        destruct (eval_expr_aux expr1 log1 sys input). cbn in *. subst.
        pose proof (IHexpr2 l log2 szB).
        destruct (eval_expr_aux expr2 (l ++ log2) sys input). cbn in *. subst.
        destruct (eval_expr_aux expr2 l sys input). cbn in *. subst.
        pose proof (IHexpr1 log1 log2 cmp_sz). 
        destruct (eval_expr_aux expr1 (log1 ++ log2) sys input). cbn in *. subst. 
        destruct (eval_expr_aux expr1 log1 sys input). cbn in *. subst.
        pose proof (IHexpr2 l1 log2 cmp_sz).
        destruct (eval_expr_aux expr2 (l1 ++ log2) sys input). cbn in *. subst.
        destruct (eval_expr_aux expr2 l1 sys input). cbn in *. subst. reflexivity.
    - cbn.
      pose proof (IHexpr1 log1 log2 1).
      pose proof (snd_eval_expr_aux_log_irrelevant expr1 log1 (log1 ++ log2) sys input 1).
      destruct (eval_expr_aux expr1 (log1 ++ log2) sys input). cbn in *. subst.
      destruct (eval_expr_aux expr1 log1 sys input). cbn in *. subst.
      destr.
  Qed.
    
  Lemma snd_eval_expr_aux_app:
    forall expr1 expr2 sys input szB1 szB2,
      (snd (eval_expr_aux (szB:=szB2) expr2 [] sys input) ++ snd (eval_expr_aux (szB:=szB1) expr1 [] sys input))
      =
      snd (let (_, log_src1) := eval_expr_aux (szB:=szB1) expr1 [] sys input in eval_expr_aux (szB:=szB2) expr2 log_src1 sys input).
  Proof.
    intros expr1 expr2 sys input szB1 szB2.

    generalize dependent szB2.
    generalize dependent szB1.
    induction expr2; intros szB1 szB2; try (destruct (eval_expr_aux expr1 [] sys input) as [val1 log1] eqn:Heval1; reflexivity).
    - destruct op. cbn.
      pose proof (IHexpr2 szB1 szB2).
      destruct (eval_expr_aux expr1 [] sys input).
      destruct (eval_expr_aux expr2 [] sys input).
      destruct (eval_expr_aux expr2 l sys input).
      cbn in *. subst. reflexivity.
    - destruct op.
      + cbn in *. 
        pose proof (IHexpr2_1 szB1 szB2).
        destruct (eval_expr_aux expr1 [] sys input).
        destruct (eval_expr_aux expr2_1 [] sys input). 
        destruct (eval_expr_aux expr2_1 l sys input). 
        cbn in *. subst. 
        destruct (eval_expr_aux expr2_2 l0 sys input) eqn:Eq1.
        destruct (eval_expr_aux expr2_2 (l0 ++ l) sys input) eqn:Eq2.
        apply (f_equal snd) in Eq1.
        apply (f_equal snd) in Eq2.
        cbn in *. subst. apply snd_eval_expr_aux_app_log.
      + cbn in *. 
        pose proof (IHexpr2_1 szB1 szB2).
        destruct (eval_expr_aux expr1 [] sys input).
        destruct (eval_expr_aux expr2_1 [] sys input). 
        destruct (eval_expr_aux expr2_1 l sys input). 
        cbn in *. subst. 
        destruct (eval_expr_aux expr2_2 l0 sys input) eqn:Eq1.
        destruct (eval_expr_aux expr2_2 (l0 ++ l) sys input) eqn:Eq2.
        apply (f_equal snd) in Eq1.
        apply (f_equal snd) in Eq2.
        cbn in *. subst. apply snd_eval_expr_aux_app_log.
      + cbn in *. 
        pose proof (IHexpr2_1 szB1 szB2).
        destruct (eval_expr_aux expr1 [] sys input).
        destruct (eval_expr_aux expr2_1 [] sys input). 
        destruct (eval_expr_aux expr2_1 l sys input). 
        cbn in *. subst. 
        destruct (eval_expr_aux expr2_2 l0 sys input) eqn:Eq1.
        destruct (eval_expr_aux expr2_2 (l0 ++ l) sys input) eqn:Eq2.
        apply (f_equal snd) in Eq1.
        apply (f_equal snd) in Eq2.
        cbn in *. subst. apply snd_eval_expr_aux_app_log.
      + cbn in *. 
        pose proof (IHexpr2_1 szB1 szB2).
        destruct (eval_expr_aux expr1 [] sys input).
        destruct (eval_expr_aux expr2_1 [] sys input). 
        destruct (eval_expr_aux expr2_1 l sys input). 
        cbn in *. subst. 
        destruct (eval_expr_aux expr2_2 l0 sys input) eqn:Eq1.
        destruct (eval_expr_aux expr2_2 (l0 ++ l) sys input) eqn:Eq2.
        apply (f_equal snd) in Eq1.
        apply (f_equal snd) in Eq2.
        cbn in *. subst. apply snd_eval_expr_aux_app_log.
      + cbn in *. 
        pose proof (IHexpr2_1 szB1 szB2).
        destruct (eval_expr_aux expr1 [] sys input).
        destruct (eval_expr_aux expr2_1 [] sys input). 
        destruct (eval_expr_aux expr2_1 l sys input). 
        cbn in *. subst. 
        destruct (eval_expr_aux expr2_2 l0 sys input) eqn:Eq1.
        destruct (eval_expr_aux expr2_2 (l0 ++ l) sys input) eqn:Eq2.
        apply (f_equal snd) in Eq1.
        apply (f_equal snd) in Eq2.
        cbn in *. subst. apply snd_eval_expr_aux_app_log.
      + cbn in *. 
        pose proof (IHexpr2_1 szB1 szB2).
        destruct (eval_expr_aux expr1 [] sys input).
        destruct (eval_expr_aux expr2_1 [] sys input). 
        destruct (eval_expr_aux expr2_1 l sys input). 
        cbn in *. subst. 
        destruct (eval_expr_aux expr2_2 l0 sys input) eqn:Eq1.
        destruct (eval_expr_aux expr2_2 (l0 ++ l) sys input) eqn:Eq2.
        apply (f_equal snd) in Eq1.
        apply (f_equal snd) in Eq2.
        cbn in *. subst. apply snd_eval_expr_aux_app_log.
      + cbn in *. 
        pose proof (IHexpr2_1 szB1 szB2).
        pose proof (IHexpr2_1 szB1 cmp_sz).
        destruct (eval_expr_aux expr1 [] sys input).
        destruct (eval_expr_aux expr2_1 [] sys input). 
        destruct (eval_expr_aux expr2_1 l sys input). 
        cbn in *. subst. 
        destruct (eval_expr_aux expr2_2 l0 sys input) eqn:Eq1.
        destruct (eval_expr_aux expr2_2 (l0 ++ l) sys input) eqn:Eq2.
        destruct (eval_expr_aux expr2_1 [] sys input). 
        destruct (eval_expr_aux expr2_1 l sys input). 
        cbn in *. subst. 
        destruct (eval_expr_aux expr2_2 l3 sys input) eqn:Eq5.
        destruct (eval_expr_aux expr2_2 (l3 ++ l) sys input) eqn:Eq6.
        apply (f_equal snd) in Eq1.
        apply (f_equal snd) in Eq2.
        apply (f_equal snd) in Eq5.
        apply (f_equal snd) in Eq6.
        cbn in *. subst.
        apply (snd_eval_expr_aux_app_log expr2_2 _ l sys input). 
    - cbn.
      pose proof (IHexpr2_2 szB1 szB2).
      pose proof (IHexpr2_3 szB1 szB2).
      destruct (eval_expr_aux expr1 [] sys input).
      pose proof (snd_eval_expr_aux_log_irrelevant expr2_1 [] l sys input 1).
      destruct (eval_expr_aux expr2_1 [] sys input) eqn:Eq1.
      destruct (eval_expr_aux expr2_1 l sys input) eqn:Eq2.
      destruct (eval_expr_aux expr2_2 [] sys input) eqn:Eq3.
      destruct (eval_expr_aux expr2_2 l sys input) eqn:Eq4.
      destruct (eval_expr_aux expr2_3 [] sys input) eqn:Eq5.
      destruct (eval_expr_aux expr2_3 l sys input) eqn:Eq6.
      apply (f_equal snd) in Eq1.
      apply (f_equal snd) in Eq2.
      apply (f_equal snd) in Eq3.
      apply (f_equal snd) in Eq4.
      apply (f_equal snd) in Eq5.
      apply (f_equal snd) in Eq6.
      cbn in *. subst. destr.
      * rewrite (snd_eval_expr_aux_app_log expr2_3 _ l sys input szB2). f_equal. f_equal.
        rewrite (snd_eval_expr_aux_app_log expr2_1 _ l sys input 1). reflexivity.
      * rewrite (snd_eval_expr_aux_app_log expr2_2 _ l sys input szB2). f_equal. f_equal.
        rewrite (snd_eval_expr_aux_app_log expr2_1 _ l sys input 1). reflexivity.
  Qed. 

  Lemma snd_eval_expr_aux_app2:
    forall expr1 expr2 sys input szB1 szB2,
      (snd (eval_expr_aux (szB:=szB2) expr2 [] sys input) ++ snd (eval_expr_aux (szB:=szB1) expr1 [] sys input))
      =
      snd (eval_expr_aux (szB:=szB2) expr2 (snd (eval_expr_aux (szB:=szB1) expr1 [] sys input)) sys input).
  Proof.
    intros expr1 expr2 sys input szB1 szB2.
    rewrite snd_eval_expr_aux_app. 
    destruct (eval_expr_aux expr1 [] sys input) as [val1 log1] eqn:Heval1.
    apply (f_equal snd) in Heval1. cbn in Heval1. subst log1. 
    reflexivity.
  Qed.

  Definition expr_log (expr: tf_expr) (szB: nat) (sys_state: sys_state_t) (input: input_t) log :=
    fold_right (fun reg acc => log_cons (R:=R) (REnv:=REnv) reg {| kind := LogRead; port := match reg with
                                                   | tf_in v => P1
                                                   | _ => P0
                                                   end; val := tt |} acc ) log (snd (eval_expr_aux (szB:=szB) expr [] sys_state input)).
   
  Lemma latest_write0_expr_log :
    forall expr szB sys input log_a v,
      latest_write0 (expr_log expr szB sys input log_a) (tf_in v) =
      latest_write0 log_a (tf_in v).
  Proof.
    intros expr szB sys input log_a v.

    unfold expr_log.
    induction ((snd (eval_expr_aux expr [] sys input))).
    - reflexivity.
    - destruct (eq_dec (tf_in v) a) as [Heq | Hneq]; subst.
      + simpl. rewrite SemanticProperties.latest_write0_cons_eq. exact IHl.
      + simpl. rewrite SemanticProperties.latest_write0_cons_neq; try assumption.
  Qed.

  Lemma inputs_are_buffered_expr_log :
    forall input r log_a log_r expr szB sys,
      inputs_are_buffered input r (log_app log_a log_r) ->
      inputs_are_buffered input r (log_app (expr_log expr szB sys input log_a) log_r).
  Proof.
    intros input r log_a log_r expr szB sys Hlatest.
    unfold inputs_are_buffered in *. intros v. specialize (Hlatest v).
    rewrite SemanticProperties.latest_write0_app in *.
    rewrite latest_write0_expr_log. exact Hlatest.
  Qed.

  Lemma interp_synth_convert :
    forall r sigma log_r log_a szA szB (expr : action R Sigma _ (bits_t szA)),
      interp_action (R:=R) (REnv:=REnv) r sigma CtxEmpty log_r log_a (synth_convert (in_var_size := szA) tf_ctx szB expr) = 
      match 
        interp_action (R:=R) (REnv:=REnv) r sigma CtxEmpty log_r log_a expr 
      return option (Log R REnv * bits_t szB * _) with
      | Some (l, v, g) => Some (l, convert (szB:=szB) v, g)
      | None => None
      end.
  Proof.
    intros r sigma log_r log_a szA szB expr.

    unfold synth_convert, convert.
    destruct (eq_dec szA szB) as [Heq | Hneq]; subst.
    - sauto.
    - cbn. unfold opt_bind. reflexivity.
  (* Timeout 600 Time Qed.  *)
  Admitted. (* SPEEDUP *)
  (* ??? seconds *)

  Lemma interp_action_expr :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log_r log_a expr dst_sz,
      state_matches sys r ->
      may_read_all log_r P0 (map tf_reg spec_all_states) = true ->
      may_read_all log_r P1 (map tf_in spec_all_inputs) = true ->
      may_read_all log_r P0 (map tf_out spec_all_outputs) = true ->
      inputs_are_buffered input r (log_app log_a log_r) ->
      interp_action r sigma CtxEmpty log_r log_a (expr_to_action tf_ctx expr dst_sz)
      = Some (
          expr_log expr dst_sz sys input log_a, 
          tf_eval_expr (szB:=dst_sz) spec_states_size spec_inputs_size spec_outputs_size expr sys input, 
          CtxEmpty
        ).
  Proof.
    intros sys r act input sigma log_r log_a expr dst_sz.
    intros Hstate Hrd0_st Hrd1_in Hrd0_out.

    unfold state_matches in Hstate. destruct Hstate as [Hstate_r Hstate_out].

    generalize dependent dst_sz.
    generalize dependent log_a.
    induction expr; intros log_a dst_sz Hin_buf.
    + (* Const *)
      reflexivity.
    + (* Var *)
      cbn. rewrite interp_synth_convert.
      rewrite interp_action_read0 with (idx:=(tf_reg v)).
      * rewrite Hstate_r. reflexivity.
      * apply may_read_all_one_state. exact Hrd0_st.
    + (* Input *)
      cbn. rewrite interp_synth_convert.
      cbn [interp_action]. rewrite may_read_all_one_input with (i:=v); try assumption.
      unfold inputs_are_buffered, inputs_are_buffered in Hin_buf. specialize (Hin_buf v).
      destruct Hin_buf.
      * rewrite H. reflexivity.
      * destruct H as [H1 H2]. rewrite H1. rewrite H2. reflexivity. 
    + (* Output *)
      cbn. rewrite interp_synth_convert.
      rewrite interp_action_read0 with (idx:=(tf_out v)).
      * rewrite Hstate_out. reflexivity.
      * apply may_read_all_one_output. exact Hrd0_out.
    + (* Op1 *)
      cbn. unfold opt_bind. rewrite IHexpr; try assumption.
      destruct op; simpl. unfold Bits.neg. f_equal. f_equal. f_equal.
      unfold expr_log. simpl. destruct (eval_expr_aux expr [] sys input) as [val log_expr]. reflexivity.
    + (* Op2 *)
      destruct op.
      - cbn. unfold opt_bind. rewrite IHexpr1; clear IHexpr1; try assumption. rewrite IHexpr2; clear IHexpr2.
        * f_equal. f_equal. f_equal.
          unfold expr_log. rewrite <- fold_right_app. simpl. f_equal.
          destruct (eval_expr_aux expr1 [] sys input) as [val1 log_expr1] eqn:Eq1. 
          destruct (eval_expr_aux expr2 log_expr1 sys input) as [val2 log_expr2] eqn:Eq2.
          apply (f_equal snd) in Eq1. apply (f_equal snd) in Eq2. cbn in *. subst.
          apply snd_eval_expr_aux_app2.
        * apply inputs_are_buffered_expr_log. exact Hin_buf.
      - cbn. unfold opt_bind. rewrite IHexpr1; clear IHexpr1; try assumption. rewrite IHexpr2; clear IHexpr2.
        * f_equal. f_equal. f_equal.
          unfold expr_log. rewrite <- fold_right_app. simpl. f_equal.
          destruct (eval_expr_aux expr1 [] sys input) as [val1 log_expr1] eqn:Eq1. 
          destruct (eval_expr_aux expr2 log_expr1 sys input) as [val2 log_expr2] eqn:Eq2.
          apply (f_equal snd) in Eq1. apply (f_equal snd) in Eq2. cbn in *. subst.
          apply snd_eval_expr_aux_app2.
        * apply inputs_are_buffered_expr_log. exact Hin_buf.
      - cbn. unfold opt_bind. rewrite IHexpr1; clear IHexpr1; try assumption. rewrite IHexpr2; clear IHexpr2.
        * f_equal. f_equal. f_equal.
          unfold expr_log. rewrite <- fold_right_app. simpl. f_equal.
          destruct (eval_expr_aux expr1 [] sys input) as [val1 log_expr1] eqn:Eq1. 
          destruct (eval_expr_aux expr2 log_expr1 sys input) as [val2 log_expr2] eqn:Eq2.
          apply (f_equal snd) in Eq1. apply (f_equal snd) in Eq2. cbn in *. subst.
          apply snd_eval_expr_aux_app2.
        * apply inputs_are_buffered_expr_log. exact Hin_buf.
      - cbn. unfold opt_bind. rewrite IHexpr1; clear IHexpr1; try assumption. rewrite IHexpr2; clear IHexpr2.
        * f_equal. f_equal. f_equal.
          unfold expr_log. rewrite <- fold_right_app. simpl. f_equal.
          destruct (eval_expr_aux expr1 [] sys input) as [val1 log_expr1] eqn:Eq1. 
          destruct (eval_expr_aux expr2 log_expr1 sys input) as [val2 log_expr2] eqn:Eq2.
          apply (f_equal snd) in Eq1. apply (f_equal snd) in Eq2. cbn in *. subst.
          apply snd_eval_expr_aux_app2.
        * apply inputs_are_buffered_expr_log. exact Hin_buf.
      - cbn. unfold opt_bind. rewrite IHexpr1; clear IHexpr1; try assumption. rewrite IHexpr2; clear IHexpr2.
        * f_equal. f_equal. f_equal.
          unfold expr_log. rewrite <- fold_right_app. simpl. f_equal.
          destruct (eval_expr_aux expr1 [] sys input) as [val1 log_expr1] eqn:Eq1. 
          destruct (eval_expr_aux expr2 log_expr1 sys input) as [val2 log_expr2] eqn:Eq2.
          apply (f_equal snd) in Eq1. apply (f_equal snd) in Eq2. cbn in *. subst.
          apply snd_eval_expr_aux_app2.
        * apply inputs_are_buffered_expr_log. exact Hin_buf.
      - cbn. rewrite interp_synth_convert.
        cbn. rewrite IHexpr1; clear IHexpr1; try assumption. cbn. rewrite IHexpr2; clear IHexpr2.
        * cbn. f_equal. f_equal. f_equal.
          unfold expr_log. rewrite <- fold_right_app. simpl. f_equal.
          destruct (eval_expr_aux expr1 [] sys input) as [val1 log_expr1] eqn:Eq1. 
          destruct (eval_expr_aux expr2 log_expr1 sys input) as [val2 log_expr2] eqn:Eq2.
          apply (f_equal snd) in Eq1. apply (f_equal snd) in Eq2. cbn in *. subst.
          apply snd_eval_expr_aux_app2.
        * apply inputs_are_buffered_expr_log. exact Hin_buf.
      - cbn.
        destruct cmp_op.
        * rewrite interp_synth_convert.
          cbn. rewrite IHexpr1; clear IHexpr1; try assumption. cbn. rewrite IHexpr2; clear IHexpr2.
          ** cbn. f_equal. f_equal. f_equal.
            ++ unfold expr_log. rewrite <- fold_right_app. simpl. f_equal.
              destruct (eval_expr_aux expr1 [] sys input) as [val1 log_expr1] eqn:Eq1. 
              destruct (eval_expr_aux expr2 log_expr1 sys input) as [val2 log_expr2] eqn:Eq2.
              apply (f_equal snd) in Eq1. apply (f_equal snd) in Eq2. cbn in *. subst.
              set (x1 := eval_expr_aux expr1 [] sys input) at 2. destruct x1.
              destruct (eval_expr_aux expr2 l sys input). cbn in *. 
              apply snd_eval_expr_aux_app2.
            ++ unfold BitFuns._eq. destr. 
              -- f_equal. apply beq_dec_iff in Heqb. rewrite Heqb. rewrite beq_dec_refl. reflexivity.
              -- f_equal. f_equal. assumption.  
          ** apply inputs_are_buffered_expr_log. exact Hin_buf.
        * rewrite interp_synth_convert.
          cbn. rewrite IHexpr1; clear IHexpr1; try assumption. cbn. rewrite IHexpr2; clear IHexpr2.
          ** cbn. f_equal. f_equal. f_equal.
            ++ unfold expr_log. rewrite <- fold_right_app. simpl. f_equal.
              destruct (eval_expr_aux expr1 [] sys input) as [val1 log_expr1] eqn:Eq1. 
              destruct (eval_expr_aux expr2 log_expr1 sys input) as [val2 log_expr2] eqn:Eq2.
              apply (f_equal snd) in Eq1. apply (f_equal snd) in Eq2. cbn in *. subst.
              set (x1 := eval_expr_aux expr1 [] sys input) at 2. destruct x1.
              destruct (eval_expr_aux expr2 l sys input). cbn in *. 
              apply snd_eval_expr_aux_app2.
            ++ unfold BitFuns._neq. destr. 
              -- f_equal. apply beq_dec_iff in Heqb. rewrite Heqb. rewrite beq_dec_refl. reflexivity.
              -- f_equal. f_equal. rewrite negb_true_iff. assumption.  
          ** apply inputs_are_buffered_expr_log. exact Hin_buf.
        * rewrite interp_synth_convert.
          cbn. rewrite IHexpr1; clear IHexpr1; try assumption. cbn. rewrite IHexpr2; clear IHexpr2.
          ** cbn. f_equal. f_equal. f_equal.
            ++ unfold expr_log. rewrite <- fold_right_app. simpl. f_equal.
              destruct (eval_expr_aux expr1 [] sys input) as [val1 log_expr1] eqn:Eq1. 
              destruct (eval_expr_aux expr2 log_expr1 sys input) as [val2 log_expr2] eqn:Eq2.
              apply (f_equal snd) in Eq1. apply (f_equal snd) in Eq2. cbn in *. subst.
              set (x1 := eval_expr_aux expr1 [] sys input) at 2. destruct x1.
              destruct (eval_expr_aux expr2 l sys input). cbn in *. 
              apply snd_eval_expr_aux_app2.
            ++ unfold BitFuns.bitfun_of_predicate. destr. 
          ** apply inputs_are_buffered_expr_log. exact Hin_buf.
        * rewrite interp_synth_convert.
          cbn. rewrite IHexpr1; clear IHexpr1; try assumption. cbn. rewrite IHexpr2; clear IHexpr2.
          ** cbn. f_equal. f_equal. f_equal.
            ++ unfold expr_log. rewrite <- fold_right_app. simpl. f_equal.
              destruct (eval_expr_aux expr1 [] sys input) as [val1 log_expr1] eqn:Eq1. 
              destruct (eval_expr_aux expr2 log_expr1 sys input) as [val2 log_expr2] eqn:Eq2.
              apply (f_equal snd) in Eq1. apply (f_equal snd) in Eq2. cbn in *. subst.
              set (x1 := eval_expr_aux expr1 [] sys input) at 2. destruct x1.
              destruct (eval_expr_aux expr2 l sys input). cbn in *. 
              apply snd_eval_expr_aux_app2.
            ++ unfold BitFuns.bitfun_of_predicate. destr. 
          ** apply inputs_are_buffered_expr_log. exact Hin_buf.
        * rewrite interp_synth_convert.
          cbn. rewrite IHexpr1; clear IHexpr1; try assumption. cbn. rewrite IHexpr2; clear IHexpr2.
          ** cbn. f_equal. f_equal. f_equal.
            ++ unfold expr_log. rewrite <- fold_right_app. simpl. f_equal.
              destruct (eval_expr_aux expr1 [] sys input) as [val1 log_expr1] eqn:Eq1. 
              destruct (eval_expr_aux expr2 log_expr1 sys input) as [val2 log_expr2] eqn:Eq2.
              apply (f_equal snd) in Eq1. apply (f_equal snd) in Eq2. cbn in *. subst.
              set (x1 := eval_expr_aux expr1 [] sys input) at 2. destruct x1.
              destruct (eval_expr_aux expr2 l sys input). cbn in *. 
              apply snd_eval_expr_aux_app2.
            ++ unfold BitFuns.bitfun_of_predicate. destr. 
          ** apply inputs_are_buffered_expr_log. exact Hin_buf.
        * rewrite interp_synth_convert.
          cbn. rewrite IHexpr1; clear IHexpr1; try assumption. cbn. rewrite IHexpr2; clear IHexpr2.
          ** cbn. f_equal. f_equal. f_equal.
            ++ unfold expr_log. rewrite <- fold_right_app. simpl. f_equal.
              destruct (eval_expr_aux expr1 [] sys input) as [val1 log_expr1] eqn:Eq1. 
              destruct (eval_expr_aux expr2 log_expr1 sys input) as [val2 log_expr2] eqn:Eq2.
              apply (f_equal snd) in Eq1. apply (f_equal snd) in Eq2. cbn in *. subst.
              set (x1 := eval_expr_aux expr1 [] sys input) at 2. destruct x1.
              destruct (eval_expr_aux expr2 l sys input). cbn in *. 
              apply snd_eval_expr_aux_app2.
            ++ unfold BitFuns.bitfun_of_predicate. destr. 
          ** apply inputs_are_buffered_expr_log. exact Hin_buf.
    + (* If *)
      cbn. unfold opt_bind. rewrite IHexpr1; try assumption.
      destruct (tf_eval_expr spec_states_size spec_inputs_size spec_outputs_size expr1 sys input) eqn:Eq1.
      destruct vhd eqn:Eq2; cbn in *.
      * rewrite IHexpr2; try assumption.
        ++ f_equal. f_equal. f_equal.
          unfold expr_log. rewrite <- fold_right_app. simpl. f_equal.
          let_to_projs. simpl. rewrite <- (fst_eval_expr_aux_eq_tf_eval_expr expr1 [] sys input) in Eq1.
          subst. destruct vtl.
          change (vect_cons_t bool (vect_nil_t bool)) with (type_denote (bits_t (S O))).
          rewrite Eq1. simpl.
          change (vect_cons_t bool (vect_nil_t bool)) with (type_denote (bits_t 1)).
          apply snd_eval_expr_aux_app2.
        ++ apply inputs_are_buffered_expr_log. exact Hin_buf.
      * rewrite IHexpr3; try assumption.
        ++ f_equal. f_equal. f_equal.
          -- unfold expr_log. rewrite <- fold_right_app. simpl. f_equal.
            let_to_projs. simpl. rewrite <- (fst_eval_expr_aux_eq_tf_eval_expr expr1 [] sys input) in Eq1.
            subst. destruct vtl.
            change (vect_cons_t bool (vect_nil_t bool)) with (type_denote (bits_t (S O))).
            rewrite Eq1. simpl.
            change (vect_cons_t bool (vect_nil_t bool)) with (type_denote (bits_t 1)).
            apply snd_eval_expr_aux_app2.
          -- subst. destruct vtl. reflexivity.
        ++ apply inputs_are_buffered_expr_log. exact Hin_buf.
  (* Timeout 10 Time Qed. *)
  Admitted. (* SPEEDUP *)
  (* 2 seconds *)

  Definition affected_regs (ops: list (@tf_op spec_states spec_inputs spec_outputs)) : list reg_t :=
    fold_right (fun op acc => match op with
                             | tf_assign dst _ => tf_reg dst :: acc
                             | tf_output dst _ => tf_out dst :: acc
                             | _ => acc
                             end) [] ops.

  Definition aux_log sys input (ops: list (@tf_op spec_states spec_inputs spec_outputs)) (log_a: Log R ContextEnv) : Log R ContextEnv :=
    fold_left (fun acc op => match op with
                             | tf_assign dst expr => log_cons (R:=R) (REnv:=REnv) (tf_reg dst) (Write0 (tf_eval_expr spec_states_size spec_inputs_size spec_outputs_size expr sys input)) (expr_log expr (spec_states_size dst) sys input acc)
                             | tf_output dst expr => log_cons (R:=R) (REnv:=REnv) (tf_out dst) (Write0 (tf_eval_expr spec_states_size spec_inputs_size spec_outputs_size expr sys input)) (expr_log expr (spec_outputs_size dst) sys input acc)
                             | _ => acc
                             end) ops log_a.

  Lemma inputs_are_buffered_log_app_log_cons_neq:
    forall input r log_a log_r reg entry,
      ~ In reg (map tf_in spec_all_inputs) ->
      inputs_are_buffered input r (log_app log_a log_r) ->
      inputs_are_buffered input r (log_app (log_cons (R:=R) (REnv:=REnv) reg entry log_a) log_r).
  Proof.
    intros input r log_a log_r reg entry Hnot_input Hin_buf.
    unfold inputs_are_buffered in *. intros v. specialize (Hin_buf v).
    rewrite SemanticProperties.latest_write0_app in *.
    rewrite SemanticProperties.latest_write0_cons_neq in *; try assumption.
    clear Hin_buf.
    pose proof (in_spec_all_inputs v).
    intro. subst. apply (in_map (tf_in (states_var:=spec_states) (outputs_var:=spec_outputs))) in H.
    congruence.
  Qed.

  Lemma inputs_not_affected:
    forall ops v,
      ~ In (tf_in v) (affected_regs ops).
  Proof.
    intros ops v. unfold affected_regs. induction ops as [| op ops IH].
    - auto.
    - destruct op; simpl; try apply IH.
      + (* hammer. *) timeout 10 sfirstorder.
      + (* hammer. *) timeout 10 sfirstorder.
  Qed.

  Lemma may_write_all_expr_log :
    forall log_r log_a P0 sys input expr dst_sz ops,
      may_write_all log_r log_a P0 (affected_regs ops) = true ->
      may_write_all log_r (expr_log expr dst_sz sys input log_a) P0 (affected_regs ops) = true.
  Proof.
    intros log_r log_a P0 sys input expr dst_sz ops Hwr.
    unfold may_write_all in *. rewrite forallb_forall in *. intros reg Hreg_in_aff.
    specialize (Hwr reg Hreg_in_aff).

    unfold expr_log. induction (snd (eval_expr_aux expr [] sys input)).
    - exact Hwr.
    - simpl. destruct (eq_dec reg a) as [Heq | Hneq]; subst.
      + simpl. rewrite may_write_log_cons_eq. apply andb_true_intro; split.
        * assumption.
        * destruct P0; simpl; try reflexivity. destruct a; try ring.
          contradict Hreg_in_aff. exact (inputs_not_affected ops x).          
      + simpl. rewrite may_write_log_cons_neq.
        * apply IHl.
        * assumption.
  Qed.

  Lemma may_write_expr_log :
    forall log_r log_a P0 sys input expr dst_sz reg ,
      (forall i, tf_in i <> reg) ->
      may_write log_r log_a P0 reg = true ->
      may_write log_r (expr_log expr dst_sz sys input log_a) P0 reg = true.
  Proof.
    intros log_r log_a P0 sys input expr dst_sz reg Hnot_input Hwr.
    unfold expr_log. induction (snd (eval_expr_aux expr [] sys input)).
    - exact Hwr.
    - simpl. destruct (eq_dec reg a) as [Heq | Hneq]; subst.
      + simpl. rewrite may_write_log_cons_eq. apply andb_true_intro; split.
        * assumption.
        * destruct P0; simpl; try reflexivity. destruct a; try ring.
          specialize (Hnot_input x). contradiction.
      + simpl. rewrite may_write_log_cons_neq.
        * apply IHl.
        * assumption.
  Qed.
    
  Lemma interp_action_aux :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log_r log_a ops rest,
      state_matches sys r ->
      may_read_all log_r P0 (map tf_reg spec_all_states) = true ->
      may_read_all log_r P1 (map tf_in spec_all_inputs) = true ->
      may_read_all log_r P0 (map tf_out spec_all_outputs) = true ->
      inputs_are_buffered input r (log_app log_a log_r) ->
      NoDup (affected_regs ops) ->
      may_write_all log_r log_a P0 (affected_regs ops) = true ->
      match interp_action (tau:=unit_t) r sigma CtxEmpty log_r log_a (rule_aux tf_ctx ops rest)
      return option (Log R REnv) with
      | Some (l, _, _) => Some (l)
      | None => None
      end =
      match interp_action r sigma CtxEmpty log_r (aux_log sys input ops log_a) rest
      with
      | Some (l, _, _) => Some l
      | None => None
      end.
  Proof.
    intros sys r act input sigma log_r log_a ops rest.
    intros Hstate Hrd0_st Hrd1_in Hrd0_out Hin_buf HNoDup_aff Hwr0_aff.

    generalize dependent log_a. generalize dependent rest.
    induction ops as [| op ops H0 ]; intros.
    - reflexivity.
    - destruct op.
      + cbn. apply H0; assumption.
      + simpl. simpl in Hwr0_aff. apply may_write_all_cons in Hwr0_aff. destruct Hwr0_aff as [Hwr0_dst Hwr0_rest].
        unfold opt_bind. 
        change (@tf_states_type _ (tfs_states_size (tf_sched_ctx tf_ctx)) dst)
          with (bits_t (tfs_states_size (tf_sched_ctx tf_ctx) dst)) in *.
        rewrite (interp_action_expr sys r act input sigma log_r log_a expr); try assumption.
        extract_match_term. assert (MT = true).
        * subst. apply may_write_expr_log.
          -- intros. (* hammer. *) timeout 10 sauto.
          -- assumption.
        * rewrite H. apply H0; clear H0.   
          -- simpl in HNoDup_aff. inversion HNoDup_aff; subst. assumption.
          -- apply inputs_are_buffered_log_app_log_cons_neq; try apply inputs_are_buffered_expr_log; try assumption.
             exact (not_in_reg_reg_all_inputs dst).
          -- simpl in HNoDup_aff. inversion HNoDup_aff; subst.
             rewrite may_write_all_log_cons_neq; [|assumption].
             apply may_write_all_expr_log; assumption.
      + simpl. simpl in Hwr0_aff. apply may_write_all_cons in Hwr0_aff. destruct Hwr0_aff as [Hwr0_dst Hwr0_rest].
        unfold opt_bind. 
        change (@tf_outputs_type _ (tfs_outputs_size (tf_sched_ctx tf_ctx)) dst)
          with (bits_t (tfs_outputs_size (tf_sched_ctx tf_ctx) dst)) in *.
        rewrite (interp_action_expr sys r act input sigma log_r log_a expr); try assumption.
        extract_match_term. assert (MT = true).
        * subst. apply may_write_expr_log.
          -- intros. (* hammer. *) timeout 10 sauto.
          -- assumption.
        * rewrite H. apply H0; clear H0.   
          -- simpl in HNoDup_aff. inversion HNoDup_aff; subst. assumption.
          -- apply inputs_are_buffered_log_app_log_cons_neq; try apply inputs_are_buffered_expr_log; try assumption.
             exact (not_in_reg_out_all_inputs dst).
          -- simpl in HNoDup_aff. inversion HNoDup_aff; subst.
             rewrite may_write_all_log_cons_neq; [|assumption].
             apply may_write_all_expr_log; assumption.
  (* Timeout 10 Time Qed.  *)
  Admitted. (* SPEEDUP *)
  (* > 10 seconds *)

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

  Lemma nodup_affected_regs_fst:
    forall act,
      NoDup (affected_regs (fst (spec_schedule act))).
  Proof.
    intros act. 
    pose proof (spec_schedule_ops_nodup act). unfold tfs_ops_no_duplicates in *.
    rewrite flat_map_app in H. apply NoDup_app_remove_r in H.

    induction (fst (spec_schedule act)).
    - simpl. apply NoDup_nil. 
    - simpl in *. destruct a.
      + simpl in H. apply IHl. exact H.
      + simpl in H. apply NoDup_cons_iff in H. destruct H as [Hnotin H]. specialize (IHl H); clear H. 
        apply NoDup_cons; try assumption.
        induction l.
        * auto.
        * simpl in *. apply Common.not_in_app_iff in Hnotin. destruct Hnotin as [Hnotin Hnotin_l].
          specialize (IHl0 Hnotin_l); clear Hnotin_l.          
          destruct a.
          -- simpl. apply IHl0. exact IHl.
          -- simpl. destruct (eq_dec dst dst0) as [Heq | Hneq]; subst.
              ++ contradict Hnotin. sauto.
              ++ intro. destruct H.
              ** timeout 10 sauto.
              ** inversion IHl; subst. apply IHl0; assumption.
          -- simpl. intro. destruct H.
              ** timeout 10 sauto.
              ** inversion IHl; subst. apply IHl0; assumption.
      + simpl in H. apply NoDup_cons_iff in H. destruct H as [Hnotin H]. specialize (IHl H); clear H. 
        apply NoDup_cons; try assumption.
        induction l.
        * auto.
        * simpl in *. apply Common.not_in_app_iff in Hnotin. destruct Hnotin as [Hnotin Hnotin_l].
          specialize (IHl0 Hnotin_l); clear Hnotin_l.          
          destruct a.
          -- simpl. apply IHl0. exact IHl.
          -- simpl. intro. destruct H.
              ** timeout 10 sauto.
              ** inversion IHl; subst. apply IHl0; assumption.
          -- simpl. destruct (eq_dec dst dst0) as [Heq | Hneq]; subst.
              ++ contradict Hnotin. sauto.
              ++ intro. destruct H.
              ** timeout 10 sauto.
              ** inversion IHl; subst. apply IHl0; assumption.
  Qed.

  Lemma nodup_affected_regs_snd:
    forall act,
      NoDup (affected_regs (snd (spec_schedule act))).
  Proof.
    intros act. 
    pose proof (spec_schedule_ops_nodup act). unfold tfs_ops_no_duplicates in *.
    rewrite flat_map_app in H. apply NoDup_app_remove_l in H.

    induction (snd (spec_schedule act)).
    - simpl. apply NoDup_nil. 
    - simpl in *. destruct a.
      + simpl in H. apply IHl. exact H.
      + simpl in H. apply NoDup_cons_iff in H. destruct H as [Hnotin H]. specialize (IHl H); clear H. 
        apply NoDup_cons; try assumption.
        induction l.
        * auto.
        * simpl in *. apply Common.not_in_app_iff in Hnotin. destruct Hnotin as [Hnotin Hnotin_l].
          specialize (IHl0 Hnotin_l); clear Hnotin_l.          
          destruct a.
          -- simpl. apply IHl0. exact IHl.
          -- simpl. destruct (eq_dec dst dst0) as [Heq | Hneq]; subst.
              ++ contradict Hnotin. sauto.
              ++ intro. destruct H.
              ** timeout 10 sauto.
              ** inversion IHl; subst. apply IHl0; assumption.
          -- simpl. intro. destruct H.
              ** timeout 10 sauto.
              ** inversion IHl; subst. apply IHl0; assumption.
      + simpl in H. apply NoDup_cons_iff in H. destruct H as [Hnotin H]. specialize (IHl H); clear H. 
        apply NoDup_cons; try assumption.
        induction l.
        * auto.
        * simpl in *. apply Common.not_in_app_iff in Hnotin. destruct Hnotin as [Hnotin Hnotin_l].
          specialize (IHl0 Hnotin_l); clear Hnotin_l.          
          destruct a.
          -- simpl. apply IHl0. exact IHl.
          -- simpl. intro. destruct H.
              ** timeout 10 sauto.
              ** inversion IHl; subst. apply IHl0; assumption.
          -- simpl. destruct (eq_dec dst dst0) as [Heq | Hneq]; subst.
              ++ contradict Hnotin. sauto.
              ++ intro. destruct H.
              ** timeout 10 sauto.
              ** inversion IHl; subst. apply IHl0; assumption.
  Qed.

  (* Lemma affected_regs_fst_not_in_snd:
    forall act reg, 
      In reg (affected_regs (fst (spec_schedule act))) 
      -> ~ In reg (affected_regs (snd (spec_schedule act))).
  Proof. *)

  Lemma interp_action_cmd :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log_r log_a,
      state_matches sys r ->
      may_read_all log_r P0 (map tf_reg spec_all_states) = true ->
      may_write_all log_r log_a P0 (map tf_reg spec_all_states) = true ->
      may_read_all log_r P1 (map tf_in spec_all_inputs) = true ->
      may_read_all log_r P0 (map tf_out spec_all_outputs) = true ->
      may_write_all log_r log_a P0 (map tf_out spec_all_outputs) = true ->
      inputs_are_buffered input r (log_app log_a log_r) ->
      match interp_action r sigma CtxEmpty log_r log_a (_rule_cmd tf_ctx act) with
      | Some (l, v, _) => Some (l)
      | None => None
      end =
      Some ( construct_log sys act input r.[tf_ready] log_a ).
  Proof.
    intros sys r act input sigma log_r log_a.
    intros Hstate Hrd0_st Hwr0_st Hrd1_in Hrd0_out Hwr0_out Hin_buf.
    
    unfold _rule_cmd. 
    rewrite (interp_action_aux sys r act input sigma log_r log_a); try timeout 1 assumption.
    2: exact (nodup_affected_regs_fst act).
    2: {
      unfold affected_regs. 
      induction (fst (spec_schedule act)).
      - simpl. unfold may_write_all. rewrite forallb_forall. intros reg Hreg_in_aff. contradiction.
      - simpl. unfold may_write_all in *. rewrite forallb_forall in *. intros reg Hreg_in_aff. specialize (IHl reg).
        destruct a.
        + specialize (IHl Hreg_in_aff). apply IHl.
        + simpl in Hreg_in_aff. destruct (Hreg_in_aff); clear Hreg_in_aff; subst.
            * apply Hwr0_st. apply in_map. exact (in_spec_all_states dst).
            * apply IHl. apply H.
        + simpl in Hreg_in_aff. destruct (Hreg_in_aff); clear Hreg_in_aff; subst.
            * apply Hwr0_out. apply in_map. exact (in_spec_all_outputs dst).
            * apply IHl. apply H.
    }

    admit.
  Admitted.

  (*
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
   *)

  Definition good_log (log: Log R ContextEnv) : Prop :=
    may_read_all log P0 (map tf_reg spec_all_states) = true /\
    may_write_all log log_empty P0 (map tf_reg spec_all_states) = true /\
    may_read_all log P0 (map tf_in spec_all_inputs) = true /\
    may_write_all log log_empty P0 (map tf_in spec_all_inputs) = true /\
    may_read_all log P0 (map tf_out spec_all_outputs) = true /\
    may_write_all log log_empty P0 (map tf_out spec_all_outputs) = true /\
    may_read log P0 (tf_ready) = true /\
    may_write log log_empty P0 (tf_ready) = true /\
    may_read log P0 (tf_cmd) = true /\
    may_write log log_empty P0 (tf_cmd) = true.

  (* Lemma interp_rule_correct :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log,
      state_matches sys r ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      good_log log ->
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
Abort. *)

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

  (* Below is done *)

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
        * rewrite (latest_write_cmd_nrdy sys r act input sigma log); try assumption. apply (Hin_nrdy Hnotready).
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
    unfold interp_rule, rules, rule_cmd_guard. simpl_eq.
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
      <->
      state_env_matches (tfs_next_cycle sched_ctx act sys input) act input (commit_update r
          match interp_rule r sigma log (rules (rule_cmd act)) with
          | Some l => (log_app l log)
          | None => log
          end).
  Proof.
    intros sys r act input sigma log actions Hstate Hin_rdy Hin_nrdy Hlog H_notin_actions.

    induction actions as [|a actions IH].
    - cbn [fold_right].

      remember (commit_update r
                  match interp_rule r sigma log (rules (rule_cmd act)) with
                  | Some l => interp_scheduler' r sigma rules (log_app l log) (system_schedule_outputs tf_ctx)
                  | None => interp_scheduler' r sigma rules log (system_schedule_outputs tf_ctx)
                  end) as r1.
      remember (commit_update r
                  match interp_rule r sigma log (rules (rule_cmd act)) with
                  | Some l => log_app l log
                  | None => log
                  end) as r2.
      assert (state_equal r1 r2) as Heq_s. {
        subst r1 r2. unfold state_equal, env_equal; split; intros x; unfold commit_update; rewrite !getenv_create; match_eq; destruct interp_rule; apply latest_write_schedule_outputs; reflexivity.
      }
      assert (env_equal r1 r2) as Heq_e. {
        subst r1 r2. unfold state_equal, env_equal; split; try intros x; unfold commit_update; rewrite !getenv_create; match_eq; destruct interp_rule; apply latest_write_schedule_outputs; reflexivity.
      }

      apply state_env_matches_comp with (r1:=r1) (r2:=r2); try assumption.
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
    { subst mr. rewrite may_read_log_empty. reflexivity. }
    rewrite H. clear H mr.
    
    unfold opt_bind.
    set (cond := Bits.single _). cbn in cond. subst cond. cbv iota.
    
    (* prove we may write *)
    set (mw := may_write _ _ _ _). assert (mw = true). 
    { 
      subst mw. rewrite !may_write_log_cons_neq.
      - rewrite may_write_log_empty. reflexivity.
      - sauto.
      - sauto.
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
      unfold good_log. repeat split; try apply may_read_all_log_empty; try apply may_write_all_log_empty; 
      try apply may_read_log_empty; try apply may_write_log_empty.

    - specialize (Hin_nrdy Hnotready) as H_in.

      (* simplify the busy rule *)
      specialize (interp_rule_busy_not_ready r sigma Hnotready) as H_busy_not_ready.
      rewrite H_busy_not_ready. clear H_busy_not_ready.

      apply synthesis_correct_aux; try assumption.

      (* Show that the log is good *)
      unfold good_log. repeat split.
      + rewrite !SemanticProperties.log_app_empty_l. rewrite !may_read_all_log1_cons_neq.
        * apply may_read_all_log_empty.
        * exact not_in_reg_ready_all_states.
        * exact not_in_reg_ready_all_states.
        * exact not_in_reg_cmd_ack_all_states.
      + rewrite !SemanticProperties.log_app_empty_l. rewrite !may_write_all_log1_cons_neq.
        * apply may_write_all_log_empty.
        * exact not_in_reg_ready_all_states.
        * exact not_in_reg_ready_all_states.
        * exact not_in_reg_cmd_ack_all_states.
      + rewrite !SemanticProperties.log_app_empty_l. rewrite !may_read_all_log1_cons_neq.
        * apply may_read_all_log_empty.
        * exact not_in_reg_ready_all_inputs.
        * exact not_in_reg_ready_all_inputs.
        * exact not_in_reg_cmd_ack_all_inputs.
      + rewrite !SemanticProperties.log_app_empty_l. rewrite !may_write_all_log1_cons_neq.
        * apply may_write_all_log_empty.
        * exact not_in_reg_ready_all_inputs.
        * exact not_in_reg_ready_all_inputs.
        * exact not_in_reg_cmd_ack_all_inputs.
      + rewrite !SemanticProperties.log_app_empty_l. rewrite !may_read_all_log1_cons_neq.
        * apply may_read_all_log_empty.
        * exact not_in_reg_ready_all_outputs.
        * exact not_in_reg_ready_all_outputs.
        * exact not_in_reg_cmd_ack_all_outputs.
      + rewrite !SemanticProperties.log_app_empty_l. rewrite !may_write_all_log1_cons_neq.
        * apply may_write_all_log_empty.
        * exact not_in_reg_ready_all_outputs.
        * exact not_in_reg_ready_all_outputs.
        * exact not_in_reg_cmd_ack_all_outputs.
      + rewrite !SemanticProperties.log_app_empty_l. rewrite may_read_log1_cons_neq. rewrite !may_read_log1_cons_eq.
        * rewrite may_read_log_empty. ring.
        * sauto.
      + rewrite !SemanticProperties.log_app_empty_l. rewrite may_write_log1_cons_neq. rewrite !may_write_log1_cons_eq.
        * rewrite may_write_log_empty. ring.
        * sauto.
      + rewrite !SemanticProperties.log_app_empty_l. rewrite !may_read_log1_cons_neq.
        * apply may_read_log_empty.
        * sauto.
        * sauto.
        * sauto.
      + rewrite !SemanticProperties.log_app_empty_l. rewrite !may_write_log1_cons_neq.
        * apply may_write_log_empty.
        * sauto.
        * sauto.
        * sauto.
  Qed.

End SynthesisCorrectness.
