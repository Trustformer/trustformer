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
  Local Notation spec_externs := (tfs_spec_externs (tfs_ctx (tf_sched_ctx tf_ctx))).
  Local Notation spec_externs_sig := (tfs_spec_externs_sig (tfs_ctx (tf_sched_ctx tf_ctx))).
  Local Notation spec_externs_fin := (tfs_spec_externs_fin (tfs_ctx (tf_sched_ctx tf_ctx))).
  Local Notation spec_all_externs := (@finite_elements spec_externs spec_externs_fin).
  Local Notation spec_externs_arg := (@tfe_arg_size _ spec_externs_sig).
  Local Notation spec_externs_res := (@tfe_res_size _ spec_externs_sig).
  Local Notation spec_ext_arg := (tfs_ext_arg (tf_sched_ctx tf_ctx)).
  Local Notation spec_ext_res := (tfs_ext_res (tf_sched_ctx tf_ctx)).
  Hint Extern 0 (tf_externs spec_externs) => exact spec_externs_sig : typeclass_instances.
  Hint Extern 1 (tf_externs _) => exact spec_externs_sig : typeclass_instances.
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

  Hint Extern 0 (FiniteType spec_states) => exact (tfs_states_fin (tf_sched_ctx tf_ctx)) : typeclass_instances.  Hint Extern 0 (FiniteType spec_inputs) => exact (tfs_inputs_fin (tf_sched_ctx tf_ctx)) : typeclass_instances.
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

  (* Interface obligation on the attached trusted modules: each one computes the
     function its declaration says it computes. Unlike [input_matches] this holds in
     every cycle, because the design only ever samples a result port on the cycle
     that port carries the result. See D3 in agents/extern-calls-mvp/PLAN.md. *)
  Definition externs_match (sigma: forall f, Sig_denote (Sigma f)) : Prop :=
    forall f, sigma (ext_call f) = tfe_denote f.

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

    Lemma interp_action_read1 :
      forall r sigma sig (ctx: tcontext sig) log_r log_a idx,
        may_read log_r P1 idx = true ->
        interp_action (tau:=R idx) r sigma ctx log_r log_a (Read P1 idx) =
        Some (log_cons idx {| kind := LogRead; port := P1; val := tt |} log_a,
              match latest_write0 (log_app log_a log_r) idx with
              | Some v => v
              | None => r.[idx]
              end,
              ctx).
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

    Lemma interp_action_write_const :
      forall r sigma sig (ctx: tcontext sig) log_r log_a prt idx (v: R idx),
        may_write log_r log_a prt idx = true ->
        interp_action (tau:=unit_t) r sigma ctx log_r log_a (Write prt idx (Const (tau:=R idx) v)) =
        Some (log_cons idx {| kind := LogWrite; port := prt; val := v |} log_a, Bits.nil, ctx).
    Proof. intros; simpl. rewrite H. reflexivity. Qed.

    Lemma interp_action_reset_buffers_cons :
      forall r sigma log_r log_a s rest code,
        may_write log_r log_a P1 (tf_reg s) = true ->
        interp_action (tau:=unit_t) r sigma CtxEmpty log_r log_a (rule_reset_buffers tf_ctx (s :: rest) code) =
        interp_action r sigma CtxEmpty log_r
            (log_cons (tf_reg s) (Write1 Bits.zero) log_a)
            (rule_reset_buffers tf_ctx rest code).
    Proof.
      intros. simpl. rewrite H. reflexivity.
    Qed.

    (* Concrete result log of folding all the P1 buffer-reset writes onto log_a. *)
    Definition reset_log (regs: list spec_states) (log_a: Log R ContextEnv) : Log R ContextEnv :=
      fold_left (fun acc s => log_cons (R:=R) (REnv:=REnv) (tf_reg s) (Write1 Bits.zero) acc) regs log_a.

    (* Full stepper: peel the entire reset_buffers prologue, leaving `code` to run on
       the reset_log. Distinctness (NoDup) keeps the write-validity hypothesis alive
       across the fold. *)
    Lemma interp_action_reset_buffers :
      forall r sigma log_r regs code log_a,
        NoDup (map tf_reg regs : list reg_t) ->
        may_write_all log_r log_a P1 (map tf_reg regs) = true ->
        interp_action (tau:=unit_t) r sigma CtxEmpty log_r log_a (rule_reset_buffers tf_ctx regs code) =
        interp_action r sigma CtxEmpty log_r (reset_log regs log_a) code.
    Proof.
      intros r sigma log_r regs code.
      induction regs as [| s rest IH]; intros log_a Hnd Hwr.
      - reflexivity.
      - simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin_s Hnd_rest].
        simpl in Hwr. apply may_write_all_cons in Hwr. destruct Hwr as [Hwr_s Hwr_rest].
        rewrite interp_action_reset_buffers_cons by exact Hwr_s.
        rewrite IH.
        + reflexivity.
        + exact Hnd_rest.
        + rewrite may_write_all_log_cons_neq by exact Hnotin_s. exact Hwr_rest.
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
  Time Qed. (* ca. 0.05 s *)

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

        set (MW := may_write _ _ P0 tf_cmd). assert (MW = true) as HMW
          by abstract (subst MW; rewrite !may_write_log_cons_neq; try assumption; timeout 10 sauto).
        rewrite HMW. clear HMW MW.
        cbn.

        set (MW := may_write _ _ P0 tf_ready). assert (MW = true) as HMW.
        { 
          subst MW. rewrite !may_write_log_cons_neq; [|(* hammer *) timeout 10 sauto]. rewrite may_write_fold_cons_w0_inputs. 
          2: { intro. rewrite in_map_iff in H. destruct H as [x [Heq Hin]]. congruence. }
          rewrite !may_write_log_cons_eq. rewrite Hwr0_ready. ring. 
        } rewrite HMW. clear HMW MW.
        abstract (unfold log_after_cmd_guard_rdy; reflexivity).
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
  Time Qed. (* ca. 0.15 s *)

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
            match op with
            | tf_not =>
                let (val_src, log_src) := (eval_expr_aux src log sys_state input) in
                (Bits.neg val_src, log_src)
            | tf_resize source_size =>
                let (val_src, log_src) :=
                  (eval_expr_aux (szB:=source_size) src log sys_state input) in
                (convert val_src, log_src)
            end
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
        (* An external call reads a port, never a register, so the read-log is unchanged. *)
        | tf_ext f arg =>
            let (val_arg, log_arg) :=
              eval_expr_aux (szB:=spec_externs_arg f) arg log sys_state input in
            (convert (tfe_denote f val_arg), log_arg)
        end.

  Lemma fst_eval_expr_aux_eq_tf_eval_expr:
    forall expr log1 sys input szB,
      fst (eval_expr_aux (szB:=szB) expr log1 sys input) = tf_eval_expr (szB:=szB) spec_states_size spec_inputs_size spec_outputs_size expr sys input.
  Proof.
    intros expr log1 sys input szB.

    generalize dependent szB.
    generalize dependent log1.
    induction expr; intros log1 szB; try reflexivity.
    - destruct op.
      + cbn. rewrite Common.fst_let_repackage. f_equal.
        apply IHexpr.
      + cbn. rewrite Common.fst_let_repackage. f_equal.
        apply (IHexpr log1 source_size).
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
    - cbn. rewrite Common.fst_let_repackage. f_equal. f_equal.
      apply (IHexpr log1 (spec_externs_arg f)).
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
    - destruct op.
      + cbn.
        pose proof (IHexpr log1 log2 szB).
        destruct (eval_expr_aux expr log1 sys input).
        destruct (eval_expr_aux expr log2 sys input).
        cbn in *. subst. reflexivity.
      + cbn.
        pose proof (IHexpr log1 log2 source_size).
        destruct (eval_expr_aux (szB:=source_size) expr log1 sys input).
        destruct (eval_expr_aux (szB:=source_size) expr log2 sys input).
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
    - cbn.
      pose proof (IHexpr log1 log2 (spec_externs_arg f)).
      destruct (eval_expr_aux expr log1 sys input). cbn in *. subst.
      destruct (eval_expr_aux expr log2 sys input). cbn in *. subst. reflexivity.
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
    - destruct op.
      + cbn.
        pose proof (IHexpr log1 log2 szB).
        destruct (eval_expr_aux expr log1 sys input).
        destruct (eval_expr_aux expr (log1 ++ log2) sys input).
        cbn in *. subst. reflexivity.
      + cbn.
        pose proof (IHexpr log1 log2 source_size).
        destruct (eval_expr_aux (szB:=source_size) expr log1 sys input).
        destruct (eval_expr_aux (szB:=source_size) expr (log1 ++ log2) sys input).
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
    - cbn.
      pose proof (IHexpr log1 log2 (spec_externs_arg f)).
      destruct (eval_expr_aux expr (log1 ++ log2) sys input). cbn in *. subst.
      destruct (eval_expr_aux expr log1 sys input). cbn in *. subst. reflexivity.
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
    - destruct op.
      + cbn.
        pose proof (IHexpr2 szB1 szB2).
        destruct (eval_expr_aux expr1 [] sys input).
        destruct (eval_expr_aux expr2 [] sys input).
        destruct (eval_expr_aux expr2 l sys input).
        cbn in *. subst. reflexivity.
      + cbn.
        pose proof (IHexpr2 szB1 source_size).
        destruct (eval_expr_aux expr1 [] sys input).
        destruct (eval_expr_aux (szB:=source_size) expr2 [] sys input).
        destruct (eval_expr_aux (szB:=source_size) expr2 l sys input).
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
    - cbn.
      pose proof (IHexpr2 szB1 (spec_externs_arg f)).
      destruct (eval_expr_aux expr1 [] sys input).
      destruct (eval_expr_aux (szB:=spec_externs_arg f) expr2 [] sys input).
      destruct (eval_expr_aux (szB:=spec_externs_arg f) expr2 l sys input).
      cbn in *. subst. reflexivity.
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

  (* expr_log only appends LogRead entries, so latest_write0 ignores it for ANY
     register (generalizes latest_write0_expr_log beyond tf_in). Building block for
     the aux_log <-> updates bridge (Phase D). *)
  Lemma latest_write0_expr_log_any :
    forall expr szB sys input log_a reg,
      latest_write0 (expr_log expr szB sys input log_a) reg =
      latest_write0 log_a reg.
  Proof.
    intros expr szB sys input log_a reg.
    unfold expr_log.
    induction ((snd (eval_expr_aux expr [] sys input))).
    - reflexivity.
    - destruct (eq_dec reg a) as [Heq | Hneq]; subst.
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
  Time Qed. (* ca. 0.1 s *)

  (* Stated over [expr_to_action] with [tau] pinned to the reduced [bits_t …]: the
     elaborated goal carries that form, whereas [ExternalCall]'s own typing gives the
     convertible-but-not-syntactic [retSig (Sigma (ext_call f))], and [rewrite]
     matches syntactically. *)
  Lemma interp_ext_step :
    forall r sigma log_r log_a (f : spec_externs) (e : tf_expr),
      interp_action (R:=R) (Sigma:=Sigma) (REnv:=REnv) (tau := bits_t (spec_externs_res f))
        r sigma CtxEmpty log_r log_a
        (ExternalCall (ext_call f) (expr_to_action tf_ctx e (spec_externs_arg f)))
      = match
          interp_action (R:=R) (Sigma:=Sigma) (REnv:=REnv) (tau := bits_t (spec_externs_arg f))
            r sigma CtxEmpty log_r log_a
            (expr_to_action tf_ctx e (spec_externs_arg f))
        with
        | Some (l, v, g) => Some (l, sigma (ext_call f) v, g)
        | None => None
        end.
  Proof. reflexivity. Qed.

Set Printing Implicit.
  Lemma interp_action_expr :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log_r log_a expr dst_sz,
      state_matches sys r ->
      externs_match sigma ->
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
    intros Hstate Hsig Hrd0_st Hrd1_in Hrd0_out.

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
      destruct op.
      * cbn. unfold opt_bind. rewrite IHexpr; try assumption.
        simpl. unfold Bits.neg. f_equal. f_equal. f_equal.
        unfold expr_log. simpl. destruct (eval_expr_aux expr [] sys input) as [val log_expr]. reflexivity.
      * cbn. rewrite interp_synth_convert. rewrite IHexpr; try assumption.
        unfold expr_log. cbn.
        destruct (eval_expr_aux (szB:=source_size) expr [] sys input).
        reflexivity.
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
    + (* Ext: the attached module computes [tfe_denote f], by [externs_match] *)
      cbn. rewrite interp_synth_convert, interp_ext_step.
      rewrite (IHexpr log_a (spec_externs_arg f) Hin_buf).
      unfold expr_log. cbn. rewrite Hsig.
      destruct (eval_expr_aux (szB:=spec_externs_arg f) expr [] sys input).
      reflexivity.
  Time Qed. (* ca. 1.7 s *)

  Definition affected_regs (ops: list (@tf_op spec_states spec_inputs spec_outputs spec_externs)) : list reg_t :=
    fold_right (fun op acc => match op with
                             | tf_assign dst _ => tf_reg dst :: acc
                             | tf_output dst _ => tf_out dst :: acc
                             | _ => acc
                             end) [] ops.

  Definition aux_log sys input (ops: list (@tf_op spec_states spec_inputs spec_outputs spec_externs)) (log_a: Log R ContextEnv) : Log R ContextEnv :=
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
      externs_match sigma ->
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
    intros Hstate Hsig Hrd0_st Hrd1_in Hrd0_out Hin_buf HNoDup_aff Hwr0_aff.

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
  Time Qed. (* ca. 0.3 s *)

  (* --- aux_log <-> abstract-updates bridge (Phase D building blocks) --- *)

  Lemma tfs_get_updates_cons :
    forall op ops sys input,
      tfs_get_updates sched_ctx (op :: ops) sys input =
      tf_op_step_updates (tfs_states_size sched_ctx) (tfs_inputs_size sched_ctx)
        (tfs_outputs_size sched_ctx) op sys input
        :: tfs_get_updates sched_ctx ops sys input.
  Proof. reflexivity. Qed.

  (* If a register is not written by any op, find_st_update yields None. *)
  Lemma find_st_update_not_affected :
    forall ops sys input x,
      ~ In (tf_reg x) (affected_regs ops) ->
      find_st_update sched_ctx x (tfs_get_updates sched_ctx ops sys input) = None.
  Proof.
    induction ops as [| op ops IH]; intros sys input x Hnotin.
    - reflexivity.
    - rewrite tfs_get_updates_cons.
      destruct op; simpl affected_regs in Hnotin; cbn [find_st_update tf_op_step_updates].
      + apply IH. exact Hnotin.
      + apply Decidable.not_or in Hnotin. destruct Hnotin as [Hneq Hnotin].
        destruct (eq_dec dst x) as [Heq | Hneq'].
        * subst. contradiction Hneq. reflexivity.
        * apply IH. exact Hnotin.
      + apply Decidable.not_or in Hnotin. destruct Hnotin as [_ Hnotin].
        apply IH. exact Hnotin.
  Qed.

  (* Symmetric helper for outputs. *)
  Lemma find_out_update_not_affected :
    forall ops sys input x,
      ~ In (tf_out x) (affected_regs ops) ->
      find_out_update sched_ctx x (tfs_get_updates sched_ctx ops sys input) = None.
  Proof.
    induction ops as [| op ops IH]; intros sys input x Hnotin.
    - reflexivity.
    - rewrite tfs_get_updates_cons.
      destruct op; simpl affected_regs in Hnotin; cbn [find_out_update tf_op_step_updates].
      + apply IH. exact Hnotin.
      + apply Decidable.not_or in Hnotin. destruct Hnotin as [_ Hnotin].
        apply IH. exact Hnotin.
      + apply Decidable.not_or in Hnotin. destruct Hnotin as [Hneq Hnotin].
        destruct (eq_dec dst x) as [Heq | Hneq'].
        * subst. contradiction Hneq. reflexivity.
        * apply IH. exact Hnotin.
  Qed.

  (* One-step unfolding of the aux_log fold_left. *)
  Lemma aux_log_cons :
    forall op ops sys input log_a,
      aux_log sys input (op :: ops) log_a =
      aux_log sys input ops
        (match op with
         | tf_assign dst expr =>
             log_cons (R:=R) (REnv:=REnv) (tf_reg dst)
               (Write0 (tf_eval_expr spec_states_size spec_inputs_size spec_outputs_size expr sys input))
               (expr_log expr (spec_states_size dst) sys input log_a)
         | tf_output dst expr =>
             log_cons (R:=R) (REnv:=REnv) (tf_out dst)
               (Write0 (tf_eval_expr spec_states_size spec_inputs_size spec_outputs_size expr sys input))
               (expr_log expr (spec_outputs_size dst) sys input log_a)
         | _ => log_a
         end).
  Proof. reflexivity. Qed.

  (* CRUX BRIDGE (registers): under NoDup, latest_write0 over aux_log agrees with
     find_st_update over the abstract updates, falling back to log_a. *)
  Lemma latest_write0_aux_log_reg :
    forall ops sys input log_a x,
      NoDup (affected_regs ops) ->
      latest_write0 (aux_log sys input ops log_a) (tf_reg x) =
      match find_st_update sched_ctx x (tfs_get_updates sched_ctx ops sys input) with
      | Some v => Some v
      | None => latest_write0 log_a (tf_reg x)
      end.
  Proof.
    induction ops as [| op ops IH]; intros sys input log_a x Hnd.
    - reflexivity.
    - rewrite aux_log_cons, tfs_get_updates_cons.
      destruct op; simpl affected_regs in Hnd;
        cbn [find_st_update tf_op_step_updates].
      + (* tf_nop *) apply IH. exact Hnd.
      + (* tf_assign dst expr *)
        apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
        destruct (eq_dec dst x) as [Heq | Hneq].
        * subst dst.
          rewrite IH by exact Hnd.
          rewrite (find_st_update_not_affected ops sys input x Hnotin).
          rewrite SemanticProperties.latest_write0_cons_eq. reflexivity.
        * rewrite IH by exact Hnd.
          destruct (find_st_update sched_ctx x (tfs_get_updates sched_ctx ops sys input)); try reflexivity.
          rewrite SemanticProperties.latest_write0_cons_neq.
          -- apply latest_write0_expr_log_any.
          -- intro Hc. apply Hneq. injection Hc. auto.
      + (* tf_output dst expr *)
        apply NoDup_cons_iff in Hnd. destruct Hnd as [_ Hnd].
        rewrite IH by exact Hnd.
        destruct (find_st_update sched_ctx x (tfs_get_updates sched_ctx ops sys input)); try reflexivity.
        rewrite SemanticProperties.latest_write0_cons_neq.
        * apply latest_write0_expr_log_any.
        * intro Hc. discriminate Hc.
  Qed.

  (* CRUX BRIDGE (outputs): symmetric to the register version. *)
  Lemma latest_write0_aux_log_out :
    forall ops sys input log_a x,
      NoDup (affected_regs ops) ->
      latest_write0 (aux_log sys input ops log_a) (tf_out x) =
      match find_out_update sched_ctx x (tfs_get_updates sched_ctx ops sys input) with
      | Some v => Some v
      | None => latest_write0 log_a (tf_out x)
      end.
  Proof.
    induction ops as [| op ops IH]; intros sys input log_a x Hnd.
    - reflexivity.
    - rewrite aux_log_cons, tfs_get_updates_cons.
      destruct op; simpl affected_regs in Hnd;
        cbn [find_out_update tf_op_step_updates].
      + (* tf_nop *) apply IH. exact Hnd.
      + (* tf_assign dst expr *)
        apply NoDup_cons_iff in Hnd. destruct Hnd as [_ Hnd].
        rewrite IH by exact Hnd.
        destruct (find_out_update sched_ctx x (tfs_get_updates sched_ctx ops sys input)); try reflexivity.
        rewrite SemanticProperties.latest_write0_cons_neq.
        * apply latest_write0_expr_log_any.
        * intro Hc. discriminate Hc.
      + (* tf_output dst expr *)
        apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
        destruct (eq_dec dst x) as [Heq | Hneq].
        * subst dst.
          rewrite IH by exact Hnd.
          rewrite (find_out_update_not_affected ops sys input x Hnotin).
          rewrite SemanticProperties.latest_write0_cons_eq. reflexivity.
        * rewrite IH by exact Hnd.
          destruct (find_out_update sched_ctx x (tfs_get_updates sched_ctx ops sys input)); try reflexivity.
          rewrite SemanticProperties.latest_write0_cons_neq.
          -- apply latest_write0_expr_log_any.
          -- intro Hc. apply Hneq. injection Hc. auto.
  Qed.

  (* may_write at P0 means no write0 exists in either log, so latest_write0 is None. *)
  Lemma may_write0_latest_write0_None :
    forall (log_r log_a : Log R ContextEnv) (idx : reg_t),
      may_write log_r log_a P0 idx = true ->
      latest_write0 log_a idx = None /\ latest_write0 log_r idx = None.
  Proof.
    intros log_r log_a idx H.
    (* Keep may_write transparent through Qed: with it opaque the kernel refuses to
       unfold it and normalises the whole log/ContextEnv tower instead (~70 s). *)
    Local Transparent may_write.
    unfold may_write in H.
    apply andb_prop in H. destruct H as [H01 _].
    apply andb_prop in H01. destruct H01 as [_ Hw0].
    apply negb_true_iff in Hw0.
    rewrite SemanticProperties.log_existsb_app in Hw0.
    apply orb_false_iff in Hw0. destruct Hw0 as [Hw0a Hw0r].
    split.
    - exact (SemanticProperties.latest_write0_None (R:=R) (REnv:=REnv) log_a idx Hw0a).
    - exact (SemanticProperties.latest_write0_None (R:=R) (REnv:=REnv) log_r idx Hw0r).
  Qed.
  Local Opaque may_write.

  (* Value-level bridge: the HW value read at P1 for tf_reg x from the always-ops log
     (falling back to r) equals the abstract find_st_val over tfs_get_updates.
     The may_write hypothesis guarantees the pre-existing logs don't write tf_reg x,
     so the fallback threads through to r.[tf_reg x] = (fst sys).[x]. *)
  Lemma read_aux_log_reg_val :
    forall sys r ops input log_r log_a x,
      state_matches sys r ->
      NoDup (affected_regs ops) ->
      may_write_all log_r log_a P0 (map tf_reg spec_all_states) = true ->
      match latest_write0 (log_app (aux_log sys input ops log_a) log_r) (tf_reg x) with
      | Some v => v
      | None => r.[tf_reg x]
      end =
      find_st_val sched_ctx x (tfs_get_updates sched_ctx ops sys input) sys.
  Proof.
    intros sys r ops input log_r log_a x Hstate Hnd Hwr.
    unfold find_st_val.
    rewrite SemanticProperties.latest_write0_app.
    rewrite (latest_write0_aux_log_reg ops sys input log_a x Hnd).
    destruct (find_st_update sched_ctx x (tfs_get_updates sched_ctx ops sys input)) eqn:Hfind.
    - reflexivity.
    - pose proof (may_write_all_one_state log_r log_a P0 x Hwr) as Hw1.
      apply may_write0_latest_write0_None in Hw1. destruct Hw1 as [Hla Hlr].
      rewrite Hla, Hlr. destruct Hstate as [Hst _]. rewrite Hst. reflexivity.
  Qed.

  (* When the done-signal register has width 1, the HW gate `Bits.single (convert 1 v)`
     agrees with the abstract gate `negb (beq_dec v 0)`. *)
  Lemma convert1_single_beq :
    forall sz (v : bits_t sz),
      sz = 1 ->
      Bits.single (convert (szA:=sz) (szB:=1) v) = negb (beq_dec v Bits.zero).
  Proof.
    intros sz v Hsz. subst sz.
    unfold convert. destruct (eq_dec 1 1) as [e | n]; [| congruence].
    assert (e = eq_refl) as He by (apply Eqdep_dec.UIP_dec; exact PeanoNat.Nat.eq_dec).
    subst e. simpl.
    rewrite Common.bits_single_is_neg_beq_dec. rewrite negb_involutive. reflexivity.
  Qed.

  Definition construct_log (sys: sys_state_t) (act: spec_action) (input: input_t) (ready: bits_t 1) (log_a: Log R ContextEnv): Log R ContextEnv :=
    (* base = the log after running the always-ops on the guard log log_a. *)
    let base := aux_log sys input (fst (spec_schedule act)) log_a in
    (* read_log = base plus the P1 read of the done-state register that the
       done-gate `If`'s condition performs. *)
    let read_log := log_cons (R:=R) (REnv:=REnv) (tf_reg spec_done_state) Read1 base in
    (* The done-state gate mirrors tfs_next_cycle's `if beq_dec done_val 0`.
       done == 0  ->  not-done  ->  If's false branch (Const vect_nil): only the read.
       done != 0  ->  done      ->  run done-ops, reset the buffer regs at P1, set ready. *)
    if beq_dec (find_st_val sched_ctx spec_done_state
                  (tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input) sys) Bits.zero
    then read_log
    else
      log_cons (R:=R) (REnv:=REnv) tf_ready (Write1 Ob~1)
        (reset_log spec_reset_states
           (aux_log sys input (snd (spec_schedule act)) read_log)).

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

  (* The StOp/OutOp flat_map used by tfs_ops_no_duplicates. *)
  Local Notation ops_tags ops :=
    (flat_map (fun op =>
       match op with
       | tf_assign dst _ => [StOp dst]
       | tf_output dst _ => [OutOp dst]
       | _ => []
       end) ops).

  (* A state register appearing in affected_regs shows up as a StOp tag. *)
  Lemma affected_reg_in_ops_tags :
    forall ops x,
      In (tf_reg x) (affected_regs ops) -> In (StOp x) (ops_tags ops).
  Proof.
    induction ops as [| op ops IH]; intros x Hin; [ contradiction |].
    destruct op; simpl in *.
    - apply IH; assumption.
    - destruct Hin as [Heq | Hin].
      + left. injection Heq as ->. reflexivity.
      + right. apply IH; assumption.
    - (* tf_output: affected head is tf_out, cannot equal tf_reg x *)
      destruct Hin as [Heq | Hin]; [ discriminate Heq |].
      right. apply IH; assumption.
  Qed.

  (* The done register is not written by the done-ops (snd): it is assigned by the
     always-ops (fst), and NoDup over fst++snd forbids it appearing again in snd. *)
  Lemma done_not_in_affected_snd :
    forall act,
      ~ In (tf_reg spec_done_state) (affected_regs (snd (spec_schedule act))).
  Proof.
    intros act Hin.
    apply affected_reg_in_ops_tags in Hin.
    pose proof (tfs_done_signal_assigned_by_always (tf_sched_ctx tf_ctx) act) as Hfst.
    pose proof (spec_schedule_ops_nodup act) as Hnd.
    unfold tfs_ops_no_duplicates in Hnd.
    rewrite flat_map_app in Hnd.
    apply in_split in Hfst. destruct Hfst as [l1 [l2 Hsplit]].
    rewrite Hsplit in Hnd.
    rewrite <- app_assoc in Hnd. simpl in Hnd.
    apply NoDup_remove_2 in Hnd.
    apply Hnd. apply in_or_app. right. apply in_or_app. right. exact Hin.
  Qed.

  (* ---- Preservation helpers for the done-branch side-conditions ---- *)

  (* Generic: consing an entry that is not a P1 write preserves may_write at P1. *)
  Lemma may_write_log_cons_P1_not_w1 :
    forall log_r log_a idx k entry,
      is_write1 (kind entry) (port entry) = false ->
      may_write log_r (log_cons (R:=R) (REnv:=REnv) k entry log_a) P1 idx
      = may_write log_r log_a P1 idx.
  Proof.
    intros log_r log_a idx k entry Hw1.
    destruct (eq_dec idx k) as [Heq | Hneq].
    - subst k. rewrite may_write_log_cons_eq, Hw1. simpl.
      destruct (may_write log_r log_a P1 idx); reflexivity.
    - rewrite may_write_log_cons_neq by assumption. reflexivity.
  Qed.

  (* may_write_all version of the above. *)
  Lemma may_write_all_log_cons_P1_not_w1 :
    forall log_r log_a regs k entry,
      is_write1 (kind entry) (port entry) = false ->
      may_write_all log_r (log_cons (R:=R) (REnv:=REnv) k entry log_a) P1 regs
      = may_write_all log_r log_a P1 regs.
  Proof.
    intros log_r log_a regs k entry Hw1.
    unfold may_write_all. apply forallb_pointwise. intros idx Hin.
    apply may_write_log_cons_P1_not_w1. assumption.
  Qed.

  (* expr_log only conses LogRead entries, so it preserves may_write at P1. *)
  Lemma may_write_expr_log_P1 :
    forall log_r log_a sys input expr szB idx,
      may_write log_r (expr_log expr szB sys input log_a) P1 idx
      = may_write log_r log_a P1 idx.
  Proof.
    intros log_r log_a sys input expr szB idx.
    unfold expr_log.
    induction (snd (eval_expr_aux expr [] sys input)) as [| a l IH].
    - reflexivity.
    - simpl. rewrite may_write_log_cons_P1_not_w1 by reflexivity. exact IH.
  Qed.

  (* aux_log only conses Write0/LogRead entries, so it preserves may_write at P1. *)
  Lemma may_write_aux_log_P1 :
    forall ops sys input log_r idx log_a,
      may_write log_r (aux_log sys input ops log_a) P1 idx
      = may_write log_r log_a P1 idx.
  Proof.
    induction ops as [| op ops IH]; intros sys input log_r idx log_a.
    - reflexivity.
    - rewrite aux_log_cons. rewrite IH. destruct op.
      + reflexivity.
      + rewrite may_write_log_cons_P1_not_w1 by reflexivity.
        rewrite may_write_expr_log_P1. reflexivity.
      + rewrite may_write_log_cons_P1_not_w1 by reflexivity.
        rewrite may_write_expr_log_P1. reflexivity.
  Qed.

  Lemma may_write_all_aux_log_P1 :
    forall ops sys input log_r regs log_a,
      may_write_all log_r (aux_log sys input ops log_a) P1 regs
      = may_write_all log_r log_a P1 regs.
  Proof.
    intros ops sys input log_r regs log_a.
    unfold may_write_all. apply forallb_pointwise. intros idx Hin.
    apply may_write_aux_log_P1.
  Qed.

  (* One-step unfolding of the reset_log fold_left. *)
  Lemma reset_log_cons :
    forall s regs log_a,
      reset_log (s :: regs) log_a
      = reset_log regs (log_cons (R:=R) (REnv:=REnv) (tf_reg s) (Write1 Bits.zero) log_a).
  Proof. reflexivity. Qed.

  (* reset_log conses Write1 only on reset registers, so it preserves may_write on
     any register outside that set (any port). *)
  Lemma may_write_reset_log_neq :
    forall regs log_r prt idx log_a,
      ~ In idx (map tf_reg regs) ->
      may_write log_r (reset_log regs log_a) prt idx = may_write log_r log_a prt idx.
  Proof.
    induction regs as [| s regs IH]; intros log_r prt idx log_a Hnotin.
    - reflexivity.
    - rewrite reset_log_cons. simpl in Hnotin. apply Decidable.not_or in Hnotin.
      destruct Hnotin as [Hne Hnotin].
      rewrite IH by exact Hnotin.
      rewrite may_write_log_cons_neq by exact (not_eq_sym Hne). reflexivity.
  Qed.

  (* aux_log preserves inputs_are_buffered (it never writes tf_in registers). *)
  Lemma inputs_are_buffered_aux_log :
    forall ops sys input r log_a log_r,
      inputs_are_buffered input r (log_app log_a log_r) ->
      inputs_are_buffered input r (log_app (aux_log sys input ops log_a) log_r).
  Proof.
    induction ops as [| op ops IH]; intros sys input r log_a log_r Hbuf.
    - exact Hbuf.
    - rewrite aux_log_cons. apply IH. destruct op.
      + exact Hbuf.
      + apply inputs_are_buffered_log_app_log_cons_neq.
        * apply not_in_reg_reg_all_inputs.
        * apply inputs_are_buffered_expr_log. exact Hbuf.
      + apply inputs_are_buffered_log_app_log_cons_neq.
        * apply not_in_reg_out_all_inputs.
        * apply inputs_are_buffered_expr_log. exact Hbuf.
  Qed.

  (* Generalized version of may_write_all_expr_log to an arbitrary register list that
     contains no input register. *)
  Lemma may_write_all_expr_log_gen :
    forall log_r log_a sys input expr szB regs,
      (forall i, ~ In (tf_in i) regs) ->
      may_write_all log_r log_a P0 regs = true ->
      may_write_all log_r (expr_log expr szB sys input log_a) P0 regs = true.
  Proof.
    intros log_r log_a sys input expr szB regs Hnoin Hwr.
    unfold may_write_all in *. rewrite forallb_forall in *.
    intros reg Hin. apply may_write_expr_log.
    - intros i Heq. apply (Hnoin i). rewrite Heq. exact Hin.
    - apply Hwr. exact Hin.
  Qed.

  (* aux_log preserves may_write at P0 on a register list disjoint from the ops'
     affected registers (and containing no input register). *)
  Lemma may_write_all_aux_log_P0 :
    forall ops sys input log_r regs log_a,
      (forall reg, In reg regs -> ~ In reg (affected_regs ops)) ->
      (forall i, ~ In (tf_in i) regs) ->
      may_write_all log_r log_a P0 regs = true ->
      may_write_all log_r (aux_log sys input ops log_a) P0 regs = true.
  Proof.
    induction ops as [| op ops IH]; intros sys input log_r regs log_a Hdisj Hnoin Hwr.
    - exact Hwr.
    - rewrite aux_log_cons. apply IH.
      + intros reg Hin Hin2. apply (Hdisj reg Hin).
        destruct op; simpl; (exact Hin2 || (right; exact Hin2)).
      + exact Hnoin.
      + destruct op.
        * exact Hwr.
        * rewrite may_write_all_log_cons_neq.
          -- apply may_write_all_expr_log_gen; assumption.
          -- intro Hin. apply (Hdisj (tf_reg dst) Hin). simpl. left. reflexivity.
        * rewrite may_write_all_log_cons_neq.
          -- apply may_write_all_expr_log_gen; assumption.
          -- intro Hin. apply (Hdisj (tf_out dst) Hin). simpl. left. reflexivity.
  Qed.

  (* An output register appearing in affected_regs shows up as an OutOp tag. *)
  Lemma affected_out_in_ops_tags :
    forall ops x,
      In (tf_out x) (affected_regs ops) -> In (OutOp x) (ops_tags ops).
  Proof.
    induction ops as [| op ops IH]; intros x Hin; [ contradiction |].
    destruct op; simpl in *.
    - apply IH; assumption.
    - destruct Hin as [Heq | Hin]; [ discriminate Heq | right; apply IH; assumption ].
    - destruct Hin as [Heq | Hin];
        [ left; injection Heq as ->; reflexivity | right; apply IH; assumption ].
  Qed.

  (* Every affected register is a state (tf_reg) or an output (tf_out). *)
  Lemma affected_regs_shape :
    forall ops reg,
      In reg (affected_regs ops) ->
      (exists x, reg = tf_reg x) \/ (exists x, reg = tf_out x).
  Proof.
    induction ops as [| op ops IH]; intros reg Hin; [ contradiction |].
    destruct op; simpl in *.
    - apply IH; assumption.
    - destruct Hin as [<- | Hin]; [ left; eexists; reflexivity | apply IH; assumption ].
    - destruct Hin as [<- | Hin]; [ right; eexists; reflexivity | apply IH; assumption ].
  Qed.

  Lemma NoDup_app_disjoint {A: Type} :
    forall (l1 l2 : list A) x,
      NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
  Proof.
    intros l1 l2 x Hnd H1 H2.
    apply in_split in H1. destruct H1 as [a [b Heq]]. subst l1.
    rewrite <- app_assoc in Hnd. simpl in Hnd.
    apply NoDup_remove_2 in Hnd. apply Hnd.
    apply in_or_app. right. apply in_or_app. right. exact H2.
  Qed.

  Lemma NoDup_map_inj {A B: Type} (f: A -> B) :
    (forall a b, f a = f b -> a = b) ->
    forall l, NoDup l -> NoDup (map f l).
  Proof.
    intros Hinj l. induction l as [| a l IH]; simpl; intros Hnd.
    - constructor.
    - inversion Hnd; subst. constructor.
      + intro Hin. apply in_map_iff in Hin.
        destruct Hin as [b [Heq Hin]]. apply Hinj in Heq. subst. contradiction.
      + apply IH; assumption.
  Qed.

  (* The always-ops (fst) and done-ops (snd) affect disjoint register sets. *)
  Lemma affected_fst_snd_disjoint :
    forall act reg,
      In reg (affected_regs (fst (spec_schedule act))) ->
      ~ In reg (affected_regs (snd (spec_schedule act))).
  Proof.
    intros act reg Hfst Hsnd.
    pose proof (spec_schedule_ops_nodup act) as Hnd.
    unfold tfs_ops_no_duplicates in Hnd. rewrite flat_map_app in Hnd.
    destruct (affected_regs_shape _ _ Hfst) as [[x ->] | [x ->]].
    - eapply NoDup_app_disjoint;
        [ exact Hnd | apply affected_reg_in_ops_tags; exact Hfst
        | apply affected_reg_in_ops_tags; exact Hsnd ].
    - eapply NoDup_app_disjoint;
        [ exact Hnd | apply affected_out_in_ops_tags; exact Hfst
        | apply affected_out_in_ops_tags; exact Hsnd ].
  Qed.

  Lemma interp_action_cmd :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log_r log_a,
      state_matches sys r ->
      externs_match sigma ->
      may_read_all log_r P0 (map tf_reg spec_all_states) = true ->
      may_write_all log_r log_a P0 (map tf_reg spec_all_states) = true ->
      may_read_all log_r P1 (map tf_in spec_all_inputs) = true ->
      may_read_all log_r P0 (map tf_out spec_all_outputs) = true ->
      may_write_all log_r log_a P0 (map tf_out spec_all_outputs) = true ->
      may_write log_r log_a P1 tf_ready = true ->
      inputs_are_buffered input r (log_app log_a log_r) ->
      match interp_action r sigma CtxEmpty log_r log_a (_rule_cmd tf_ctx act) with
      | Some (l, v, _) => Some (l)
      | None => None
      end =
      Some ( construct_log sys act input r.[tf_ready] log_a ).
  Proof.
    intros sys r act input sigma log_r log_a.
    intros Hstate Hsig Hrd0_st Hwr0_st Hrd1_in Hrd0_out Hwr0_out Hwr1_ready Hin_buf.
    
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

    (* Step the done-gate `If`: evaluate its P1 read of the done-state register,
       reduce the guard `Bits.single (convert 1 done)` to `negb (beq_dec done 0)`. *)
    rewrite interp_action_if.
    rewrite interp_synth_convert.
    (* Reduce the done-state P1 read directly (its interp carries tau := bits_t (size done)
       from synth_convert, so an interp_action_read1 rewrite won't match the implicit tau). *)
    assert (Hmr : may_read log_r P1 (tf_reg spec_done_state) = true)
      by (apply may_read0_implies_may_read1; apply (may_read_all_one_state _ _ _ Hrd0_st)).
    cbn [interp_action]. rewrite Hmr. clear Hmr.
    cbn [opt_bind].
    rewrite (convert1_single_beq _ _ (tfs_done_signal_size sched_ctx)).
    rewrite (read_aux_log_reg_val sys r (fst (spec_schedule act)) input log_r log_a
               spec_done_state Hstate (nodup_affected_regs_fst act) Hwr0_st).
    unfold construct_log.
    destruct (beq_dec (find_st_val sched_ctx spec_done_state
                (tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input) sys) Bits.zero) eqn:Hdv.
    - (* done = 0: not-done, take the If's false branch (Const vect_nil). *)
      cbn [interp_action]. reflexivity.
    - (* done <> 0: run the done-ops, reset buffers, set ready. *)
      cbn [negb].
      (* Auxiliary facts shared by several side-conditions. *)
      assert (Hwr1_reset : may_write_all log_r log_a P1 (map tf_reg spec_reset_states) = true).
      { unfold may_write_all. rewrite forallb_forall. intros reg Hreg.
        rewrite in_map_iff in Hreg. destruct Hreg as [s [Heq Hin]]. subst reg.
        apply may_write0_implies_may_write1.
        unfold may_write_all in Hwr0_st. rewrite forallb_forall in Hwr0_st.
        apply Hwr0_st. apply in_map. exact (in_spec_all_states s). }
      assert (Hwr0_snd : may_write_all log_r log_a P0 (affected_regs (snd (spec_schedule act))) = true).
      { unfold may_write_all. rewrite forallb_forall. intros reg Hin.
        destruct (affected_regs_shape _ _ Hin) as [[x ->] | [x ->]].
        - unfold may_write_all in Hwr0_st. rewrite forallb_forall in Hwr0_st.
          apply Hwr0_st. apply in_map. exact (in_spec_all_states x).
        - unfold may_write_all in Hwr0_out. rewrite forallb_forall in Hwr0_out.
          apply Hwr0_out. apply in_map. exact (in_spec_all_outputs x). }
      (* Step the done-ops (snd) via interp_action_aux onto read_log. *)
      set (read_log := log_cons (R:=R) (REnv:=REnv) (tf_reg spec_done_state) Read1
                         (aux_log sys input (fst (spec_schedule act)) log_a)) in *.
      rewrite (interp_action_aux sys r act input sigma log_r read_log
                 (snd (spec_schedule act))
                 (rule_reset_buffers tf_ctx spec_reset_states
                    (Write P1 tf_ready (Const (tau:=bits_t 1) Ob~1)))).
      + (* after aux_log(snd): step reset buffers then the ready write *)
        rewrite (interp_action_reset_buffers r sigma log_r spec_reset_states
                   (Write P1 tf_ready (Const (tau:=bits_t 1) Ob~1))
                   (aux_log sys input (snd (spec_schedule act)) read_log)).
        * rewrite interp_action_write_const.
          -- reflexivity.
          -- (* may_write log_r (reset_log …) P1 tf_ready *)
             rewrite may_write_reset_log_neq.
             2:{ intro H. rewrite in_map_iff in H.
                 destruct H as [s [Heq _]]. discriminate Heq. }
             rewrite may_write_aux_log_P1. unfold read_log.
             rewrite may_write_log_cons_P1_not_w1 by reflexivity.
             rewrite may_write_aux_log_P1.
             exact Hwr1_ready.
        * (* NoDup (map tf_reg spec_reset_states) *)
          apply NoDup_map_inj.
          -- intros a b Heq. congruence.
          -- exact (tfs_reset_states_nodup sched_ctx).
        * (* may_write_all log_r (aux_log … (snd) read_log) P1 (map tf_reg spec_reset_states) *)
          rewrite may_write_all_aux_log_P1. unfold read_log.
          rewrite may_write_all_log_cons_P1_not_w1 by reflexivity.
          rewrite may_write_all_aux_log_P1. exact Hwr1_reset.
      + exact Hstate.
      + exact Hsig.
      + exact Hrd0_st.
      + exact Hrd1_in.
      + exact Hrd0_out.
      + (* inputs_are_buffered input r (log_app read_log log_r) *)
        unfold read_log.
        apply inputs_are_buffered_log_app_log_cons_neq.
        * apply not_in_reg_reg_all_inputs.
        * apply inputs_are_buffered_aux_log. exact Hin_buf.
      + exact (nodup_affected_regs_snd act).
      + (* may_write_all log_r read_log P0 (affected_regs (snd)) *)
        unfold read_log.
        rewrite may_write_all_log_cons_neq by (apply done_not_in_affected_snd).
        apply may_write_all_aux_log_P0.
        * intros reg Hin Hin2. exact (affected_fst_snd_disjoint act reg Hin2 Hin).
        * intros i. apply (inputs_not_affected (snd (spec_schedule act)) i).
        * exact Hwr0_snd.
  Qed.

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

  (* Folding the input-buffer writes leaves latest_write0 untouched on a register
     whose input is not in the folded list. *)
  Lemma latest_write0_input_fold_neq :
    forall (inputs: list spec_inputs) (sigma: forall f, Sig_denote (Sigma f)) log2 a,
      ~ In a inputs ->
      latest_write0
        (fold_left (fun log x => log_cons (R:=R) (REnv:=REnv) (tf_in x)
                     (Write0 (sigma (ext_input x) Ob~1)) log) inputs log2) (tf_in a)
      = latest_write0 log2 (tf_in a).
  Proof.
    induction inputs as [| b inputs IH]; intros sigma log2 a Hnotin.
    - reflexivity.
    - simpl. rewrite IH by (intro; apply Hnotin; right; assumption).
      rewrite SemanticProperties.latest_write0_cons_neq. reflexivity.
      intro Heq. apply Hnotin. left. injection Heq as ->. reflexivity.
  Qed.

  (* For an input in the folded (NoDup) list, latest_write0 returns its buffered value. *)
  Lemma latest_write0_input_fold_eq :
    forall (inputs: list spec_inputs) (sigma: forall f, Sig_denote (Sigma f)) log2 v,
      In v inputs -> NoDup inputs ->
      latest_write0
        (fold_left (fun log x => log_cons (R:=R) (REnv:=REnv) (tf_in x)
                     (Write0 (sigma (ext_input x) Ob~1)) log) inputs log2) (tf_in v)
      = Some (sigma (ext_input v) Ob~1).
  Proof.
    induction inputs as [| b inputs IH]; intros sigma log2 v Hin Hnd.
    - contradiction.
    - simpl. inversion Hnd as [| ? ? Hnotin Hnd']; subst.
      destruct Hin as [-> | Hin].
      + rewrite latest_write0_input_fold_neq by exact Hnotin.
        rewrite SemanticProperties.latest_write0_cons_eq. reflexivity.
      + apply IH; assumption.
  Qed.

  (* The command-guard log buffers all inputs: whichever branch runs, the resulting
     log satisfies inputs_are_buffered (needed to feed interp_action_cmd). *)
  Lemma inputs_are_buffered_guard_log :
    forall (r: ContextEnv.(env_t) R) (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f)) log,
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      may_write_all log log_empty P0 (map tf_in spec_all_inputs) = true ->
      inputs_are_buffered input r
        (log_app (if Bits.single r.[tf_ready]
                  then log_after_cmd_guard_rdy act sigma
                  else log_cons tf_cmd Read0 (log_cons tf_ready Read0 log_empty)) log).
  Proof.
    intros r act input sigma log Hrdy Hnrdy Hwr0_in.
    unfold inputs_are_buffered. intros v.
    destruct (reg_ready_or_not r) as [Hready | Hnotready].
    - rewrite Hready. replace (Bits.single Ob~1) with true by reflexivity. cbv iota.
      left. unfold log_after_cmd_guard_rdy.
      rewrite SemanticProperties.latest_write0_app.
      rewrite SemanticProperties.latest_write0_cons_neq by discriminate.
      rewrite SemanticProperties.latest_write0_cons_neq by discriminate.
      rewrite latest_write0_input_fold_eq by (apply in_spec_all_inputs || apply nodup_spec_all_inputs).
      destruct (Hrdy Hready) as [_ [_ Hin]]. rewrite (Hin v). reflexivity.
    - rewrite Hnotready. replace (Bits.single Ob~0) with false by reflexivity. cbv iota.
      rewrite SemanticProperties.latest_write0_app.
      rewrite SemanticProperties.latest_write0_cons_neq by discriminate.
      rewrite SemanticProperties.latest_write0_cons_neq by discriminate.
      rewrite SemanticProperties.latest_write0_empty.
      assert (Hmw : may_write log log_empty P0 (tf_in v) = true).
      { unfold may_write_all in Hwr0_in. rewrite forallb_forall in Hwr0_in.
        apply Hwr0_in. apply in_map. apply in_spec_all_inputs. }
      apply may_write0_latest_write0_None in Hmw. destruct Hmw as [_ Hlr].
      right. rewrite Hlr. split; [ reflexivity |].
      destruct (Hnrdy Hnotready) as [_ Hin]. exact (Hin v).
  Qed.

  Lemma interp_rule_correct :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R)
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log,
      state_matches sys r ->
      externs_match sigma ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      good_log log ->
      let guard_log := if Bits.single r.[tf_ready] then log_after_cmd_guard_rdy act sigma else log_cons tf_cmd Read0 (log_cons tf_ready Read0 log_empty) in
      interp_rule r sigma log (rules (rule_cmd act)) = Some (construct_log sys act input r.[tf_ready] guard_log).
  Proof.
    intros sys r act input sigma log Hstate Hsig Hinput_rdy Hinput_nrdy Hgood.
    cbv zeta.
    unfold good_log in Hgood.
    destruct Hgood as [Hrd0_st [Hwr0_st [Hrd0_in [Hwr0_in [Hrd0_out
                       [Hwr0_out [Hrd0_rdy [Hwr0_ready [Hrd0_cmd Hwr0_cmd]]]]]]]]].
    unfold interp_rule, rules.

    rewrite interp_action_seq. unfold opt_bind.
    rewrite (interp_action_cmd_guard sys r act input sigma log); try assumption.

    setoid_rewrite (interp_action_cmd sys r act input sigma log
              (if Bits.single r.[tf_ready]
                then log_after_cmd_guard_rdy act sigma
                else log_cons tf_cmd Read0 (log_cons tf_ready Read0 log_empty))).
    - reflexivity.
    - exact Hstate.
    - exact Hsig.
    - exact Hrd0_st.
    - (* may_write_all log guard_log P0 states *)
      destruct (reg_ready_or_not r) as [Hready | Hnotready].
      + rewrite Hready. cbn. unfold log_after_cmd_guard_rdy.
        rewrite !may_write_all_log_cons_neq. rewrite may_write_all_fold_cons_w0_inputs. rewrite !may_write_all_log_cons_neq. exact Hwr0_st.
        all: (try exact not_in_reg_ready_all_states); (try exact not_in_reg_cmd_all_states).
        intros. rewrite in_map_iff in H. destruct H as [x0 [Heq Hin]]. subst. exact (not_in_reg_reg_all_inputs x0).
      + rewrite Hnotready. cbn. rewrite !may_write_all_log_cons_neq. exact Hwr0_st.
        all: (try exact not_in_reg_ready_all_states); (try exact not_in_reg_cmd_all_states).
    - (* may_read_all log P1 inputs *)
      apply may_read_all0_implies_may_read_all1. exact Hrd0_in.
    - exact Hrd0_out.
    - (* may_write_all log guard_log P0 outputs *)
      destruct (reg_ready_or_not r) as [Hready | Hnotready].
      + rewrite Hready. cbn. unfold log_after_cmd_guard_rdy.
        rewrite !may_write_all_log_cons_neq. rewrite may_write_all_fold_cons_w0_inputs. rewrite !may_write_all_log_cons_neq. exact Hwr0_out.
        all: (try exact not_in_reg_ready_all_outputs); (try exact not_in_reg_cmd_all_outputs).
        intros. rewrite in_map_iff in H. destruct H as [x0 [Heq Hin]]. subst. exact (not_in_reg_out_all_inputs x0).
      + rewrite Hnotready. cbn. rewrite !may_write_all_log_cons_neq. exact Hwr0_out.
        all: (try exact not_in_reg_ready_all_outputs); (try exact not_in_reg_cmd_all_outputs).
    - (* may_write log guard_log P1 tf_ready *)
      destruct (reg_ready_or_not r) as [Hready | Hnotready].
      + rewrite Hready. cbn. unfold log_after_cmd_guard_rdy.
        rewrite may_write_log_cons_eq. rewrite may_write_log_cons_neq.
        rewrite may_write_fold_cons_w0_inputs. rewrite !may_write_log_cons_eq. simpl. rewrite !andb_true_r.
        * apply may_write0_implies_may_write1. exact Hwr0_ready.
        * exact not_in_reg_ready_all_inputs.
        * intro. congruence.
      + rewrite Hnotready. cbn. rewrite may_write_log_cons_neq. rewrite may_write_log_cons_eq. simpl. rewrite !andb_true_r.
        * apply may_write0_implies_may_write1. exact Hwr0_ready.
        * intro. congruence.
    - (* inputs_are_buffered input r (log_app guard_log log) *)
      apply inputs_are_buffered_guard_log; assumption.
  Qed.

  (* ---- latest_write (combined-port) transport lemmas for reading off construct_log ---- *)

  (* may_write P0 forbids BOTH write0 and write1, so latest_write is None. *)
  Lemma may_write0_latest_write_None :
    forall (log : Log R ContextEnv) (idx : reg_t),
      may_write log log_empty P0 idx = true ->
      latest_write log idx = None.
  Proof.
    intros log idx H.
    (* Keep may_write transparent through Qed: see may_write0_latest_write0_None. *)
    Local Transparent may_write.
    unfold may_write in H.
    apply andb_prop in H. destruct H as [H01 Hw1].
    apply andb_prop in H01. destruct H01 as [_ Hw0].
    apply negb_true_iff in Hw0. apply negb_true_iff in Hw1.
    rewrite SemanticProperties.log_existsb_app in Hw0.
    rewrite SemanticProperties.log_existsb_app in Hw1.
    apply orb_false_iff in Hw0. destruct Hw0 as [_ Hw0log].
    apply orb_false_iff in Hw1. destruct Hw1 as [_ Hw1log].
    exact (SemanticProperties.latest_write_None (R:=R) (REnv:=REnv) log idx Hw0log Hw1log).
  Qed.
  Local Opaque may_write.

  (* expr_log only conses LogRead entries, so latest_write ignores it (any reg). *)
  Lemma latest_write_expr_log_any :
    forall expr szB sys input log_a reg,
      latest_write (expr_log expr szB sys input log_a) reg =
      latest_write log_a reg.
  Proof.
    intros expr szB sys input log_a reg.
    unfold expr_log.
    induction ((snd (eval_expr_aux expr [] sys input))).
    - reflexivity.
    - destruct (eq_dec reg a) as [Heq | Hneq]; subst.
      + simpl. rewrite SemanticProperties.latest_write_cons_eq. exact IHl.
      + simpl. rewrite SemanticProperties.latest_write_cons_neq; assumption.
  Qed.

  (* aux_log conses Write0 only on tf_reg/tf_out of affected ops; latest_write
     is unchanged on any register outside those constructors. *)
  Lemma latest_write_aux_log_neq :
    forall ops sys input log_a idx,
      (forall dst, idx <> tf_reg dst) ->
      (forall dst, idx <> tf_out dst) ->
      latest_write (aux_log sys input ops log_a) idx = latest_write log_a idx.
  Proof.
    induction ops as [| op ops IH]; intros sys input log_a idx Hreg Hout.
    - reflexivity.
    - rewrite aux_log_cons. rewrite IH by assumption. destruct op.
      + reflexivity.
      + rewrite SemanticProperties.latest_write_cons_neq by (apply Hreg).
        apply latest_write_expr_log_any.
      + rewrite SemanticProperties.latest_write_cons_neq by (apply Hout).
        apply latest_write_expr_log_any.
  Qed.

  (* reset_log conses Write1 only on tf_reg of reset states; latest_write is
     unchanged on any register outside that set. *)
  Lemma latest_write_reset_log_neq :
    forall regs log_a idx,
      (forall s, idx <> tf_reg s) ->
      latest_write (reset_log regs log_a) idx = latest_write log_a idx.
  Proof.
    induction regs as [| s regs IH]; intros log_a idx Hreg.
    - reflexivity.
    - rewrite reset_log_cons. rewrite IH by assumption.
      rewrite SemanticProperties.latest_write_cons_neq by (apply Hreg).
      reflexivity.
  Qed.

  (* construct_log only writes tf_reg/tf_out registers and tf_ready; on any other
     register it agrees with the guard log it is built from. *)
  Lemma latest_write_construct_log_neq :
    forall sys act input ready guard_log idx,
      (forall dst, idx <> tf_reg dst) ->
      (forall dst, idx <> tf_out dst) ->
      idx <> tf_ready ->
      latest_write (construct_log sys act input ready guard_log) idx =
      latest_write guard_log idx.
  Proof.
    intros sys act input ready guard_log idx Hreg Hout Hrdy.
    unfold construct_log.
    destruct (beq_dec _ _).
    - rewrite SemanticProperties.latest_write_cons_neq by (apply Hreg).
      apply latest_write_aux_log_neq; assumption.
    - rewrite SemanticProperties.latest_write_cons_neq by exact Hrdy.
      rewrite latest_write_reset_log_neq by (intros s; apply Hreg).
      rewrite latest_write_aux_log_neq by assumption.
      rewrite SemanticProperties.latest_write_cons_neq by (apply Hreg).
      apply latest_write_aux_log_neq; assumption.
  Qed.

  (* Folding the input-buffer writes: latest_write matches latest_write0 shape. *)
  Lemma latest_write_input_fold_neq :
    forall (inputs: list spec_inputs) (sigma: forall f, Sig_denote (Sigma f)) log2 a,
      ~ In a inputs ->
      latest_write
        (fold_left (fun log x => log_cons (R:=R) (REnv:=REnv) (tf_in x)
                     (Write0 (sigma (ext_input x) Ob~1)) log) inputs log2) (tf_in a)
      = latest_write log2 (tf_in a).
  Proof.
    induction inputs as [| b inputs IH]; intros sigma log2 a Hnotin.
    - reflexivity.
    - simpl. rewrite IH by (intro; apply Hnotin; right; assumption).
      rewrite SemanticProperties.latest_write_cons_neq. reflexivity.
      intro Heq. apply Hnotin. left. injection Heq as ->. reflexivity.
  Qed.

  Lemma latest_write_input_fold_eq :
    forall (inputs: list spec_inputs) (sigma: forall f, Sig_denote (Sigma f)) log2 v,
      In v inputs -> NoDup inputs ->
      latest_write
        (fold_left (fun log x => log_cons (R:=R) (REnv:=REnv) (tf_in x)
                     (Write0 (sigma (ext_input x) Ob~1)) log) inputs log2) (tf_in v)
      = Some (sigma (ext_input v) Ob~1).
  Proof.
    induction inputs as [| b inputs IH]; intros sigma log2 v Hin Hnd.
    - contradiction.
    - simpl. inversion Hnd as [| ? ? Hnotin Hnd']; subst.
      destruct Hin as [-> | Hin].
      + rewrite latest_write_input_fold_neq by exact Hnotin.
        rewrite SemanticProperties.latest_write_cons_eq. reflexivity.
      + apply IH; assumption.
  Qed.

  Lemma latest_write_cmd_rdy :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log,
      state_matches sys r ->
      externs_match sigma ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      good_log log ->
      r.[tf_ready] = Ob~1 ->
      latest_write match interp_rule r sigma log (rules (rule_cmd act)) with
        | Some l => log_app l log
        | None => log
        end tf_cmd = Some (spec_action_encoding act).
  Proof.
    intros sys r act input sigma log Hstate Hsig Hin_rdy Hin_nrdy Hgood Hrdy.
    rewrite (interp_rule_correct sys r act input sigma log Hstate Hsig Hin_rdy Hin_nrdy Hgood).
    cbv zeta.
    rewrite Hrdy. replace (Bits.single Ob~1) with true by reflexivity. cbv iota.
    rewrite SemanticProperties.latest_write_app.
    rewrite latest_write_construct_log_neq by (intros; discriminate).
    unfold log_after_cmd_guard_rdy.
    rewrite SemanticProperties.latest_write_cons_neq by discriminate.
    rewrite SemanticProperties.latest_write_cons_eq. reflexivity.
  Qed.

  Lemma latest_write_cmd_nrdy :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log,
      state_matches sys r ->
      externs_match sigma ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      good_log log ->
      r.[tf_ready] = Ob~0 ->
      latest_write match interp_rule r sigma log (rules (rule_cmd act)) with
        | Some l => log_app l log
        | None => log
        end tf_cmd = None.
  Proof.
    intros sys r act input sigma log Hstate Hsig Hin_rdy Hin_nrdy Hgood Hnrdy.
    assert (Hcmd : may_write log log_empty P0 tf_cmd = true).
    { unfold good_log in Hgood.
      destruct Hgood as [_ [_ [_ [_ [_ [_ [_ [_ [_ Hwr0_cmd]]]]]]]]]. exact Hwr0_cmd. }
    pose proof (may_write0_latest_write_None log tf_cmd Hcmd) as Hnone.
    rewrite (interp_rule_correct sys r act input sigma log Hstate Hsig Hin_rdy Hin_nrdy Hgood).
    cbv zeta.
    rewrite Hnrdy. replace (Bits.single Ob~0) with false by reflexivity. cbv iota.
    rewrite SemanticProperties.latest_write_app.
    rewrite latest_write_construct_log_neq by (intros; discriminate).
    rewrite SemanticProperties.latest_write_cons_eq.
    rewrite SemanticProperties.latest_write_cons_neq by discriminate.
    rewrite SemanticProperties.latest_write_empty.
    exact Hnone.
  Qed.

  Lemma latest_write_input_rdy :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log x,
      state_matches sys r ->
      externs_match sigma ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      good_log log ->
      r.[tf_ready] = Ob~1 ->
      latest_write match interp_rule r sigma log (rules (rule_cmd act)) with
        | Some l => log_app l log
        | None => log
        end (tf_in x) = Some (input x).
  Proof.
    intros sys r act input sigma log x Hstate Hsig Hin_rdy Hin_nrdy Hgood Hrdy.
    rewrite (interp_rule_correct sys r act input sigma log Hstate Hsig Hin_rdy Hin_nrdy Hgood).
    cbv zeta.
    rewrite Hrdy. replace (Bits.single Ob~1) with true by reflexivity. cbv iota.
    rewrite SemanticProperties.latest_write_app.
    rewrite latest_write_construct_log_neq by (intros; discriminate).
    unfold log_after_cmd_guard_rdy.
    rewrite SemanticProperties.latest_write_cons_neq by discriminate.
    rewrite SemanticProperties.latest_write_cons_neq by discriminate.
    rewrite latest_write_input_fold_eq by (apply in_spec_all_inputs || apply nodup_spec_all_inputs).
    destruct (Hin_rdy Hrdy) as [_ [_ Hin]]. rewrite (Hin x). reflexivity.
  Qed.

  Lemma latest_write_input_nrdy :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log x,
      state_matches sys r ->
      externs_match sigma ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      good_log log ->
      r.[tf_ready] = Ob~0 ->
      latest_write match interp_rule r sigma log (rules (rule_cmd act)) with
        | Some l => log_app l log
        | None => log
        end (tf_in x) = None.
  Proof.
    intros sys r act input sigma log x Hstate Hsig Hin_rdy Hin_nrdy Hgood Hnrdy.
    assert (Hin_none : may_write log log_empty P0 (tf_in x) = true).
    { unfold good_log in Hgood.
      destruct Hgood as [_ [_ [_ [Hwr0_in [_ [_ [_ [_ [_ _]]]]]]]]].
      unfold may_write_all in Hwr0_in. rewrite forallb_forall in Hwr0_in.
      apply Hwr0_in. apply in_map. apply in_spec_all_inputs. }
    pose proof (may_write0_latest_write_None log (tf_in x) Hin_none) as Hnone.
    rewrite (interp_rule_correct sys r act input sigma log Hstate Hsig Hin_rdy Hin_nrdy Hgood).
    cbv zeta.
    rewrite Hnrdy. replace (Bits.single Ob~0) with false by reflexivity. cbv iota.
    rewrite SemanticProperties.latest_write_app.
    rewrite latest_write_construct_log_neq by (intros; discriminate).
    rewrite SemanticProperties.latest_write_cons_neq by discriminate.
    rewrite SemanticProperties.latest_write_cons_neq by discriminate.
    rewrite SemanticProperties.latest_write_empty.
    exact Hnone.
  Qed.

  (* ---- value-bridge lemmas for tf_reg / tf_out over construct_log ---- *)

  Lemma tfs_reset_updates_cons :
    forall a regs,
      tfs_reset_updates sched_ctx (a :: regs) =
      tf_st_update _ _ a (tfs_states_init sched_ctx a) :: tfs_reset_updates sched_ctx regs.
  Proof. reflexivity. Qed.

  Lemma find_st_update_app :
    forall x a b,
      find_st_update sched_ctx x (a ++ b) =
      match find_st_update sched_ctx x a with
      | Some v => Some v
      | None => find_st_update sched_ctx x b
      end.
  Proof.
    intros x a b. induction a as [| u a IH].
    - reflexivity.
    - rewrite <- app_comm_cons. destruct u as [| var val | var val]; cbn [find_st_update].
      + apply IH.
      + destruct (eq_dec var x) as [e | n]; [ subst x; reflexivity | apply IH ].
      + apply IH.
  Qed.

  Lemma find_out_update_app :
    forall x a b,
      find_out_update sched_ctx x (a ++ b) =
      match find_out_update sched_ctx x a with
      | Some v => Some v
      | None => find_out_update sched_ctx x b
      end.
  Proof.
    intros x a b. induction a as [| u a IH].
    - reflexivity.
    - rewrite <- app_comm_cons. destruct u as [| var val | var val]; cbn [find_out_update].
      + apply IH.
      + apply IH.
      + destruct (eq_dec var x) as [e | n]; [ subst x; reflexivity | apply IH ].
  Qed.

  Lemma find_st_update_reset_None :
    forall regs x, ~ In x regs ->
      find_st_update sched_ctx x (tfs_reset_updates sched_ctx regs) = None.
  Proof.
    induction regs as [| a regs IH]; intros x Hnotin.
    - reflexivity.
    - apply Decidable.not_or in Hnotin. destruct Hnotin as [Hne Hnotin].
      rewrite tfs_reset_updates_cons. cbn [find_st_update].
      destruct (eq_dec a x) as [Heq | Hneq].
      + subst. contradiction Hne. reflexivity.
      + apply IH. exact Hnotin.
  Qed.

  Lemma find_out_update_reset_None :
    forall regs x,
      find_out_update sched_ctx x (tfs_reset_updates sched_ctx regs) = None.
  Proof.
    induction regs as [| a regs IH]; intros x.
    - reflexivity.
    - rewrite tfs_reset_updates_cons. cbn [find_out_update]. apply IH.
  Qed.

  (* Combined-port aux_log register bridge (mirrors latest_write0_aux_log_reg). *)
  Lemma latest_write_aux_log_reg :
    forall ops sys input log_a x,
      NoDup (affected_regs ops) ->
      latest_write (aux_log sys input ops log_a) (tf_reg x) =
      match find_st_update sched_ctx x (tfs_get_updates sched_ctx ops sys input) with
      | Some v => Some v
      | None => latest_write log_a (tf_reg x)
      end.
  Proof.
    induction ops as [| op ops IH]; intros sys input log_a x Hnd.
    - reflexivity.
    - rewrite aux_log_cons, tfs_get_updates_cons.
      destruct op; simpl affected_regs in Hnd;
        cbn [find_st_update tf_op_step_updates].
      + apply IH. exact Hnd.
      + apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
        destruct (eq_dec dst x) as [Heq | Hneq].
        * subst dst.
          rewrite IH by exact Hnd.
          rewrite (find_st_update_not_affected ops sys input x Hnotin).
          rewrite SemanticProperties.latest_write_cons_eq. reflexivity.
        * rewrite IH by exact Hnd.
          destruct (find_st_update sched_ctx x (tfs_get_updates sched_ctx ops sys input)); try reflexivity.
          rewrite SemanticProperties.latest_write_cons_neq.
          -- apply latest_write_expr_log_any.
          -- intro Hc. apply Hneq. injection Hc. auto.
      + apply NoDup_cons_iff in Hnd. destruct Hnd as [_ Hnd].
        rewrite IH by exact Hnd.
        destruct (find_st_update sched_ctx x (tfs_get_updates sched_ctx ops sys input)); try reflexivity.
        rewrite SemanticProperties.latest_write_cons_neq.
        * apply latest_write_expr_log_any.
        * intro Hc. discriminate Hc.
  Qed.

  Lemma latest_write_aux_log_out :
    forall ops sys input log_a x,
      NoDup (affected_regs ops) ->
      latest_write (aux_log sys input ops log_a) (tf_out x) =
      match find_out_update sched_ctx x (tfs_get_updates sched_ctx ops sys input) with
      | Some v => Some v
      | None => latest_write log_a (tf_out x)
      end.
  Proof.
    induction ops as [| op ops IH]; intros sys input log_a x Hnd.
    - reflexivity.
    - rewrite aux_log_cons, tfs_get_updates_cons.
      destruct op; simpl affected_regs in Hnd;
        cbn [find_out_update tf_op_step_updates].
      + apply IH. exact Hnd.
      + apply NoDup_cons_iff in Hnd. destruct Hnd as [_ Hnd].
        rewrite IH by exact Hnd.
        destruct (find_out_update sched_ctx x (tfs_get_updates sched_ctx ops sys input)); try reflexivity.
        rewrite SemanticProperties.latest_write_cons_neq.
        * apply latest_write_expr_log_any.
        * intro Hc. discriminate Hc.
      + apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
        destruct (eq_dec dst x) as [Heq | Hneq].
        * subst dst.
          rewrite IH by exact Hnd.
          rewrite (find_out_update_not_affected ops sys input x Hnotin).
          rewrite SemanticProperties.latest_write_cons_eq. reflexivity.
        * rewrite IH by exact Hnd.
          destruct (find_out_update sched_ctx x (tfs_get_updates sched_ctx ops sys input)); try reflexivity.
          rewrite SemanticProperties.latest_write_cons_neq.
          -- apply latest_write_expr_log_any.
          -- intro Hc. apply Hneq. injection Hc. auto.
  Qed.

  (* A P1 read entry never counts as a write. *)
  Lemma latest_write_cons_read1 :
    forall (log: Log R ContextEnv) idx idx',
      latest_write (log_cons idx' Read1 log) idx = latest_write log idx.
  Proof.
    intros log idx idx'. destruct (eq_dec idx idx') as [Heq | Hneq].
    - subst. rewrite SemanticProperties.latest_write_cons_eq. reflexivity.
    - rewrite SemanticProperties.latest_write_cons_neq by exact Hneq. reflexivity.
  Qed.

  (* Combined-port reset_log register bridge: reset writes Bits.zero at P1. *)
  Lemma latest_write_reset_log_reg :
    forall regs log_a x,
      NoDup regs ->
      (forall v, In v regs -> tfs_states_init sched_ctx v = Bits.zero) ->
      latest_write (reset_log regs log_a) (tf_reg x) =
      match find_st_update sched_ctx x (tfs_reset_updates sched_ctx regs) with
      | Some v => Some v
      | None => latest_write log_a (tf_reg x)
      end.
  Proof.
    induction regs as [| a regs IH]; intros log_a x Hnd Hinit.
    - reflexivity.
    - rewrite reset_log_cons.
      apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
      rewrite IH by (assumption || (intros v Hv; apply Hinit; right; exact Hv)).
      rewrite tfs_reset_updates_cons. cbn [find_st_update].
      destruct (eq_dec a x) as [Heq | Hneq].
      + destruct Heq.
        rewrite (find_st_update_reset_None regs a Hnotin).
        rewrite SemanticProperties.latest_write_cons_eq.
        rewrite (Hinit a (or_introl eq_refl)). reflexivity.
      + destruct (find_st_update sched_ctx x (tfs_reset_updates sched_ctx regs)); try reflexivity.
        rewrite SemanticProperties.latest_write_cons_neq. reflexivity.
        intro Hc. apply Hneq. injection Hc. auto.
  Qed.

  (* Folding the input-buffer writes leaves latest_write untouched on non-tf_in regs. *)
  Lemma latest_write_input_fold_other :
    forall (inputs: list spec_inputs) (sigma: forall f, Sig_denote (Sigma f)) log2 idx,
      (forall v, idx <> tf_in v) ->
      latest_write
        (fold_left (fun log x => log_cons (R:=R) (REnv:=REnv) (tf_in x)
                     (Write0 (sigma (ext_input x) Ob~1)) log) inputs log2) idx
      = latest_write log2 idx.
  Proof.
    induction inputs as [| b inputs IH]; intros sigma log2 idx Hneq.
    - reflexivity.
    - simpl. rewrite IH by exact Hneq.
      rewrite SemanticProperties.latest_write_cons_neq by (apply Hneq). reflexivity.
  Qed.

  (* The command-guard log never writes any register other than tf_ready/tf_cmd/tf_in. *)
  Lemma latest_write_guard_log_other :
    forall (r: ContextEnv.(env_t) R) act sigma idx,
      idx <> tf_ready -> idx <> tf_cmd -> (forall v, idx <> tf_in v) ->
      latest_write (if Bits.single r.[tf_ready]
                    then log_after_cmd_guard_rdy act sigma
                    else log_cons tf_cmd Read0 (log_cons tf_ready Read0 log_empty)) idx = None.
  Proof.
    intros r act sigma idx Hrdy Hcmd Hin.
    destruct (reg_ready_or_not r) as [Hready | Hnotready].
    - rewrite Hready. replace (Bits.single Ob~1) with true by reflexivity. cbv iota.
      unfold log_after_cmd_guard_rdy.
      rewrite (SemanticProperties.latest_write_cons_neq (R:=R) (REnv:=REnv)) by exact Hrdy.
      rewrite (SemanticProperties.latest_write_cons_neq (R:=R) (REnv:=REnv)) by exact Hcmd.
      rewrite latest_write_input_fold_other by exact Hin.
      rewrite (SemanticProperties.latest_write_cons_neq (R:=R) (REnv:=REnv)) by exact Hrdy.
      rewrite (SemanticProperties.latest_write_cons_neq (R:=R) (REnv:=REnv)) by exact Hrdy.
      rewrite (SemanticProperties.latest_write_cons_neq (R:=R) (REnv:=REnv)) by exact Hrdy.
      apply (SemanticProperties.latest_write_empty (R:=R) (REnv:=REnv)).
    - rewrite Hnotready. replace (Bits.single Ob~0) with false by reflexivity. cbv iota.
      rewrite (SemanticProperties.latest_write_cons_neq (R:=R) (REnv:=REnv)) by exact Hcmd.
      rewrite (SemanticProperties.latest_write_cons_neq (R:=R) (REnv:=REnv)) by exact Hrdy.
      apply (SemanticProperties.latest_write_empty (R:=R) (REnv:=REnv)).
  Qed.

  (* The main register bridge over construct_log, assuming the guard log has no
     write on tf_reg x. Mirrors the abstract done-gate. *)
  Lemma latest_write_construct_log_reg :
    forall sys act input ready guard_log x,
      latest_write guard_log (tf_reg x) = None ->
      latest_write (construct_log sys act input ready guard_log) (tf_reg x) =
      find_st_update sched_ctx x
        (if beq_dec (find_st_val sched_ctx spec_done_state (tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input) sys) Bits.zero
         then tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input
         else tfs_reset_updates sched_ctx spec_reset_states
              ++ tfs_get_updates sched_ctx (snd (spec_schedule act)) sys input
              ++ tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input).
  Proof.
    intros sys act input ready guard_log x Hguard.
    unfold construct_log.
    destruct (beq_dec _ _) eqn:Hdone.
    - (* not-done: only the always-ops (fst) run *)
      rewrite latest_write_cons_read1.
      rewrite (latest_write_aux_log_reg (fst (spec_schedule act)) sys input guard_log x
                 (nodup_affected_regs_fst act)).
      rewrite Hguard.
      destruct (find_st_update sched_ctx x (tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input)); reflexivity.
    - (* done: reset ++ done-ops (snd) ++ always-ops (fst) *)
      rewrite SemanticProperties.latest_write_cons_neq by discriminate.
      rewrite (latest_write_reset_log_reg spec_reset_states _ x
                 (tfs_reset_states_nodup sched_ctx)
                 (tfs_reset_states_init_zero sched_ctx)).
      rewrite (latest_write_aux_log_reg (snd (spec_schedule act)) sys input _ x
                 (nodup_affected_regs_snd act)).
      rewrite latest_write_cons_read1.
      rewrite (latest_write_aux_log_reg (fst (spec_schedule act)) sys input guard_log x
                 (nodup_affected_regs_fst act)).
      rewrite Hguard.
      rewrite !find_st_update_app.
      destruct (find_st_update sched_ctx x (tfs_reset_updates sched_ctx spec_reset_states)); try reflexivity.
      destruct (find_st_update sched_ctx x (tfs_get_updates sched_ctx (snd (spec_schedule act)) sys input)); try reflexivity.
      destruct (find_st_update sched_ctx x (tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input)); reflexivity.
  Qed.

  Lemma latest_write_construct_log_out :
    forall sys act input ready guard_log x,
      latest_write guard_log (tf_out x) = None ->
      latest_write (construct_log sys act input ready guard_log) (tf_out x) =
      find_out_update sched_ctx x
        (if beq_dec (find_st_val sched_ctx spec_done_state (tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input) sys) Bits.zero
         then tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input
         else tfs_reset_updates sched_ctx spec_reset_states
              ++ tfs_get_updates sched_ctx (snd (spec_schedule act)) sys input
              ++ tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input).
  Proof.
    intros sys act input ready guard_log x Hguard.
    unfold construct_log.
    destruct (beq_dec _ _) eqn:Hdone.
    - rewrite latest_write_cons_read1.
      rewrite (latest_write_aux_log_out (fst (spec_schedule act)) sys input guard_log x
                 (nodup_affected_regs_fst act)).
      rewrite Hguard.
      destruct (find_out_update sched_ctx x (tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input)); reflexivity.
    - rewrite SemanticProperties.latest_write_cons_neq by discriminate.
      rewrite latest_write_reset_log_neq by (intros s; discriminate).
      rewrite (latest_write_aux_log_out (snd (spec_schedule act)) sys input _ x
                 (nodup_affected_regs_snd act)).
      rewrite latest_write_cons_read1.
      rewrite (latest_write_aux_log_out (fst (spec_schedule act)) sys input guard_log x
                 (nodup_affected_regs_fst act)).
      rewrite Hguard.
      rewrite !find_out_update_app.
      rewrite (find_out_update_reset_None spec_reset_states x).
      destruct (find_out_update sched_ctx x (tfs_get_updates sched_ctx (snd (spec_schedule act)) sys input)); try reflexivity.
      destruct (find_out_update sched_ctx x (tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input)); reflexivity.
  Qed.

  Lemma latest_write_reg :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log x,
      state_matches sys r ->
      externs_match sigma ->
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
    intros sys r act input sigma log x Hstate Hsig Hin_rdy Hin_nrdy Hgood.
    assert (Hlog : latest_write log (tf_reg x) = None).
    { unfold good_log in Hgood.
      destruct Hgood as [_ [Hwr0_st _]].
      apply may_write0_latest_write_None.
      unfold may_write_all in Hwr0_st. rewrite forallb_forall in Hwr0_st.
      apply Hwr0_st. apply in_map. apply in_spec_all_states. }
    rewrite (interp_rule_correct sys r act input sigma log Hstate Hsig Hin_rdy Hin_nrdy Hgood).
    cbv zeta.
    rewrite SemanticProperties.latest_write_app.
    rewrite latest_write_construct_log_reg
      by (apply latest_write_guard_log_other; discriminate).
    rewrite Hlog.
    destruct (find_st_update sched_ctx x _); reflexivity.
  Qed.

  Lemma latest_write_out :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log x,
      state_matches sys r ->
      externs_match sigma ->
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
    intros sys r act input sigma log x Hstate Hsig Hin_rdy Hin_nrdy Hgood.
    assert (Hlog : latest_write log (tf_out x) = None).
    { unfold good_log in Hgood.
      destruct Hgood as [_ [_ [_ [_ [_ [Hwr0_out _]]]]]].
      apply may_write0_latest_write_None.
      unfold may_write_all in Hwr0_out. rewrite forallb_forall in Hwr0_out.
      apply Hwr0_out. apply in_map. apply in_spec_all_outputs. }
    rewrite (interp_rule_correct sys r act input sigma log Hstate Hsig Hin_rdy Hin_nrdy Hgood).
    cbv zeta.
    rewrite SemanticProperties.latest_write_app.
    rewrite latest_write_construct_log_out
      by (apply latest_write_guard_log_other; discriminate).
    rewrite Hlog.
    destruct (find_out_update sched_ctx x _); reflexivity.
  Qed.

  (* ==================================================================== *)
  (* rule_ext: the external calls, issued once, after every action rule.  *)
  (* ==================================================================== *)

  (* [may_read _ P1] and [may_write _ _ P1] inspect the very same log. *)
  Lemma may_read_P1_may_write :
    forall (log_r log_a: Log R ContextEnv) idx,
      may_read (log_app log_a log_r) P1 idx = may_write log_r log_a P1 idx.
  Proof.
    Local Transparent may_read may_write. reflexivity.
  Qed.

  Lemma may_write_app_empty :
    forall (log_r log_a: Log R ContextEnv) prt idx,
      may_write (log_app log_a log_r) log_empty prt idx = may_write log_r log_a prt idx.
  Proof.
    intros log_r log_a prt idx. unfold may_write.
    rewrite SemanticProperties.log_app_empty_r. reflexivity.
  Qed.

  (* Without a P1 write in the log the two latest-write notions coincide. *)
  Lemma latest_write0_eq_latest_write :
    forall (L: Log R ContextEnv) idx,
      may_read L P1 idx = true ->
      latest_write0 L idx = latest_write L idx.
  Proof.
    intros L idx H.
    unfold may_read in H. apply negb_true_iff in H.
    unfold latest_write0, latest_write, log_find, log_existsb in *.
    induction (ContextEnv.(getenv) L idx) as [| e l IH]; [ reflexivity |].
    destruct e as [k p v]. cbn [existsb] in H. apply orb_false_iff in H.
    destruct H as [Hh Ht]. specialize (IH Ht).
    destruct k, p; cbn [list_find_opt log_latest_write0_fn log_latest_write_fn] in *;
      solve [ exact IH | reflexivity | discriminate Hh ].
  Qed.
  Local Opaque may_read may_write.

  (* The ext updates depend on the state only through the argument registers. *)
  Lemma find_st_update_ext_updates_ext :
    forall (st1 st2: ContextEnv.(env_t) spec_states_t),
      (forall f, st1.[spec_ext_arg f] = st2.[spec_ext_arg f]) ->
      forall x, find_st_update sched_ctx x (tfs_ext_updates sched_ctx st1)
              = find_st_update sched_ctx x (tfs_ext_updates sched_ctx st2).
  Proof.
    intros st1 st2 Heq x. unfold tfs_ext_updates.
    match goal with |- context [List.map _ ?L] => induction L as [| f fs IH] end;
      cbn [List.map find_st_update]; [ reflexivity |].
    destruct (eq_dec (spec_ext_res f) x) as [Heqx | Hne]; [| exact IH ].
    rewrite (Heq f). reflexivity.
  Qed.

  (* ---- the ext registers survive the guard log and the command rule's log ---- *)

  Lemma may_write_all_singleton :
    forall log_r log_a prt idx,
      may_write_all log_r log_a prt [idx] = may_write log_r log_a prt idx.
  Proof. intros. unfold may_write_all. cbn [forallb]. apply andb_true_r. Qed.

  Lemma may_write_aux_log_P0_one :
    forall ops sys input log_r log_a idx,
      ~ In idx (affected_regs ops) ->
      (forall i, idx <> tf_in i) ->
      may_write log_r log_a P0 idx = true ->
      may_write log_r (aux_log sys input ops log_a) P0 idx = true.
  Proof.
    intros ops sys input log_r log_a idx Hna Hni Hb.
    rewrite <- may_write_all_singleton.
    apply may_write_all_aux_log_P0.
    - intros reg [<- | []]. exact Hna.
    - intros i [Heq | []]. exact (Hni i Heq).
    - rewrite may_write_all_singleton. exact Hb.
  Qed.

  Lemma may_write_construct_log_P0 :
    forall sys act input ready log_r log_a x,
      ~ In (tf_reg x) (affected_regs (fst (spec_schedule act))) ->
      ~ In (tf_reg x) (affected_regs (snd (spec_schedule act))) ->
      x <> spec_done_state ->
      ~ In x spec_reset_states ->
      may_write log_r log_a P0 (tf_reg x) = true ->
      may_write log_r (construct_log sys act input ready log_a) P0 (tf_reg x) = true.
  Proof.
    intros sys act input ready log_r log_a x Hfst Hsnd Hdone Hreset Hbase.
    assert (Hni : forall i, tf_reg (states_var:=spec_states) (inputs_var:=spec_inputs)
                              (outputs_var:=spec_outputs) x <> tf_in i) by discriminate.
    assert (Hdone' : tf_reg (states_var:=spec_states) (inputs_var:=spec_inputs)
                       (outputs_var:=spec_outputs) x <> tf_reg spec_done_state)
      by (intro Heq; injection Heq as Heq'; exact (Hdone Heq')).
    assert (Hreset' : ~ In (tf_reg (states_var:=spec_states) (inputs_var:=spec_inputs)
                              (outputs_var:=spec_outputs) x) (map tf_reg spec_reset_states)).
    { intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Heq Hy]].
      injection Heq as Heq'. subst y. exact (Hreset Hy). }
    unfold construct_log. cbv zeta.
    destruct (beq_dec _ _).
    - rewrite may_write_log_cons_neq by exact Hdone'.
      apply may_write_aux_log_P0_one; assumption.
    - rewrite may_write_log_cons_neq by discriminate.
      rewrite may_write_reset_log_neq by exact Hreset'.
      apply may_write_aux_log_P0_one; [ exact Hsnd | exact Hni |].
      rewrite may_write_log_cons_neq by exact Hdone'.
      apply may_write_aux_log_P0_one; assumption.
  Qed.

  Lemma may_write_construct_log_P1 :
    forall sys act input ready log_r log_a x,
      ~ In x spec_reset_states ->
      may_write log_r log_a P1 (tf_reg x) = true ->
      may_write log_r (construct_log sys act input ready log_a) P1 (tf_reg x) = true.
  Proof.
    intros sys act input ready log_r log_a x Hreset Hbase.
    assert (Hreset' : ~ In (tf_reg (states_var:=spec_states) (inputs_var:=spec_inputs)
                              (outputs_var:=spec_outputs) x) (map tf_reg spec_reset_states)).
    { intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Heq Hy]].
      injection Heq as Heq'. subst y. exact (Hreset Hy). }
    unfold construct_log. cbv zeta.
    destruct (beq_dec _ _).
    - rewrite may_write_log_cons_P1_not_w1 by reflexivity.
      rewrite may_write_aux_log_P1. exact Hbase.
    - rewrite may_write_log_cons_neq by discriminate.
      rewrite may_write_reset_log_neq by exact Hreset'.
      rewrite may_write_aux_log_P1.
      rewrite may_write_log_cons_P1_not_w1 by reflexivity.
      rewrite may_write_aux_log_P1. exact Hbase.
  Qed.

  Lemma may_write_guard_log_other :
    forall (r: ContextEnv.(env_t) R) act sigma log_r prt idx,
      idx <> tf_ready -> idx <> tf_cmd -> (forall v, idx <> tf_in v) ->
      may_write log_r (if Bits.single r.[tf_ready]
                       then log_after_cmd_guard_rdy act sigma
                       else log_cons tf_cmd Read0 (log_cons tf_ready Read0 log_empty)) prt idx
      = may_write log_r log_empty prt idx.
  Proof.
    intros r act sigma log_r prt idx Hrdy Hcmd Hin.
    assert (Hfold : ~ In idx (map tf_in spec_all_inputs)).
    { intro Hmem. apply in_map_iff in Hmem. destruct Hmem as [v [Heq _]].
      exact (Hin v (eq_sym Heq)). }
    destruct (reg_ready_or_not r) as [Hready | Hnotready].
    - rewrite Hready. replace (Bits.single Ob~1) with true by reflexivity. cbv iota.
      unfold log_after_cmd_guard_rdy.
      rewrite may_write_log_cons_neq by exact Hrdy.
      rewrite may_write_log_cons_neq by exact Hcmd.
      rewrite may_write_fold_cons_w0_inputs by exact Hfold.
      rewrite !may_write_log_cons_neq by exact Hrdy.
      reflexivity.
    - rewrite Hnotready. replace (Bits.single Ob~0) with false by reflexivity. cbv iota.
      rewrite may_write_log_cons_neq by exact Hcmd.
      rewrite may_write_log_cons_neq by exact Hrdy.
      reflexivity.
  Qed.

  (* What the ext rule needs of the log it runs on: it writes the result registers at
     P0 and reads the argument registers at P1. *)
  Definition ext_ok (L: Log R ContextEnv) : Prop :=
    (forall f, may_write L log_empty P0 (tf_reg (spec_ext_res f)) = true) /\
    (forall f, may_read L P1 (tf_reg (spec_ext_arg f)) = true).

  Lemma ext_res_not_affected :
    forall act f,
      ~ In (tf_reg (spec_ext_res f)) (affected_regs (fst (spec_schedule act)))
      /\ ~ In (tf_reg (spec_ext_res f)) (affected_regs (snd (spec_schedule act))).
  Proof.
    intros act f.
    pose proof (tfs_ext_res_not_scheduled (tf_sched_ctx tf_ctx) act f) as Hns.
    unfold tfs_ops_tags in Hns. rewrite flat_map_app in Hns.
    split; intro Hin; apply affected_reg_in_ops_tags in Hin; apply Hns;
      apply in_or_app; [ left | right ]; exact Hin.
  Qed.

  Lemma ext_ok_cmd_log :
    forall (r: ContextEnv.(env_t) R) sys act input sigma log,
      good_log log ->
      ext_ok (log_app (construct_log sys act input r.[tf_ready]
                        (if Bits.single r.[tf_ready]
                         then log_after_cmd_guard_rdy act sigma
                         else log_cons tf_cmd Read0 (log_cons tf_ready Read0 log_empty))) log).
  Proof.
    intros r sys act input sigma log Hgood.
    destruct Hgood as [Hrd0_st [Hwr0_st _]].
    split; intro f.
    - rewrite may_write_app_empty.
      destruct (ext_res_not_affected act f) as [Hfst Hsnd].
      apply may_write_construct_log_P0.
      + exact Hfst.
      + exact Hsnd.
      + exact (tfs_ext_res_not_done (tf_sched_ctx tf_ctx) f).
      + exact (tfs_ext_res_not_reset (tf_sched_ctx tf_ctx) f).
      + rewrite may_write_guard_log_other by discriminate.
        unfold may_write_all in Hwr0_st. rewrite forallb_forall in Hwr0_st.
        apply Hwr0_st. apply in_map. apply in_spec_all_states.
    - rewrite may_read_P1_may_write.
      apply may_write_construct_log_P1.
      + exact (tfs_ext_arg_not_reset (tf_sched_ctx tf_ctx) f).
      + rewrite may_write_guard_log_other by discriminate.
        apply may_write0_implies_may_write1.
        unfold may_write_all in Hwr0_st. rewrite forallb_forall in Hwr0_st.
        apply Hwr0_st. apply in_map. apply in_spec_all_states.
  Qed.

  (* ---- interpreting rule_ext ---- *)

  Definition ext_val (r: ContextEnv.(env_t) R) (L: Log R ContextEnv) (f: spec_externs)
    : bits_t (spec_states_size (spec_ext_res f)) :=
    convert (tfe_denote f
               (convert (match latest_write0 L (tf_reg (spec_ext_arg f)) with
                         | Some v => v
                         | None => r.[tf_reg (spec_ext_arg f)]
                         end))).

  Fixpoint ext_rule_log (r: ContextEnv.(env_t) R) (L: Log R ContextEnv)
    (fs: list spec_externs) (log_a: Log R ContextEnv) : Log R ContextEnv :=
    match fs with
    | [] => log_a
    | f :: rest =>
        ext_rule_log r L rest
          (log_cons (R:=R) (REnv:=REnv) (tf_reg (spec_ext_res f)) (Write0 (ext_val r L f))
             (log_cons (R:=R) (REnv:=REnv) (tf_reg (spec_ext_arg f)) Read1 log_a))
    end.

  Lemma latest_write0_log_cons_read :
    forall (log: Log R ContextEnv) idx idx' le,
      kind le = LogRead ->
      latest_write0 (log_cons (R:=R) (REnv:=REnv) idx' le log) idx = latest_write0 log idx.
  Proof.
    intros log idx idx' le Hk.
    destruct (eq_dec idx' idx) as [Heq | Hne].
    - subst idx'. rewrite SemanticProperties.latest_write0_cons_eq.
      destruct le; simpl in *; destruct kind; [ reflexivity | discriminate Hk ].
    - rewrite SemanticProperties.latest_write0_cons_neq by (intro; congruence). reflexivity.
  Qed.

  (* [tau] is pinned on both sides: [ExternalCall]'s own typing gives the
     convertible-but-not-syntactic [arg1Sig/retSig (Sigma (ext_call f))]. *)
  Lemma interp_ext_call_read_step :
    forall (r: ContextEnv.(env_t) R) sigma log_r log_a (f: spec_externs),
      interp_action (R:=R) (Sigma:=Sigma) (REnv:=REnv) (tau := bits_t (spec_externs_res f))
        r sigma CtxEmpty log_r log_a
        (ExternalCall (ext_call f)
           (synth_convert (in_var_size := spec_states_size (spec_ext_arg f)) tf_ctx
              (spec_externs_arg f) (Read P1 (tf_reg (spec_ext_arg f)))))
      = match
          interp_action (R:=R) (Sigma:=Sigma) (REnv:=REnv) (tau := bits_t (spec_externs_arg f))
            r sigma CtxEmpty log_r log_a
            (synth_convert (in_var_size := spec_states_size (spec_ext_arg f)) tf_ctx
               (spec_externs_arg f) (Read P1 (tf_reg (spec_ext_arg f))))
        with
        | Some (l, v, g) => Some (l, sigma (ext_call f) v, g)
        | None => None
        end.
  Proof. reflexivity. Qed.

  (* Same as [interp_action_read1] but with [tau] in the reduced [bits_t …] form the
     surrounding [synth_convert] forces. *)
  Lemma interp_action_read1_reg :
    forall (r: ContextEnv.(env_t) R) sigma log_r log_a x,
      may_read log_r P1 (tf_reg x) = true ->
      interp_action (pos_t:=pos_t) (var_t:=var_t) (fn_name_t:=fn_name_t)
        (R:=R) (Sigma:=Sigma) (REnv:=REnv)
        (tau := bits_t (spec_states_size x)) r sigma CtxEmpty log_r log_a
        (Read P1 (tf_reg x))
      = Some (log_cons (R:=R) (REnv:=REnv) (tf_reg x) Read1 log_a,
              match latest_write0 (log_app log_a log_r) (tf_reg x) with
              | Some v => v
              | None => r.[tf_reg x]
              end,
              CtxEmpty).
  Proof. intros; simpl. rewrite H. reflexivity. Qed.

  Lemma interp_ext_value :
    forall (r: ContextEnv.(env_t) R) sigma log_r log_a (f: spec_externs),
      externs_match sigma ->
      may_read log_r P1 (tf_reg (spec_ext_arg f)) = true ->
      interp_action (R:=R) (Sigma:=Sigma) (REnv:=REnv)
        (tau := bits_t (spec_states_size (spec_ext_res f)))
        r sigma CtxEmpty log_r log_a
        (synth_convert (in_var_size := spec_externs_res f) tf_ctx
           (spec_states_size (spec_ext_res f))
           (ExternalCall (ext_call f)
              (synth_convert (in_var_size := spec_states_size (spec_ext_arg f)) tf_ctx
                 (spec_externs_arg f) (Read P1 (tf_reg (spec_ext_arg f))))))
      = Some (log_cons (R:=R) (REnv:=REnv) (tf_reg (spec_ext_arg f)) Read1 log_a,
              ext_val r (log_app log_a log_r) f, CtxEmpty).
  Proof.
    intros r sigma log_r log_a f Hsig Hrd.
    rewrite interp_synth_convert.
    rewrite interp_ext_call_read_step.
    rewrite interp_synth_convert.
    rewrite (interp_action_read1_reg r sigma log_r log_a (spec_ext_arg f) Hrd).
    unfold ext_val. rewrite (Hsig f). reflexivity.
  Qed.

  Lemma interp_action_write0_reg :
    forall (r: ContextEnv.(env_t) R) sigma log_r log_a x
           (v: action R Sigma [] (bits_t (spec_states_size x))),
      interp_action (tau:=unit_t) r sigma CtxEmpty log_r log_a (Write P0 (tf_reg x) v)
      = match interp_action (tau := bits_t (spec_states_size x)) r sigma CtxEmpty log_r log_a v with
        | Some (l, val, g) =>
            if may_write log_r l P0 (tf_reg x)
            then Some (log_cons (R:=R) (REnv:=REnv) (tf_reg x) (Write0 val) l, Bits.nil, g)
            else None
        | None => None
        end.
  Proof. reflexivity. Qed.

  Lemma ext_val_app :
    forall (r: ContextEnv.(env_t) R) log_r log_a f,
      latest_write0 log_a (tf_reg (spec_ext_arg f)) = None ->
      ext_val r (log_app log_a log_r) f = ext_val r log_r f.
  Proof.
    intros r log_r log_a f H. unfold ext_val.
    rewrite SemanticProperties.latest_write0_app, H. reflexivity.
  Qed.

  Lemma ext_res_neq_arg :
    forall g h, tf_reg (states_var:=spec_states) (inputs_var:=spec_inputs)
                  (outputs_var:=spec_outputs) (spec_ext_res g) <> tf_reg (spec_ext_arg h).
  Proof.
    intros g h Heq. injection Heq as Heq'.
    exact (tfs_ext_res_not_arg (tf_sched_ctx tf_ctx) g h Heq').
  Qed.

  Lemma interp_rule_ext_calls_gen :
    forall (r: ContextEnv.(env_t) R) sigma log_r fs log_a,
      externs_match sigma ->
      NoDup fs ->
      (forall f, may_read log_r P1 (tf_reg (spec_ext_arg f)) = true) ->
      (forall f, In f fs -> may_write log_r log_a P0 (tf_reg (spec_ext_res f)) = true) ->
      (forall f, latest_write0 log_a (tf_reg (spec_ext_arg f)) = None) ->
      interp_action (tau:=unit_t) r sigma CtxEmpty log_r log_a
        (rule_ext_calls tf_ctx fs (Const (tau:=unit_t) vect_nil))
      = Some (ext_rule_log r log_r fs log_a, Bits.nil, CtxEmpty).
  Proof.
    intros r sigma log_r fs. induction fs as [| f fs IH]; intros log_a Hsig Hnd Hrd Hwr Hlw.
    - reflexivity.
    - apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
      assert (Hres_res : forall g, In g fs ->
                tf_reg (states_var:=spec_states) (inputs_var:=spec_inputs)
                  (outputs_var:=spec_outputs) (spec_ext_res g) <> tf_reg (spec_ext_res f)).
      { intros g Hg Heq. injection Heq as Heq'.
        apply tfs_ext_res_inj in Heq'. subst g. exact (Hnotin Hg). }
      cbn [rule_ext_calls ext_rule_log].
      rewrite interp_action_seq. unfold opt_bind.
      rewrite interp_action_write0_reg.
      rewrite (interp_ext_value r sigma log_r log_a f Hsig (Hrd f)).
      rewrite (may_write_log_cons_neq log_r log_a P0
                 (tf_reg (spec_ext_arg f)) (tf_reg (spec_ext_res f)) Read1 (ext_res_neq_arg f f)).
      rewrite (Hwr f (or_introl eq_refl)).
      rewrite (ext_val_app r log_r log_a f (Hlw f)).
      apply IH; try assumption.
      + intros g Hg.
        rewrite (may_write_log_cons_neq _ _ P0 _ _ _ (Hres_res g Hg)).
        rewrite (may_write_log_cons_neq _ _ P0 _ _ _ (ext_res_neq_arg g f)).
        exact (Hwr g (or_intror Hg)).
      + intros g.
        rewrite SemanticProperties.latest_write0_cons_neq
          by (apply not_eq_sym; exact (ext_res_neq_arg f g)).
        rewrite latest_write0_log_cons_read by reflexivity.
        exact (Hlw g).
  Qed.

  Definition ext_updates_of (r: ContextEnv.(env_t) R) (L: Log R ContextEnv)
    (fs: list spec_externs) : list (tf_update spec_states_size spec_outputs_size) :=
    List.map (fun f => tf_st_update spec_states_size spec_outputs_size
                         (spec_ext_res f) (ext_val r L f)) fs.

  Lemma ext_updates_of_nil : forall r L, ext_updates_of r L [] = [].
  Proof. reflexivity. Qed.

  Lemma ext_updates_of_cons : forall r L f fs,
    ext_updates_of r L (f :: fs)
    = tf_st_update spec_states_size spec_outputs_size (spec_ext_res f) (ext_val r L f)
      :: ext_updates_of r L fs.
  Proof. reflexivity. Qed.

  Lemma find_st_update_ext_updates_of_in :
    forall (r: ContextEnv.(env_t) R) L fs x v,
      find_st_update sched_ctx x (ext_updates_of r L fs) = Some v ->
      exists g, In g fs /\ spec_ext_res g = x.
  Proof.
    intros r L fs. induction fs as [| f fs IH]; intros x v H.
    - rewrite ext_updates_of_nil in H. discriminate H.
    - rewrite ext_updates_of_cons in H. cbn [find_st_update] in H.
      destruct (eq_dec (spec_ext_res f) x) as [Heq | Hne].
      + exists f. split; [ left; reflexivity | exact Heq ].
      + destruct (IH x v H) as [g [Hg Hres]]. exists g. split; [ right; exact Hg | exact Hres ].
  Qed.

  Lemma latest_write_ext_rule_log_reg :
    forall (r: ContextEnv.(env_t) R) L fs log_a x,
      NoDup fs ->
      latest_write (ext_rule_log r L fs log_a) (tf_reg x)
      = match find_st_update sched_ctx x (ext_updates_of r L fs) with
        | Some v => Some v
        | None => latest_write log_a (tf_reg x)
        end.
  Proof.
    intros r L fs. induction fs as [| f fs IH]; intros log_a x Hnd.
    - rewrite ext_updates_of_nil. reflexivity.
    - apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
      cbn [ext_rule_log]. rewrite ext_updates_of_cons. cbn [find_st_update].
      rewrite (IH _ x Hnd).
      destruct (find_st_update sched_ctx x (ext_updates_of r L fs)) as [v |] eqn:Hfs.
      + destruct (eq_dec (spec_ext_res f) x) as [Heq | Hne]; [| reflexivity ].
        exfalso. destruct (find_st_update_ext_updates_of_in r L fs x v Hfs) as [g [Hg Hres]].
        assert (g = f) as ->.
        { apply (tfs_ext_res_inj (tf_sched_ctx tf_ctx)). rewrite Hres, Heq. reflexivity. }
        exact (Hnotin Hg).
      + destruct (eq_dec (spec_ext_res f) x) as [Heq | Hne].
        * destruct Heq. rewrite SemanticProperties.latest_write_cons_eq. reflexivity.
        * rewrite SemanticProperties.latest_write_cons_neq
            by (intro Hc; injection Hc as Hc'; exact (Hne (eq_sym Hc'))).
          rewrite Common.latest_write_log_cons_read by reflexivity. reflexivity.
  Qed.

  Lemma latest_write_ext_rule_log_other :
    forall (r: ContextEnv.(env_t) R) L fs log_a idx,
      (forall y, idx <> tf_reg y) ->
      latest_write (ext_rule_log r L fs log_a) idx = latest_write log_a idx.
  Proof.
    intros r L fs. induction fs as [| f fs IH]; intros log_a idx Hidx; [ reflexivity |].
    cbn [ext_rule_log]. rewrite (IH _ idx Hidx).
    rewrite SemanticProperties.latest_write_cons_neq by (apply Hidx).
    rewrite Common.latest_write_log_cons_read by reflexivity. reflexivity.
  Qed.

  Lemma nodup_spec_all_externs : NoDup spec_all_externs.
  Proof. apply NoDup_map_inv with (f:=(finite_index (FiniteType:=spec_externs_fin))). apply finite_injective. Qed.

  Lemma interp_rule_ext :
    forall (r: ContextEnv.(env_t) R) sigma L,
      externs_match sigma ->
      ext_ok L ->
      interp_rule r sigma L (rules (@rule_ext spec_outputs spec_action))
      = Some (ext_rule_log r L spec_all_externs log_empty).
  Proof.
    intros r sigma L Hsig [Hwr Hrd]. unfold interp_rule, rules.
    rewrite interp_rule_ext_calls_gen with (fs := spec_all_externs).
    - reflexivity.
    - exact Hsig.
    - exact nodup_spec_all_externs.
    - exact Hrd.
    - intros f _. exact (Hwr f).
    - intro f. apply (SemanticProperties.latest_write0_empty (R:=R) (REnv:=REnv)).
  Qed.

  Local Notation cmd_log r sigma log act :=
    (match interp_rule r sigma log (rules (@rule_cmd spec_outputs spec_action act)) with
     | Some l => log_app l log
     | None => log
     end).

  (* A definition rather than a notation: the [match]'s return predicate would
     otherwise be re-elaborated at every use site and [rewrite] would stop matching. *)
  Definition ext_step (r: ContextEnv.(env_t) R) (sigma: forall f, Sig_denote (Sigma f)) L :=
    match interp_rule r sigma L (rules (@rule_ext spec_outputs spec_action)) with
    | Some l => log_app l L
    | None => L
    end.

  Lemma latest_write_ext_full_reg :
    forall (r: ContextEnv.(env_t) R) sigma (L: Log R ContextEnv) x,
      externs_match sigma -> ext_ok L ->
      latest_write (ext_step r sigma L) (tf_reg x)
      = match find_st_update sched_ctx x (ext_updates_of r L spec_all_externs) with
        | Some v => Some v
        | None => latest_write L (tf_reg x)
        end.
  Proof.
    intros r sigma L x Hsig Hok. unfold ext_step.
    rewrite (interp_rule_ext r sigma L Hsig Hok).
    rewrite SemanticProperties.latest_write_app.
    rewrite (latest_write_ext_rule_log_reg r L spec_all_externs log_empty x nodup_spec_all_externs).
    destruct (find_st_update sched_ctx x (ext_updates_of r L spec_all_externs)); [ reflexivity |].
    rewrite (SemanticProperties.latest_write_empty (R:=R) (REnv:=REnv)). reflexivity.
  Qed.

  Lemma latest_write_ext_full_other :
    forall (r: ContextEnv.(env_t) R) sigma (L: Log R ContextEnv) idx,
      externs_match sigma -> ext_ok L ->
      (forall y, idx <> tf_reg y) ->
      latest_write (ext_step r sigma L) idx = latest_write L idx.
  Proof.
    intros r sigma L idx Hsig Hok Hidx. unfold ext_step.
    rewrite (interp_rule_ext r sigma L Hsig Hok).
    rewrite SemanticProperties.latest_write_app.
    rewrite (latest_write_ext_rule_log_other r L spec_all_externs log_empty idx Hidx).
    rewrite (SemanticProperties.latest_write_empty (R:=R) (REnv:=REnv)). reflexivity.
  Qed.

  Lemma tfs_ext_updates_eq :
    forall (r: ContextEnv.(env_t) R) L (st: ContextEnv.(env_t) spec_states_t),
      (forall f, st.[spec_ext_arg f]
                 = match latest_write0 L (tf_reg (spec_ext_arg f)) with
                   | Some v => v
                   | None => r.[tf_reg (spec_ext_arg f)]
                   end) ->
      tfs_ext_updates sched_ctx st = ext_updates_of r L spec_all_externs.
  Proof.
    intros r L st H. unfold tfs_ext_updates, ext_updates_of, ext_val.
    apply map_ext. intro f. rewrite (H f). reflexivity.
  Qed.

  Lemma find_out_update_ext_updates :
    forall st x, find_out_update sched_ctx x (tfs_ext_updates sched_ctx st) = None.
  Proof.
    intros st x. unfold tfs_ext_updates.
    match goal with |- context [List.map _ ?L] => induction L as [| f fs IH] end;
      cbn [List.map find_out_update]; [ reflexivity | exact IH ].
  Qed.

  Lemma find_st_val_app :
    forall x a b sys,
      find_st_val sched_ctx x (a ++ b) sys
      = match find_st_update sched_ctx x a with
        | Some v => v
        | None => find_st_val sched_ctx x b sys
        end.
  Proof.
    intros x a b sys. unfold find_st_val. rewrite find_st_update_app.
    destruct (find_st_update sched_ctx x a); reflexivity.
  Qed.

  (* Bridges the two sides through [apply], whose unification is up to conversion:
     the ext-update option appears on both sides but from two different lemma
     statements, so [destruct] would abstract only one of them. *)
  Lemma commit_ext_reg_step :
    forall (r: ContextEnv.(env_t) R) (L: Log R ContextEnv) x
           (ups: list (tf_update spec_states_size spec_outputs_size)) sys
           (o: option (bits_t (spec_states_size x))),
      (match latest_write L (tf_reg x) with Some v => v | None => r.[tf_reg x] end
       = find_st_val sched_ctx x ups sys) ->
      match (match o with Some v => Some v | None => latest_write L (tf_reg x) end) with
      | Some v => v
      | None => r.[tf_reg x]
      end
      = match o with Some v => v | None => find_st_val sched_ctx x ups sys end.
  Proof. intros r L x ups sys o H. destruct o; [ reflexivity | exact H ]. Qed.

  (* Same reason as above: reach the committed value through [apply], not [rewrite]. *)
  Lemma commit_of_latest_write :
    forall (r: ContextEnv.(env_t) R) (L: Log R ContextEnv) idx (v: R idx),
      latest_write L idx = Some v ->
      match latest_write L idx with Some u => u | None => r.[idx] end = v.
  Proof. intros r L idx v H. rewrite H. reflexivity. Qed.

  Lemma commit_of_no_write :
    forall (r: ContextEnv.(env_t) R) (L: Log R ContextEnv) idx (v: R idx),
      latest_write L idx = None -> r.[idx] = v ->
      match latest_write L idx with Some u => u | None => r.[idx] end = v.
  Proof. intros r L idx v H Hv. rewrite H. exact Hv. Qed.

  Lemma ext_ok_after_cmd :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) act input sigma log,
      state_matches sys r ->
      externs_match sigma ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      good_log log ->
      ext_ok (cmd_log r sigma log act).
  Proof.
    intros sys r act input sigma log Hstate Hsig Hin_rdy Hin_nrdy Hlog.
    rewrite (interp_rule_correct sys r act input sigma log Hstate Hsig Hin_rdy Hin_nrdy Hlog).
    apply (ext_ok_cmd_log r sys act input sigma log Hlog).
  Qed.

  Lemma interp_scheduler'_ext_cons :
    forall (r: ContextEnv.(env_t) R) sigma (L: Log R ContextEnv) s,
      interp_scheduler' r sigma rules L (@rule_ext spec_outputs spec_action |> s)
      = interp_scheduler' r sigma rules (ext_step r sigma L) s.
  Proof.
    intros. cbn [interp_scheduler']. unfold ext_step.
    destruct (interp_rule _ _ _ _); reflexivity.
  Qed.

  (* Below is done *)

  Lemma synthesis_correct_aux3 :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log,
      state_matches sys r ->
      externs_match sigma ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      good_log log ->
      state_env_matches (tfs_next_cycle sched_ctx act sys input) act input
        (commit_update r (ext_step r sigma (cmd_log r sigma log act))).
  Proof.
    intros sys r act input sigma log Hstate Hsig Hin_rdy Hin_nrdy Hlog.
    pose proof (ext_ok_after_cmd sys r act input sigma log Hstate Hsig Hin_rdy Hin_nrdy Hlog) as Hok.
    (* The base cycle, read off the command rule's log. *)
    assert (Hbase : forall y,
              match latest_write (cmd_log r sigma log act) (tf_reg y) with
              | Some v => v
              | None => r.[tf_reg y]
              end
              = find_st_val sched_ctx y
                  (if beq_dec (find_st_val sched_ctx spec_done_state
                                 (tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input) sys) Bits.zero
                   then tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input
                   else tfs_reset_updates sched_ctx spec_reset_states
                        ++ tfs_get_updates sched_ctx (snd (spec_schedule act)) sys input
                        ++ tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input) sys).
    { intro y. rewrite (latest_write_reg sys r act input sigma log y Hstate Hsig Hin_rdy Hin_nrdy Hlog).
      unfold find_st_val. destruct (find_st_update sched_ctx y _); [ reflexivity |].
      apply Hstate. }
    assert (Hst : forall f,
              (ContextEnv.(create)
                 (fun y => find_st_val sched_ctx y
                    (if beq_dec (find_st_val sched_ctx spec_done_state
                                   (tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input) sys) Bits.zero
                     then tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input
                     else tfs_reset_updates sched_ctx spec_reset_states
                          ++ tfs_get_updates sched_ctx (snd (spec_schedule act)) sys input
                          ++ tfs_get_updates sched_ctx (fst (spec_schedule act)) sys input) sys)).[spec_ext_arg f]
              = match latest_write0 (cmd_log r sigma log act) (tf_reg (spec_ext_arg f)) with
                | Some v => v
                | None => r.[tf_reg (spec_ext_arg f)]
                end).
    { intro f. rewrite getenv_create.
      rewrite <- (Hbase (spec_ext_arg f)).
      match_eq. symmetry. apply latest_write0_eq_latest_write. exact (proj2 Hok f). }
    unfold state_env_matches; split.
    - unfold state_matches; split; intros x.
      + unfold commit_update. rewrite getenv_create.
        rewrite (latest_write_ext_full_reg r sigma (cmd_log r sigma log act) x Hsig Hok).
        unfold tfs_next_cycle. cbn [fst snd]. rewrite getenv_create.
        rewrite find_st_val_app.
        rewrite (tfs_ext_updates_eq r (cmd_log r sigma log act) _ Hst).
        apply (commit_ext_reg_step r (cmd_log r sigma log act) x _ sys _ (Hbase x)).
      + unfold commit_update. rewrite getenv_create.
        rewrite (latest_write_ext_full_other r sigma _ (tf_out x))
          by (solve [ assumption | intros; discriminate ]).
        unfold tfs_next_cycle. cbn [fst snd]. rewrite getenv_create.
        unfold find_out_val at 1. rewrite find_out_update_app, find_out_update_ext_updates.
        assert (r.[tf_out x] = (snd sys).[x]) as Hreg. { apply Hstate. } rewrite Hreg. clear Hreg.
        match_eq. apply latest_write_out; try assumption.
    - unfold env_matches; split; intros.
      + unfold commit_update. rewrite getenv_create.
        rewrite (latest_write_ext_full_other r sigma _ tf_cmd)
          by (solve [ assumption | intros; discriminate ]).
        destruct (reg_ready_or_not r) as [Hready | Hnotready].
        * apply commit_of_latest_write.
          apply (latest_write_cmd_rdy sys r act input sigma log); assumption.
        * apply commit_of_no_write.
          -- apply (latest_write_cmd_nrdy sys r act input sigma log); assumption.
          -- apply (Hin_nrdy Hnotready).
      + unfold commit_update. rewrite getenv_create.
        rewrite (latest_write_ext_full_other r sigma _ (tf_in x))
          by (solve [ assumption | intros; discriminate ]).
        destruct (reg_ready_or_not r) as [Hready | Hnotready].
        * apply commit_of_latest_write.
          apply (latest_write_input_rdy sys r act input sigma log x); assumption.
        * apply commit_of_no_write.
          -- apply (latest_write_input_nrdy sys r act input sigma log x); assumption.
          -- apply (Hin_nrdy Hnotready).
  Qed.

  Lemma interp_rule_cmd_wrong :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log a,
      state_matches sys r ->
      externs_match sigma ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      act <> a ->
      interp_rule r sigma log (rules (rule_cmd a)) = None.
  Proof.
    intros sys r act input sigma log a Hstate Hsig Hin_rdy Hin_nrdy Hact_neq_a.
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

  Lemma commit_schedule_outputs_equal :
    forall (r: ContextEnv.(env_t) R) sigma (L: Log R ContextEnv) sys act input,
      state_env_matches sys act input
        (commit_update r (interp_scheduler' r sigma rules L (system_schedule_outputs tf_ctx)))
      <-> state_env_matches sys act input (commit_update r L).
  Proof.
    intros r sigma L sys act input.
    apply state_env_matches_comp.
    - unfold state_equal; split; intros x; unfold commit_update; rewrite !getenv_create;
        match_eq; apply latest_write_schedule_outputs; reflexivity.
    - unfold env_equal; split; try intros x; unfold commit_update; rewrite !getenv_create;
        match_eq; apply latest_write_schedule_outputs; reflexivity.
  Qed.

  Lemma synthesis_correct_aux2 :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log (actions: list spec_action),
      state_matches sys r ->
      externs_match sigma ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      good_log log ->
      ~ In act actions ->
      state_env_matches (tfs_next_cycle sched_ctx act sys input) act input
        (commit_update r
          match interp_rule r sigma log (rules (rule_cmd act)) with
          | Some l => interp_scheduler' r sigma rules (log_app l log) (fold_right (fun (t : spec_action) (acc : scheduler) => rule_cmd t |> acc) (system_schedule_ext tf_ctx) actions)
          | None => interp_scheduler' r sigma rules log (fold_right (fun (t : spec_action) (acc : scheduler) => rule_cmd t |> acc) (system_schedule_ext tf_ctx) actions)
          end)
      <->
      state_env_matches (tfs_next_cycle sched_ctx act sys input) act input
        (commit_update r (ext_step r sigma (cmd_log r sigma log act))).
  Proof.
    intros sys r act input sigma log actions Hstate Hsig Hin_rdy Hin_nrdy Hlog H_notin_actions.

    induction actions as [|a actions IH].
    - cbn [fold_right]. unfold system_schedule_ext.
      destruct (interp_rule r sigma log (rules (rule_cmd act))) as [l | ] eqn:Hc;
        rewrite interp_scheduler'_ext_cons; apply commit_schedule_outputs_equal.
    - apply not_in_cons in H_notin_actions. destruct H_notin_actions as [Hneq Hnotin].

      cbn [fold_right interp_scheduler'].
      destruct (interp_rule r sigma log (rules (rule_cmd act))) as [l | ] eqn:H_interp_cmd.
      + rewrite (interp_rule_cmd_wrong sys r act input sigma (log_app l log) a Hstate Hsig Hin_rdy Hin_nrdy); try assumption.
        apply IH; try assumption.
      + rewrite (interp_rule_cmd_wrong sys r act input sigma log a Hstate Hsig Hin_rdy Hin_nrdy); try assumption.
        apply IH; try assumption.
  Qed.


  Lemma synthesis_correct_aux :
    forall (sys: sys_state_t) (r: ContextEnv.(env_t) R) 
           (act: spec_action) (input: input_t)
           (sigma: forall f, Sig_denote (Sigma f))
           log,
      state_matches sys r ->
      externs_match sigma ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      good_log log ->
      state_env_matches (tfs_next_cycle sched_ctx act sys input) act input (commit_update r (interp_scheduler' r sigma rules log (system_schedule_actions tf_ctx))).
  Proof.
    intros sys r act input sigma log Hstate Hsig Hin_rdy Hin_nrdy Hlog.
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
      apply (synthesis_correct_aux3 sys r act input sigma log Hstate Hsig Hin_rdy Hin_nrdy Hlog).

    - (* current action is not the requested action *)
      assert (H_act_neq_a: act <> a). { intro H. subst. contradiction. }
      cbn [fold_right interp_scheduler'].

      rewrite (interp_rule_cmd_wrong sys r act input sigma log a Hstate Hsig Hin_rdy Hin_nrdy H_act_neq_a).
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
      (* the attached trusted modules compute what their declarations say *)
      externs_match sigma ->
      ( r.[tf_ready] = Ob~1 -> input_matches act input sigma ) ->
      ( r.[tf_ready] = Ob~0 -> env_matches act input r ) ->
      state_env_matches (tfs_next_cycle sched_ctx act sys input) act input (interp_cycle sigma rules system_schedule r).
  Proof.
    intros sys r act input sigma Hstate Hsig Hin_rdy Hin_nrdy.
    
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

  (* Tracks which axioms / Admitted lemmas `synthesis_correct` still depends on.
     Goal: shrink this to "Closed under the global context" (no admits). *)
  Print Assumptions synthesis_correct.

End SynthesisCorrectness.
