Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Trustformer.v1.TrustformerSyntax.
Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Section Semantics.

    (* Given some (finite) variables, each with some HW register type, we define our semantics  *)
    Context (states_var: Type) (states_var_fin : FiniteType states_var) (states_size : states_var -> nat).

    Definition tf_states_type (x: states_var) := 
      bits_t (states_size x).

    (* Given a variable, a current variable, and a thunk to compute the new value if they match,
       returns Some new value if they match, None otherwise *)
    Definition when_vars_match
      (op_var: states_var)
      (current_var: states_var)
      (thunk: unit -> option (type_denote (tf_states_type current_var)))
      : option (type_denote (tf_states_type current_var)) :=
      match eq_dec op_var current_var with
      | left e =>
        match e with
        | eq_refl => thunk tt
        end
      | right _ => None
      end.

    (* Given a current state, a variable & an operation, returns the new value for the variable if it is written to *)
    Definition tf_op_step_writes
      (state: ContextEnv.(env_t) tf_states_type)
      (var: states_var)
      (state_op: TrustformerSyntax.tf_ops states_var)
      : option (type_denote (tf_states_type var)) :=
        match state_op with
        | tf_nop _ => None
        | tf_neg _ x =>
            when_vars_match x var (fun _ => Some (Bits.neg state.[var]))
        end.
    
    (* Given a current state and an operation, returns the variable that is changed, if any *)
    Definition tf_op_step_changed
      (state: ContextEnv.(env_t) tf_states_type)
      (state_op: TrustformerSyntax.tf_ops states_var)
      : option (states_var) :=
        match state_op with
        | tf_nop _ => None
        | tf_neg _ x => Some x
        end.

    (* Semantics of a single operation step *)
    Definition tf_op_step_commit
      (state: ContextEnv.(env_t) tf_states_type)
      (state_op: TrustformerSyntax.tf_ops states_var)
      : 
      (ContextEnv.(env_t) tf_states_type) :=
        (ContextEnv.(create)
          (fun k => 
            match tf_op_step_writes state k state_op with
              | Some v => v
              | None => state.[k]
              end)).

    (* TODO: Semantics of a chain of operation steps *)

    Section Properties.

      (* Nop Operation *)
      Lemma tf_op_step_writes_nop :
        forall (state: ContextEnv.(env_t) tf_states_type) (x : states_var),
        tf_op_step_writes state x (tf_nop states_var) = None.
      Proof.
        intros.
        unfold tf_op_step_writes.
        reflexivity.
      Qed.

      Lemma tf_op_step_commit_nop :
        forall (state: ContextEnv.(env_t) tf_states_type) (t : unit),
        tf_op_step_commit state (tf_nop states_var) = state.
      Proof.
        intros.
        unfold tf_op_step_commit.
        apply equiv_eq. intros k. rewrite getenv_create.
        rewrite tf_op_step_writes_nop.
        timeout 10 sauto.
      Qed.

      (* Neg Operation *)
      Lemma tf_op_step_writes_neg_other_var :
        forall (state: ContextEnv.(env_t) tf_states_type) (x y : states_var),
        x <> y -> tf_op_step_writes state y (tf_neg states_var x) = None.
      Proof.
        intros.
        unfold tf_op_step_writes.
        unfold when_vars_match.
        destruct (eq_dec x y).
        - contradiction.
        - reflexivity.
      Qed.

      Lemma tf_op_step_commit_neg_other_var :
        forall (state: ContextEnv.(env_t) tf_states_type) (x y : states_var),
        x <> y -> (tf_op_step_commit state (tf_neg states_var x)).[y] = state.[y].
      Proof.
        intros.
        unfold tf_op_step_commit.
        rewrite getenv_create.
        rewrite tf_op_step_writes_neg_other_var.
        timeout 10 sauto. timeout 10 sauto.
      Qed.

      Lemma tf_op_step_writes_neg_same_var :
        forall (state: ContextEnv.(env_t) tf_states_type) (x : states_var),
        tf_op_step_writes state x (tf_neg states_var x) = Some (Bits.neg (state.[x])).
      Proof.
        intros.
        unfold tf_op_step_writes, when_vars_match.
        destruct (eq_dec x x).
        - destruct e. reflexivity.
        - contradiction.
      Qed.

      Lemma tf_op_step_commit_neg_same_var :
        forall (state: ContextEnv.(env_t) tf_states_type) (x : states_var),
        (tf_op_step_commit state (tf_neg states_var x)).[x] = Bits.neg (state.[x]).
      Proof.
        intros.
        unfold tf_op_step_commit. rewrite getenv_create.
        rewrite tf_op_step_writes_neg_same_var.
        destruct (eq_dec x x).
        - reflexivity.
        - contradiction.
      Qed.

      (* Unchanged Property *)
      Definition tf_op_var_not_written
        (var: states_var)
        (state_op: TrustformerSyntax.tf_ops states_var)
        : Prop :=
        forall state,
        tf_op_step_writes state var state_op = None.

      Definition tf_op_var_not_written_dec
        (var: states_var)
        (state_op: TrustformerSyntax.tf_ops states_var)
        : {tf_op_var_not_written var state_op} + {~ (tf_op_var_not_written var state_op)}.
      Proof.
        unfold tf_op_var_not_written.
        destruct state_op. 
        - (* tf_nop *)
          left. intros. rewrite tf_op_step_writes_nop. reflexivity.
        - (* tf_neg *)
          destruct (eq_dec x var).
          + right. intros H. specialize (H (ContextEnv.(create) (fun k => Bits.zero))).
            subst x. rewrite tf_op_step_writes_neg_same_var in H.
            inversion H.
          + left. intros. rewrite tf_op_step_writes_neg_other_var; auto. 
      Defined.

      Definition tf_op_var_not_written_dec_nop
        (var: states_var)
        : tf_op_var_not_written var (tf_nop states_var).
      Proof.
        unfold tf_op_var_not_written.
        intros. rewrite tf_op_step_writes_nop. reflexivity.
      Qed.

      Definition filter_written_vars
        (state_op: TrustformerSyntax.tf_ops states_var)
        :
        forall x, In x (filter (fun v => if tf_op_var_not_written_dec v state_op then false else true) finite_elements) <-> ~ tf_op_var_not_written x state_op. 
      Proof.
        intros. split; intros H.
        - unfold tf_op_var_not_written in *. unfold not. intros.
          apply filter_In in H. destruct H as [H1 H2].
          destruct (tf_op_var_not_written_dec x state_op).
          + inversion H2.
          + auto.
        - unfold tf_op_var_not_written in *. unfold not in H.
          apply filter_In. split.
          + apply nth_error_In with (n := finite_index x). exact (finite_surjective x).
          + destruct (tf_op_var_not_written_dec x state_op).
            * exfalso; apply H; auto.
            * reflexivity.
      Qed.

      Definition filter_written_vars_nop
        :
        (filter (fun v => if tf_op_var_not_written_dec v (tf_nop states_var) then false else true) finite_elements) = [].
      Proof.
        set (f_list := filter _ _).
        destruct (f_list) eqn:E.
        - reflexivity.
        - assert (In s f_list) by (timeout 10 sauto). subst f_list.
          rewrite filter_written_vars in H. contradict H. unfold tf_op_var_not_written. intros. rewrite tf_op_step_writes_nop. reflexivity.
      Qed.

      Definition filter_written_vars_neg
        :
        forall x, (filter (fun v => if tf_op_var_not_written_dec v (tf_neg states_var x) then false else true) finite_elements) = [x].
      Proof.
        intros.
        set (f_list := filter _ _).
        assert (NoDup f_list).
        {
          subst f_list. apply NoDup_filter. apply finite_nodup.
        }
        assert (In x f_list).
        {
          subst f_list. apply filter_written_vars. unfold not. intros. specialize (H0 (ContextEnv.(create) (fun k => Bits.zero))).
          rewrite tf_op_step_writes_neg_same_var in H0. inversion H0.
        }
        assert (forall y, y <> x -> ~ In y f_list).
        {
          subst f_list. intros. rewrite filter_written_vars. unfold not. intros. apply H2. clear H2.
          unfold tf_op_var_not_written. intros. rewrite tf_op_step_writes_neg_other_var; auto.
        }

        destruct f_list as [| y l].
        - exfalso. apply H0.
        - assert (Heq_y_x : y = x).
          {
            destruct (eq_dec y x) as [Heq | Hneq].
            - exact Heq.
            - exfalso. specialize (H1 y Hneq). timeout 10 sauto.
          } subst y.
          assert (Heq_l_nil : l = []).
          {
            destruct l as [| z l'].
            - reflexivity.
            - exfalso.
              assert (H_z_neq_x : z <> x).
              { inversion H. timeout 10 sauto. }
              specialize (H1 z H_z_neq_x).
              exfalso. apply H1.
              timeout 10 sauto.
          } subst l.
          
          reflexivity.
      Qed.

    End Properties.

End Semantics.


