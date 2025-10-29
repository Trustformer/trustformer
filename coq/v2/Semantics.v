Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Trustformer.v2.Syntax.
Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Section Semantics.

    (* Given some (finite) variables, each with some HW register size, we define our semantics  *)
    Context (states_var: Type) (states_var_fin : FiniteType states_var) 
            (inputs_var: Type) (inputs_var_fin : FiniteType inputs_var) 
            (outputs_var: Type) (outputs_var_fin : FiniteType outputs_var) 
            (states_size : states_var -> nat)
            (inputs_size : inputs_var -> nat)
            (outputs_size : outputs_var -> nat).

    (* All spec states are mapped to bits, the size is given by the states_size function *)
    Definition tf_states_type (x: states_var) := 
      bits_t (states_size x).

    Definition tf_inputs_type (x: inputs_var) := 
      bits_t (inputs_size x).

    Definition tf_outputs_type (x: outputs_var) := 
      bits_t (outputs_size x).

    (* Given a variable, a current variable, and a thunk to compute the new value if they match,
       returns `Some new value` if they match, None otherwise *)
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

    (* Given a variable, a current variable, and a thunk to compute the new value if they match,
       returns `Some new value` if they match, None otherwise *)
    Definition when_outputs_match
      (op_var: outputs_var)
      (current_var: outputs_var)
      (thunk: unit -> option (type_denote (tf_outputs_type current_var)))
      : option (type_denote (tf_outputs_type current_var)) :=
      match eq_dec op_var current_var with
      | left e =>
        match e with
        | eq_refl => thunk tt
        end
      | right _ => None
      end.

    Lemma __convert_lt:
      forall a b, a < b -> Nat.max a b = b.
    Proof. lia. Qed.

    Definition convert {szA szB}
      (original : bits_t szA)
      : bits_t szB :=
      match eq_dec szA szB with
      | left e => eq_rect szA (fun sz => bits_t sz) original szB e
      | right n =>
          match lt_dec szA szB with
          | left l =>
            let p := __convert_lt _ _ l in
            eq_rect (Nat.max szA szB) bits_t (Bits.extend_end original szB false) szB p
          | right r =>
            Bits.slice 0 szB original
          end
      end.

    (* Given a current state, a variable & an operation, returns the new value for the variable if it is written to *)
    Definition tf_op_step_writes
      (state: ContextEnv.(env_t) tf_states_type)
      (input: forall (x : inputs_var), (type_denote (tf_inputs_type x)))
      (var: states_var)
      (state_op: tf_ops states_var inputs_var outputs_var)
      : option (type_denote (tf_states_type var)) :=
        match state_op with
        | tf_nop _ _ _ => None
        | tf_neg _ _ _ x =>
            when_vars_match x var (fun _ => Some (Bits.neg state.[var]))
        | tf_input _ _ _ x y =>
            when_vars_match x var (fun _ => Some (convert (input y)))
        | tf_output _ _ _ x y =>
            None
        end.
    
    (* Currently simple due to single cycle synth, later we need to detect when the out field was written to *)
    Definition tf_op_step_outputs
      (state: ContextEnv.(env_t) tf_states_type)
      (var: outputs_var)
      (state_op: tf_ops states_var inputs_var outputs_var)
      : option (type_denote (tf_outputs_type var)) :=
        match state_op with
        | tf_output _ _ _ x y => when_outputs_match y var (fun _ => Some (convert (state.[x])))
        | _ => None
        end.

    (* Given a current state and an operation, returns the new state after the operation is applied *)
    Definition tf_op_step_commit
      (state: ContextEnv.(env_t) tf_states_type)
      (input: forall (x : inputs_var), (type_denote (tf_inputs_type x)))
      (state_op: tf_ops states_var inputs_var outputs_var)
      : 
      (ContextEnv.(env_t) tf_states_type) :=
        (ContextEnv.(create)
          (fun k => 
            match tf_op_step_writes state input k state_op with
              | Some v => v
              | None => state.[k]
              end)).

    Definition tf_op_outputs
      (state: ContextEnv.(env_t) tf_states_type)
      (input: forall (x : inputs_var), (type_denote (tf_inputs_type x)))
      (output: ContextEnv.(env_t) tf_outputs_type)
      (state_op: tf_ops states_var inputs_var outputs_var)
      : 
      (ContextEnv.(env_t) tf_outputs_type) :=
        (ContextEnv.(create)
          (fun k => 
            match tf_op_step_outputs state k state_op with
              | Some v => v
              | None => output.[k]
              end)).

    (* TODO: Semantics of a chain of operation steps *)

    Section Properties.

      (* Unchanged Property *)
      Definition tf_op_var_not_written
        (var: states_var)
        (state_op: tf_ops states_var inputs_var outputs_var)
        : Prop :=
        forall state input,
        tf_op_step_writes state input var state_op = None.

      Definition tf_op_var_not_written_dec
        (var: states_var)
        (state_op: tf_ops states_var inputs_var outputs_var)
        : {tf_op_var_not_written var state_op} + {~ (tf_op_var_not_written var state_op)}.
      Proof.
        unfold tf_op_var_not_written.
        destruct state_op. 
        - (* tf_nop *)
          left. intros. timeout 10 sauto.
        - (* tf_neg *)
          destruct (eq_dec x var).
          + right. intros H. specialize (H (ContextEnv.(create) (fun k => Bits.zero)) (fun k => Bits.zero)).
            subst x. timeout 10 simpl in H. unfold when_vars_match in H. destruct (eq_dec var var).
            destruct e. timeout 10 sauto. timeout 10 sauto.
          + left. intros. timeout 10 simpl. unfold when_vars_match. destruct (eq_dec x var). destruct e. timeout 10 sauto. timeout 10 sauto.
        - (* tf_input *)
          destruct (eq_dec x var).
          + right. intros H. specialize (H (ContextEnv.(create) (fun k => Bits.zero)) (fun k => Bits.zero)).
            subst x. timeout 10 simpl in H. unfold when_vars_match in H. destruct (eq_dec var var).
            destruct e. timeout 10 sauto. timeout 10 sauto.
          + left. intros. timeout 10 simpl. unfold when_vars_match. destruct (eq_dec x var). destruct e. timeout 10 sauto. timeout 10 sauto.
        - (* tf_output *)
          left. intros. timeout 10 sauto. 
      Defined.

      Definition filter_written_vars
        (state_op: tf_ops states_var inputs_var outputs_var)
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

      (* Outputs *)
      Definition tf_op_no_output
        (var: outputs_var)
        (state_op: tf_ops states_var inputs_var outputs_var)
        : Prop :=
        forall state,
        tf_op_step_outputs state var state_op = None.
      
      Definition tf_op_no_output_dec
        (var: outputs_var)
        (state_op: tf_ops states_var inputs_var outputs_var)
        : {tf_op_no_output var state_op} + {~ (tf_op_no_output var state_op)}.
      Proof.
        unfold tf_op_no_output.
        destruct state_op. 
        - (* tf_nop *) left. intros. timeout 10 sauto.
        - (* tf_neg *) left. intros. timeout 10 sauto.
        - (* tf_input *) left. intros. timeout 10 sauto.
        - (* tf_output *)
          destruct (eq_dec y var).
          + right. intros H. specialize (H (ContextEnv.(create) (fun k => Bits.zero))).
            subst y. timeout 10 simpl in H. unfold when_outputs_match in H. destruct (eq_dec var var).
            destruct e. timeout 10 sauto. timeout 10 sauto.
          + left. intros. timeout 10 simpl. unfold when_outputs_match. destruct (eq_dec y var). destruct e. timeout 10 sauto. timeout 10 sauto.
      Defined.

    End Properties.

End Semantics.


