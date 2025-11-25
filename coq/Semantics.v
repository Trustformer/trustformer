Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Trustformer.Syntax.
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

    (* Logic for the implicit type conversion *)
    Lemma __convert_le:
      forall a b, a <= b -> Nat.max a b = b.
    Proof. lia. Qed.

    Definition convert {szA szB}
      (original : bits_t szA)
      : bits_t szB :=
      match eq_dec szA szB with
      | left e => eq_rect szA (fun sz => bits_t sz) original szB e
      | right n =>
          match le_dec szA szB with
          | left l =>
            let p := __convert_le _ _ l in
            eq_rect (Nat.max szA szB) bits_t (Bits.extend_end original szB false) szB p
          | right r =>
            Bits.slice 0 szB original
          end
      end.

    (* Evaluation of expressions *)
    Fixpoint tf_eval_expr {szB}
      (expr: tf_expr _ _)
      (state: ContextEnv.(env_t) tf_states_type)
      (input: forall (x : inputs_var), (type_denote (tf_inputs_type x)))
      : bits_t szB :=
        match expr with
        | tf_const _ _ value =>
            Bits.of_nat szB value
        | tf_var _ _ v =>
            convert state.[v]
        | tf_input _ _ v =>
            convert (input v)
        | tf_op1 _ _ op src =>
            let val_src := tf_eval_expr src state input in
            match op with
            | tf_not => Bits.neg val_src
            end
        | tf_op2 _ _ op src1 src2 =>
            let val_src1 := tf_eval_expr src1 state input in
            let val_src2 := tf_eval_expr src2 state input in
            match op with
            | tf_and => Bits.and val_src1 val_src2
            | tf_or => Bits.or val_src1 val_src2
            | tf_xor => Bits.xor val_src1 val_src2
            | tf_add => Bits.plus val_src1 val_src2
            | tf_sub => Bits.minus val_src1 val_src2
            | tf_mul => convert (Bits.mul val_src1 val_src2)
            | tf_cmp szC cmp_op =>
                let val_cmp_src1 := tf_eval_expr (szB:=szC) src1 state input in
                let val_cmp_src2 := tf_eval_expr (szB:=szC) src2 state input in
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
                end
            end
        end.

    Inductive tf_update :=
        | tf_no_update
        | tf_st_update (var: states_var) (value: bits_t (states_size var))
        | tf_out_update (var: outputs_var) (value: bits_t (outputs_size var))
        .

    Definition tf_op_step_updates
      (state_op: tf_op states_var inputs_var outputs_var)
      (state: ContextEnv.(env_t) tf_states_type)
      (input: forall (x : inputs_var), (type_denote (tf_inputs_type x)))
      : tf_update :=
        match state_op with
        | tf_nop _ _ _ => tf_no_update
        | tf_assign _ _ _ dst expr => tf_st_update dst (tf_eval_expr (szB:=(states_size dst)) expr state input)
        | tf_output _ _ _ dst expr => tf_out_update dst (tf_eval_expr (szB:=(outputs_size dst)) expr state input)
        end.

    Definition tf_op_step_commit
      (sys_state: ContextEnv.(env_t) tf_states_type * ContextEnv.(env_t) tf_outputs_type)
      (update: tf_update)
      : 
      (ContextEnv.(env_t) tf_states_type * ContextEnv.(env_t) tf_outputs_type) :=
        match update with
        | tf_no_update => sys_state
        | tf_st_update var value =>
            (ContextEnv.(putenv) (fst sys_state) var value, snd sys_state)
        | tf_out_update var value =>
            (fst sys_state, ContextEnv.(putenv) (snd sys_state) var value)
        end.

    Fixpoint tf_ops_updates
      (state_ops: tf_ops states_var inputs_var outputs_var)
      (sys_state: ContextEnv.(env_t) tf_states_type * ContextEnv.(env_t) tf_outputs_type)
      (input: forall (x : inputs_var), (type_denote (tf_inputs_type x)))
      : 
      (list tf_update) :=
        match state_ops with
        | tf_ops_base _ _ _ op =>
            [tf_op_step_updates op (fst sys_state) input]
        | tf_ops_cons _ _ _ op ops =>
            let update1 := tf_op_step_updates op (fst sys_state) input in
            let new_sys_state1 := tf_op_step_commit sys_state update1 in
            update1 :: tf_ops_updates ops new_sys_state1 input
        | tf_ops_if _ _ _ cond then_ops else_ops =>
            let cond_val := tf_eval_expr (szB:=1) cond (fst sys_state) input in
            if beq_dec cond_val Bits.zero then (* Note: we check for false i.e. all bits are zero, thus the bodies here are switched *)
              tf_ops_updates else_ops sys_state input 
            else
              tf_ops_updates then_ops sys_state input
        end.

    Definition tf_ops_run
      (state_ops: tf_ops states_var inputs_var outputs_var)
      (sys_state: ContextEnv.(env_t) tf_states_type * ContextEnv.(env_t) tf_outputs_type)
      (input: forall (x : inputs_var), (type_denote (tf_inputs_type x)))
      : 
      (ContextEnv.(env_t) tf_states_type * ContextEnv.(env_t) tf_outputs_type) :=
        let updates := tf_ops_updates state_ops sys_state input in
        fold_left tf_op_step_commit updates sys_state.

    Section Properties.

      Definition tf_op_var_written
        (var: states_var)
        (state_op: tf_op states_var inputs_var outputs_var)
        : Prop :=
        exists state input value,
          tf_op_step_updates state_op state input = tf_st_update var value.

      Definition tf_op_var_written_dec
        (var: states_var)
        (state_op: tf_op states_var inputs_var outputs_var)
        : {tf_op_var_written var state_op} + {~ (tf_op_var_written var state_op)}.
      Proof.
        unfold tf_op_var_written.
        destruct state_op.   
        - (* tf_nop *)
          right. intros H. destruct H as [state [input [value H]]]. inversion H.
        - (* tf_assign *)
          destruct (eq_dec dst var).
          + left. exists (ContextEnv.(create) (fun k => Bits.zero)). exists (fun k => Bits.zero).
            subst dst. timeout 10 simpl. econstructor. reflexivity.
          + right. intros H. destruct H as [state [input [value H]]]. inversion H. congruence.
        - (* tf_output *)
          right. intros H. destruct H as [state [input [value H]]]. inversion H.
      Defined.

      Fixpoint tf_ops_var_written
        (var: states_var)
        (state_ops: tf_ops states_var inputs_var outputs_var)
        : Prop :=
        match state_ops with
        | tf_ops_base _ _ _ op =>
            tf_op_var_written var op
        | tf_ops_cons _ _ _ op ops =>
            tf_op_var_written var op \/
            tf_ops_var_written var ops
        | tf_ops_if _ _ _ cond then_ops else_ops =>
            tf_ops_var_written var then_ops \/
            tf_ops_var_written var else_ops
        end.

      Definition tf_ops_var_written_dec
        (var: states_var)
        (state_ops: tf_ops states_var inputs_var outputs_var)
        : {tf_ops_var_written var state_ops} + {~ (tf_ops_var_written var state_ops)}.
      Proof.
        induction state_ops.
        - exact (tf_op_var_written_dec var op).
        - simpl. destruct (tf_op_var_written_dec var op).
          + left. left. exact t.
          + destruct IHstate_ops.
            * left. right. exact t.
            * right. unfold not. intros. destruct H as [H|H]; congruence.
        - simpl. destruct IHstate_ops1.
          + left. left. exact t.
          + destruct IHstate_ops2.
            * left. right. exact t.
            * right. unfold not. intros. destruct H as [H|H]; congruence.
      Defined.
          

      Definition tf_op_out_written
        (var: outputs_var)
        (state_op: tf_op states_var inputs_var outputs_var)
        : Prop :=
        exists state input value,
          tf_op_step_updates state_op state input = tf_out_update var value.

      Definition tf_op_out_written_dec
        (var: outputs_var)
        (state_op: tf_op states_var inputs_var outputs_var)
        : {tf_op_out_written var state_op} + {~ (tf_op_out_written var state_op)}.
      Proof.
        unfold tf_op_out_written.
        destruct state_op.   
        - (* tf_nop *)
          right. intros H. destruct H as [state [input [value H]]]. inversion H.
        - (* tf_assign *)
          right. intros H. destruct H as [state [input [value H]]]. inversion H.
        - (* tf_output *)
          destruct (eq_dec dst var).
          + left. exists (ContextEnv.(create) (fun k => Bits.zero)). exists (fun k => Bits.zero).
            subst dst. timeout 10 simpl. econstructor. reflexivity.
          + right. intros H. destruct H as [state [input [value H]]]. inversion H. congruence.
      Defined.

      Fixpoint tf_ops_out_written
        (var: outputs_var)
        (state_ops: tf_ops states_var inputs_var outputs_var)
        : Prop :=
        match state_ops with
        | tf_ops_base _ _ _ op =>
            tf_op_out_written var op
        | tf_ops_cons _ _ _ op ops =>
            tf_op_out_written var op \/
            tf_ops_out_written var ops
        | tf_ops_if _ _ _ cond then_ops else_ops =>
            tf_ops_out_written var then_ops \/
            tf_ops_out_written var else_ops
        end.

      Definition tf_ops_out_written_dec
        (var: outputs_var)
        (state_ops: tf_ops states_var inputs_var outputs_var)
        : {tf_ops_out_written var state_ops} + {~ (tf_ops_out_written var state_ops)}.
      Proof.
        induction state_ops.
        - exact (tf_op_out_written_dec var op).
        - simpl. destruct (tf_op_out_written_dec var op).
          + left. left. exact t.
          + destruct IHstate_ops.
            * left. right. exact t.
            * right. unfold not. intros. destruct H as [H|H]; congruence.
        - simpl. destruct IHstate_ops1.
          + left. left. exact t.
          + destruct IHstate_ops2.
            * left. right. exact t.
            * right. unfold not. intros. destruct H as [H|H]; congruence.
      Defined.

    End Properties.

End Semantics.


