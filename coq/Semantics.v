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
    Context {states_var: Type} {states_var_fin : FiniteType states_var} 
            {inputs_var: Type} {inputs_var_fin : FiniteType inputs_var} 
            {outputs_var: Type} {outputs_var_fin : FiniteType outputs_var} 
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
    Definition convert {szA szB}
      (original : bits_t szA)
      : bits_t szB :=
      match eq_dec szA szB with
      | left e => eq_rect szA (fun sz => bits_t sz) original szB e
      | right n => Bits.slice 0 szB original
      end.

    (* Evaluation of expressions *)
    Fixpoint tf_eval_expr {szB}
      (expr: tf_expr)
      (sys_state: ContextEnv.(env_t) tf_states_type * ContextEnv.(env_t) tf_outputs_type)
      (input: forall (x : inputs_var), (type_denote (tf_inputs_type x)))
      : bits_t szB :=
        match expr with
        | tf_const value =>
            Bits.of_nat szB value
        | tf_svar v =>
            convert (fst sys_state).[v]
        | tf_ivar v =>
            convert (input v)
        | tf_ovar v =>
            convert (snd sys_state).[v]
        | tf_op1 op src =>
            match op with
          | tf_not => Bits.neg (tf_eval_expr src sys_state input)
          | tf_resize source_size =>
            convert (tf_eval_expr (szB:=source_size) src sys_state input)
            end
        | tf_op2 op src1 src2 =>
            let val_src1 := tf_eval_expr src1 sys_state input in
            let val_src2 := tf_eval_expr src2 sys_state input in
            match op with
            | tf_and => Bits.and val_src1 val_src2
            | tf_or => Bits.or val_src1 val_src2
            | tf_xor => Bits.xor val_src1 val_src2
            | tf_add => Bits.plus val_src1 val_src2
            | tf_sub => Bits.minus val_src1 val_src2
            | tf_mul => convert (Bits.mul val_src1 val_src2)
            | tf_cmp szC cmp_op =>
                let val_cmp_src1 := tf_eval_expr (szB:=szC) src1 sys_state input in
                let val_cmp_src2 := tf_eval_expr (szB:=szC) src2 sys_state input in
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
                end
            end
        | tf_expr_if cond then_expr else_expr =>
            let cond_val := tf_eval_expr (szB:=1) cond sys_state input in
            if beq_dec cond_val Bits.zero then (* Note: we check for false i.e. all bits are zero, thus the bodies here are switched *)
              tf_eval_expr else_expr sys_state input 
            else
              tf_eval_expr then_expr sys_state input
        end.

    Inductive tf_update :=
        | tf_no_update
        | tf_st_update (var: states_var) (value: bits_t (states_size var))
        | tf_out_update (var: outputs_var) (value: bits_t (outputs_size var))
        .

    Definition tf_op_step_updates
      (state_op: tf_op)
      (sys_state: ContextEnv.(env_t) tf_states_type * ContextEnv.(env_t) tf_outputs_type)
      (input: forall (x : inputs_var), (type_denote (tf_inputs_type x)))
      : tf_update :=
        match state_op with
        | tf_nop => tf_no_update
        | tf_assign dst expr => tf_st_update dst (tf_eval_expr (szB:=(states_size dst)) expr sys_state input)
        | tf_output dst expr => tf_out_update dst (tf_eval_expr (szB:=(outputs_size dst)) expr sys_state input)
        end.

    Definition tf_op_step_commit_state
      (sys_state: ContextEnv.(env_t) tf_states_type)
      (update: tf_update)
      : ContextEnv.(env_t) tf_states_type :=
        match update with
        | tf_no_update => sys_state
        | tf_st_update var value =>
            ContextEnv.(putenv) sys_state var value
        | tf_out_update _ _ =>
            sys_state
        end.

    Definition tf_op_step_commit_output
      (sys_state: ContextEnv.(env_t) tf_outputs_type)
      (update: tf_update)
      : ContextEnv.(env_t) tf_outputs_type :=
        match update with
        | tf_no_update => sys_state
        | tf_st_update _ _ =>
            sys_state
        | tf_out_update var value =>
            ContextEnv.(putenv) sys_state var value
        end.

    Definition tf_op_step_commit
      (sys_state: ContextEnv.(env_t) tf_states_type * ContextEnv.(env_t) tf_outputs_type)
      (update: tf_update)
      : 
      (ContextEnv.(env_t) tf_states_type * ContextEnv.(env_t) tf_outputs_type) :=
        (tf_op_step_commit_state (fst sys_state) update,
         tf_op_step_commit_output (snd sys_state) update).

    Fixpoint tf_ops_updates
      (state_ops: tf_ops)
      (sys_state: ContextEnv.(env_t) tf_states_type * ContextEnv.(env_t) tf_outputs_type)
      (input: forall (x : inputs_var), (type_denote (tf_inputs_type x)))
      : 
      (list tf_update * (ContextEnv.(env_t) tf_states_type * ContextEnv.(env_t) tf_outputs_type)) :=
        match state_ops with
        | tf_ops_base op =>
            let update := tf_op_step_updates op sys_state input in
            ( [update], tf_op_step_commit sys_state update )
        | tf_ops_cons ops1 ops2 =>
            let (updates1, sys_state1) := tf_ops_updates ops1 sys_state input in
            let (updates2, sys_state2) := tf_ops_updates ops2 sys_state1 input in
            (updates1 ++ updates2, sys_state2)
        | tf_ops_if cond then_ops else_ops =>
            let cond_val := tf_eval_expr (szB:=1) cond sys_state input in
            if beq_dec cond_val Bits.zero then (* Note: we check for false i.e. all bits are zero, thus the bodies here are switched *)
              tf_ops_updates else_ops sys_state input 
            else
              tf_ops_updates then_ops sys_state input
        end.

    Definition tf_ops_run
      (state_ops: tf_ops)
      (sys_state: ContextEnv.(env_t) tf_states_type * ContextEnv.(env_t) tf_outputs_type)
      (input: forall (x : inputs_var), (type_denote (tf_inputs_type x)))
      : 
      (ContextEnv.(env_t) tf_states_type * ContextEnv.(env_t) tf_outputs_type) :=
        snd (tf_ops_updates state_ops sys_state input).

    (* Section Properties.

      Lemma tf_ops_updates_correct:
        forall state_ops sys_state input updates final_state,
          tf_ops_updates state_ops sys_state input = (updates, final_state) ->
          final_state = fold_left tf_op_step_commit updates sys_state.
      Proof.
        intros state_ops. induction state_ops; intros; rename H into Hupd; simpl in *.
        - (* tf_ops_base *)
          inversion Hupd. reflexivity.
        - (* tf_ops_cons *)
          destruct (tf_ops_updates state_ops1 sys_state input) as [updates1 sys_state1] eqn:H1.
          destruct (tf_ops_updates state_ops2 sys_state1 input) as [updates2 sys_state2] eqn:H2.
          inversion Hupd. subst final_state.
          specialize (IHstate_ops1 sys_state input updates1 sys_state1 H1).
          specialize (IHstate_ops2 sys_state1 input updates2 sys_state2 H2).
          rewrite IHstate_ops1 in *. rewrite IHstate_ops2 in *.
          clear IHstate_ops1 IHstate_ops2.
          rewrite <- fold_left_app. reflexivity.
        - (* tf_ops_if *)
          set (cond_val := tf_eval_expr (szB:=1) _ _ _) in *.
          destruct cond_val; destruct vtl; destruct vhd; simpl in *.
          + (* then branch taken *)
            specialize (IHstate_ops1 sys_state input updates final_state Hupd).
            exact IHstate_ops1.
          + (* then branch not taken *)
            specialize (IHstate_ops2 sys_state input updates final_state Hupd).
            exact IHstate_ops2.
      Qed.

      Lemma tf_ops_updates_correct2:
        forall state_ops sys_state input,
          snd (tf_ops_updates state_ops sys_state input) = 
          fold_left tf_op_step_commit (fst (tf_ops_updates state_ops sys_state input)) sys_state.
      Proof.
        intros. destruct (tf_ops_updates state_ops sys_state input) eqn:Hupd.
        cbn in *. apply (tf_ops_updates_correct state_ops sys_state input). exact Hupd.
      Qed.

      Definition tf_op_var_written
        (var: states_var)
        (state_op: tf_op)
        : Prop :=
        exists state input value,
          tf_op_step_updates state_op state input = tf_st_update var value.

      Definition tf_op_var_written_dec
        (var: states_var)
        (state_op: tf_op)
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
        (state_ops: tf_ops)
        : Prop :=
        match state_ops with
        | tf_ops_base op =>
            tf_op_var_written var op
        | tf_ops_cons ops1 ops2 =>
            tf_ops_var_written var ops1 \/
            tf_ops_var_written var ops2
        | tf_ops_if cond then_ops else_ops =>
            tf_ops_var_written var then_ops \/
            tf_ops_var_written var else_ops
        end.

      Definition tf_ops_var_written_dec
        (var: states_var)
        (state_ops: tf_ops)
        : {tf_ops_var_written var state_ops} + {~ (tf_ops_var_written var state_ops)}.
      Proof.
        induction state_ops.
        - exact (tf_op_var_written_dec var op).
        - simpl. destruct IHstate_ops1.
          + left. left. exact t.
          + destruct IHstate_ops2.
            * left. right. exact t.
            * right. unfold not. intros. destruct H as [H|H]; congruence.
        - simpl. destruct IHstate_ops1.
          + left. left. exact t.
          + destruct IHstate_ops2.
            * left. right. exact t.
            * right. unfold not. intros. destruct H as [H|H]; congruence.
      Defined.
          
      Lemma tf_ops_var_not_written_means_ops_run_unchanged:
        forall state_ops sys_state input var,
          ~ tf_ops_var_written var state_ops ->
          (fst (tf_ops_run state_ops sys_state input)).[var] = (fst sys_state).[var].
      Proof.
        intros state_ops. (* destruct sys_state as [state output]. generalize dependent state. generalize dependent output. *)
        unfold tf_ops_run. induction state_ops; intros; rename H into Hnw; simpl.
        - (* tf_ops_base *)
          unfold tf_ops_var_written, tf_op_var_written in Hnw.
          destruct op; cbn; try reflexivity.
          destruct (eq_dec dst var).
          * rewrite e. contradict Hnw. eexists (fst sys_state), input, _. cbn. rewrite e. reflexivity.
          * rewrite get_put_neq by exact n. reflexivity.
        - (* tf_ops_cons *)
          cbn in Hnw.
          assert (~ tf_ops_var_written var state_ops1) as Hnw1 by (intro H; apply Hnw; left; assumption).
          assert (~ tf_ops_var_written var state_ops2) as Hnw2 by (intro H; apply Hnw; right; assumption).
          destruct (tf_ops_updates state_ops1 sys_state input) as [updates1 s1] eqn:Heq1.
          destruct (tf_ops_updates state_ops2 s1 input) as [updates2 s2] eqn:Heq2.
          cbn.
          specialize (IHstate_ops2 s1 input var Hnw2). rewrite Heq2 in IHstate_ops2.
          cbn in IHstate_ops2. rewrite IHstate_ops2.        

          specialize (IHstate_ops1 sys_state input var Hnw1). rewrite Heq1 in IHstate_ops1.
          cbn in IHstate_ops1. apply IHstate_ops1.
        - (* tf_ops_if *)
          cbn in Hnw. set (cond_val := tf_eval_expr (szB:=1) _ _ _) in *.
          destruct cond_val; destruct vtl; cbn.
          destruct vhd; cbn.
          + (* then branch taken *)
            apply (IHstate_ops1 sys_state). intro. apply Hnw; clear Hnw . left. exact H.
          +  (* then branch not taken *)
            apply (IHstate_ops2 sys_state). intro. apply Hnw; clear Hnw. right. exact H.
      Qed.

      Definition tf_op_out_written
        (var: outputs_var)
        (state_op: tf_op)
        : Prop :=
        exists state input value,
          tf_op_step_updates state_op state input = tf_out_update var value.

      Definition tf_op_out_written_dec
        (var: outputs_var)
        (state_op: tf_op)
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
        (state_ops: tf_ops)
        : Prop :=
        match state_ops with
        | tf_ops_base op =>
            tf_op_out_written var op
        | tf_ops_cons ops1 ops2 =>
            tf_ops_out_written var ops1 \/
            tf_ops_out_written var ops2
        | tf_ops_if cond then_ops else_ops =>
            tf_ops_out_written var then_ops \/
            tf_ops_out_written var else_ops
        end.

      Definition tf_ops_out_written_dec
        (var: outputs_var)
        (state_ops: tf_ops)
        : {tf_ops_out_written var state_ops} + {~ (tf_ops_out_written var state_ops)}.
      Proof.
        induction state_ops.
        - exact (tf_op_out_written_dec var op).
        - simpl. destruct IHstate_ops1.
          + left. left. exact t.
          + destruct IHstate_ops2.
            * left. right. exact t.
            * right. unfold not. intros. destruct H as [H|H]; congruence.
        - simpl. destruct IHstate_ops1.
          + left. left. exact t.
          + destruct IHstate_ops2.
            * left. right. exact t.
            * right. unfold not. intros. destruct H as [H|H]; congruence.
      Defined.

      Definition tf_ops_out_not_written_means_ops_run_unchanged:
        forall state_ops sys_state input var,
          ~ tf_ops_out_written var state_ops ->
          (snd (tf_ops_run state_ops sys_state input)).[var] = (snd sys_state).[var].
      Proof.
        intros state_ops.
        unfold tf_ops_run. induction state_ops; intros; rename H into Hnw; simpl.
        - (* tf_ops_base *)
          unfold tf_ops_out_written, tf_op_out_written in Hnw.
          destruct op; cbn; try reflexivity.
          destruct (eq_dec dst var).
          * rewrite e. contradict Hnw. eexists (fst sys_state), input, _. cbn. rewrite e. reflexivity.
          * rewrite get_put_neq by exact n. reflexivity.
        - (* tf_ops_cons *)
          cbn in Hnw.
          assert (~ tf_ops_out_written var state_ops1) as Hnw1 by (intro H; apply Hnw; left; assumption).
          assert (~ tf_ops_out_written var state_ops2) as Hnw2 by (intro H; apply Hnw; right; assumption).
          destruct (tf_ops_updates state_ops1 sys_state input) as [updates1 s1] eqn:Heq1.
          destruct (tf_ops_updates state_ops2 s1 input) as [updates2 s2] eqn:Heq2.
          cbn.
          specialize (IHstate_ops2 s1 input var Hnw2). rewrite Heq2 in IHstate_ops2.
          cbn in IHstate_ops2. rewrite IHstate_ops2.        

          specialize (IHstate_ops1 sys_state input var Hnw1). rewrite Heq1 in IHstate_ops1.
          cbn in IHstate_ops1. apply IHstate_ops1.
        - (* tf_ops_if *)
          cbn in Hnw. set (cond_val := tf_eval_expr (szB:=1) _ _ _) in *.
          destruct cond_val; destruct vtl; cbn.
          destruct vhd; cbn.
          + (* then branch taken *)
            apply (IHstate_ops1 sys_state). intro. apply Hnw; clear Hnw . left. exact H.
          +  (* then branch not taken *)
            apply (IHstate_ops2 sys_state). intro. apply Hnw; clear Hnw. right. exact H.
      Qed.

    End Properties.
 *)
End Semantics.


