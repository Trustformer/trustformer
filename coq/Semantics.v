Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Trustformer.Syntax.

Section Semantics.

    (* Given some (finite) variables, each with some HW register size, we define our semantics  *)
    Context {states_var: Type} {states_var_fin : FiniteType states_var} 
            {inputs_var: Type} {inputs_var_fin : FiniteType inputs_var} 
            {outputs_var: Type} {outputs_var_fin : FiniteType outputs_var}
            {ips_var: Type}
            (states_size : states_var -> nat)
            (inputs_size : inputs_var -> nat)
            (outputs_size : outputs_var -> nat)
            (ips : ips_var -> ip_decl).

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
          | tf_slice source_size offset =>
            Bits.slice offset szB
              (convert (szB:=slice_pad source_size offset szB) (tf_eval_expr (szB:=source_size) src sys_state input))
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
                | tf_slt =>
                    if Bits.signed_lt val_cmp_src1 val_cmp_src2 then convert (Bits.of_nat 1 1) else convert (Bits.of_nat 1 0)
                end
            (* Like tf_cmp, operands evaluate at their OWN widths.  [Bits.app x y]
               puts [y] at the low indices, so this reads "hi followed by lo". *)
            | tf_concat hi_sz lo_sz =>
                let val_hi := tf_eval_expr (szB:=hi_sz) src1 sys_state input in
                let val_lo := tf_eval_expr (szB:=lo_sz) src2 sys_state input in
                convert (Bits.app val_hi val_lo)
            | tf_lsr => Bits.lsr (Bits.to_nat val_src2) val_src1
            | tf_lsl => Bits.lsl (Bits.to_nat val_src2) val_src1
            | tf_asr => Bits.asr (Bits.to_nat val_src2) val_src1
            | tf_islice src_sz =>
                let val_x := tf_eval_expr (szB:=src_sz) src1 sys_state input in
                let val_o := tf_eval_expr (szB:=Nat.log2_up src_sz) src2 sys_state input in
                Bits.slice (Bits.to_nat (convert (szB:=Nat.log2_up (islice_pad src_sz szB)) val_o)) szB
                  (convert (szB:=islice_pad src_sz szB) val_x)
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
        (* The D reading: [dst] gets [ip_fn] of the argument. *)
        | tf_call ip dst arg =>
            let d := ips ip in
            tf_st_update dst
              (convert (ip_fn d (tf_eval_expr (szB:=(ip_req_sz d))
                                              arg sys_state input)))
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

End Semantics.


