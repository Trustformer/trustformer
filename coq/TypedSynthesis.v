Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.
Require Export Koika.Primitives.

Require Koika.Properties.SemanticProperties.
Require Import Coq.Program.Program.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Utils.
Require Import Trustformer.Scheduler.Contract.
Require Trustformer.Properties.Common.
From Koika.Utils Require Import Tactics.

Require Import Streams.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Init.Tactics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.micromega.Lia.

Require Import Hammer.Plugin.Hammer.
Set Hammer ATPLimit 5.
Set Hammer GSMode 63.

Record TFSynthContext := {
  tf_sched_ctx : TFSchedule;

  tf_action_reg_size : nat;
  tf_action_encoding : (tfs_action tf_sched_ctx) -> bits_t tf_action_reg_size;
  tf_action_encoding_inj : forall a1 a2, tf_action_encoding a1 = tf_action_encoding a2 -> a1 = a2;
  tf_action_names : Show (tfs_action tf_sched_ctx);
}.

Section SynthesisTypes.

  Context {states_var: Type}.
  Context {inputs_var: Type}.
  Context {outputs_var: Type}.
  Context {externs_var: Type}.
  Context {actions: Type}.

  Inductive _reg_t := 
    | tf_cmd
    | tf_cmd_ack
    | tf_ready
    | tf_reg (x : states_var)
    | tf_in (x : inputs_var)
    | tf_out (x : outputs_var)
    | tf_out_ack (x : outputs_var)
    .

  Inductive _rule_name_t :=
    | rule_cmd (cmd: actions)
    | rule_out (out: outputs_var)
    (* Issues the external calls. Un-gated by action, so the design contains exactly
       one [ExternalCall] per function and therefore one Verilog driver per port. *)
    | rule_ext
    | rule_busy
    .

  Inductive _ext_fn_t := 
    | ext_in_cmd
    | ext_input (x : inputs_var)
    | ext_output (x : outputs_var)
    (* Trusted external function port. Carries the argument out and the result back
       in; assumed not to be observable by the attacker. *)
    | ext_call (f : externs_var)
    .

End SynthesisTypes.

Section TypedSynthesis.

    Context (tf_ctx: TFSynthContext).

    (* ====== Abbreviations ====== *)

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

    Local Notation spec_action := (tfs_action (tf_sched_ctx tf_ctx)).    Local Notation spec_action_fin := (tfs_action_fin (tf_sched_ctx tf_ctx)).
    Local Notation spec_all_actions := (@finite_elements spec_action spec_action_fin).
    Local Notation spec_action_index := (@finite_index spec_action spec_action_fin).
    Local Notation spec_action_num := (Datatypes.length spec_all_actions).

    Local Notation spec_action_reg_size := (tf_action_reg_size tf_ctx).
    Local Notation spec_action_encoding := (tf_action_encoding tf_ctx).
    Local Notation spec_action_encoding_inj := (tf_action_encoding_inj tf_ctx).

    Local Notation spec_schedule := (tfs_schedule (tf_sched_ctx tf_ctx)).
    Local Notation spec_done_state := (tfs_done_signal (tf_sched_ctx tf_ctx)).
    Local Notation spec_reset_states := (tfs_reset_states (tf_sched_ctx tf_ctx)).

    (* ====== Instances ====== *)

    Hint Extern 0 (FiniteType spec_states) => exact (tfs_states_fin (tf_sched_ctx tf_ctx)) : typeclass_instances.
    Hint Extern 0 (FiniteType spec_inputs) => exact (tfs_inputs_fin (tf_sched_ctx tf_ctx)) : typeclass_instances.
    Hint Extern 0 (FiniteType spec_outputs) => exact (tfs_outputs_fin (tf_sched_ctx tf_ctx)) : typeclass_instances.
    Hint Extern 0 (FiniteType spec_action) => exact (tfs_action_fin (tf_sched_ctx tf_ctx)) : typeclass_instances.

    Hint Extern 0 (Show spec_states) => exact (tfs_states_names (tf_sched_ctx tf_ctx)) : typeclass_instances.
    Hint Extern 0 (Show spec_inputs) => exact (tfs_inputs_names (tf_sched_ctx tf_ctx)) : typeclass_instances.
    Hint Extern 0 (Show spec_outputs) => exact (tfs_outputs_names (tf_sched_ctx tf_ctx)) : typeclass_instances.
    Hint Extern 0 (Show spec_action) => exact (tf_action_names tf_ctx) : typeclass_instances.


    Instance _eq_dec_states : EqDec spec_states.
    Proof. pose spec_states_fin. apply EqDec_FiniteType. Defined.

    Instance _eq_dec_outputs : EqDec spec_outputs.
    Proof. pose spec_outputs_fin. apply EqDec_FiniteType. Defined.

    (* ====== Registers ====== *)

    Local Notation reg_t := (@_reg_t spec_states spec_inputs spec_outputs).

    Definition _reg_t_index2 (s: reg_t) : nat * nat :=
      match s with
      | tf_cmd => (0, 0)
      | tf_cmd_ack => (1, 0)
      | tf_ready => (2, 0)
      | tf_reg x => (3, spec_state_index x)
      | tf_in x => (4, spec_input_index x)
      | tf_out x => (5, spec_output_index x)
      | tf_out_ack x => (6, spec_output_index x)
      end.

    Definition _reg_t_elements2 : list (list reg_t) :=
      [ [tf_cmd] ] ++
      [ [tf_cmd_ack] ] ++
      [ [tf_ready] ] ++
      [ map tf_reg spec_all_states ] ++
      [ map tf_in spec_all_inputs ] ++
      [ map tf_out spec_all_outputs ] ++
      [ map tf_out_ack spec_all_outputs ].

    (* These three must stay Qed-opaque: a transparent proof inside the FiniteType2
       record forces the kernel to rebuild a huge term on every conversion that goes
       through ContextEnv, which costs seconds per Qed in the downstream proofs. *)
    Lemma _reg_t_surjective2 :
      forall a : reg_t, forall n m,
        _reg_t_index2 a = (n, m) ->
        exists l, nth_error _reg_t_elements2 n = Some l /\ nth_error l m = Some a.
    Proof.
        unfold _reg_t_index2, _reg_t_elements2.
        intros x n m EQ.
        destruct x; inversion EQ; clear EQ; subst.
        + (* tf_cmd *)
          exists [tf_cmd]. split; auto.
        + (* tf_cmd_ack *)
          exists [tf_cmd_ack]. split; auto.
        + (* tf_ready *)
          exists [tf_ready]. split; auto.
        + (* tf_reg *)
          exists (map tf_reg spec_all_states). split; auto.
          apply map_nth_error. apply finite_surjective.
        + (* tf_in *)
          exists (map tf_in spec_all_inputs). split; auto.
          apply map_nth_error. apply finite_surjective.
        + (* tf_out *)
          exists (map tf_out spec_all_outputs). split; auto.
          apply map_nth_error. apply finite_surjective.
        + (* tf_out_ack *)
          exists (map tf_out_ack spec_all_outputs). split; auto.
          apply map_nth_error. apply finite_surjective.
    Qed.

    Lemma _reg_t_index_of2 :
      forall n l,
        nth_error _reg_t_elements2 n = Some l ->
        forall m x, nth_error l m = Some x -> _reg_t_index2 x = (n, m).
    Proof.
        unfold _reg_t_index2, _reg_t_elements2.
        intros n l Hn m x Hm.
      
        destruct n as [|n].
        { inversion Hn. subst. destruct m. inversion Hm. subst; reflexivity. inversion Hm. rewrite nth_error_nil in H0. congruence. }
        destruct n as [|n].
        { inversion Hn. subst. destruct m. inversion Hm. subst; reflexivity. inversion Hm. rewrite nth_error_nil in H0. congruence. }
        destruct n as [|n].
        { inversion Hn. subst. destruct m. inversion Hm. subst; reflexivity. inversion Hm. rewrite nth_error_nil in H0. congruence. }
        
        (* For mapped blocks, we use the injectivity of the map and the underlying finite type *)
        destruct n as [|n].
        { inversion Hn; subst. apply nth_error_map_inv in Hm. destruct Hm as [s [Hs ?]]; subst.
          apply finite_elements_index in Hs. subst. reflexivity. }
        destruct n as [|n].
        { inversion Hn; subst. apply nth_error_map_inv in Hm. destruct Hm as [s [Hs ?]]; subst.
          apply finite_elements_index in Hs. subst. reflexivity. }
        destruct n as [|n].
        { inversion Hn; subst. apply nth_error_map_inv in Hm. destruct Hm as [s [Hs ?]]; subst.
          apply finite_elements_index in Hs. subst. reflexivity. }
        destruct n as [|n].
        { inversion Hn; subst. apply nth_error_map_inv in Hm. destruct Hm as [s [Hs ?]]; subst.
          apply finite_elements_index in Hs. subst. reflexivity. }
        
        inversion Hn. rewrite nth_error_nil in H0. congruence. 
    Qed.

    Lemma _reg_t_injective2 :
      Forall (fun l => NoDup (map _reg_t_index2 l)) _reg_t_elements2.
    Proof.
        unfold _reg_t_index2, _reg_t_elements2.
        do 6 (try apply Forall_app; try split).
        all: constructor; [| constructor].        
        + apply NoDup_one.
        + apply NoDup_one.
        + apply NoDup_one.
        + cbn [map]. rewrite map_map.
          apply NoDup_map_pair.
          apply finite_injective.
        + cbn [map]. rewrite map_map.
          apply NoDup_map_pair.
          apply finite_injective.
        + cbn [map]. rewrite map_map.
          apply NoDup_map_pair.
          apply finite_injective.
        + cbn [map]. rewrite map_map.
          apply NoDup_map_pair.
          apply finite_injective.
    Qed.

    Instance _reg_t_fin2 : FiniteType2 reg_t :=
      {| finite2_index := _reg_t_index2;
         finite2_elements := _reg_t_elements2;
         finite2_surjective := _reg_t_surjective2;
         finite2_ := _reg_t_index_of2;
         finite2_injective2 := _reg_t_injective2 |}.

    Instance _reg_t_finite : FiniteType reg_t.
    Proof.
      apply FiniteType2_FiniteType.
    Defined.

    Definition _reg_name (x: spec_states) : string :=
      "tf_st_" ++ string_id_of_nat (spec_state_index x).

    Definition _in_name (x: spec_inputs) : string :=
      "tf_in_" ++ string_id_of_nat (spec_input_index x).

    Definition _out_name (x: spec_outputs) : string :=
      "tf_out_" ++ string_id_of_nat (spec_output_index x).

    Instance reg_names : Show reg_t :=
      { show := fun r => match r with
          | tf_cmd => "cmd"
          | tf_cmd_ack => "cmd_ack"
          | tf_ready => "ready"
          | tf_reg x => String.append "st_" (show x)
          | tf_in x => String.append "in_" (show x)
          | tf_out x => String.append "out_" (show x)
          | tf_out_ack x => String.append "out_ack_" (show x)
          end
      }.

    (* ====== Register Types ====== *)

    Definition R (r: reg_t) :=
    match r with
    | tf_cmd => bits_t spec_action_reg_size
    | tf_cmd_ack => bits_t 1
    | tf_ready => bits_t 1
    | tf_reg x => spec_states_t x
    | tf_in x => spec_inputs_t x
    | tf_out x => spec_outputs_t x
    | tf_out_ack x => bits_t 1
    end.

    Definition r (reg: reg_t) : R reg :=
      match reg with
      | tf_cmd => Bits.zero
      | tf_cmd_ack => Bits.zero
      | tf_ready => Bits.of_nat 1 1
      | tf_reg x => spec_states_init x
      | tf_in x => Bits.zero
      | tf_out x => Bits.zero
      | tf_out_ack x => Bits.zero
      end.

    (* ====== External Functions ====== *)

    Local Notation spec_externs := (tfs_spec_externs (tfs_ctx (tf_sched_ctx tf_ctx))).
    Local Notation spec_externs_sig := (tfs_spec_externs_sig (tfs_ctx (tf_sched_ctx tf_ctx))).
    Local Notation spec_externs_fin := (tfs_spec_externs_fin (tfs_ctx (tf_sched_ctx tf_ctx))).
    Local Notation spec_externs_arg := (@tfe_arg_size _ spec_externs_sig).
    Local Notation spec_externs_res := (@tfe_res_size _ spec_externs_sig).
    Local Notation spec_all_externs := (@finite_elements spec_externs spec_externs_fin).
    Local Notation spec_ext_arg := (tfs_ext_arg (tf_sched_ctx tf_ctx)).
    Local Notation spec_ext_res := (tfs_ext_res (tf_sched_ctx tf_ctx)).

    Hint Extern 0 (FiniteType spec_externs) => exact spec_externs_fin : typeclass_instances.
    Hint Extern 0 (tf_externs spec_externs) => exact spec_externs_sig : typeclass_instances.
    Hint Extern 0 (Show spec_externs) =>
      exact (tfs_spec_externs_names (tfs_ctx (tf_sched_ctx tf_ctx))) : typeclass_instances.

    Local Notation ext_fn_t := (@_ext_fn_t spec_inputs spec_outputs spec_externs).

    Definition Sigma (fn: ext_fn_t) : ExternalSignature :=
      match fn with
      | ext_in_cmd => {$ bits_t 1 ~> maybe (bits_t spec_action_reg_size) $}
      | ext_input x => {$ bits_t 1 ~> spec_inputs_t x $}
      | ext_output x => {$ spec_outputs_t x ~> bits_t 1 $}
      | ext_call f => {$ bits_t (spec_externs_arg f) ~> bits_t (spec_externs_res f) $}
      end.

    (* The "ext_" prefix is what separates the trusted function wires from the normal
       module I/O in the generated Verilog. *)
    Definition ext_fn_specs (fn : ext_fn_t) := 
      match fn with
      | ext_in_cmd => {| efr_name := "in_cmd"; 
                        efr_internal := false |}
      | ext_input x => {| efr_name := String.append "in_param_" (show x); 
                          efr_internal := false |}
      | ext_output x => {| efr_name := String.append "out_param_" (show x); 
                           efr_internal := false |}
      | ext_call f => {| efr_name := String.append "ext_" (show f);
                         efr_internal := false |}
      end.

    Instance ext_fn_names : Show ext_fn_t :=
      { show := fun r => match r with
          | ext_in_cmd => "in_cmd"
          | ext_input x => String.append "in_param_" (show x)
          | ext_output x => String.append "out_param_" (show x)
          | ext_call f => String.append "ext_" (show f)
          end
      }.
    
    (* ====== Rules ====== *)

    Local Notation rule_name_t := (@_rule_name_t spec_outputs spec_action).

    Instance rule_names : Show rule_name_t :=
      { show := fun r => match r with
          | rule_cmd cmd => String.append "rule_cmd_" (show cmd)
          | rule_out out => String.append "rule_out_" (show out)
          | rule_ext => "rule_ext"
          | rule_busy => "rule_busy"
          end
      }.

    Definition system_schedule_outputs : scheduler := 
      List.fold_right (fun t acc => @rule_out spec_outputs spec_action t |> acc) Done spec_all_outputs.

    (* [rule_ext] runs *after* every action rule: it reads the argument registers at P1
       (the value the action just wrote) and writes the result registers at P0. Koika
       admits no ordering in which both hops are P0 (campaign extern-calls-mvp, D8). *)
    Definition system_schedule_ext : scheduler :=
      @rule_ext spec_outputs spec_action |> system_schedule_outputs.

    Definition system_schedule_actions : scheduler  :=
      List.fold_right (fun t acc => @rule_cmd spec_outputs spec_action t |> acc) system_schedule_ext spec_all_actions.

    Definition system_schedule := rule_busy |> system_schedule_actions.
    
    Local Notation action := (action R Sigma).

    Definition synth_convert {sig in_var_size} (out_var_size : nat)
      (code : action sig (bits_t in_var_size))
      : action sig (bits_t out_var_size) :=
      match eq_dec in_var_size out_var_size with
      | left e => eq_rect in_var_size (fun sz => action sig (bits_t sz)) code out_var_size e
      | right n => (Unop (PrimTyped.Bits1 (PrimTyped.Slice in_var_size 0 out_var_size)) code)
      end.

    Fixpoint expr_to_action {sig} (e: tf_expr) (target_size: nat) 
      : action sig (bits_t target_size) :=
      match e with
      | tf_const value =>
          Const (tau:=bits_t target_size) (Bits.of_nat target_size value)
          
      | tf_svar v =>
          let act := Read P0 (tf_reg v) in
          synth_convert target_size act
          
      | tf_ivar v =>
          let act := Read P1 (tf_in v) in
          synth_convert target_size act
          
      | tf_ovar v =>
          let act := Read P0 (tf_out v) in
          synth_convert target_size act
          
      | tf_op1 op src =>
          match op with
          | tf_not =>
            let src_act := expr_to_action src target_size in
            Unop (PrimTyped.Bits1 (PrimTyped.Not target_size)) src_act
          | tf_resize source_size =>
            synth_convert target_size (expr_to_action src source_size)
          end
          
      | tf_op2 op src1 src2 =>
          match op with
          | tf_and => 
              Binop (PrimTyped.Bits2 (PrimTyped.And target_size)) 
                    (expr_to_action src1 target_size) 
                    (expr_to_action src2 target_size)
          | tf_or => 
              Binop (PrimTyped.Bits2 (PrimTyped.Or target_size)) 
                    (expr_to_action src1 target_size) 
                    (expr_to_action src2 target_size)
          | tf_xor => 
              Binop (PrimTyped.Bits2 (PrimTyped.Xor target_size)) 
                    (expr_to_action src1 target_size) 
                    (expr_to_action src2 target_size)
          | tf_add => 
              Binop (PrimTyped.Bits2 (PrimTyped.Plus target_size)) 
                    (expr_to_action src1 target_size) 
                    (expr_to_action src2 target_size)
          | tf_sub => 
              Binop (PrimTyped.Bits2 (PrimTyped.Minus target_size)) 
                    (expr_to_action src1 target_size) 
                    (expr_to_action src2 target_size)
                    
          | tf_mul => 
              let act := Binop (PrimTyped.Bits2 (PrimTyped.Mul target_size target_size)) 
                              (expr_to_action src1 target_size) 
                              (expr_to_action src2 target_size) in
              synth_convert target_size act
              
          | tf_cmp cmp_sz cmp_op =>
              let s1 := expr_to_action src1 cmp_sz in
              let s2 := expr_to_action src2 cmp_sz in
              match cmp_op with
                | tf_eq => synth_convert target_size (in_var_size:=1) (Binop (PrimTyped.Bits2 (PrimTyped.EqBits cmp_sz false)) s1 s2)
                | tf_neq => synth_convert target_size (in_var_size:=1) (Binop (PrimTyped.Bits2 (PrimTyped.EqBits cmp_sz true)) s1 s2)
                | tf_lt => synth_convert target_size (in_var_size:=1) (Binop (PrimTyped.Bits2 (PrimTyped.Compare false cLt cmp_sz)) s1 s2)
                | tf_le => synth_convert target_size (in_var_size:=1) (Binop (PrimTyped.Bits2 (PrimTyped.Compare false cLe cmp_sz)) s1 s2)
                | tf_gt => synth_convert target_size (in_var_size:=1) (Binop (PrimTyped.Bits2 (PrimTyped.Compare false cGt cmp_sz)) s1 s2)
                | tf_ge => synth_convert target_size (in_var_size:=1) (Binop (PrimTyped.Bits2 (PrimTyped.Compare false cGe cmp_sz)) s1 s2)
              end
          end
          
      | tf_expr_if cond then_expr else_expr =>
          If (expr_to_action cond 1)
            (expr_to_action then_expr target_size)
            (expr_to_action else_expr target_size)

      | tf_ext f arg =>
          synth_convert target_size
            (ExternalCall (ext_call f) (expr_to_action arg (spec_externs_arg f)))
      end.

    Definition op_to_action {sig tau} (op: tf_op) (code: action sig tau) : action sig tau :=
      match op with
      | tf_nop => 
          code
      | tf_assign x expr => 
          Seq (Write P0 (tf_reg x) (expr_to_action expr (spec_states_size x))) code
      | tf_output x expr => 
          Seq (Write P0 (tf_out x) (expr_to_action expr (spec_outputs_size x))) code
      end.

    Fixpoint rule_aux {sig tau}
      (rule_ops: list tf_op)
      (code: action sig tau)
      : action sig tau :=
      match rule_ops with
      | [] => code
      | op :: ops => op_to_action op (rule_aux ops code)
      end.    

    Fixpoint rule_reset_buffers {sig tau} (regs: list spec_states)
      (code: action sig tau) : action sig tau :=
      match regs with
      | [] => code
      | r :: rs => Seq (Write P1 (tf_reg r) (Const (tau:=R (tf_reg r)) Bits.zero)) (rule_reset_buffers rs code)
      end.

    (* One [ExternalCall] per function, in a rule of its own, so the emitted Verilog has
       a single driver per port no matter how many call sites the actions contain.
       [Read P1] picks up the argument the action rule just wrote; [Write P0] means the
       action reads the *previous* cycle's result, i.e. both ends of the port pair are
       registered. *)
    Fixpoint rule_ext_calls {sig} (fs: list spec_externs)
      (code: action sig unit_t) : action sig unit_t :=
      match fs with
      | [] => code
      | f :: rest =>
          Seq (Write P0 (tf_reg (spec_ext_res f))
                 (synth_convert (in_var_size := spec_externs_res f)
                    (spec_states_size (spec_ext_res f))
                    (ExternalCall (ext_call f)
                       (synth_convert (in_var_size := spec_states_size (spec_ext_arg f))
                          (spec_externs_arg f)
                          (Read P1 (tf_reg (spec_ext_arg f)))))))
              (rule_ext_calls rest code)
      end.

    Definition _rule_cmd {sig} (cmd: spec_action)
      : action sig unit_t :=
      (* Bound once: [spec_schedule] runs the whole scheduler. *)
      let sched_ops := spec_schedule cmd in
      let always_ops := fst sched_ops in
      let done_ops := snd sched_ops in
      rule_aux always_ops (
        If (tau:=unit_t) (synth_convert 1 (Read P1 (tf_reg spec_done_state)))
          (
            rule_aux done_ops (
              rule_reset_buffers spec_reset_states (
                Write P1 (tf_ready) (Const (tau:=bits_t 1) Ob~1)
              )
            )
          )
          (
            Const (tau:=unit_t) (vect_nil)
          )
        )
      .

    Definition Guard {sig} (cond: action sig (bits_t 1)) : action sig unit_t :=
      If cond (Const (tau:=unit_t) (vect_nil)) (Fail unit_t).

    Program Definition write_input_step {sig} (r : spec_inputs) : action sig (spec_inputs_t r) :=
      ExternalCall (ext_input r) (Const (tau:=bits_t 1) Ob~1).
    
    Fixpoint rule_buffer_inputs {sig tau} (regs: list spec_inputs)
      (code: action sig tau) : action sig tau :=
      match regs with
      | [] => code
      | r :: rs => 
          Seq 
            (Write P0 (tf_in r) (write_input_step r)) 
            (rule_buffer_inputs rs code)
      end.

    Program Definition rule_cmd_guard {sig} (cmd: spec_action) 
      : action sig unit_t :=
      let cmd_enc := spec_action_encoding cmd in
      
      If (Read P0 tf_ready)
        (
          let valid_bit := Unop (R:=R) (PrimTyped.Struct1 PrimTyped.GetField (Maybe (bits_t spec_action_reg_size)) thisone) (ExternalCall ext_in_cmd (Read P0 tf_ready)) in
          let data_val := Unop (R:=R) (PrimTyped.Struct1 PrimTyped.GetField (Maybe (bits_t spec_action_reg_size)) (anotherone thisone)) (ExternalCall ext_in_cmd (Read P0 tf_ready)) in
          
          Seq (Guard valid_bit) (
            Seq (Guard (Binop (PrimTyped.Bits2 (PrimTyped.EqBits spec_action_reg_size false)) data_val (Const cmd_enc))) (
              rule_buffer_inputs spec_all_inputs (
                Seq (Write P0 tf_cmd (Const cmd_enc)) (
                  Write P0 tf_ready (Const (tau:=bits_t 1) Ob~0)
                )
              )
            )
          )
        )
        (
          Guard (Binop (PrimTyped.Bits2 (PrimTyped.EqBits spec_action_reg_size false)) (Read P0 tf_cmd) (Const cmd_enc))
        ).

    Program Definition rules {sig} (rl: rule_name_t) : action sig unit_t :=
      match rl with
      | rule_busy =>
          If (Read P0 tf_ready)
          ( (Fail unit_t) )
          (
            let valid_bit := Unop (R:=R) (PrimTyped.Struct1 PrimTyped.GetField (Maybe (bits_t spec_action_reg_size)) thisone) (ExternalCall ext_in_cmd (Read P0 tf_ready)) in
            Write P0 tf_cmd_ack valid_bit
          )
      | rule_cmd cmd => 
            Seq (rule_cmd_guard cmd) (_rule_cmd cmd)
      | rule_ext =>
            rule_ext_calls spec_all_externs (Const (tau:=unit_t) (vect_nil))
      | rule_out out =>
            Write P1 (tf_out_ack out) (ExternalCall (ext_output out) (Read P1 (tf_out out)))
      end.

End TypedSynthesis.

(* ====== Graded-opacity policy (campaign: synthesis-usability, Phase 1) ======
   These definitions build large dependently-typed Koika terms. We forbid
   *implicit* reduction (simpl/cbn) so proofs don't blow up, while still allowing
   *explicit* reduction (unfold / cbv [..] / change) at the leaves where Koika
   typing requires it (e.g. R (tf_reg x) = bits_t ...). Behavior-preserving. *)
Arguments _reg_t_finite _ : simpl never.
Arguments system_schedule _ : simpl never.
Arguments Sigma _ _ : simpl never.
Arguments r _ _ : simpl never.
(* NOTE: `Arguments R _ _ : simpl never` is intentionally NOT enabled yet.
   It breaks proofs that rely on `simpl` reducing R (e.g. Synthesis.v ~1773).
   Enable it in Phase 3 together with rewriting those sites via the R_* lemmas
   below (R hardening is entangled with the proof scripts). *)

(* Per-branch rewrite lemmas for R. Once `R` is `simpl never`, proofs use these to
   reduce R at the leaves where Koika typing needs a concrete `bits_t`, instead of
   relying on `simpl`/`cbn` unfolding all of R. *)
Section R_branches.
  Context (tf_ctx: TFSynthContext).
  Local Notation sctx := (tf_sched_ctx tf_ctx).

  Lemma R_tf_reg : forall x,
    R tf_ctx (tf_reg x) = bits_t (tfs_states_size sctx x).
  Proof. reflexivity. Qed.

  Lemma R_tf_in : forall x,
    R tf_ctx (tf_in x) = bits_t (tfs_inputs_size sctx x).
  Proof. reflexivity. Qed.

  Lemma R_tf_out : forall x,
    R tf_ctx (tf_out x) = bits_t (tfs_outputs_size sctx x).
  Proof. reflexivity. Qed.

  Lemma R_tf_cmd : R tf_ctx tf_cmd = bits_t (tf_action_reg_size tf_ctx).
  Proof. reflexivity. Qed.

  Lemma R_tf_ready : R tf_ctx tf_ready = bits_t 1.
  Proof. reflexivity. Qed.

  Lemma R_tf_cmd_ack : R tf_ctx tf_cmd_ack = bits_t 1.
  Proof. reflexivity. Qed.

  Lemma R_tf_out_ack : forall x, R tf_ctx (tf_out_ack x) = bits_t 1.
  Proof. reflexivity. Qed.
End R_branches.


