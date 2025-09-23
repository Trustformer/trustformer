Require Import Koika.Frontend.
Require Import Koika.Std.
Require Export Koika.Utils.Common.
Require Export Koika.Utils.Environments.
Require Import Streams.
Require Import Coq.Logic.Eqdep_dec.
Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.
Hammer_version.

Module TestDesign.

  Section Operations.
    
    Inductive fs_ops {in_t : Type} {state_t: Type} :=
    | fs_neg 
    | fs_load_in (src : in_t)
    | fs_load_st (src : state_t)
    | fs_nop.

  End Operations.

  Section FSpec.

    Definition sz := 32.
    Definition bits_false := Bits.of_nat sz 0.
    Definition bits_true := Bits.neg (bits_false).

    Inductive fs_action_t :=
    | fs_act_run
    | fs_act_nop
    .
    Lemma fs_action_t_eq_dec : forall a1 a2 : fs_action_t, {a1 = a2} + {a1 <> a2}.
    Proof. sauto. Qed.
    Definition all_fs_actions : list fs_action_t := [fs_act_run; fs_act_nop].
    Lemma all_fs_actions_complete : forall a : fs_action_t, In a all_fs_actions.
    Proof. sauto. Qed.
    Definition fs_action_encoding (a: fs_action_t) : bits_t sz :=
    match a with
    | fs_act_run => Bits.of_nat sz 1
    | fs_act_nop => Bits.of_nat sz 0
    end.
    
    Inductive fs_inputs_var :=
    .
    Lemma fs_inputs_var_eq_dec : forall x1 x2 : fs_inputs_var, {x1 = x2} + {x1 <> x2}.
    Proof. decide equality. Qed.
    Definition all_fs_inputs : list fs_inputs_var := [].
    Lemma all_fs_inputs_complete : forall x : fs_inputs_var, In x all_fs_inputs.
    Proof. intros x. destruct x; simpl; auto. Qed.
    Definition fs_inputs_type (x: fs_inputs_var) : type :=
    match x with
    end.
    Definition fs_inputs_init (x: fs_inputs_var) : (fs_inputs_type x) :=
    match x with
    end.

    Inductive fs_outputs_var := 
    | fs_out_val
    .
    Lemma fs_outputs_var_eq_dec : forall x1 x2 : fs_outputs_var, {x1 = x2} + {x1 <> x2}.
    Proof. decide equality. Qed.
    Definition all_fs_outputs : list fs_outputs_var := [fs_out_val].
    Lemma all_fs_outputs_complete : forall x : fs_outputs_var, In x all_fs_outputs.
    Proof. intros x. destruct x; simpl; auto. Qed.
    Definition fs_outputs_type (x: fs_outputs_var) : type :=
    match x with
    | fs_out_val => bits_t sz
    end.
    Definition fs_outputs_init (x: fs_outputs_var) : (fs_outputs_type x) :=
    match x with
    | fs_out_val => Bits.zero
    end.    

    Inductive fs_states_var :=
    | fs_st_val
    .
    Lemma fs_states_var_eq_dec : forall x1 x2 : fs_states_var, {x1 = x2} + {x1 <> x2}.
    Proof. decide equality. Qed.
    Definition all_fs_states : list fs_states_var := [fs_st_val].
    Lemma all_fs_states_complete : forall x : fs_states_var, In x all_fs_states.
    Proof. intros x. destruct x; simpl; auto. Qed.
    Definition fs_states_type (x: fs_states_var) : type :=
    match x with
    | fs_st_val => bits_t sz
    end.
    Definition fs_states_init (x: fs_states_var) : (fs_states_type x) :=
    match x with
    | fs_st_val => Bits.zero
    end.
    
    Definition fs_transitions
      (act: fs_action_t)
      :
      (forall x : fs_states_var, list (@fs_ops fs_inputs_var fs_states_var) ) 
      * 
      (forall x : fs_outputs_var, list (@fs_ops fs_inputs_var fs_states_var) )
      :=
      match act with
      | fs_act_run =>
          (
            fun x =>
              match x with
              | fs_st_val => [fs_neg]
              end,
            fun x => 
              match x with
              | fs_out_val => [fs_load_st fs_st_val]
              end
          )
      | fs_act_nop =>
          (fun x => [], fun x => [])
      end.

      Definition _fs_single_state_step
        (input: (forall x : fs_inputs_var, fs_inputs_type x))
        (state: (forall x : fs_states_var, fs_states_type x))
        (state_op: forall x : fs_states_var, @fs_ops fs_inputs_var fs_states_var )
        : 
        (forall x : fs_states_var, fs_states_type x) :=
        fun s =>
          let op := state_op s in
          match op with
          | fs_neg => value_of_bits (Bits.neg (bits_of_value (state s)))
          | fs_load_in src => 
              match eq_dec (fs_inputs_type src) (fs_states_type s) with
              | left e => eq_rect _ type_denote (input src) _ e
              | right _ => state s
              end
          | fs_load_st src => match eq_dec (fs_states_type src) (fs_states_type s) with
              | left e => eq_rect _ type_denote (state src) _ e
              | right _ => state s
              end
          | fs_nop => state s
          end.
      
      Definition fs_single_output_step
        (input: (forall x : fs_inputs_var, fs_inputs_type x))
        (state: (forall x : fs_states_var, fs_states_type x))
        (output: (forall x : fs_outputs_var, fs_outputs_type x))
        (output_op: forall x : fs_outputs_var, @fs_ops fs_inputs_var fs_states_var )
        : 
        (forall x : fs_outputs_var, fs_outputs_type x) :=
        fun s =>
          let op := output_op s in
          match op with
          | fs_neg => value_of_bits (Bits.neg (bits_of_value (output s)))
          | fs_load_in src => 
              match eq_dec (fs_inputs_type src) (fs_outputs_type s) with
              | left e => eq_rect _ type_denote (input src) _ e
              | right _ => output s
              end
          | fs_load_st src => match eq_dec (fs_states_type src) (fs_outputs_type s) with
              | left e => eq_rect _ type_denote (state src) _ e
              | right _ => output s
              end
          | fs_nop => output s
          end.

      Definition get_state_ops_max_length
        (state_ops: (forall x : fs_states_var, list (@fs_ops fs_inputs_var fs_states_var) ))
        : nat :=
        List.fold_right (fun x acc => max acc (List.length (state_ops x))) 0 all_fs_states.
      Definition get_output_ops_max_length
        (output_ops: (forall x : fs_outputs_var, list (@fs_ops fs_inputs_var fs_states_var) ))
        : nat :=
        List.fold_right (fun x acc => max acc (List.length (output_ops x))) 0 all_fs_outputs.
      Definition get_ops_max_length
        (state_ops: (forall x : fs_states_var, list (@fs_ops fs_inputs_var fs_states_var) ))
        (output_ops: (forall x : fs_outputs_var, list (@fs_ops fs_inputs_var fs_states_var) ))
        : nat :=
        max (get_state_ops_max_length state_ops) (get_output_ops_max_length output_ops).

      Fixpoint _fs_step_aux 
        (idx_rev : nat)
        (maxN : nat)
        (input: (forall x : fs_inputs_var, fs_inputs_type x))
        (state: (forall x : fs_states_var, fs_states_type x))
        (output: (forall x : fs_outputs_var, fs_outputs_type x))
        (state_ops: (forall x : fs_states_var, list (@fs_ops fs_inputs_var fs_states_var) ))
        (output_ops: (forall x : fs_outputs_var, list (@fs_ops fs_inputs_var fs_states_var) ))
        : 
        (forall x : fs_states_var, fs_states_type x) *
        (forall x : fs_outputs_var, fs_outputs_type x) :=
      
      match idx_rev with
      | 0 => (state, output)
      | S idx_rev' => 
        let idx := maxN - idx_rev in
        let new_state := 
          fun x => _fs_single_state_step input state (fun y => List.nth idx (state_ops y) (fs_nop)) x in
        let new_output := 
          fun x => fs_single_output_step input new_state output (fun y => List.nth idx (output_ops y) (fs_nop)) x in
        _fs_step_aux idx_rev' maxN input new_state new_output state_ops output_ops
      end.

      Definition fs_step 
        (input: (forall x : fs_inputs_var, fs_inputs_type x))
        (state: (forall x : fs_states_var, fs_states_type x))
        (output: (forall x : fs_outputs_var, fs_outputs_type x))
        (state_ops: (forall x : fs_states_var, list (@fs_ops fs_inputs_var fs_states_var) ))
        (output_ops: (forall x : fs_outputs_var, list (@fs_ops fs_inputs_var fs_states_var) ))
        : 
        (forall x : fs_states_var, fs_states_type x) *
        (forall x : fs_outputs_var, fs_outputs_type x) :=
        let maxN := get_ops_max_length state_ops output_ops in
        _fs_step_aux maxN maxN input state output state_ops output_ops.

    Section Examples.
      Definition in_init := fun x => fs_inputs_init x.
      Definition s_init := (fun x => fs_states_init x).
      Definition out_init := (fun x => fs_outputs_init x).

      Definition s1_trans := fs_transitions fs_act_run.
      Definition s1 := (fs_step in_init s_init out_init (fst s1_trans) (snd s1_trans)).
      Definition s1_state := (fst s1).
      Definition s1_output := (snd s1).
      
      Example s_example : s_init fs_st_val = bits_false.
      Proof. reflexivity. Qed.
      Example s1_example : s1_state fs_st_val = bits_true.
      Proof. ssimpl. Qed.

      Example s_out_example : out_init fs_out_val = bits_false.
      Proof. ssimpl. Qed.
      Example s1_out_example : s1_output fs_out_val = bits_true.
      Proof. ssimpl. Qed.    
    End Examples.
  End FSpec.


  Section Emulator.

    (* Inductive emu_state *)

    (* *)

  End Emulator.


  (* =============================================================================== *)
  (* The stuff starting from here should not require changes when changing the above *)
  (* =============================================================================== *)


  Inductive reg_t := 
  | in_reg (x : fs_inputs_var)
  | st_reg (x : fs_states_var)
  | out_reg (x : fs_outputs_var)
  | ack_reg (x : fs_outputs_var).

  Definition R (r: reg_t) :=
  match r with
  | in_reg x => fs_inputs_type x
  | st_reg x => fs_states_type x
  | out_reg x => fs_outputs_type x
  | ack_reg x => bits_t 1
  end.

  Definition r (reg: reg_t) : R reg :=
    match reg with
    | in_reg x => fs_inputs_init x
    | st_reg x => fs_states_init x
    | out_reg x => fs_outputs_init x
    | ack_reg x => Bits.zero
    end.

  Inductive ext_fn_t := 
  | ext_in_cmd
  | ext_in (x: fs_inputs_var) 
  | ext_out (x: fs_outputs_var).

  Definition Sigma (fn: ext_fn_t) :=
    match fn with
    | ext_in_cmd => {$ bits_t 1 ~> maybe (bits_t sz) $}
    | ext_in x => {$ bits_t 1 ~> maybe (fs_inputs_type x) $}
    | ext_out x => {$ fs_outputs_type x ~> bits_t 1 $}
    end.

  Definition ext_fn_specs (fn : ext_fn_t) := 
    match fn with
    | ext_in_cmd => {| efr_name := "in_cmd"; 
                       efr_internal := false |}
    | ext_in x => {| efr_name := "in_" ++ show x;
                    efr_internal := false |}
    | ext_out x => {| efr_name := "out_" ++ show x;
                     efr_internal := false |}
    end.
  
  Inductive rule_name_t :=
  | rule_cmd (cmd: fs_action_t)
  | rule_in (x: fs_inputs_var)
  | rule_out (x: fs_outputs_var)
  .

  Definition system_schedule_out : scheduler :=
    List.fold_right (fun t acc => rule_out t |> acc) Done all_fs_outputs.
  Definition system_schedule_cmds : scheduler :=
    List.fold_right (fun t acc => rule_cmd t |> acc) system_schedule_out all_fs_actions.
  Definition system_schedule_in : scheduler :=
    List.fold_right (fun t acc => rule_in t |> acc) system_schedule_cmds all_fs_inputs.
  Definition system_schedule := system_schedule_in.
  Eval compute in system_schedule.

  Definition _rule_in x : uaction reg_t ext_fn_t :=
    {{ 
      let tmp := extcall (ext_in x)(Ob~1) in
      guard(get(tmp, valid));
      write0(in_reg x, get(tmp, data))
    }}.
  
  Definition _rule_out x : uaction reg_t ext_fn_t :=
    {{ 
      write1(ack_reg x, extcall (ext_out x)(read1(out_reg x)))
    }}.
  
  Definition op_to_uaction (reg: string) (op: @fs_ops fs_inputs_var fs_states_var) (code: uaction reg_t ext_fn_t) : uaction reg_t ext_fn_t :=
    match op with
    | fs_neg => UBind reg (UUnop (UBits1 UNot) (UVar reg)) code
    | fs_load_in src => UBind reg {{read1(in_reg src)}} code
    | fs_load_st src => UBind reg (UVar (show src)) code
    | fs_nop => code
    end.

  Fixpoint _rule_aux
    (currentN : nat)
    (state_ops: (forall x : fs_states_var, list (@fs_ops fs_inputs_var fs_states_var) ))
    (output_ops: (forall x : fs_outputs_var, list (@fs_ops fs_inputs_var fs_states_var) ))
    (code: uaction reg_t ext_fn_t)
    : uaction reg_t ext_fn_t :=
    match currentN with
      | 0 => code
      | S idx =>
        let state_op := fun y => List.nth idx (state_ops y) (fs_nop) in
        let output_op := fun y => List.nth idx (output_ops y) (fs_nop) in
        let state_op_tuples := List.map (fun x => (x, state_op x)) all_fs_states in
        let output_op_tuples := List.map (fun x => (x, output_op x)) all_fs_outputs in
        let output_code := List.fold_right (fun '(x, op) acc => op_to_uaction (show x) op acc) code output_op_tuples in
        let state_code := List.fold_right (fun '(x, op) acc => op_to_uaction (show x) op acc) output_code state_op_tuples in
        _rule_aux idx state_ops output_ops state_code
      end.

  Definition _rule_write_output_ops (output_ops: (forall x : fs_outputs_var, list (@fs_ops fs_inputs_var fs_states_var) )) (code: uaction reg_t ext_fn_t) : uaction reg_t ext_fn_t  := 
    List.fold_right (fun x acc => 
      let ops := output_ops x in
      let ops := List.filter (fun op => match op with fs_nop => false | _ => true end) ops in
      match ops with
      | [] => acc
      | _ => USeq {{write0(out_reg x, `UVar (show x)`)}} acc
      end
    ) code all_fs_outputs.

  Definition _rule_read_state_ops (state_ops: (forall x : fs_states_var, list (@fs_ops fs_inputs_var fs_states_var) )) (code: uaction reg_t ext_fn_t) : uaction reg_t ext_fn_t  := 
    List.fold_right (fun x acc => 
      let ops := state_ops x in
      let ops := List.filter (fun op => match op with fs_nop => false | _ => true end) ops in
      match ops with
      | [] => acc
      | _ => UBind (show x) {{ read0(st_reg x) }} acc
      end
    ) code all_fs_states.
  
  Definition _rule_write_state_ops (state_ops: (forall x : fs_states_var, list (@fs_ops fs_inputs_var fs_states_var) )) (code: uaction reg_t ext_fn_t) : uaction reg_t ext_fn_t  := 
    List.fold_right (fun x acc => 
      let ops := state_ops x in
      let ops := List.filter (fun op => match op with fs_nop => false | _ => true end) ops in
      match ops with
      | [] => acc
      | _ => USeq {{ write0(st_reg x, `UVar (show x)`) }} acc
      end
    ) code all_fs_states.

  Definition _rule_cmd cmd : uaction reg_t ext_fn_t :=
    let (state_ops, output_ops) := fs_transitions cmd in
    let maxN := get_ops_max_length state_ops output_ops in
    _rule_read_state_ops state_ops (_rule_aux maxN state_ops output_ops (_rule_write_state_ops state_ops (_rule_write_output_ops output_ops {{ pass }}))).

  Eval compute in _rule_cmd fs_act_nop.
  Eval compute in _rule_cmd fs_act_run.

  Definition rules :=
    tc_rules R Sigma
      (fun rl =>  match rl with
        | rule_cmd cmd => 
          let cmd_enc := fs_action_encoding cmd in
          {{
                let in_cmd := extcall ext_in_cmd(Ob~1) in
                guard(get(in_cmd, valid) && get(in_cmd, data) == #cmd_enc);
                `_rule_cmd cmd`
          }} 
        | rule_in x => _rule_in x
        | rule_out x => _rule_out x
        end).

  Definition package :=
    {| ip_koika := {| koika_reg_types := R;
                      koika_reg_init := r;
                      koika_ext_fn_types := Sigma;
                      koika_rules := rules;
                      koika_rule_external := (fun _ => false);
                      koika_scheduler := system_schedule;
                      koika_module_name := "TestDesign" |};

    ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn; efs_method := false |};
                 sp_prelude := None |};

    ip_verilog := {| vp_ext_fn_specs := ext_fn_specs |} |}.
  
  Section Correctness.
    (* TODO generalize: each cycle could be a different omega *)
    Context (σ: forall f, Sig_denote (Sigma f)).

    Arguments id _ _ / : assert.
    Arguments env_t: simpl never.
    Arguments vect: simpl never.
    Arguments may_read /.
    Arguments may_write /.
    (* Opaque TypedSemantics.interp_cycle. *)

    Section Spec1.

      Definition next_hw_cycle (hw_reg_state: ContextEnv.(env_t) R) := 
          TypedSemantics.interp_cycle σ rules system_schedule hw_reg_state.
      
      Definition initial_hw_state : ContextEnv.(env_t) R := ContextEnv.(create) r.

      (* helpers for encoding the action/command *)
      Definition encoded_action (a: fs_action_t) : type_denote (maybe (bits_t sz)) :=
        (Ob~1, (fs_action_encoding a, tt)).
      Lemma retSig_eq_bits : retSig (Sigma ext_in_cmd) = maybe (bits_t sz).
      Proof. simpl. reflexivity. Qed.
      
      Definition StateR (hw_reg_state: ContextEnv.(env_t) R) (fs_state: (forall x : fs_states_var, fs_states_type x)) : Prop :=
        forall x, hw_reg_state.[st_reg x] = fs_state x.

      Definition OutputR (hw_reg_state: ContextEnv.(env_t) R) (fs_output: (forall x : fs_outputs_var, fs_outputs_type x)) : Prop :=
        forall x, hw_reg_state.[out_reg x] = fs_output x.

      Definition InputR (hw_reg_state: ContextEnv.(env_t) R) (fs_input: (forall x : fs_inputs_var, fs_inputs_type x)) : Prop :=
        forall x, hw_reg_state.[in_reg x] = fs_input x.
      
      Theorem InitState_correct :
        StateR initial_hw_state fs_states_init 
        /\ InputR initial_hw_state fs_inputs_init 
        /\ OutputR initial_hw_state fs_outputs_init.
      Proof.
        unfold initial_hw_state, fs_states_init, fs_inputs_init, fs_outputs_init. split.
        - intros x; sauto.
        - split. intros x; sauto.
          intros x; sauto.
      Qed.

      Theorem NextCycle_State_correct :
        forall cmd fs_state fs_input fs_output hw_reg_state, 
        (  σ ext_in_cmd (Ob~1) = encoded_action cmd
        /\ StateR hw_reg_state fs_state
        /\ InputR hw_reg_state fs_input
        /\ OutputR hw_reg_state fs_output
        ) ->
        StateR (next_hw_cycle hw_reg_state) (fst (fs_step fs_input fs_state fs_output (fst (fs_transitions cmd)) (snd (fs_transitions cmd)))).
      Proof.
        intros cmd fs_state fs_input fs_output hw_reg_state H.
        destruct H as [H_cmd [H_state [H_input H_output]]].
        intros state_var.
        unfold next_hw_cycle.
        unfold interp_cycle.
        (* vm_compute (system_schedule). *)
        (* vm_compute (rules). *)
        unfold commit_update.
        rewrite getenv_create.
        destruct (latest_write (interp_scheduler hw_reg_state σ rules system_schedule) (st_reg state_var)).
        - admit.
        - destruct cmd, state_var. 
          + admit.
          (* +  vm_compute (fst (fs_step fs_input fs_state fs_output (fst (fs_transitions fs_act  
        
        timeout 5 sauto.  
        unfold interp_scheduler.
        unfold interp_scheduler'.
        destruct.

        destruct cmd, state_var.
        - unfold interp_scheduler.
          unfold interp_scheduler'.
          unfold commit_update.
          rewrite getenv_create.

      Qed.


      Theorem NextCycle_State_correct :
        forall cmd fs_state fs_input fs_output hw_reg_state, 
        (  σ ext_in_cmd (Ob~1) = encoded_action cmd
        /\ StateR hw_reg_state fs_state
        /\ InputR hw_reg_state fs_input
        /\ OutputR hw_reg_state fs_output
        ) ->
        StateR (next_hw_cycle hw_reg_state) (fst (fs_step fs_input fs_state fs_output (fst (fs_transitions cmd)) (snd (fs_transitions cmd)))).
      Proof.
        intros cmd fs_state fs_input fs_output hw_reg_state H.
        destruct H as [H_cmd [H_state [H_input H_output]]].
        intros state_var.
        unfold next_hw_cycle.
        unfold interp_cycle.
        vm_compute (system_schedule).
        destruct cmd, state_var.
        - vm_compute (fst (fs_step fs_input fs_state fs_output (fst (fs_transitions fs_act_run)) (snd (fs_transitions fs_act_run))) fs_st_val).
          unfold interp_scheduler.
          unfold interp_scheduler'.
          unfold commit_update.
          rewrite getenv_create.
          unfold interp_rule.
          unfold interp_action. *)
      Admitted.

    End Spec1.
  End Correctness.
End TestDesign.

(* ==== Synthesis ==== *)
Definition prog := Interop.Backends.register TestDesign.package.
Set Extraction Output Directory "build".
Extraction "TestDesign.ml" prog.
