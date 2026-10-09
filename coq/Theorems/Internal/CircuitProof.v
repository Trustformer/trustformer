(*! The cycle-level proof behind IPR.v: cycle by cycle, the circuit idles at a ready
    cycle or runs the command it took there as the IR does, and an emulator that sees
    only the attacker's wires and the spec's answers keeps pace with it. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Backend.Lowering.
Require Export Trustformer.Theorems.IPRDefinitions.
Require Export Trustformer.Theorems.Internal.IRDefinitions.
Require Export Trustformer.Theorems.Internal.CircuitDefinitions.
Require Import Trustformer.Theorems.Internal.AttackerClock.
Require Trustformer.Declassification.Extract.
Require Trustformer.Theorems.Internal.IPRProof.
Require Trustformer.Theorems.Internal.SchedulerSimulationLemmas.
Require Trustformer.Theorems.Internal.SchedulerRoundTrip.
Require Trustformer.Theorems.Internal.SynthesisProof.
Require Import IPR.Common IPR.Machine IPR.Emulator IPR.Definition.

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

Section SpecInputs.

  Context {states_var: Type} {states_var_fin : FiniteType states_var}
          {inputs_var: Type} {inputs_var_fin : FiniteType inputs_var}
          {outputs_var: Type} {outputs_var_fin : FiniteType outputs_var}
          {ips_var: Type}
          (states_size : states_var -> nat) (inputs_size : inputs_var -> nat)
          (outputs_size : outputs_var -> nat) (ips : ips_var -> ip_decl).

  Local Notation input_t := (forall x : inputs_var, type_denote (tf_inputs_type inputs_size x)).

  (* The spec reads its inputs only by applying them, so equal values give equal runs. *)
  Lemma eval_expr_inputs_ext :
    forall (e: @tf_expr states_var inputs_var outputs_var) szB sys (i1 i2 : input_t),
      (forall x, i1 x = i2 x) ->
      tf_eval_expr states_size inputs_size outputs_size (szB := szB) e sys i1
      = tf_eval_expr states_size inputs_size outputs_size (szB := szB) e sys i2.
  Proof.
    induction e; intros szB sys i1 i2 H;
      repeat match goal with
             | o : tf_unary_ops |- _ => destruct o
             | o : tf_binary_ops |- _ => destruct o
             | o : tf_comparison_ops |- _ => destruct o
             end;
      simpl;
      repeat match goal with
             | IH : forall _ _ _ _, _ -> _ |- _ => rewrite (IH _ _ i1 i2 H)
             end;
      try rewrite H; reflexivity.
  Qed.

  Lemma ops_updates_inputs_ext :
    forall (ops: @tf_ops states_var inputs_var outputs_var ips_var) sys (i1 i2 : input_t),
      (forall x, i1 x = i2 x) ->
      tf_ops_updates states_size inputs_size outputs_size ips ops sys i1
      = tf_ops_updates states_size inputs_size outputs_size ips ops sys i2.
  Proof.
    induction ops as [op | ops1 IH1 ops2 IH2 | c t IHt f IHf]; intros sys i1 i2 H; simpl.
    - unfold tf_op_step_updates.
      destruct op; try reflexivity; rewrite (eval_expr_inputs_ext _ _ sys i1 i2 H); reflexivity.
    - rewrite (IH1 sys i1 i2 H).
      destruct (tf_ops_updates states_size inputs_size outputs_size ips ops1 sys i2) as [u1 s1].
      rewrite (IH2 s1 i1 i2 H). reflexivity.
    - rewrite (eval_expr_inputs_ext c 1 sys i1 i2 H).
      destruct (beq_dec _ _); [ apply IHf | apply IHt ]; exact H.
  Qed.

  Lemma ops_run_inputs_ext :
    forall (ops: @tf_ops states_var inputs_var outputs_var ips_var) sys (i1 i2 : input_t),
      (forall x, i1 x = i2 x) ->
      tf_ops_run states_size inputs_size outputs_size ips ops sys i1
      = tf_ops_run states_size inputs_size outputs_size ips ops sys i2.
  Proof.
    intros ops sys i1 i2 H. unfold tf_ops_run.
    rewrite (ops_updates_inputs_ext ops sys i1 i2 H). reflexivity.
  Qed.

End SpecInputs.

Section OneCommand.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation sched := (tfs_schedule ctx cost_limit).
  Local Notation s_sz := (tfs_spec_states_size ctx).
  Local Notation i_sz := (tfs_spec_inputs_size ctx).
  Local Notation o_sz := (tfs_spec_outputs_size ctx).
  Local Notation src_sys_state :=
    (ContextEnv.(env_t) (tf_states_type s_sz) * ContextEnv.(env_t) (tf_outputs_type o_sz))%type.
  Local Notation sched_sys_state :=
    (ContextEnv.(env_t) (tf_states_type (tfs_states_size sched))
     * ContextEnv.(env_t) (tf_outputs_type o_sz))%type.
  Local Notation input_t :=
    (forall x : tfs_spec_inputs ctx, type_denote (tf_inputs_type i_sz x)).
  Local Notation resp_val :=
    (forall p : tfs_ips sched, bits_t (ip_resp_sz (tfs_ip sched p))).
  Local Notation spec_run act sp input :=
    (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act)
       sp input).

  Local Notation run_n := (IRDefinitions.run_n ctx cost_limit).
  Local Notation done_set := (IRDefinitions.done_set ctx cost_limit).
  Local Notation start_rel := (IRDefinitions.start_rel ctx cost_limit).
  Local Notation ip_contract := (IRDefinitions.ip_contract ctx cost_limit).
  Local Notation first_done := (IRDefinitions.first_done ctx cost_limit).
  Local Notation emulate := (IRDefinitions.emulate ctx).
  Local Notation L_pub := (AttackerClock.L_pub ctx cost_limit).
  Local Notation observe := (AttackerClock.observe ctx).

  (* ONE COMMAND on the IR: done first on the cycle [L_pub] computes from the
     public view, with the outputs at [pre] until then and [post] on it. *)
  Lemma command_emulated (act: tfs_action sched)
      (sp0: src_sys_state) (ss0: sched_sys_state)
      (input: input_t) (resp: nat -> resp_val) :
    start_rel sp0 ss0 ->
    ip_contract act input resp ss0 ->
    let pre  := snd sp0 in
    let post := snd (spec_run act sp0 input) in
    let N    := L_pub act (observe input pre post) in
    first_done act input resp ss0 N
    /\ forall k, k <= N -> forall ov,
         (snd (run_n k act input resp ss0)).[ov] = emulate pre post N k ov.
  Proof.
    intros Hstart Hipc. cbv zeta.
    destruct (Extract.act_slot_exists ctx cost_limit act) as [a_idx Halign].
    rewrite <- (Extract.L_is_public ctx cost_limit act a_idx sp0 ss0 input resp
                  Halign Hstart Hipc _ (fun _ => eq_refl) (fun _ => eq_refl) (fun _ => eq_refl)).
    split.
    - exact (IPRProof.L_first_done ctx cost_limit act sp0 ss0 input resp Hstart).
    - exact (IPRProof.emulator_correct_L ctx cost_limit act sp0 ss0 input resp
               Hstart Hipc).
  Qed.

  (* The circuit reads the done flag as [done_set] does. *)
  Lemma not_done_beq (ss: sched_sys_state) :
    ~ done_set ss -> beq_dec (fst ss).[tfs_done_signal sched] Bits.zero = true.
  Proof.
    intro Hnd. apply beq_dec_iff.
    destruct (eq_dec ((fst ss).[tfs_done_signal sched]) Bits.zero) as [E | E];
      [ exact E | exfalso; exact (Hnd E) ].
  Qed.

  Lemma done_beq (ss: sched_sys_state) :
    done_set ss -> beq_dec (fst ss).[tfs_done_signal sched] Bits.zero = false.
  Proof.
    intro Hd.
    destruct (beq_dec (fst ss).[tfs_done_signal sched] Bits.zero) eqn:E;
      [| reflexivity ].
    exfalso. apply Hd. apply beq_dec_iff in E. exact E.
  Qed.

End OneCommand.


Section Model.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation sched := (tfs_schedule ctx cost_limit).
  Context (enc_sz: nat) (enc: tfs_action sched -> bits_t enc_sz)
          (enc_inj: forall a b, enc a = enc b -> a = b)
          (names: Show (tfs_action sched)).

  Local Notation synth := (synth ctx cost_limit enc_sz enc enc_inj names).
  Local Notation wires := (forall f, Sig_denote (Sigma synth f)).
  Local Notation s_sz := (tfs_spec_states_size ctx).
  Local Notation i_sz := (tfs_spec_inputs_size ctx).
  Local Notation o_sz := (tfs_spec_outputs_size ctx).
  Local Notation src_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation src_sys_state :=
    (ContextEnv.(env_t) (tf_states_type s_sz) * src_out_env)%type.
  Local Notation input_t :=
    (forall x : tfs_spec_inputs ctx, type_denote (tf_inputs_type i_sz x)).
  Local Notation command := (tfs_action sched * input_t)%type.
  Local Notation run act sp input :=
    (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act) sp input).
  Local Notation L_pub := (AttackerClock.L_pub ctx cost_limit).
  Local Notation pub_inputs := (forall v, option (type_denote (tf_inputs_type i_sz v))).

  (* [in_cmd]'s code, decoded as the circuit's guards compare it. *)
  Definition decode (code: bits_t enc_sz) : option (tfs_action sched) :=
    List.find (fun a => beq_dec (enc a) code) (@finite_elements _ (tfs_action_fin sched)).

  Lemma decode_some code a : decode code = Some a -> enc a = code.
  Proof. intro H. apply find_some in H. destruct H as [_ H]. apply beq_dec_iff in H. exact H. Qed.

  Lemma decode_none code : decode code = None -> forall a, enc a <> code.
  Proof.
    intros H a E.
    assert (Hin : In a (@finite_elements _ (tfs_action_fin sched)))
      by (apply nth_error_In with (finite_index a); apply finite_surjective).
    pose proof (find_none _ _ H a Hin) as Hn. cbv beta in Hn.
    rewrite E in Hn. assert (Hb : beq_dec code code = true) by (apply beq_dec_iff; reflexivity).
    rewrite Hb in Hn. discriminate.
  Qed.

  Lemma decode_enc a : decode (enc a) = Some a.
  Proof.
    destruct (decode (enc a)) as [a' |] eqn:D.
    - f_equal. apply enc_inj. exact (decode_some _ _ D).
    - exfalso. exact (decode_none _ D a eq_refl).
  Qed.

  Lemma bits1_single_true (b: bits_t 1) : Bits.single b = true -> b = Ob~1.
  Proof. destruct b as [x []]. cbn. intros ->. reflexivity. Qed.

  Lemma bits1_single_false (b: bits_t 1) : Bits.single b = false -> b = Ob~0.
  Proof. destruct b as [x []]. cbn. intros ->. reflexivity. Qed.

  (* The command a cycle's wires offer: a valid [in_cmd] naming an action. *)
  Definition cmd_of (w: wires) : option command :=
    let cmd := w ext_in_cmd Ob~1 in
    if Bits.single (fst cmd)
    then match decode (fst (snd cmd)) with
         | Some act => Some (act, port_inputs ctx cost_limit enc_sz enc enc_inj names w)
         | None => None
         end
    else None.

  Lemma cmd_of_some w act input :
    cmd_of w = Some (act, input) ->
    fst (w ext_in_cmd Ob~1) = Ob~1 /\ fst (snd (w ext_in_cmd Ob~1)) = enc act
    /\ input = port_inputs ctx cost_limit enc_sz enc enc_inj names w.
  Proof.
    unfold cmd_of. cbv zeta.
    destruct (Bits.single (fst (w ext_in_cmd Ob~1))) eqn:V; [| discriminate ].
    destruct (decode (fst (snd (w ext_in_cmd Ob~1)))) as [a |] eqn:D; [| discriminate ].
    intro H. inversion H; subst.
    split; [ exact (bits1_single_true _ V) | split; [ exact (eq_sym (decode_some _ _ D)) | reflexivity ] ].
  Qed.

  Lemma cmd_of_none w :
    cmd_of w = None ->
    forall a, fst (w ext_in_cmd Ob~1) = Ob~0 \/ fst (snd (w ext_in_cmd Ob~1)) <> enc a.
  Proof.
    unfold cmd_of. cbv zeta. intros H a.
    destruct (Bits.single (fst (w ext_in_cmd Ob~1))) eqn:V.
    - destruct (decode (fst (snd (w ext_in_cmd Ob~1)))) as [a' |] eqn:D; [ discriminate |].
      right. intro E. exact (decode_none _ D a (eq_sym E)).
    - left. exact (bits1_single_false _ V).
  Qed.

  (* The emulator over full outputs, which the cycle-level proof tracks: it shows
     [em_pre] for [em_left] more cycles, then [em_post]. *)
  Record em := { em_pre : src_out_env; em_post : src_out_env; em_left : nat }.

  Definition em_start (outs: src_out_env) : em :=
    {| em_pre := outs; em_post := outs; em_left := 0 |}.

  Definition em_ready (e: em) : bool := Nat.eqb (em_left e) 0.

  Definition em_shown (e: em) : src_out_env :=
    if em_ready e then em_post e else em_pre e.

  Definition em_tick (e: em) : em :=
    {| em_pre := em_pre e; em_post := em_post e; em_left := pred (em_left e) |}.

  Definition em_take (e: em) (act: tfs_action sched) (pin: pub_inputs)
      (post: src_out_env) : em :=
    {| em_pre := em_post e; em_post := post;
       em_left := pred (L_pub act {| seen_in := pin; seen_pre := mask_out ctx (em_post e);
                                     seen_post := mask_out ctx post |}) |}.

  (* The spec beside that emulator, taking each offered command when idle; [pv k]
     is the public inputs as the emulator reads them in cycle [k]. *)
  Fixpoint ideal_run (sp0: src_sys_state) (cmds: nat -> option command)
      (pv: nat -> pub_inputs) (n: nat) : src_sys_state * em :=
    match n with
    | 0 => (sp0, em_start (snd sp0))
    | S k =>
        let '(sp, e) := ideal_run sp0 cmds pv k in
        match cmds k with
        | Some (act, input) =>
            if em_ready e
            then let sp' := run act sp input in (sp', em_take e act (pv k) (snd sp'))
            else (sp, em_tick e)
        | None => (sp, em_tick e)
        end
    end.

End Model.

Arguments em_pre {ctx}. Arguments em_post {ctx}. Arguments em_left {ctx}.
Arguments em_start {ctx}. Arguments em_ready {ctx}. Arguments em_shown {ctx}. Arguments em_tick {ctx}.


Section Emulator.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation sched := (tfs_schedule ctx cost_limit).
  Context (enc_sz: nat) (enc: tfs_action sched -> bits_t enc_sz).

  Local Notation s_sz := (tfs_spec_states_size ctx).
  Local Notation i_sz := (tfs_spec_inputs_size ctx).
  Local Notation o_sz := (tfs_spec_outputs_size ctx).
  Local Notation src_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation src_sys_state :=
    (ContextEnv.(env_t) (tf_states_type s_sz) * src_out_env)%type.
  Local Notation input_t :=
    (forall x : tfs_spec_inputs ctx, type_denote (tf_inputs_type i_sz x)).
  Local Notation run act sp input :=
    (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act) sp input).
  Local Notation pub_inputs := (forall v, option (type_denote (tf_inputs_type i_sz v))).
  Local Notation pub_outputs := (forall o, option (type_denote (tf_outputs_type o_sz o))).
  Local Notation atk_in := (CircuitDefinitions.atk_in ctx enc_sz).
  Local Notation atk_out := (IPRDefinitions.atk_out ctx).
  Local Notation query := (IPRDefinitions.query ctx cost_limit).
  Local Notation L_pub := (AttackerClock.L_pub ctx cost_limit).

  (* The emulator's own state: the outputs it shows before and after the running
     command, and that command's cycles left. *)
  Definition pe_state : Type := (pub_outputs * pub_outputs * nat)%type.

  (* The command taken this cycle: a valid [in_cmd] naming an action, when idle. *)
  Definition pe_takes (a: atk_in) (x: pe_state) : option (tfs_action sched * pub_inputs) :=
    let '(valid, code, pin) := a in
    let '(_, _, rem) := x in
    if Nat.eqb rem 0 && Bits.single valid
    then match decode ctx cost_limit enc_sz enc code with
         | Some act => Some (act, pin)
         | None => None
         end
    else None.

  Definition pe_after (x: pe_state) (act: tfs_action sched) (pin: pub_inputs)
      (post': pub_outputs) : pe_state :=
    let '(_, post, _) := x in
    (post, post', pred (L_pub act {| seen_in := pin; seen_pre := post; seen_post := post' |})).

  Definition pe_tick (x: pe_state) : pe_state :=
    let '(pre, post, rem) := x in (pre, post, pred rem).

  Definition pe_shown (x: pe_state) : pub_outputs :=
    let '(pre, post, rem) := x in if Nat.eqb rem 0 then post else pre.

  Definition pe_ready (x: pe_state) : bits_t 1 :=
    let '(_, _, rem) := x in if Nat.eqb rem 0 then Ob~1 else Ob~0.

  (* ONE CYCLE OF THE EMULATOR in IPR's emulator language: it learns the outputs
     once, then calls the spec only to run a command it takes. *)
  Definition pe_step (a: atk_in) : eproc (option pe_state) query pub_outputs atk_out :=
    EBind EGet (fun st =>
    EBind (match st with
           | Some x => ERet x
           | None => EBind (ECall Peek) (fun o => ERet (o, o, 0))
           end) (fun x =>
    match pe_takes a x with
    | Some (act, pin) =>
        EBind (ECall (Run act pin)) (fun post' =>
        EBind (EPut (Some (pe_after x act pin post'))) (fun _ =>
        ERet (pe_ready x, pe_shown (pe_after x act pin post'))))
    | None =>
        EBind (EPut (Some (pe_tick x))) (fun _ => ERet (pe_ready x, pe_shown (pe_tick x)))
    end)).

  Definition the_emulator : emulator query pub_outputs atk_in atk_out :=
    {| estate := option pe_state; einit := None; estep := pe_step |}.

  Local Notation M2 src := (closed_spec ctx cost_limit src).

  (* What one emulator step does, beside the spec in state [(sp, seen)]. *)
  Lemma pe_step_exec (src: trusted_source ctx) (a: atk_in) (sp: src_sys_state)
      (seen: list src_out_env) (x: pe_state) (st: option pe_state) :
    (st = Some x \/ (st = None /\ x = (mask_out ctx (snd sp), mask_out ctx (snd sp), 0))) ->
    eexec (mux (M2 src)) _ (pe_step a) ((sp, seen), st)
      match pe_takes a x with
      | Some (act, pin) =>
          let seen' := seen ++ [snd sp] in
          let sp' := run act sp (fill ctx pin (src seen')) in
          let x' := pe_after x act pin (mask_out ctx (snd sp')) in
          Result (pe_ready x, pe_shown x') ((sp', seen'), Some x')
      | None => Result (pe_ready x, pe_shown (pe_tick x)) ((sp, seen), Some (pe_tick x))
      end.
  Proof.
    intro Hst. unfold pe_step.
    eapply EexecBind; [ apply EexecGet |]. cbv beta.
    eapply EexecBind with (v := x) (s' := ((sp, seen), st)).
    { destruct Hst as [-> | [-> ->]]; [ apply EexecRet |].
      eapply EexecBind.
      - apply EexecCall. refine (MuxStepR _ _ (M2 src) _ _ _ _ _).
        reflexivity.
      - apply EexecRet. }
    cbv beta.
    destruct (pe_takes a x) as [[act pin] |] eqn:T.
    - eapply EexecBind.
      + apply EexecCall. refine (MuxStepR _ _ (M2 src) _ _ _ _ _).
        reflexivity.
      + cbv beta. eapply EexecBind; [ apply EexecPut |]. cbv beta. apply EexecRet.
    - eapply EexecBind; [ apply EexecPut |]. cbv beta. apply EexecRet.
  Qed.

End Emulator.

Section CircuitProof.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation sched := (tfs_schedule ctx cost_limit).
  Context (enc_sz: nat) (enc: tfs_action sched -> bits_t enc_sz)
          (enc_inj: forall a b, enc a = enc b -> a = b)
          (names: Show (tfs_action sched)).

  Local Notation synth := (synth ctx cost_limit enc_sz enc enc_inj names).
  Local Notation tsched := (tf_sched_ctx synth).
  Local Notation reg_t :=
    (@_reg_t (tfs_states tsched) (tfs_inputs tsched) (tfs_outputs tsched) (tfs_ips tsched)).
  Hint Extern 0 (FiniteType reg_t) => exact (_reg_t_finite synth) : typeclass_instances.
  Local Notation wires := (forall f, Sig_denote (Sigma synth f)).

  Local Notation s_sz := (tfs_spec_states_size ctx).
  Local Notation i_sz := (tfs_spec_inputs_size ctx).
  Local Notation o_sz := (tfs_spec_outputs_size ctx).
  Local Notation src_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation src_sys_state :=
    (ContextEnv.(env_t) (tf_states_type s_sz) * src_out_env)%type.
  Local Notation sched_sys_state :=
    (ContextEnv.(env_t) (tf_states_type (tfs_states_size sched))
     * ContextEnv.(env_t) (tf_outputs_type o_sz))%type.
  Local Notation input_t :=
    (forall x : tfs_spec_inputs ctx, type_denote (tf_inputs_type i_sz x)).
  Local Notation resp_val :=
    (forall p : tfs_ips sched, bits_t (ip_resp_sz (tfs_ip sched p))).
  Local Notation command := (tfs_action sched * input_t)%type.
  Local Notation spec_run act sp input :=
    (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act) sp input).
  Local Notation circuit_state := (ContextEnv.(env_t) (R synth)).

  Local Notation pub_inputs := (forall v, option (type_denote (tf_inputs_type i_sz v))).

  Context (c0: circuit_state) (sp0: src_sys_state).
  Context (env: nat -> wires) (pv: nat -> pub_inputs).

  Local Notation circuit_run := (CircuitDefinitions.circuit_run ctx cost_limit enc_sz enc enc_inj names c0).
  Local Notation ip_contract := (CircuitDefinitions.ip_contract ctx cost_limit enc_sz enc enc_inj names c0).
  Local Notation cmds k := (cmd_of ctx cost_limit enc_sz enc enc_inj names (env k)).
  Local Notation ideal k :=
    (ideal_run ctx cost_limit sp0 (fun i => cmd_of ctx cost_limit enc_sz enc enc_inj names (env i)) pv k).
  Local Notation L_pub := (AttackerClock.L_pub ctx cost_limit).
  Local Notation observe := (AttackerClock.observe ctx).

  Local Notation run_n := (IRDefinitions.run_n ctx cost_limit).
  Local Notation sched_input := (IRDefinitions.sched_input ctx cost_limit).
  Local Notation done_set := (IRDefinitions.done_set ctx cost_limit).
  Local Notation start_rel := (IRDefinitions.start_rel ctx cost_limit).
  Local Notation state_matches := (IRDefinitions.state_matches synth).
  Local Notation env_matches := (IRDefinitions.env_matches synth).

  Local Notation N_of act input sp :=
    (L_pub act (observe input (snd sp) (snd (spec_run act sp input)))).

  Hypothesis Hrest : at_rest ctx cost_limit enc_sz enc enc_inj names c0 sp0.
  Hypothesis Hipc : ip_contract env.
  (* The emulator reads each cycle's public inputs as the circuit does. *)
  Hypothesis Hpv :
    forall k v, pv k v = mask_in ctx (port_inputs ctx cost_limit enc_sz enc enc_inj names (env k)) v.

  (* What the IPs answer in cycle [k], read off the wires. *)
  Definition resp (k: nat) : resp_val := fun p => env k (ext_input (inr p)) Ob~1.

  (* ------------------------------------------------------------------- *)
  (* One cycle of the circuit is one IR step.                            *)
  (* ------------------------------------------------------------------- *)

  (* On the cycle a command is taken, the wires carry it as [input_matches] reads it. *)
  Lemma accept_matches (k: nat) (act: tfs_action sched) (input: input_t) :
    cmds k = Some (act, input) ->
    IRDefinitions.input_matches synth act (sched_input input (resp k)) (env k).
  Proof.
    intro Hc. destruct (cmd_of_some _ _ _ _ _ _ _ _ _ Hc) as [Hv [Henc ->]].
    split; [ exact Hv | split; [ exact Henc |] ].
    intros [v | p]; reflexivity.
  Qed.

  Lemma live_matches (k: nat) (input: input_t) :
    IRDefinitions.live_inputs_match synth (sched_input input (resp k)) (env k).
  Proof. intros [v | p] p' Hv; [ discriminate Hv | reflexivity ]. Qed.

  (* Only the latched inputs matter to [env_matches], not the live answers. *)
  Lemma env_matches_resp act (input: input_t) (r1 r2: resp_val) c :
    env_matches act (sched_input input r1) c -> env_matches act (sched_input input r2) c.
  Proof.
    intros [Hcmd Hin]. split; [ exact Hcmd |].
    intros [v | p] Hx; [ exact (Hin (inl v) Hx) | discriminate Hx ].
  Qed.

  Lemma step_active (k: nat) act (input: input_t) (ss: sched_sys_state) :
    state_matches ss (circuit_run env k) ->
    ((circuit_run env k).[tf_ready] = Ob~1 -> cmds k = Some (act, input)) ->
    ((circuit_run env k).[tf_ready] = Ob~0 ->
       env_matches act (sched_input input (resp k)) (circuit_run env k)) ->
    let ss' := IRDefinitions.sched_step ctx cost_limit act ss (sched_input input (resp k)) in
    state_matches ss' (circuit_run env (S k))
    /\ env_matches act (sched_input input (resp k)) (circuit_run env (S k))
    /\ (circuit_run env (S k)).[tf_ready]
       = if beq_dec (fst ss').[tfs_done_signal sched] Bits.zero then Ob~0 else Ob~1.
  Proof.
    intros Hst Hrdy Hnrdy ss'.
    assert (Hin_rdy : (circuit_run env k).[tf_ready] = Ob~1 ->
              IRDefinitions.input_matches synth act (sched_input input (resp k)) (env k))
      by (intro H; apply accept_matches, Hrdy, H).
    destruct (SynthesisProof.synthesis_correct synth ss (circuit_run env k) act
                (sched_input input (resp k)) (env k) Hst Hin_rdy Hnrdy (live_matches k input))
      as [Hst' Henv'].
    pose proof (SynthesisProof.cycle_ready synth ss (circuit_run env k) act
                  (sched_input input (resp k)) (env k) Hst Hin_rdy Hnrdy (live_matches k input)) as Hr.
    split; [ exact Hst' | split; [ exact Henv' |] ].
    change (circuit_run env (S k))
      with (interp_cycle (env k) (rules synth) (system_schedule synth) (circuit_run env k)).
    rewrite Hr. subst ss'.
    rewrite (SchedulerSimulationLemmas.sched_step_done ctx cost_limit). reflexivity.
  Qed.

  Lemma ready_bits_neq : Ob~0 <> Ob~1.
  Proof. discriminate. Qed.

  (* From the cycle it is taken, a command runs on the circuit as [run_n] runs it,
     up to its first done cycle. *)
  Lemma track (k0: nat) act (input: input_t) (ss0: sched_sys_state) :
    cmds k0 = Some (act, input) ->
    (circuit_run env k0).[tf_ready] = Ob~1 ->
    state_matches ss0 (circuit_run env k0) ->
    forall j,
      (forall i, 0 < i < j -> ~ done_set (run_n i act input (fun i => resp (k0 + i)) ss0)) ->
      state_matches (run_n j act input (fun i => resp (k0 + i)) ss0) (circuit_run env (k0 + j))
      /\ (0 < j ->
          env_matches act (sched_input input (resp (k0 + j))) (circuit_run env (k0 + j))
          /\ (circuit_run env (k0 + j)).[tf_ready]
             = if beq_dec (fst (run_n j act input (fun i => resp (k0 + i)) ss0)).[tfs_done_signal sched]
                          Bits.zero
               then Ob~0 else Ob~1).
  Proof.
    intros Hc Hrdy0 Hst0 j. induction j as [| j IH]; intro Hnd.
    - rewrite Nat.add_0_r. split; [ exact Hst0 | lia ].
    - destruct IH as [Hst Hj]; [ intros i Hi; apply Hnd; lia |].
      assert (Hready : (circuit_run env (k0 + j)).[tf_ready] = Ob~1 -> cmds (k0 + j) = Some (act, input)).
      { intro H. destruct j as [| j].
        - rewrite Nat.add_0_r. exact Hc.
        - exfalso. destruct (Hj ltac:(lia)) as [_ Hr]. rewrite Hr in H.
          rewrite (not_done_beq ctx cost_limit _ (Hnd (S j) ltac:(lia))) in H.
          exact (ready_bits_neq H). }
      assert (Hbusy : (circuit_run env (k0 + j)).[tf_ready] = Ob~0 ->
                env_matches act (sched_input input (resp (k0 + j))) (circuit_run env (k0 + j))).
      { intro H. destruct j as [| j].
        - exfalso. rewrite Nat.add_0_r in H. rewrite Hrdy0 in H. exact (ready_bits_neq (eq_sym H)).
        - exact (proj1 (Hj ltac:(lia))). }
      destruct (step_active (k0 + j) act input _ Hst Hready Hbusy) as [Hst' [Henv' Hr']].
      rewrite Nat.add_succ_r.
      split; [ exact Hst' | intros _; split ].
      + exact (env_matches_resp act input _ _ _ Henv').
      + exact Hr'.
  Qed.

  (* The datasheet on the wires gives the IR's, for a command taken at [k0]. *)
  Lemma ip_contract_ir (k0: nat) act (input: input_t) (ss0: sched_sys_state) :
    cmds k0 = Some (act, input) ->
    (circuit_run env k0).[tf_ready] = Ob~1 ->
    state_matches ss0 (circuit_run env k0) ->
    IRDefinitions.ip_contract ctx cost_limit act input (fun i => resp (k0 + i)) ss0.
  Proof.
    intros Hc Hrdy Hst p s Hlive Hstrobe Hquiet.
    assert (Hm : forall w, w <= s + pred (ip_lat (tfs_ip sched p)) ->
               state_matches (run_n w act input (fun i => resp (k0 + i)) ss0)
                             (circuit_run env (k0 + w)))
      by (intros w Hw; apply (track k0 act input ss0 Hc Hrdy Hst w);
          intros i Hi; apply Hlive; lia).
    pose proof (Hipc p (k0 + s)) as H. cbv beta zeta in H.
    change (tfs_ip tsched p) with (tfs_ip sched p) in H.
    unfold resp. rewrite Nat.add_assoc.
    rewrite (proj1 (Hm s ltac:(lia))) in H.
    apply H.
    - exact Hstrobe.
    - intros w Hw. replace w with (k0 + (w - k0)) by lia.
      rewrite (proj1 (Hm (w - k0) ltac:(lia))).
      apply Hquiet; lia.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The ideal world's side.                                             *)
  (* ------------------------------------------------------------------- *)

  (* The emulator is idle and shows the spec's outputs. *)
  Definition em_idle (e: em ctx) (sp: src_sys_state) : Prop :=
    em_left e = 0 /\ em_post e = snd sp.

  Lemma ideal_idle k sp e :
    ideal k = (sp, e) -> em_idle e sp -> cmds k = None ->
    exists e', ideal (S k) = (sp, e') /\ em_idle e' sp.
  Proof.
    intros He [Hl Hp] Hc. cbn [ideal_run]. rewrite He, Hc.
    eexists. split; [ reflexivity |]. split; cbn; [ rewrite Hl | exact Hp ]; reflexivity.
  Qed.

  (* The latency the emulator computes, from its view of a command's inputs. *)
  Local Notation N_pv k0 act input sp :=
    (L_pub act {| seen_in := pv k0; seen_pre := mask_out ctx (snd sp);
                  seen_post := mask_out ctx (snd (spec_run act sp input)) |}).

  Lemma ideal_busy k0 sp e act input :
    ideal k0 = (sp, e) -> em_idle e sp -> cmds k0 = Some (act, input) ->
    N_pv k0 act input sp = N_of act input sp ->
    forall j, 0 < j <= N_of act input sp ->
      exists e', ideal (k0 + j) = (spec_run act sp input, e')
        /\ em_pre e' = snd sp /\ em_post e' = snd (spec_run act sp input)
        /\ em_left e' = N_of act input sp - j.
  Proof.
    intros He [Hl Hp] Hc HL j. induction j as [| j IH]; intro Hj; [ lia |].
    rewrite Nat.add_succ_r. cbn [ideal_run].
    destruct j as [| j].
    - rewrite Nat.add_0_r, He, Hc. cbv beta iota zeta.
      unfold em_ready. rewrite Hl. change (Nat.eqb 0 0) with true. cbv iota.
      eexists. split; [ reflexivity |]. cbn [em_pre em_post em_left em_take].
      rewrite Hp, HL. split; [ reflexivity | split; [ reflexivity | symmetry; apply Nat.sub_1_r ] ].
    - destruct (IH ltac:(lia)) as [e' [He' [Hpre [Hpost Hleft]]]]. rewrite He'.
      assert (Hbusy : em_ready e' = false)
        by (unfold em_ready; rewrite Hleft; apply Nat.eqb_neq; lia).
      exists (em_tick e'). cbv beta iota zeta.
      destruct (cmds (k0 + S j)) as [[a i] |]; [ cbv iota; rewrite Hbusy; cbv iota |];
        (split; [ reflexivity |]); cbn [em_pre em_post em_left em_tick];
        rewrite Hpre, Hpost, Hleft; (split; [ reflexivity | split; [ reflexivity | lia ] ]).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* One command on the circuit, then the run by induction over cycles.  *)
  (* ------------------------------------------------------------------- *)

  (* Taken at a ready cycle [k0], a command keeps the outputs and ready down for
     [N - 1] cycles, then reaches the next ready cycle in step with the spec. *)
  Lemma segment (k0: nat) (ss: sched_sys_state) (sp: src_sys_state) act input :
    (circuit_run env k0).[tf_ready] = Ob~1 ->
    state_matches ss (circuit_run env k0) ->
    start_rel sp ss ->
    cmds k0 = Some (act, input) ->
    0 < N_of act input sp
    /\ (forall j, 0 < j < N_of act input sp ->
          (circuit_run env (k0 + j)).[tf_ready] = Ob~0
          /\ forall ov, (circuit_run env (k0 + j)).[tf_out ov] = (snd sp).[ov])
    /\ exists ss', (circuit_run env (k0 + N_of act input sp)).[tf_ready] = Ob~1
                  /\ state_matches ss' (circuit_run env (k0 + N_of act input sp))
                  /\ start_rel (spec_run act sp input) ss'.
  Proof.
    intros Hrdy Hst Hstart Hc.
    pose proof (ip_contract_ir k0 act input ss Hc Hrdy Hst) as Hipc_ir.
    destruct (command_emulated ctx cost_limit act sp ss input (fun i => resp (k0 + i))
                Hstart Hipc_ir) as [Hfd Hout].
    cbv zeta in Hfd, Hout.
    pose proof Hfd as [HN0 [Hdone Hbefore]].
    split; [ exact HN0 | split ].
    - intros j Hj.
      destruct (track k0 act input ss Hc Hrdy Hst j (fun i Hi => Hbefore i ltac:(lia)))
        as [Hstj Hj'].
      destruct (Hj' ltac:(lia)) as [_ Hr]. split.
      + rewrite Hr, (not_done_beq ctx cost_limit _ (Hbefore j ltac:(lia))). reflexivity.
      + intro ov. pose proof (Hout j ltac:(lia) ov) as Ho.
        unfold IRDefinitions.emulate in Ho. rewrite (proj2 (Nat.ltb_lt _ _) (proj2 Hj)) in Ho.
        rewrite (proj2 Hstj ov). exact Ho.
    - exists (run_n (N_of act input sp) act input (fun i => resp (k0 + i)) ss).
      destruct (track k0 act input ss Hc Hrdy Hst (N_of act input sp)
                  (fun i Hi => Hbefore i ltac:(lia))) as [HstN HN'].
      destruct (HN' HN0) as [_ Hr]. split; [| split].
      + rewrite Hr, (done_beq ctx cost_limit _ Hdone). reflexivity.
      + exact HstN.
      + exact (SchedulerRoundTrip.start_rel_after_done ctx cost_limit act sp ss input
                 (fun i => resp (k0 + i)) _ Hstart Hipc_ir HN0 Hbefore Hdone).
  Qed.

  (* The emulator's latency is the command's: its view reads as the run's own. *)
  Lemma latency_pv (k0: nat) (ss: sched_sys_state) (sp: src_sys_state) act input :
    (circuit_run env k0).[tf_ready] = Ob~1 ->
    state_matches ss (circuit_run env k0) ->
    start_rel sp ss ->
    cmds k0 = Some (act, input) ->
    N_pv k0 act input sp = N_of act input sp.
  Proof.
    intros Hrdy Hst Hstart Hc.
    pose proof (ip_contract_ir k0 act input ss Hc Hrdy Hst) as Hipc_ir.
    destruct (Extract.act_slot_exists ctx cost_limit act) as [a_idx Halign].
    destruct (cmd_of_some _ _ _ _ _ _ _ _ _ Hc) as [_ [_ Hin]].
    transitivity (ProofDefinitions.L ctx cost_limit act input (fun i => resp (k0 + i)) ss).
    - symmetry. apply (Extract.L_is_public ctx cost_limit act a_idx sp ss input
                         (fun i => resp (k0 + i)) Halign Hstart Hipc_ir);
        intro x; [ cbn [seen_in]; rewrite (Hpv k0 x), Hin | |]; reflexivity.
    - exact (Extract.L_is_public ctx cost_limit act a_idx sp ss input (fun i => resp (k0 + i))
               Halign Hstart Hipc_ir _ (fun _ => eq_refl) (fun _ => eq_refl) (fun _ => eq_refl)).
  Qed.

  (* A cycle where the circuit waits for a command, in step with the spec. *)
  Definition ready_point (k: nat) (sp: src_sys_state) : Prop :=
    (circuit_run env k).[tf_ready] = Ob~1
    /\ (exists ss, state_matches ss (circuit_run env k) /\ start_rel sp ss)
    /\ exists e, ideal k = (sp, e) /\ em_idle e sp.

  (* Every cycle is a ready point or inside the command taken at the last one. *)
  Definition inv (k: nat) : Prop :=
    exists k0 sp, k0 <= k /\ ready_point k0 sp
      /\ (k = k0 \/ exists act input, cmds k0 = Some (act, input) /\ k - k0 < N_of act input sp).

  (* At rest, the circuit is in step with the spec state it holds. *)
  Lemma ready_point_start : ready_point 0 sp0.
  Proof.
    destruct Hrest as [Hrdy [Hout Hreg]].
    split; [ exact Hrdy | split ].
    - exists (ContextEnv.(create) (fun x => c0.[tf_reg x]),
              ContextEnv.(create) (fun o => c0.[tf_out o])).
      split; [ split; intro x; cbn [fst snd]; rewrite getenv_create; reflexivity |].
      split; [| split ].
      + apply equiv_eq. intro o. cbn [snd]. rewrite getenv_create. exact (Hout o).
      + apply equiv_eq. intro s. unfold States.maps_from. cbn [fst].
        rewrite !getenv_create. exact (Hreg (tf_dfg_s s)).
      + intros x Hx. cbn [fst]. rewrite getenv_create.
        destruct x as [| s | a n | a n | p]; try contradiction;
          [ exact (Hreg (tf_dfg_b a n)) | exact (Hreg (tf_dfg_v a n)) ].
    - eexists. split; [ reflexivity | split; reflexivity ].
  Qed.

  Lemma ready_point_next k0 sp act input :
    ready_point k0 sp -> cmds k0 = Some (act, input) ->
    ready_point (k0 + N_of act input sp) (spec_run act sp input).
  Proof.
    intros [Hrdy [[ss [Hst Hstart]] [e [He Hidle]]]] Hc.
    destruct (segment k0 ss sp act input Hrdy Hst Hstart Hc)
      as [HN0 [_ [ss' [Hr' [Hst' Hstart']]]]].
    split; [ exact Hr' | split; [ exists ss'; split; assumption |] ].
    destruct (ideal_busy k0 sp e act input He Hidle Hc
                (latency_pv k0 ss sp act input Hrdy Hst Hstart Hc) (N_of act input sp) ltac:(lia))
      as [e' [He' [_ [Hpost Hleft]]]].
    exists e'. split; [ exact He' | split; [ rewrite Hleft; apply Nat.sub_diag | exact Hpost ] ].
  Qed.

  Lemma inv_step k : inv k -> inv (S k).
  Proof.
    intros [k0 [sp [Hle [Hrp Hcase]]]].
    assert (Hrp' := Hrp). destruct Hrp' as [Hrdy [[ss [Hst Hstart]] [e [He Hidle]]]].
    destruct Hcase as [-> | [act [input [Hc Hlt]]]].
    - destruct (cmds k0) as [[act input] |] eqn:Hc.
      + (* a command is taken *)
        destruct (segment k0 ss sp act input Hrdy Hst Hstart Hc) as [HN0 _].
        destruct (Nat.eq_dec (N_of act input sp) 1) as [H1 | H1].
        * exists (S k0), (spec_run act sp input). split; [ lia | split; [| left; reflexivity ] ].
          replace (S k0) with (k0 + N_of act input sp) by lia.
          exact (ready_point_next k0 sp act input Hrp Hc).
        * exists k0, sp. split; [ lia | split; [ exact Hrp |] ].
          right. exists act, input. split; [ exact Hc | lia ].
      + (* an idle cycle *)
        exists (S k0), sp. split; [ lia | split; [| left; reflexivity ] ].
        pose proof (cmd_of_none _ _ _ _ _ _ _ Hc) as Hp.
        assert (Hid : forall x, match x with tf_out_ack _ | tf_ip_ack _ => False | _ => True end ->
                   (circuit_run env (S k0)).[x] = (circuit_run env k0).[x])
          by (intros x Hx;
              exact (SynthesisProof.cycle_idle synth (circuit_run env k0) (env k0) x Hrdy Hp Hx)).
        split; [ rewrite Hid by exact I; exact Hrdy | split ].
        * exists ss. split; [| exact Hstart ].
          split; intro x; rewrite Hid by exact I; [ apply (proj1 Hst) | apply (proj2 Hst) ].
        * exact (ideal_idle k0 sp e He Hidle Hc).
    - destruct (Nat.eq_dec (S k - k0) (N_of act input sp)) as [HN | HN].
      + exists (S k), (spec_run act sp input). split; [ lia | split; [| left; reflexivity ] ].
        replace (S k) with (k0 + N_of act input sp) by lia.
        exact (ready_point_next k0 sp act input Hrp Hc).
      + exists k0, sp. split; [ lia | split; [ exact Hrp |] ].
        right. exists act, input. split; [ exact Hc | lia ].
  Qed.

  Lemma inv_all k : inv k.
  Proof.
    induction k as [| k IH]; [| exact (inv_step k IH) ].
    exists 0, sp0. split; [ lia | split; [ exact ready_point_start | left; reflexivity ] ].
  Qed.

  Theorem circuit_emulated : forall k,
    let e := snd (ideal k) in
    ((circuit_run env k).[tf_ready] = Ob~1 <-> em_ready e = true)
    /\ forall ov, (circuit_run env k).[tf_out ov] = (em_shown e).[ov].
  Proof.
    intro k. destruct (inv_all k) as [k0 [sp [Hle [Hrp Hcase]]]].
    assert (Hrp' := Hrp). destruct Hrp' as [Hrdy [[ss [Hst Hstart]] [e [He [Hl Hp]]]]].
    assert (Hat : k = k0 ->
      let e := snd (ideal k) in
      ((circuit_run env k).[tf_ready] = Ob~1 <-> em_ready e = true)
      /\ forall ov, (circuit_run env k).[tf_out ov] = (em_shown e).[ov]).
    { intros ->. cbv zeta. rewrite He. cbn [snd].
      unfold em_shown, em_ready. rewrite Hl, Hp.
      change (Nat.eqb 0 0) with true. cbv iota.
      split; [ split; intro; [ reflexivity | exact Hrdy ] |].
      intro ov. rewrite (proj2 Hst ov). cbv iota.
      exact (f_equal (fun o => o.[ov]) (proj1 Hstart)). }
    destruct Hcase as [Hk | [act [input [Hc Hlt]]]]; [ exact (Hat Hk) |].
    destruct (Nat.eq_dec k k0) as [Hk | Hk]; [ exact (Hat Hk) |].
    destruct (segment k0 ss sp act input Hrdy Hst Hstart Hc) as [HN0 [Hmid _]].
    replace k with (k0 + (k - k0)) by lia.
    destruct (Hmid (k - k0) ltac:(lia)) as [Hr Hout].
    destruct (ideal_busy k0 sp e act input He (conj Hl Hp) Hc
                (latency_pv k0 ss sp act input Hrdy Hst Hstart Hc) (k - k0) ltac:(lia))
      as [e' [He' [Hpre [_ Hleft]]]].
    cbv zeta. rewrite He'. cbn [snd].
    assert (Hbusy : em_ready e' = false)
      by (unfold em_ready; rewrite Hleft; apply Nat.eqb_neq; lia).
    unfold em_shown. rewrite Hbusy, Hpre. split.
    - rewrite Hr. split; intro H; [ exfalso; exact (ready_bits_neq H) | discriminate H ].
    - exact Hout.
  Qed.

  (* Reset is at rest, holding the spec's initial state. *)
  Lemma reset_at_rest :
    at_rest ctx cost_limit enc_sz enc enc_inj names (ContextEnv.(create) (r synth))
      (ContextEnv.(create) (tfs_spec_states_init ctx), ContextEnv.(create) (fun _ => Bits.zero)).
  Proof.
    split; [| split].
    - rewrite getenv_create. reflexivity.
    - intro o. cbn [snd]. rewrite !getenv_create. reflexivity.
    - intro x. destruct x; try exact I; cbn [fst]; rewrite !getenv_create; reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* What the IPR proof uses, at this start state and environment.      *)
  (* ------------------------------------------------------------------- *)

  (* Matching registers and a start relation at a ready cycle mean at rest. *)
  Lemma rest_of_matches c ss sp :
    c.[tf_ready] = Ob~1 -> state_matches ss c -> start_rel sp ss ->
    at_rest ctx cost_limit enc_sz enc enc_inj names c sp.
  Proof.
    intros Hr [Hreg Hout] [Hso [Hmap Hz]]. split; [ exact Hr | split ].
    - intro o. rewrite (Hout o). exact (f_equal (fun e => e.[o]) Hso).
    - intro x. destruct x as [| s | a n | a n | p]; cbv iota; try exact I.
      + transitivity ((fst ss).[tf_dfg_s s]); [ exact (Hreg (tf_dfg_s s)) |].
        rewrite <- Hmap. unfold States.maps_from. rewrite getenv_create. reflexivity.
      + transitivity ((fst ss).[tf_dfg_b a n]); [ exact (Hreg (tf_dfg_b a n)) |].
        apply Hz. exact I.
      + transitivity ((fst ss).[tf_dfg_v a n]); [ exact (Hreg (tf_dfg_v a n)) |].
        apply Hz. exact I.
  Qed.

  (* THE FUNCTIONAL HALF here: a command offered at rest brings the circuit back
     to rest, one spec step on. *)
  Lemma functional_here act input :
    offers ctx cost_limit enc_sz enc enc_inj names (env 0) act input ->
    exists N, 0 < N
      /\ (forall j, 0 < j < N -> (circuit_run env j).[tf_ready] = Ob~0)
      /\ at_rest ctx cost_limit enc_sz enc enc_inj names (circuit_run env N) (spec_run act sp0 input).
  Proof.
    intros [Hv [Hc Hin]].
    assert (Hcmd : cmds 0 = Some (act, port_inputs ctx cost_limit enc_sz enc enc_inj names (env 0))).
    { unfold cmd_of. cbv zeta.
      lazymatch goal with |- context [Bits.single ?T] =>
        let H := fresh in assert (H : T = Ob~1) by exact Hv; rewrite H end.
      lazymatch goal with |- context [decode _ _ _ _ ?C] =>
        let H := fresh in assert (H : C = enc act) by exact Hc; rewrite H end.
      rewrite decode_enc by exact enc_inj. reflexivity. }
    destruct ready_point_start as [Hrdy [[ss [Hst Hstart]] _]].
    destruct (segment 0 ss sp0 act _ Hrdy Hst Hstart Hcmd)
      as [HN0 [Hmid [ss' [Hr' [Hst' Hstart']]]]].
    rewrite (ops_run_inputs_ext _ _ _ _ _ _ _ _ Hin) in Hstart'.
    eexists. split; [ exact HN0 | split ].
    - intros j Hj. exact (proj1 (Hmid j Hj)).
    - exact (rest_of_matches _ _ _ Hr' Hst' Hstart').
  Qed.

  Local Notation pe_state := (pe_state ctx).

  (* The IPR emulator's state is the cycle-level one's, outputs masked. *)
  Definition mask_em (e: em ctx) : pe_state :=
    (mask_out ctx (em_pre e), mask_out ctx (em_post e), em_left e).

  Lemma pe_takes_mask w e :
    pe_takes ctx cost_limit enc_sz enc (atk_in_of ctx cost_limit enc_sz enc enc_inj names w) (mask_em e)
    = if em_ready e
      then match cmd_of ctx cost_limit enc_sz enc enc_inj names w with
           | Some (act, input) => Some (act, mask_in ctx input)
           | None => None
           end
      else None.
  Proof.
    unfold pe_takes, atk_in_of, mask_em, cmd_of, em_ready. cbv zeta. cbn [fst snd].
    destruct (Nat.eqb (em_left e) 0); cbn [andb]; [| reflexivity ].
    destruct (Bits.single _); [| reflexivity ].
    destruct (decode _ _ _ _ _); reflexivity.
  Qed.

  Lemma bits1_cases (b: bits_t 1) : b = Ob~0 \/ b = Ob~1.
  Proof. destruct b as [[|] []]; [ right | left ]; reflexivity. Qed.

  Lemma pe_ready_mask e k :
    snd (ideal k) = e ->
    pe_ready ctx (mask_em e) = (circuit_run env k).[tf_ready].
  Proof.
    intro He. pose proof (circuit_emulated k) as Hk. cbv zeta in Hk. rewrite He in Hk.
    destruct Hk as [Hiff _]. unfold pe_ready, mask_em, em_ready in *. cbv zeta.
    destruct (bits1_cases ((circuit_run env k).[tf_ready])) as [H0 | H1].
    - rewrite H0 in *. destruct (Nat.eqb (em_left e) 0) eqn:E; [| reflexivity ].
      exfalso. apply ready_bits_neq. apply Hiff. reflexivity.
    - rewrite H1 in *. rewrite (proj1 Hiff eq_refl). reflexivity.
  Qed.

  Lemma pe_shown_mask e k :
    snd (ideal k) = e ->
    pe_shown ctx (mask_em e) = mask_out ctx (circuit_outputs ctx cost_limit enc_sz enc enc_inj names (circuit_run env k)).
  Proof.
    intro He. pose proof (circuit_emulated k) as Hk. cbv zeta in Hk. rewrite He in Hk.
    destruct Hk as [_ Hout].
    assert (Henv : circuit_outputs ctx cost_limit enc_sz enc enc_inj names (circuit_run env k) = em_shown e).
    { apply equiv_eq. intro o. unfold circuit_outputs. rewrite getenv_create. exact (Hout o). }
    rewrite Henv. unfold pe_shown, mask_em, em_shown, em_ready. cbv zeta.
    destruct (Nat.eqb (em_left e) 0); reflexivity.
  Qed.

  (* The emulator shows the spec's outputs once idle: [em_post] is the spec's. *)
  Lemma ideal_post k : em_post (snd (ideal k)) = snd (fst (ideal k)).
  Proof.
    induction k as [| k IH]; [ reflexivity |]. cbn [ideal_run].
    destruct (ideal k) as [sp e]. cbn [fst snd] in IH.
    destruct (cmds k) as [[act input] |]; [ destruct (em_ready e) |]; exact IH || reflexivity.
  Qed.

  (* At a ready cycle, the circuit's outputs are the spec's. *)
  Lemma ready_outputs k :
    em_ready (snd (ideal k)) = true ->
    circuit_outputs ctx cost_limit enc_sz enc enc_inj names (circuit_run env k) = snd (fst (ideal k)).
  Proof.
    intro Hr. destruct (circuit_emulated k) as [_ Hout]. cbv zeta in Hout.
    apply equiv_eq. intro o. unfold circuit_outputs. rewrite getenv_create, Hout.
    unfold em_shown. rewrite Hr, ideal_post. reflexivity.
  Qed.

End CircuitProof.
