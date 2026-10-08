(*! The proof behind [IPR.circuit_emulated]: cycle by cycle, the circuit either idles
    at a ready cycle or runs the command it took there exactly as the IR does, so
    the per-command timing theorem holds of the Kôika run itself. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Backend.Lowering.
Require Export Trustformer.Theorems.Definitions.
Require Export Trustformer.Theorems.Internal.IRDefinitions.
Require Trustformer.Declassification.Extract.
Require Trustformer.Theorems.Internal.IPRProof.
Require Trustformer.Theorems.Internal.SchedulerSimulationLemmas.
Require Trustformer.Theorems.Internal.SchedulerRoundTrip.
Require Trustformer.Theorems.Internal.SynthesisProof.

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

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
  Local Notation L_pub := (Definitions.L_pub ctx cost_limit).
  Local Notation observe := (Definitions.observe ctx).

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
                  Halign Hstart Hipc).
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

  Context (c0: circuit_state) (sp0: src_sys_state).
  Context (env: nat -> wires) (cmds: nat -> option command).

  Local Notation circuit_run := (Definitions.circuit_run ctx cost_limit enc_sz enc enc_inj names c0).
  Local Notation presents := (Definitions.presents ctx cost_limit enc_sz enc enc_inj names).
  Local Notation ip_contract := (Definitions.ip_contract ctx cost_limit enc_sz enc enc_inj names c0).
  Local Notation ideal k := (Definitions.ideal_run ctx cost_limit sp0 cmds k).
  Local Notation L_pub := (Definitions.L_pub ctx cost_limit).
  Local Notation observe := (Definitions.observe ctx).

  Local Notation run_n := (IRDefinitions.run_n ctx cost_limit).
  Local Notation sched_input := (IRDefinitions.sched_input ctx cost_limit).
  Local Notation done_set := (IRDefinitions.done_set ctx cost_limit).
  Local Notation start_rel := (IRDefinitions.start_rel ctx cost_limit).
  Local Notation state_matches := (IRDefinitions.state_matches synth).
  Local Notation env_matches := (IRDefinitions.env_matches synth).

  Local Notation N_of act input sp :=
    (L_pub act (observe input (snd sp) (snd (spec_run act sp input)))).

  Hypothesis Hrest : at_rest ctx cost_limit enc_sz enc enc_inj names c0 sp0.
  Hypothesis Hpres : forall k, presents (env k) (cmds k).
  Hypothesis Hipc : ip_contract env.

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
    intro Hc. pose proof (Hpres k) as Hp. unfold Definitions.presents in Hp. rewrite Hc in Hp.
    destruct Hp as [Hv [Henc Hin]].
    split; [ exact Hv | split; [ exact Henc |] ].
    intros [v | p]; [ exact (Hin v) | reflexivity ].
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
  Definition em_idle (e: emulator ctx) (sp: src_sys_state) : Prop :=
    em_left e = 0 /\ em_post e = snd sp.

  Lemma ideal_idle k sp e :
    ideal k = (sp, e) -> em_idle e sp -> cmds k = None ->
    exists e', ideal (S k) = (sp, e') /\ em_idle e' sp.
  Proof.
    intros He [Hl Hp] Hc. cbn [Definitions.ideal_run]. rewrite He, Hc.
    eexists. split; [ reflexivity |]. split; cbn; [ rewrite Hl | exact Hp ]; reflexivity.
  Qed.

  Lemma ideal_busy k0 sp e act input :
    ideal k0 = (sp, e) -> em_idle e sp -> cmds k0 = Some (act, input) ->
    forall j, 0 < j <= N_of act input sp ->
      exists e', ideal (k0 + j) = (spec_run act sp input, e')
        /\ em_pre e' = snd sp /\ em_post e' = snd (spec_run act sp input)
        /\ em_left e' = N_of act input sp - j.
  Proof.
    intros He [Hl Hp] Hc j. induction j as [| j IH]; intro Hj; [ lia |].
    rewrite Nat.add_succ_r. cbn [Definitions.ideal_run].
    destruct j as [| j].
    - rewrite Nat.add_0_r, He, Hc. cbv beta iota zeta.
      unfold Definitions.em_ready. rewrite Hl. change (Nat.eqb 0 0) with true. cbv iota.
      eexists. split; [ reflexivity |]. cbn [em_pre em_post em_left Definitions.em_take].
      rewrite Hp. split; [ reflexivity | split; [ reflexivity | symmetry; apply Nat.sub_1_r ] ].
    - destruct (IH ltac:(lia)) as [e' [He' [Hpre [Hpost Hleft]]]]. rewrite He'.
      assert (Hbusy : em_ready e' = false)
        by (unfold Definitions.em_ready; rewrite Hleft; apply Nat.eqb_neq; lia).
      exists (Definitions.em_tick e'). cbv beta iota zeta.
      destruct (cmds (k0 + S j)) as [[a i] |]; [ cbv iota; rewrite Hbusy; cbv iota |];
        (split; [ reflexivity |]); cbn [em_pre em_post em_left Definitions.em_tick];
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
    destruct (ideal_busy k0 sp e act input He Hidle Hc (N_of act input sp) ltac:(lia))
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
        pose proof (Hpres k0) as Hp. unfold Definitions.presents in Hp. rewrite Hc in Hp.
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
      unfold Definitions.em_shown, Definitions.em_ready. rewrite Hl, Hp.
      change (Nat.eqb 0 0) with true. cbv iota.
      split; [ split; intro; [ reflexivity | exact Hrdy ] |].
      intro ov. rewrite (proj2 Hst ov). cbv iota.
      exact (f_equal (fun o => o.[ov]) (proj1 Hstart)). }
    destruct Hcase as [Hk | [act [input [Hc Hlt]]]]; [ exact (Hat Hk) |].
    destruct (Nat.eq_dec k k0) as [Hk | Hk]; [ exact (Hat Hk) |].
    destruct (segment k0 ss sp act input Hrdy Hst Hstart Hc) as [HN0 [Hmid _]].
    replace k with (k0 + (k - k0)) by lia.
    destruct (Hmid (k - k0) ltac:(lia)) as [Hr Hout].
    destruct (ideal_busy k0 sp e act input He (conj Hl Hp) Hc (k - k0) ltac:(lia))
      as [e' [He' [Hpre [_ Hleft]]]].
    cbv zeta. rewrite He'. cbn [snd].
    assert (Hbusy : em_ready e' = false)
      by (unfold Definitions.em_ready; rewrite Hleft; apply Nat.eqb_neq; lia).
    unfold Definitions.em_shown. rewrite Hbusy, Hpre. split.
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

End CircuitProof.

