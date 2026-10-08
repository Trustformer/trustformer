(*! The proofs behind [IPR.emulator_correct_seq]: a queue runs its head command as
    [run_n] does until done, then hands the next a start state
    ([start_rel_after_done]), so the per-command guarantee chains by induction. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Export Trustformer.Theorems.Definitions.
Require Trustformer.Declassification.Extract.
Require Trustformer.Theorems.Internal.IPRProof.
Require Trustformer.Theorems.Internal.SchedulerRoundTrip.

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

Section IPRChain.

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
  Local Notation command := (tfs_action sched * input_t)%type.
  Local Notation spec_run act sp input :=
    (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act)
       sp input).

  Local Notation run_n := (run_n ctx cost_limit).
  Local Notation sched_step := (sched_step ctx cost_limit).
  Local Notation sched_input := (sched_input ctx cost_limit).
  Local Notation done_set := (done_set ctx cost_limit).
  Local Notation start_rel := (start_rel ctx cost_limit).
  Local Notation ip_contract := (ip_contract ctx cost_limit).
  Local Notation first_done := (first_done ctx cost_limit).
  Local Notation emulate := (emulate ctx).
  Local Notation L_pub := (L_pub ctx cost_limit).
  Local Notation observe := (observe ctx).
  Local Notation queue_run := (queue_run ctx cost_limit).
  Local Notation queue_ip_contract := (queue_ip_contract ctx cost_limit).
  Local Notation spec_outputs_seq := (spec_outputs_seq ctx cost_limit).
  Local Notation emulate_seq := (emulate_seq ctx cost_limit).
  Local Notation emulate_progress := (emulate_progress ctx cost_limit).

  (* ------------------------------------------------------------------- *)
  (* One command: the guarantee of [IPR.emulator_correct].                *)
  (* ------------------------------------------------------------------- *)

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

  (* ------------------------------------------------------------------- *)
  (* The queue reads the done flag as [done_set] does.                    *)
  (* ------------------------------------------------------------------- *)

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

  (* ------------------------------------------------------------------- *)
  (* A queue run cut at a cycle goes on as a queue run of its own.       *)
  (* ------------------------------------------------------------------- *)

  Lemma queue_run_add (q: list command) (resp: nat -> resp_val)
      (ss: sched_sys_state) (T: nat) (q': list command) (ss': sched_sys_state) :
    queue_run T q resp ss = (q', ss') ->
    forall n, queue_run (T + n) q resp ss
              = queue_run n q' (fun j => resp (T + j)) ss'.
  Proof.
    intros HT n. induction n as [| n IH].
    - rewrite Nat.add_0_r. exact HT.
    - rewrite Nat.add_succ_r. cbn [Definitions.queue_run]. rewrite IH.
      reflexivity.
  Qed.

  Lemma queue_run_from (q: list command) (resp: nat -> resp_val)
      (ss: sched_sys_state) (T: nat) (q': list command) (ss': sched_sys_state)
      (k: nat) :
    T <= k ->
    queue_run T q resp ss = (q', ss') ->
    queue_run k q resp ss = queue_run (k - T) q' (fun j => resp (T + j)) ss'.
  Proof.
    intros Hle HT. rewrite <- (queue_run_add q resp ss T q' ss' HT (k - T)).
    f_equal. lia.
  Qed.

  (* An empty queue holds its state. *)
  Lemma queue_run_idle (resp: nat -> resp_val) (ss: sched_sys_state) (n: nat) :
    queue_run n [] resp ss = ([], ss).
  Proof.
    induction n as [| n IH]; [ reflexivity |].
    cbn [Definitions.queue_run]. rewrite IH. reflexivity.
  Qed.

  (* Until its done cycle, the head command runs as [run_n] runs it ... *)
  Lemma queue_run_head (act: tfs_action sched) (input: input_t)
      (rest: list command) (resp: nat -> resp_val) (ss: sched_sys_state)
      (j: nat) :
    (forall i, 0 < i <= j -> ~ done_set (run_n i act input resp ss)) ->
    queue_run j ((act, input) :: rest) resp ss
    = ((act, input) :: rest, run_n j act input resp ss).
  Proof.
    induction j as [| j IH]; intro Hnd; [ reflexivity |].
    cbn [Definitions.queue_run].
    rewrite IH by (intros i Hi; apply Hnd; lia).
    cbn [fst snd Definitions.queue_step].
    rewrite (not_done_beq (sched_step act (run_n j act input resp ss)
                             (sched_input input (resp j)))
               (Hnd (S j) ltac:(lia))).
    reflexivity.
  Qed.

  (* ... and on it the queue moves on. *)
  Lemma queue_run_first_done (act: tfs_action sched) (input: input_t)
      (rest: list command) (resp: nat -> resp_val) (ss: sched_sys_state)
      (N: nat) :
    first_done act input resp ss N ->
    queue_run N ((act, input) :: rest) resp ss = (rest, run_n N act input resp ss).
  Proof.
    intros [HN0 [Hdone Hbefore]].
    destruct N as [| M]; [ lia |].
    cbn [Definitions.queue_run].
    rewrite (queue_run_head act input rest resp ss M
               (fun i Hi => Hbefore i ltac:(lia))).
    cbn [fst snd Definitions.queue_step].
    rewrite (done_beq (sched_step act (run_n M act input resp ss)
                         (sched_input input (resp M))) Hdone).
    reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The datasheet over the whole run gives each command its own.         *)
  (* ------------------------------------------------------------------- *)

  (* The head command's answers are due before its done cycle, so they are
     answers on the run that actually happens. *)
  Lemma queue_contract_head (act: tfs_action sched) (input: input_t)
      (rest: list command) (resp: nat -> resp_val) (ss: sched_sys_state) :
    queue_ip_contract ((act, input) :: rest) resp ss ->
    ip_contract act input resp ss.
  Proof.
    intros Hq p s Hlive Hstrobe Hquiet.
    assert (Hrun : forall j, j <= s + pred (ip_lat (tfs_ip sched p)) ->
              queue_run j ((act, input) :: rest) resp ss
              = ((act, input) :: rest, run_n j act input resp ss)).
    { intros j Hj. apply queue_run_head. intros i Hi. apply Hlive. lia. }
    pose proof (Hq p s) as H.
    rewrite (Hrun s ltac:(lia)) in H. cbn [snd] in H.
    apply H; [ exact Hstrobe |].
    intros w Hw1 Hw2. rewrite (Hrun w ltac:(lia)). exact (Hquiet w Hw1 Hw2).
  Qed.

  (* From any cycle on, the rest of the queue meets the datasheet again. *)
  Lemma queue_contract_shift (q: list command) (resp: nat -> resp_val)
      (ss: sched_sys_state) (T: nat) (q': list command) (ss': sched_sys_state) :
    queue_ip_contract q resp ss ->
    queue_run T q resp ss = (q', ss') ->
    queue_ip_contract q' (fun j => resp (T + j)) ss'.
  Proof.
    intros Hq HT p s Hstrobe Hquiet. cbv beta.
    rewrite <- (queue_run_add q resp ss T q' ss' HT s) in Hstrobe |- *.
    rewrite Nat.add_assoc.
    apply (Hq p (T + s) Hstrobe).
    intros w Hw1 Hw2.
    rewrite (queue_run_from q resp ss T q' ss' w ltac:(lia) HT).
    apply Hquiet; lia.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE CHAIN, by induction over the queue.                             *)
  (* ------------------------------------------------------------------- *)

  Theorem queue_emulated (q: list command) :
    forall (sp0: src_sys_state) (ss0: sched_sys_state) (resp: nat -> resp_val),
      start_rel sp0 ss0 ->
      queue_ip_contract q resp ss0 ->
      forall k,
        fst (queue_run k q resp ss0)
          = skipn (emulate_progress (snd sp0) (spec_outputs_seq q sp0) k) q
        /\ forall ov, (snd (snd (queue_run k q resp ss0))).[ov]
                      = emulate_seq (snd sp0) (spec_outputs_seq q sp0) k ov.
  Proof.
    induction q as [| [act input] rest IH]; intros sp0 ss0 resp Hstart Hq k.
    - rewrite queue_run_idle.
      cbn [fst snd skipn Definitions.spec_outputs_seq Definitions.emulate_progress
           Definitions.emulate_seq].
      split; [ reflexivity |].
      intro ov. rewrite (proj1 Hstart). reflexivity.
    - pose proof (queue_contract_head act input rest resp ss0 Hq) as Hipc.
      destruct (command_emulated act sp0 ss0 input resp Hstart Hipc) as [Hfd Hout].
      cbn [Definitions.spec_outputs_seq Definitions.emulate_progress
           Definitions.emulate_seq].
      set (sp1 := spec_run act sp0 input) in *.
      set (N := L_pub act (observe input (snd sp0) (snd sp1))) in *.
      pose proof Hfd as [HN0 [Hdone Hbefore]].
      destruct (Nat.ltb_spec k N) as [Hlt | Hge].
      + (* still on the head command: the outputs hold at [pre] *)
        rewrite (queue_run_head act input rest resp ss0 k
                   (fun i Hi => Hbefore i ltac:(lia))).
        cbn [fst snd skipn]. split; [ reflexivity |].
        intro ov. rewrite (Hout k ltac:(lia) ov).
        unfold Definitions.emulate. rewrite (proj2 (Nat.ltb_lt k N) Hlt).
        reflexivity.
      + (* the head command is done: the rest runs from a start state *)
        pose proof (queue_run_first_done act input rest resp ss0 N Hfd) as Hrun.
        pose proof (SchedulerRoundTrip.start_rel_after_done ctx cost_limit act
                      sp0 ss0 input resp N Hstart Hipc HN0 Hbefore Hdone) as Hstart1.
        pose proof (queue_contract_shift _ resp ss0 N _ _ Hq Hrun) as Hq1.
        destruct (IH sp1 (run_n N act input resp ss0) (fun j => resp (N + j))
                    Hstart1 Hq1 (k - N)) as [Hprog Hval].
        rewrite (queue_run_from _ resp ss0 N _ _ k Hge Hrun).
        split; [ rewrite Hprog; reflexivity | exact Hval ].
  Qed.

End IPRChain.
