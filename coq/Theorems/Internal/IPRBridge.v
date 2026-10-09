(*! IPR itself, as anishathalye/ipr defines it: the circuit closed over its trusted
    environment as M1, the spec closed over the same source as M2, and [driver] as
    d, from CircuitProof.v by the strategy in IPRStrategy.v. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Backend.Lowering.
Require Export Trustformer.Theorems.IPRDefinitions.
Require Import Trustformer.Theorems.Internal.CircuitDefinitions.
Require Trustformer.Theorems.Internal.CircuitProof.
Require Trustformer.Theorems.Internal.SynthesisProof.
Require Import Trustformer.Theorems.Internal.IPRStrategy.
Require Import IPR.Common IPR.Machine IPR.Driver IPR.Emulator IPR.Definition.

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

(* Equal results have equal parts, read off without evaluating either side. *)
Lemma result_inj {T S : Type} (a b : T) (s t : S) : Result a s = Result b t -> a = b /\ s = t.
Proof.
  intro H. split;
    [ exact (f_equal (fun r => match r with Result x _ => x end) H)
    | exact (f_equal (fun r => match r with Result _ y => y end) H) ].
Qed.

(* Inverting [dexec] at a known program, without an axiom. *)
Section DexecInv.

  Context {Il Ir Ol Or : Type} (M : machine (Il + Ir) (Ol + Or)).

  Definition dexec_inv (T : Type) (p : dproc Il Ol T) (s : M.(state))
    : result T M.(state) -> Prop :=
    match p in dproc _ _ T0 return result T0 M.(state) -> Prop with
    | DCall i => fun r => exists s' o, M.(step) s (inl i) (Result (inl o) s') /\ r = Result o s'
    | DRet v => fun r => r = Result v s
    | DBind p1 p2 => fun r => exists v s', dexec M _ p1 s (Result v s') /\ dexec M _ (p2 v) s' r
    | DWhile g b => fun r =>
        (exists s' s'', dexec M _ g s (Result true s') /\ dexec M _ b s' (Result tt s'')
                        /\ dexec M _ (DWhile g b) s'' r)
        \/ (exists s', dexec M _ g s (Result false s') /\ r = Result tt s')
    | DChoose p1 p2 => fun r => dexec M _ p1 s r \/ dexec M _ p2 s r
    end.

  Lemma dexec_invert T p s r : dexec M T p s r -> dexec_inv T p s r.
  Proof. destruct 1; cbn; eauto 10. Qed.

End DexecInv.

(* List facts for the IPs' request histories. *)
Lemma seq_split {A} (f: nat -> A) a b :
  map f (seq 0 (a + b)) ++ [f (a + b)] = map f (seq 0 a) ++ f a :: map f (seq (S a) b).
Proof.
  change [f (a + b)] with (map f [0 + (a + b)]).
  rewrite <- map_app, <- seq_S. replace (S (a + b)) with (a + S b) by lia.
  rewrite seq_app, map_app. reflexivity.
Qed.

Lemma in_firstn_seq n a m j : In j (firstn n (seq a m)) -> a <= j < a + n.
Proof.
  revert a m. induction n as [| n IH]; intros a m H; [ destruct H |].
  destruct m as [| m]; [ destruct H |]. cbn [firstn seq In] in H.
  destruct H as [<- | H]; [ lia |]. specialize (IH (S a) m H). lia.
Qed.

Lemma existsb_find {A} (f: A -> bool) l :
  existsb f l = match find f l with Some _ => true | None => false end.
Proof. induction l as [| a l IH]; cbn; [ reflexivity |]. destruct (f a); [ reflexivity | exact IH ]. Qed.

Section Bridge.

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
  Local Notation circuit_state := (ContextEnv.(env_t) (R synth)).

  Local Notation s_sz := (tfs_spec_states_size ctx).
  Local Notation i_sz := (tfs_spec_inputs_size ctx).
  Local Notation o_sz := (tfs_spec_outputs_size ctx).
  Local Notation src_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation src_sys_state :=
    (ContextEnv.(env_t) (tf_states_type s_sz) * src_out_env)%type.
  Local Notation pub_inputs := (forall v, option (type_denote (tf_inputs_type i_sz v))).
  Local Notation pub_outputs := (forall o, option (type_denote (tf_outputs_type o_sz o))).
  Local Notation run act sp input :=
    (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act) sp input).

  Context (ip: trusted_ip ctx cost_limit enc_sz enc enc_inj names) (src: trusted_source ctx).
  Hypothesis Hip : datasheet ctx cost_limit enc_sz enc enc_inj names ip.

  Local Notation M1 := (closed_circuit ctx cost_limit enc_sz enc enc_inj names ip src).
  Local Notation M2 := (closed_spec ctx cost_limit src).
  Local Notation d := (IPRDefinitions.driver ctx cost_limit enc_sz enc enc_inj names).
  Local Notation close := (close ctx cost_limit enc_sz enc enc_inj names ip src).
  Local Notation takes := (takes ctx cost_limit enc_sz enc enc_inj names).
  Local Notation circuit_outputs := (circuit_outputs ctx cost_limit enc_sz enc enc_inj names).
  Local Notation atk_out_of := (atk_out_of ctx cost_limit enc_sz enc enc_inj names).
  Local Notation atk_in_of := (atk_in_of ctx cost_limit enc_sz enc enc_inj names).
  Local Notation circuit_run := (circuit_run ctx cost_limit enc_sz enc enc_inj names).
  Local Notation at_rest := (at_rest ctx cost_limit enc_sz enc enc_inj names).
  Local Notation port_inputs := (port_inputs ctx cost_limit enc_sz enc enc_inj names).
  Local Notation cmd_of := (CircuitProof.cmd_of ctx cost_limit enc_sz enc enc_inj names).
  Local Notation idle := (idle_wires ctx cost_limit enc_sz enc enc_inj names).
  Local Notation offer := (offer_wires ctx cost_limit enc_sz enc enc_inj names).
  Local Notation fill := (fill ctx).
  Local Notation cycle w c := (interp_cycle w (rules synth) (system_schedule synth) c).

  (* ------------------------------------------------------------------- *)
  (* The machines.                                                        *)
  (* ------------------------------------------------------------------- *)

  (* One cycle of M1, as a function. *)
  Definition cstep (s: state M1) (w: wires) : state M1 :=
    (cycle (close (fst (fst s)) (snd (fst s)) (snd s) w) (fst (fst s)),
     fun p => snd (fst s) p ++ [(fst (fst s)).[tf_reg (tfs_drive_reg tsched p)]],
     if takes (fst (fst s)) w then snd s ++ [circuit_outputs (fst (fst s))] else snd s).

  Lemma M1_step s w :
    step M1 s w (Result (atk_out_of (fst (fst s)) (fst (fst (cstep s w)))) (cstep s w)).
  Proof. destruct s as [[c hs] seen]. reflexivity. Qed.

  Lemma M1_step_inv s w o s' :
    step M1 s w (Result o s') -> s' = cstep s w /\ o = atk_out_of (fst (fst s)) (fst (fst (cstep s w))).
  Proof.
    destruct s as [[c hs] seen]. intro H.
    destruct (result_inj _ _ _ _ H) as [-> ->]. split; reflexivity.
  Qed.

  (* Replaces a known step of M1 by the cycle it is. *)
  Ltac m1_step :=
    match goal with H : step M1 _ _ _ |- _ => apply M1_step_inv in H; destruct H as [-> ->] end.

  Lemma M1_total : total M1.
  Proof. intros s w. eexists. exact (M1_step s w). Qed.

  Lemma M2_deterministic : deterministic M2.
  Proof.
    intros [sp seen] q r1 r2 H1 H2. hnf in H1, H2. rewrite H1, H2. reflexivity.
  Qed.

  Lemma M1_resets : resets_to_init M1.
  Proof. intros s s'. split; intro H; exact H. Qed.

  Lemma M2_resets : resets_to_init M2.
  Proof. intros s s'. split; intro H; exact H. Qed.

  (* M1 from [s] on attacker wires [ws], and the wires its cycles see. *)
  Fixpoint crun (s: state M1) (ws: nat -> wires) (n: nat) : state M1 :=
    match n with 0 => s | S k => cstep (crun s ws k) (ws k) end.

  Definition cenv (s: state M1) (ws: nat -> wires) (k: nat) : wires :=
    close (fst (fst (crun s ws k))) (snd (fst (crun s ws k))) (snd (crun s ws k)) (ws k).

  Lemma crun_circuit s ws n : fst (fst (crun s ws n)) = circuit_run (fst (fst s)) (cenv s ws) n.
  Proof.
    induction n as [| n IH]; [ reflexivity |].
    change (circuit_run (fst (fst s)) (cenv s ws) (S n))
      with (cycle (cenv s ws n) (circuit_run (fst (fst s)) (cenv s ws) n)).
    rewrite <- IH. reflexivity.
  Qed.

  Lemma crun_hist s ws n p :
    snd (fst (crun s ws n)) p
    = snd (fst s) p
      ++ map (fun j => (circuit_run (fst (fst s)) (cenv s ws) j).[tf_reg (tfs_drive_reg tsched p)])
             (seq 0 n).
  Proof.
    induction n as [| n IH]; [ cbn [crun seq map]; rewrite app_nil_r; reflexivity |].
    change (snd (fst (crun s ws (S n))) p)
      with (snd (fst (crun s ws n)) p ++ [(fst (fst (crun s ws n))).[tf_reg (tfs_drive_reg tsched p)]]).
    rewrite IH, crun_circuit, seq_S, map_app, <- app_assoc. reflexivity.
  Qed.

  (* AN IP THAT MEETS ITS DATASHEET answers every run as the circuit expects. *)
  Lemma cenv_contract s ws : ip_contract ctx cost_limit enc_sz enc enc_inj names (fst (fst s)) (cenv s ws).
  Proof.
    intros p s0. cbv zeta. intros Hs Hq.
    set (lat := pred (ip_lat (tfs_ip tsched p))) in *.
    set (req := fun j => (circuit_run (fst (fst s)) (cenv s ws) j).[tf_reg (tfs_drive_reg tsched p)]).
    change (cenv s ws (s0 + lat) (ext_input (inr p)) Ob~1)
      with (ip p (snd (fst (crun s ws (s0 + lat))) p
                  ++ [(fst (fst (crun s ws (s0 + lat)))).[tf_reg (tfs_drive_reg tsched p)]])).
    rewrite crun_hist, crun_circuit. fold req.
    change ((circuit_run (fst (fst s)) (cenv s ws) (s0 + lat)).[tf_reg (tfs_drive_reg tsched p)])
      with (req (s0 + lat)).
    rewrite <- app_assoc, seq_split, app_assoc.
    apply Hip.
    - exact Hs.
    - rewrite map_length, seq_length. reflexivity.
    - intros q Hin. rewrite firstn_map in Hin. apply in_map_iff in Hin.
      destruct Hin as [j [<- Hj]]. apply in_firstn_seq in Hj.
      apply Hq. unfold lat in *. lia.
  Qed.

  (* The emulator reads the public ports as the circuit does. *)
  Lemma cenv_pv s ws k v :
    mask_in ctx (port_inputs (ws k)) v = mask_in ctx (port_inputs (cenv s ws k)) v.
  Proof.
    unfold mask_in, port_inputs, cenv, IPRDefinitions.close. cbv beta iota.
    destruct (tfs_spec_inputs_class ctx v); reflexivity.
  Qed.

  (* A cycle's inputs: the attacker's public ones, the source's secure ones. *)
  Lemma cenv_inputs s ws k v :
    port_inputs (cenv s ws k) v
    = fill (mask_in ctx (port_inputs (ws k))) (src (snd (crun s ws k) ++ [circuit_outputs (fst (fst (crun s ws k)))])) v.
  Proof.
    unfold port_inputs, cenv, IPRDefinitions.close, IPRDefinitions.fill, mask_in. cbv beta iota.
    destruct (tfs_spec_inputs_class ctx v); reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* Cycles that take no command, and the one that takes it.             *)
  (* ------------------------------------------------------------------- *)

  Lemma rest_outputs (c: circuit_state) (sp: src_sys_state) : at_rest c sp -> circuit_outputs c = snd sp.
  Proof.
    intros [_ [Hout _]]. apply equiv_eq. intro o.
    unfold IPRDefinitions.circuit_outputs. rewrite getenv_create. exact (Hout o).
  Qed.

  (* A cycle offering nothing keeps the circuit at rest, showing ready and its outputs. *)
  Lemma idle_rest (c: circuit_state) (sp: src_sys_state) (w: wires) :
    fst (w ext_in_cmd Ob~1) = Ob~0 -> at_rest c sp ->
    at_rest (cycle w c) sp /\ atk_out_of c (cycle w c) = (Ob~1, mask_out ctx (snd sp)).
  Proof.
    intros Hw Hr.
    assert (Hid : forall x, match x with tf_out_ack _ | tf_ip_ack _ => False | _ => True end ->
                    (cycle w c).[x] = c.[x]).
    { intros x Hx. apply (SynthesisProof.cycle_idle synth c w x (proj1 Hr)); [| exact Hx ].
      intro a. left. exact Hw. }
    destruct Hr as [Hrdy [Hout Hreg]].
    assert (Houts : circuit_outputs (cycle w c) = snd sp).
    { apply equiv_eq. intro o. unfold IPRDefinitions.circuit_outputs. rewrite getenv_create.
      rewrite Hid by exact I. exact (Hout o). }
    split.
    - split; [ rewrite Hid by exact I; exact Hrdy | split ].
      + intro o. rewrite Hid by exact I. exact (Hout o).
      + intro x. specialize (Hreg x). destruct x; cbv iota in *; try exact I;
          rewrite Hid by exact I; exact Hreg.
    - unfold IPRDefinitions.atk_out_of. rewrite Hrdy, Houts. reflexivity.
  Qed.

  Lemma takes_idle (c: circuit_state) (w: wires) : fst (w ext_in_cmd Ob~1) = Ob~0 -> takes c w = false.
  Proof.
    intro H. unfold IPRDefinitions.takes. cbv zeta. rewrite H.
    destruct (Bits.single (c.[tf_ready])); reflexivity.
  Qed.

  Lemma existsb_enc act :
    existsb (fun a => beq_dec (enc a) (enc act)) (@finite_elements _ (tfs_action_fin sched)) = true.
  Proof.
    apply existsb_exists. exists act. split.
    - apply nth_error_In with (finite_index act). apply finite_surjective.
    - apply beq_dec_iff. reflexivity.
  Qed.

  Lemma takes_offer (c: circuit_state) act pin : c.[tf_ready] = Ob~1 -> takes c (offer act pin) = true.
  Proof. intro H. unfold IPRDefinitions.takes. cbv zeta. rewrite H. exact (existsb_enc act). Qed.

  (* M1 takes a command just when the emulator, ready, decodes one. *)
  Lemma takes_iff (c: circuit_state) (w: wires) (e: CircuitProof.em ctx) :
    (c.[tf_ready] = Ob~1 <-> CircuitProof.em_ready e = true) ->
    takes c w = if CircuitProof.em_ready e
                then match cmd_of w with Some _ => true | None => false end
                else false.
  Proof.
    intro Hiff. unfold IPRDefinitions.takes, CircuitProof.cmd_of, CircuitProof.decode. cbv zeta.
    rewrite existsb_find.
    destruct (CircuitProof.em_ready e) eqn:Er.
    - rewrite (proj2 Hiff eq_refl). cbn [Bits.single andb].
      destruct (Bits.single (fst (w ext_in_cmd Ob~1))); [| reflexivity ].
      destruct (find _ _); reflexivity.
    - destruct (CircuitProof.bits1_cases (c.[tf_ready])) as [H0 | H1];
        [| exfalso; pose proof (proj1 Hiff H1) as E; congruence ].
      rewrite H0. reflexivity.
  Qed.

  (* Wires agreeing on [in_cmd] offer the same command, with their own inputs. *)
  Lemma cmd_of_same (w wp: wires) :
    w ext_in_cmd = wp ext_in_cmd ->
    cmd_of wp = match cmd_of w with Some (a, _) => Some (a, port_inputs wp) | None => None end.
  Proof.
    intro H. unfold CircuitProof.cmd_of. cbv zeta. rewrite H.
    destruct (Bits.single _); [| reflexivity ].
    destruct (CircuitProof.decode _ _ _ _ _); reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The functional half, through the driver.                             *)
  (* ------------------------------------------------------------------- *)

  (* Between operations, the circuit rests at the spec's state, and the source has
     been shown the same outputs on both sides. *)
  Definition Rel (s1: state M1) (s2: state M2) : Prop :=
    at_rest (fst (fst s1)) (fst s2) /\ snd s1 = snd s2.

  (* The driver's wait loop guard: one idle cycle, reporting ready. *)
  Local Notation wait_guard :=
    (DBind (DCall idle) (fun o : atk_out ctx => DRet (negb (Bits.single (fst o))))).

  Lemma guard_exec s :
    dexec (mux M1) _ wait_guard s
      (Result (negb (Bits.single ((fst (fst s)).[tf_ready]))) (cstep s idle)).
  Proof.
    eapply DexecBind.
    - apply DexecCall. exact (MuxStepL _ _ M1 _ _ _ _ (M1_step s idle)).
    - apply DexecRet.
  Qed.

  Lemma guard_inv s r :
    dexec (mux M1) _ wait_guard s r ->
    r = Result (negb (Bits.single ((fst (fst s)).[tf_ready]))) (cstep s idle).
  Proof.
    intro H. apply dexec_invert in H. destruct H as (v & s' & Hc & Hr).
    apply dexec_invert in Hc. destruct Hc as (s'' & o & Hs & Hv).
    destruct (result_inj _ _ _ _ Hv) as [Hv1 Hv2]; subst.
    inversion Hs; subst. m1_step.
    apply dexec_invert in Hr. exact Hr.
  Qed.

  Section Command.

    Variables (s: state M1) (sp: src_sys_state) (act: tfs_action sched) (pin: pub_inputs).
    Hypothesis Hrest : at_rest (fst (fst s)) sp.

    (* The driver's wires for [Run act pin]: the offer, then idle cycles. *)
    Definition cws (j: nat) : wires := match j with 0 => offer act pin | S _ => idle end.
    Local Notation s_ j := (crun s cws j).
    Local Notation c_ j := (fst (fst (crun s cws j))).
    Local Notation sp' := (run act sp (fill pin (src (snd s ++ [snd sp])))).

    Lemma offer_inputs v : port_inputs (cenv s cws 0) v = fill pin (src (snd s ++ [snd sp])) v.
    Proof.
      rewrite cenv_inputs. cbn [crun]. rewrite (rest_outputs _ _ Hrest).
      unfold port_inputs, cws, IPRDefinitions.offer_wires. cbv beta iota.
      unfold IPRDefinitions.fill, mask_in. destruct (tfs_spec_inputs_class ctx v); reflexivity.
    Qed.

    Lemma command_run :
      exists N, 0 < N /\ (forall j, 0 < j < N -> (c_ j).[tf_ready] = Ob~0) /\ at_rest (c_ N) sp'.
    Proof.
      destruct (CircuitProof.functional_here ctx cost_limit enc_sz enc enc_inj names
                  (fst (fst s)) sp (cenv s cws) (fun k => mask_in ctx (port_inputs (cws k)))
                  Hrest (cenv_contract s cws) act (port_inputs (cenv s cws 0)))
        as (N & HN0 & Hmid & HN).
      { split; [ reflexivity | split; [ reflexivity | intro v; reflexivity ] ]. }
      rewrite (CircuitProof.ops_run_inputs_ext _ _ _ _ _ _ _ _ offer_inputs) in HN.
      exists N. split; [ exact HN0 | split ].
      - intros j Hj. rewrite crun_circuit. exact (Hmid j Hj).
      - rewrite crun_circuit. exact HN.
    Qed.

    (* The source is shown the outputs once, when the command is taken. *)
    Lemma crun_seen m : snd (s_ (S m)) = snd s ++ [circuit_outputs (fst (fst s))].
    Proof.
      induction m as [| m IH].
      - change (snd (s_ 1))
          with (if takes (fst (fst s)) (offer act pin)
                then snd s ++ [circuit_outputs (fst (fst s))] else snd s).
        rewrite (takes_offer _ act pin (proj1 Hrest)). reflexivity.
      - change (snd (s_ (S (S m))))
          with (if takes (c_ (S m)) idle
                then snd (s_ (S m)) ++ [circuit_outputs (c_ (S m))] else snd (s_ (S m))).
        rewrite (takes_idle _ idle eq_refl). exact IH.
    Qed.

    Variable N : nat.
    Hypothesis HN0 : 0 < N.
    Hypothesis Hmid : forall j, 0 < j < N -> (c_ j).[tf_ready] = Ob~0.
    Hypothesis HN : at_rest (c_ N) sp'.

    Lemma rest_after m : at_rest (c_ (N + m)) sp'.
    Proof.
      induction m as [| m IH]; [ rewrite Nat.add_0_r; exact HN |].
      rewrite Nat.add_succ_r.
      assert (Hw : cws (N + m) = idle) by (destruct N; [ lia | reflexivity ]).
      change (c_ (S (N + m)))
        with (cycle (close (c_ (N + m)) (snd (fst (s_ (N + m)))) (snd (s_ (N + m))) (cws (N + m)))
                    (c_ (N + m))).
      rewrite Hw.
      exact (proj1 (idle_rest _ _ (close (c_ (N + m)) (snd (fst (s_ (N + m)))) (snd (s_ (N + m))) idle)
                      eq_refl IH)).
    Qed.

    Lemma loop_exec m j :
      j + m = N -> 1 <= j ->
      dexec (mux M1) _ (DWhile wait_guard (DRet tt)) (s_ j) (Result tt (s_ (S N))).
    Proof.
      revert j. induction m as [| m IH]; intros j Hjm Hj.
      - rewrite Nat.add_0_r in Hjm. subst j.
        pose proof (guard_exec (s_ N)) as Hg.
        rewrite (proj1 HN) in Hg.
        apply DexecWhileFalse.
        destruct N as [| N']; [ lia |]. exact Hg.
      - destruct j as [| j']; [ lia |].
        pose proof (guard_exec (s_ (S j'))) as Hg.
        rewrite (Hmid (S j') ltac:(lia)) in Hg.
        eapply DexecWhileTrue; [ exact Hg | apply DexecRet |].
        exact (IH (S (S j')) ltac:(lia) ltac:(lia)).
    Qed.

    Lemma loop_inv m j r :
      j + m = N -> 1 <= j ->
      dexec (mux M1) _ (DWhile wait_guard (DRet tt)) (s_ j) r -> r = Result tt (s_ (S N)).
    Proof.
      revert j r. induction m as [| m IH]; intros j r Hjm Hj H;
        apply dexec_invert in H;
        destruct H as [ (s1 & s2 & Hg & Hb & Hw) | (s1 & Hg & Hr) ];
        apply guard_inv in Hg; destruct (result_inj _ _ _ _ Hg) as [Hbool Hs1].
      - rewrite Nat.add_0_r in Hjm. subst j. rewrite (proj1 HN) in Hbool. discriminate.
      - rewrite Nat.add_0_r in Hjm. subst j r s1. destruct N; [ lia | reflexivity ].
      - destruct j as [| j']; [ lia |].
        apply dexec_invert in Hb. destruct (result_inj _ _ _ _ Hb) as [_ Hs2]. subst s2 s1.
        exact (IH (S (S j')) r ltac:(lia) ltac:(lia) Hw).
      - destruct j as [| j']; [ lia |].
        rewrite (Hmid (S j') ltac:(lia)) in Hbool. discriminate.
    Qed.

  End Command.

  Lemma bridge_functional : IPRStrategy.functional_simulation _ _ _ _ M1 d M2 Rel.
  Proof.
    split; [ split; [ exact (CircuitProof.reset_at_rest ctx cost_limit enc_sz enc enc_inj names)
                    | reflexivity ] |].
    split.
    - (* the driver terminates *)
      intros s1 [sp seen] [| act pin] [Hr Hseen].
      + eexists _, _. eapply DexecBind.
        * apply DexecCall. exact (MuxStepL _ _ M1 _ _ _ _ (M1_step s1 idle)).
        * apply DexecRet.
      + destruct (command_run s1 sp act pin Hr) as (N & HN0 & Hmid & HN).
        eexists _, _. eapply DexecBind.
        * apply DexecCall. exact (MuxStepL _ _ M1 _ _ _ _ (M1_step s1 (offer act pin))).
        * cbv beta. eapply DexecBind.
          -- exact (loop_exec s1 sp act pin N HN0 Hmid HN (pred N) 1 ltac:(lia) ltac:(lia)).
          -- cbv beta. eapply DexecBind.
             ++ apply DexecCall. exact (MuxStepL _ _ M1 _ _ _ _ (M1_step _ idle)).
             ++ apply DexecRet.
    - (* what the driver returns is what the spec answers *)
      intros s1 [sp seen] [| act pin] o s1' [Hr Hseen] H; cbn [fst snd] in Hr, Hseen; subst seen.
      + apply dexec_invert in H. destruct H as (v & s3 & Hc & Hret).
        apply dexec_invert in Hc. destruct Hc as (s4 & o4 & Hs & Hv).
        destruct (result_inj _ _ _ _ Hv) as [Hv1 Hv2]; subst.
        inversion Hs; subst. m1_step.
        apply dexec_invert in Hret. destruct (result_inj _ _ _ _ Hret) as [Hr1 Hr2]; subst.
        destruct (idle_rest (fst (fst s1)) sp (close (fst (fst s1)) (snd (fst s1)) (snd s1) idle)
                    eq_refl Hr) as [Hr' Hout].
        exists (sp, snd s1). split.
        * hnf.
          change (atk_out_of (fst (fst s1)) (fst (fst (cstep s1 idle))) = (Ob~1, mask_out ctx (snd sp)))
            in Hout.
          rewrite Hout. reflexivity.
        * split; [ exact Hr' |].
          change ((if takes (fst (fst s1)) idle
                   then snd s1 ++ [circuit_outputs (fst (fst s1))] else snd s1) = snd s1).
          rewrite (takes_idle _ idle eq_refl). reflexivity.
      + destruct (command_run s1 sp act pin Hr) as (N & HN0 & Hmid & HN).
        apply dexec_invert in H. destruct H as (v & s3 & Hc & Hrest1).
        apply dexec_invert in Hc. destruct Hc as (s4 & o4 & Hs & Hv).
        destruct (result_inj _ _ _ _ Hv) as [Hv1 Hv2]; subst.
        inversion Hs; subst. m1_step.
        apply dexec_invert in Hrest1. destruct Hrest1 as (v' & s5 & Hloop & Hfin).
        pose proof (loop_inv s1 sp act pin N HN0 Hmid HN (pred N) 1 _ ltac:(lia) ltac:(lia) Hloop)
          as E. destruct (result_inj _ _ _ _ E) as [E1 E2]; subst.
        apply dexec_invert in Hfin. destruct Hfin as (v'' & s6 & Hc2 & Hret).
        apply dexec_invert in Hc2. destruct Hc2 as (s7 & o7 & Hs7 & Hv7).
        destruct (result_inj _ _ _ _ Hv7) as [Hv1 Hv2]; subst.
        inversion Hs7; subst. m1_step.
        apply dexec_invert in Hret. destruct (result_inj _ _ _ _ Hret) as [Hr1 Hr2]; subst.
        pose proof (rest_after s1 sp act pin N HN0 Hmid HN 1) as HN1. rewrite Nat.add_1_r in HN1.
        destruct (idle_rest _ _ (close (fst (fst (crun s1 (cws act pin) (S N))))
                                       (snd (fst (crun s1 (cws act pin) (S N))))
                                       (snd (crun s1 (cws act pin) (S N))) idle) eq_refl HN1)
          as [Hr2 Hout].
        exists (run act sp (fill pin (src (snd s1 ++ [snd sp]))), snd s1 ++ [snd sp]). split.
        * hnf.
          change (atk_out_of (fst (fst (crun s1 (cws act pin) (S N))))
                             (fst (fst (cstep (crun s1 (cws act pin) (S N)) idle)))
                  = (Ob~1, mask_out ctx (snd (run act sp (fill pin (src (snd s1 ++ [snd sp]))))))) in Hout.
          rewrite Hout. reflexivity.
        * split; [ exact Hr2 |].
          change (snd (crun s1 (cws act pin) (S (S N))) = snd s1 ++ [snd sp]).
          rewrite (crun_seen s1 sp act pin Hr (S N)), (rest_outputs _ _ Hr). reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The physical half: the emulator's run is an ideal-world execution.  *)
  (* ------------------------------------------------------------------- *)

  (* THE EMULATOR, on the attacker's wires: it reads [in_cmd] and the public ports,
     and the spec only through its queries. *)
  Definition e_wires : emulator (query ctx cost_limit) pub_outputs wires (atk_out ctx) :=
    {| estate := option (CircuitProof.pe_state ctx);
       einit := None;
       estep := fun w => CircuitProof.pe_step ctx cost_limit enc_sz enc (atk_in_of w) |}.

  Local Notation dflt := (idle, (Ob~0, fun _ => None) : atk_out ctx).

  (* An execution of M1 from step [n] of a run on [ws] is that run, outputs included. *)
  Lemma execution_run io :
    forall s ws n s',
      (forall j, j < length io -> fst (nth j io dflt) = ws (n + j)) ->
      execution M1 (crun s ws n) (io_to_machine_trace _ _ io) s' ->
      s' = crun s ws (n + length io)
      /\ forall j, j < length io ->
           snd (nth j io dflt)
           = atk_out_of (fst (fst (crun s ws (n + j)))) (fst (fst (crun s ws (S (n + j))))).
  Proof.
    induction io as [| [w o] io IH]; intros s ws n s' Henv H.
    - cbn [io_to_machine_trace map] in H. inversion H; subst.
      split; [ rewrite Nat.add_0_r; reflexivity | cbn; lia ].
    - pose proof (Henv 0 ltac:(simpl length in *; lia)) as Hw. cbn [nth fst] in Hw.
      rewrite Nat.add_0_r in Hw. subst w.
      cbn [io_to_machine_trace map] in H. inversion H; subst. m1_step.
      match goal with He : execution M1 _ _ _ |- _ =>
        change (cstep (crun s ws n) (ws n)) with (crun s ws (S n)) in He;
        destruct (IH s ws (S n) s') as [Hend Hk]; [| exact He |] end.
      { intros j Hj. pose proof (Henv (S j) ltac:(simpl length in *; lia)) as E. cbn [nth] in E.
        rewrite E. f_equal. lia. }
      split.
      + rewrite Hend. f_equal. cbn [length]. lia.
      + intros [| j] Hj.
        * cbn [nth snd]. rewrite Nat.add_0_r. reflexivity.
        * cbn [nth]. rewrite (Hk j ltac:(simpl length in *; lia)).
          replace (n + S j) with (S n + j) by lia. reflexivity.
  Qed.

  Section Ideal.

    Variable st : nat -> state (mux M2) * estate e_wires.

    Lemma ideal_low io k :
      (forall j, j < length io ->
         eexec (mux M2) _ (estep e_wires (fst (nth j io dflt)))
           (st (k + j)) (Result (snd (nth j io dflt)) (st (S (k + j))))) ->
      execution (ideal_world M2 e_wires) (EmulatorLow (fst (st k)) (snd (st k)))
        (io_to_ideal_machine_trace _ _ _ _ io)
        (EmulatorLow (fst (st (k + length io))) (snd (st (k + length io)))).
    Proof.
      revert k. induction io as [| [w o] io IH]; intros k Hst.
      - rewrite Nat.add_0_r. apply ExecutionEmpty.
      - apply ExecutionStep with (s' := EmulatorLow (fst (st (S k))) (snd (st (S k)))).
        + hnf. apply EmulatorStepLowLow.
          pose proof (Hst 0 ltac:(simpl length in *; lia)) as H0. rewrite Nat.add_0_r in H0.
          cbn [nth fst snd] in H0. rewrite <- !surjective_pairing. exact H0.
        + change (length ((w, o) :: io)) with (S (length io)).
          replace (k + S (length io)) with (S k + length io) by lia.
          apply IH. intros j Hj. pose proof (Hst (S j) ltac:(simpl length in *; lia)) as H.
          replace (k + S j) with (S k + j) in H by lia. exact H.
    Qed.

  End Ideal.

  Section Physical.

    Variables (s: state M1) (sp: src_sys_state) (ws: nat -> wires).
    Hypothesis Hrest : at_rest (fst (fst s)) sp.

    Local Notation env := (cenv s ws).
    Local Notation pv := (fun k => mask_in ctx (port_inputs (ws k))).
    Local Notation ideal k :=
      (CircuitProof.ideal_run ctx cost_limit sp (fun i => cmd_of (env i)) pv k).
    Local Notation c_ k := (circuit_run (fst (fst s)) env k).
    Local Notation mask_em := (CircuitProof.mask_em ctx).

    (* The ideal world beside the run: the spec as the cycle-level model has it,
       the outputs the source was shown, and the emulator's state. *)
    Definition est (k: nat) : state (mux M2) * estate e_wires :=
      ((fst (ideal k), snd (crun s ws k)),
       match k with 0 => None | S _ => Some (mask_em (snd (ideal k))) end).

    Local Notation emulated := (CircuitProof.circuit_emulated ctx cost_limit enc_sz enc enc_inj names
                                  (fst (fst s)) sp env pv Hrest (cenv_contract s ws) (cenv_pv s ws)).

    Lemma tick_mask (sp1: src_sys_state) e : CircuitProof.pe_tick ctx (mask_em e) = mask_em (snd (sp1, CircuitProof.em_tick e)).
    Proof. reflexivity. Qed.

    (* EVERY CYCLE of the emulator, beside the spec, shows what the circuit shows. *)
    Lemma est_step k :
      eexec (mux M2) _ (estep e_wires (ws k)) (est k)
        (Result (atk_out_of (c_ k) (c_ (S k))) (est (S k))).
    Proof.
      assert (Hst : snd (est k) = Some (mask_em (snd (ideal k)))
                    \/ (snd (est k) = None
                        /\ mask_em (snd (ideal k))
                           = (mask_out ctx (snd (fst (ideal k))), mask_out ctx (snd (fst (ideal k))), 0)))
        by (destruct k; [ right; split; reflexivity | left; reflexivity ]).
      pose proof (CircuitProof.pe_step_exec ctx cost_limit enc_sz enc src (atk_in_of (ws k))
                    (fst (ideal k)) (snd (crun s ws k)) (mask_em (snd (ideal k))) (snd (est k)) Hst)
        as H.
      match type of H with eexec _ _ _ _ ?R =>
        replace (Result (atk_out_of (c_ k) (c_ (S k))) (est (S k))) with R; [ exact H |] end.
      rewrite CircuitProof.pe_takes_mask.
      change (est (S k)) with ((fst (ideal (S k)), snd (crun s ws (S k))),
                               Some (mask_em (snd (ideal (S k))))).
      change (snd (crun s ws (S k)))
        with (if takes (fst (fst (crun s ws k))) (ws k)
              then snd (crun s ws k) ++ [circuit_outputs (fst (fst (crun s ws k)))]
              else snd (crun s ws k)).
      rewrite !crun_circuit.
      pose proof (emulated k) as Hk. cbv zeta in Hk. destruct Hk as [Hiff _].
      rewrite (takes_iff _ (ws k) _ Hiff).
      pose proof (CircuitProof.ready_outputs ctx cost_limit enc_sz enc enc_inj names
                    (fst (fst s)) sp env pv Hrest (cenv_contract s ws) (cenv_pv s ws) k) as Hout.
      pose proof (CircuitProof.pe_ready_mask ctx cost_limit enc_sz enc enc_inj names
                    (fst (fst s)) sp env pv Hrest (cenv_contract s ws) (cenv_pv s ws)
                    (snd (ideal k)) k eq_refl) as Hready.
      pose proof (fun e => CircuitProof.pe_shown_mask ctx cost_limit enc_sz enc enc_inj names
                    (fst (fst s)) sp env pv Hrest (cenv_contract s ws) (cenv_pv s ws) e (S k)) as Hshown.
      cbn [CircuitProof.ideal_run] in Hshown |- *.
      rewrite (cmd_of_same (ws k) (env k) eq_refl) in Hshown |- *.
      destruct (ideal k) as [spk ek] eqn:Hk. cbn [fst snd] in Hout, Hready, Hshown |- *.
      rewrite Hready.
      destruct (CircuitProof.em_ready ek) eqn:Er;
        [ destruct (cmd_of (ws k)) as [[act inp] |] eqn:Hc |
          destruct (cmd_of (ws k)) as [[act inp] |] eqn:Hc ];
        cbv beta iota zeta in Hshown |- *.
      - (* a command is taken *)
        destruct (CircuitProof.cmd_of_some _ _ _ _ _ _ _ _ _ Hc) as [_ [_ ->]].
        specialize (Hout eq_refl).
        assert (Hin : forall v, port_inputs (env k) v
                       = fill (mask_in ctx (port_inputs (ws k))) (src (snd (crun s ws k) ++ [snd spk])) v)
          by (intro v; rewrite cenv_inputs, crun_circuit, Hout; reflexivity).
        rewrite <- (CircuitProof.ops_run_inputs_ext _ _ _ _ _ _ _ _ Hin).
        rewrite Hout.
        assert (Hafter :
          CircuitProof.pe_after ctx cost_limit (mask_em ek) act (mask_in ctx (port_inputs (ws k)))
            (mask_out ctx (snd (run act spk (port_inputs (env k)))))
          = mask_em (snd (run act spk (port_inputs (env k)),
                          CircuitProof.em_take ctx cost_limit ek act (mask_in ctx (port_inputs (ws k)))
                            (snd (run act spk (port_inputs (env k))))))) by reflexivity.
        rewrite Hafter, (Hshown _ eq_refl). reflexivity.
      (* idle at a ready cycle, or busy *)
      - rewrite (tick_mask spk ek), (Hshown _ eq_refl). reflexivity.
      - rewrite (tick_mask spk ek), (Hshown _ eq_refl). reflexivity.
      - rewrite (tick_mask spk ek), (Hshown _ eq_refl). reflexivity.
    Qed.

  End Physical.

  Lemma bridge_physical : IPRStrategy.physical_simulation _ _ _ _ M1 M2 Rel.
  Proof.
    exists e_wires.
    intros s1 [sp seen] w o io s1' [Hr Hseen] Hexec. cbn [fst snd] in Hr, Hseen. subst seen.
    set (io' := (w, o) :: io) in *.
    set (ws := fun k => fst (nth k io' dflt)).
    change s1 with (crun s1 ws 0) in Hexec.
    destruct (execution_run io' s1 ws 0 s1' (fun j _ => eq_refl) Hexec) as [Hend Hk].
    pose (st := est s1 sp ws).
    assert (Hstep : forall j, j < length io' ->
              eexec (mux M2) _ (estep e_wires (fst (nth j io' dflt)))
                (st j) (Result (snd (nth j io' dflt)) (st (S j)))).
    { intros j Hj. rewrite (Hk j Hj), !crun_circuit. exact (est_step s1 sp ws Hr j). }
    exists (fst (st (length io'))), (snd (st (length io'))).
    apply ExecutionStep with (s' := EmulatorLow (fst (st 1)) (snd (st 1))).
    - hnf. apply EmulatorStepHighLow.
      pose proof (Hstep 0 ltac:(simpl length in *; lia)) as H0. cbn [nth fst snd] in H0.
      rewrite <- surjective_pairing. exact H0.
    - change (length io') with (1 + length io).
      apply (ideal_low st io 1). intros j Hj.
      exact (Hstep (S j) ltac:(simpl length in *; lia)).
  Qed.

  (* IPR, AS UPSTREAM DEFINES IT, for the closed circuit, the closed spec, and the driver. *)
  Theorem ipr_holds : IPR M1 M2 d.
  Proof.
    apply (IPR_by_simulation _ _ _ _ M1 d M2 Rel).
    - exact M1_total.
    - exact M2_deterministic.
    - exact M1_resets.
    - exact M2_resets.
    - exact bridge_functional.
    - exact bridge_physical.
  Qed.

End Bridge.
