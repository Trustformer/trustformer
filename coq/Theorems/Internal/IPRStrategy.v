(*! IPR from a functional and a physical simulation, when a reset sends both machines
    to their initial states.  Adapted from ProofStrategy/Simulation.v of
    anishathalye/ipr, whose physical half cannot hold for the empty trace. !*)

Require Import IPR.Common.
Require Import IPR.Machine.
Require Import IPR.Driver.
Require Import IPR.Emulator.
Require Import IPR.Definition.

Require Import Coq.Lists.List.
Import ListNotations.

Section Strategy.

  Variable I1 O1 I2 O2 : Type.
  Variable M1 : machine I1 O1.
  Variable d : driver I1 O1 I2 O2.
  Variable M2 : machine I2 O2.

  (* Holds between the two machines in between spec-level operations. *)
  Variable R : M1.(state) -> M2.(state) -> Prop.

  Definition resets_to_init {I O : Type} (M : machine I O) : Prop :=
    forall s s', M.(reset) s s' <-> s' = M.(init).

  (* Upstream's functional simulation, less "R survives a reset": a reset lands in
     the initial states, which R relates. *)
  Definition functional_simulation : Prop :=
    R M1.(init) M2.(init) /\
      (forall s1 s2 i2,
          R s1 s2 ->
          exists o2 s1', dexec (mux M1) _ (d i2) s1 (Result o2 s1')) /\
      (forall s1 s2 i2 o2 s1',
          R s1 s2 ->
          dexec (mux M1) _ (d i2) s1 (Result o2 s1') ->
          exists s2', M2.(step) s2 i2 (Result o2 s2') /\ R s1' s2').

  Definition io_to_machine_trace (io : list (I1 * O1)) : trace I1 O1 :=
    map (fun '(i, o) => IO i o) io.

  Definition io_to_ideal_machine_trace (io : list (I1 * O1)) :
    trace (I2 + I1) (O2 + O1) :=
    map (fun '(i, o) => IO (inr i) (inr o)) io.

  (* Upstream's physical simulation over non-empty traces, and without its reset
     clause, which a reset to the initial states makes unnecessary. *)
  Definition physical_simulation : Prop :=
    exists (e : emulator I2 O2 I1 O1),
    forall s1 s2 i o io s1',
      R s1 s2 ->
      execution M1 s1 (io_to_machine_trace ((i, o) :: io)) s1' ->
      exists s2' e2',
        execution (ideal_world M2 e) (EmulatorHigh s2)
          (io_to_ideal_machine_trace ((i, o) :: io)) (EmulatorLow s2' e2').

  Definition lifted_R (e : emulator I2 O2 I1 O1)
      (ds1 : driver_state M1.(state)) (es2 : emulator_state M2.(state) e.(estate)) : Prop :=
    match ds1, es2 with
    | DriverHigh s1, EmulatorHigh s2 => R s1 s2
    | DriverLow s1, EmulatorLow s2 e2 =>
        forall io s1',
          execution M1 s1 (io_to_machine_trace io) s1' ->
          exists s2' e2',
            execution (ideal_world M2 e) (EmulatorLow s2 e2)
              (io_to_ideal_machine_trace io) (EmulatorLow s2' e2')
    | _, _ => False
    end.

  (* Inverting [eexec] at a known program, without upstream's [dependent
     induction] and the axiom it brings. *)
  Definition eexec_inv {S : Type} (T : Type) (p : eproc S I2 O2 T) (s : M2.(state) * S)
    : result T (M2.(state) * S) -> Prop :=
    match p in eproc _ _ _ T0 return result T0 (M2.(state) * S) -> Prop with
    | ECall i => fun r =>
        exists ms' o, (mux M2).(step) (fst s) (inr i) (Result (inr o) ms')
                    /\ r = Result o (ms', snd s)
    | EGet => fun r => r = Result (snd s) s
    | EPut es' => fun r => r = Result tt (fst s, es')
    | ERet v => fun r => r = Result v s
    | EBind p1 p2 => fun r =>
        exists v s', eexec (mux M2) _ p1 s (Result v s') /\ eexec (mux M2) _ (p2 v) s' r
    | EWhile g b => fun r =>
        (exists s' s'', eexec (mux M2) _ g s (Result true s')
                       /\ eexec (mux M2) _ b s' (Result tt s'')
                       /\ eexec (mux M2) _ (EWhile g b) s'' r)
        \/ (exists s', eexec (mux M2) _ g s (Result false s') /\ r = Result tt s')
    end.

  Lemma eexec_invert :
    forall (S T : Type) (p : eproc S I2 O2 T) s r,
      eexec (mux M2) T p s r -> eexec_inv T p s r.
  Proof. intros S T p s r H. destruct H; cbn; eauto 10. Qed.

  Lemma eexec_deterministic :
    forall (ES T : Type) (estep : eproc ES I2 O2 T) s2 res res',
      deterministic M2 ->
      eexec (mux M2) T estep s2 res ->
      eexec (mux M2) T estep s2 res' ->
      res = res'.
  Proof.
    intros ES T estep s2 res res' Hdet Hexec1. revert res'.
    induction Hexec1; intros res' Hexec2; apply eexec_invert in Hexec2; cbn in Hexec2.
    - destruct Hexec2 as (ms'' & o' & Hs & ->).
      inversion H; subst. inversion Hs; subst.
      match goal with
      | A : step M2 _ _ (Result ?a _), B : step M2 _ _ (Result ?b _) |- _ =>
          pose proof (Hdet _ _ _ _ A B) as E
      end.
      inversion E; subst. reflexivity.
    - symmetry. exact Hexec2.
    - symmetry. exact Hexec2.
    - symmetry. exact Hexec2.
    - destruct Hexec2 as (v' & s'' & H1 & H2).
      specialize (IHHexec1_1 _ H1). inversion IHHexec1_1; subst.
      exact (IHHexec1_2 _ H2).
    - destruct Hexec2 as [ (s1 & s1' & Hg & Hb & Hw) | (s1 & Hg & Hr) ].
      + specialize (IHHexec1_1 _ Hg). inversion IHHexec1_1; subst.
        specialize (IHHexec1_2 _ Hb). inversion IHHexec1_2; subst.
        exact (IHHexec1_3 _ Hw).
      + specialize (IHHexec1_1 _ Hg). discriminate.
    - destruct Hexec2 as [ (s1 & s1' & Hg & Hb & Hw) | (s1 & Hg & Hr) ].
      + specialize (IHHexec1 _ Hg). discriminate.
      + specialize (IHHexec1 _ Hg). inversion IHHexec1; subst. reflexivity.
  Qed.

  Section WithEmulator.

    Variable e : emulator I2 O2 I1 O1.
    Hypothesis Hdet2 : deterministic M2.

    Local Notation ideal := (ideal_world M2 e).

    (* A wire-level input moves the ideal world one way only. *)
    Lemma ideal_low_deterministic :
      forall st i1 r r',
        ideal.(step) st (inr i1) r -> ideal.(step) st (inr i1) r' -> r = r'.
    Proof.
      intros st i1 r r' H H'. cbn in H, H'.
      inversion H; subst; inversion H'; subst;
        lazymatch goal with
        | |- Result _ (EmulatorLow ?a ?b) = Result _ (EmulatorLow ?a' ?b') =>
            lazymatch goal with
            | A : eexec _ _ _ _ (Result ?o (a, b)), B : eexec _ _ _ _ (Result ?o' (a', b')) |- _ =>
                pose proof (eexec_deterministic _ _ _ _ _ _ Hdet2 A B) as E
            end
        end;
        inversion E; subst; reflexivity.
    Qed.

    Lemma execution_first :
      forall st a b tr st',
        execution ideal st (IO a b :: tr) st' ->
        exists st1, ideal.(step) st a (Result b st1) /\ execution ideal st1 tr st'.
    Proof. intros st a b tr st' H. inversion H; subst. eauto. Qed.

    Lemma execution_one :
      forall st a b st',
        execution ideal st (IO a b :: nil) st' -> ideal.(step) st a (Result b st').
    Proof.
      intros st a b st' H. destruct (execution_first _ _ _ _ _ H) as (st1 & Hs & He).
      inversion He; subst. exact Hs.
    Qed.

    (* What follows a known first step of an execution is an execution itself. *)
    Lemma execution_rest :
      forall st i1 o1 st1 io st',
        ideal.(step) st (inr i1) (Result (inr o1) st1) ->
        execution ideal st (io_to_ideal_machine_trace ((i1, o1) :: io)) st' ->
        execution ideal st1 (io_to_ideal_machine_trace io) st'.
    Proof.
      intros st i1 o1 st1 io st' Hs He. cbn in He.
      destruct (execution_first _ _ _ _ _ He) as (st1' & Hs' & He').
      pose proof (ideal_low_deterministic _ _ _ _ Hs Hs') as E. inversion E; subst. exact He'.
    Qed.

  End WithEmulator.

  Lemma machine_trace_cons :
    forall s i o s1 io s',
      M1.(step) s i (Result o s1) ->
      execution M1 s1 (io_to_machine_trace io) s' ->
      execution M1 s (io_to_machine_trace ((i, o) :: io)) s'.
  Proof. intros. cbn. econstructor; eauto. Qed.

  Theorem IPR_by_simulation :
    total M1 ->
    deterministic M2 ->
    resets_to_init M1 ->
    resets_to_init M2 ->
    functional_simulation ->
    physical_simulation ->
    IPR M1 M2 d.
  Proof.
    intros Htot1 Hdet2 Hrst1 Hrst2 (Hinit & Hterm & Hcorrect) (e & Hphys).
    assert (Hrst1i : forall s, M1.(reset) s M1.(init)) by (intro s; apply Hrst1; reflexivity).
    assert (Hrst2i : forall s, M2.(reset) s M2.(init)) by (intro s; apply Hrst2; reflexivity).
    (* Taking one wire-level step from a related pair, in either world's terms. *)
    assert (Hlow_start : forall s1 s2 i1 o1 s1',
              R s1 s2 -> M1.(step) s1 i1 (Result o1 s1') ->
              exists s2' e2',
                (ideal_world M2 e).(step) (EmulatorHigh s2) (inr i1) (Result (inr o1) (EmulatorLow s2' e2'))
                /\ lifted_R e (DriverLow s1') (EmulatorLow s2' e2')).
    { intros s1 s2 i1 o1 s1' HR Hs.
      destruct (Hphys s1 s2 i1 o1 nil s1' HR
                  (machine_trace_cons _ _ _ _ nil _ Hs (ExecutionEmpty _ _))) as (s2' & e2' & He).
      pose proof (execution_one e _ _ _ _ He) as Hst.
      exists s2', e2'. split; [ exact Hst |].
      intros io s1'' Hio.
      destruct (Hphys s1 s2 i1 o1 io s1'' HR (machine_trace_cons _ _ _ _ _ _ Hs Hio))
        as (s2'' & e2'' & He'').
      exists s2'', e2''. exact (execution_rest e Hdet2 _ _ _ _ _ _ Hst He''). }
    assert (Hlow_cont : forall s1 s2 e2 i1 o1 s1',
              lifted_R e (DriverLow s1) (EmulatorLow s2 e2) -> M1.(step) s1 i1 (Result o1 s1') ->
              exists s2' e2',
                (ideal_world M2 e).(step) (EmulatorLow s2 e2) (inr i1) (Result (inr o1) (EmulatorLow s2' e2'))
                /\ lifted_R e (DriverLow s1') (EmulatorLow s2' e2')).
    { intros s1 s2 e2 i1 o1 s1' HR Hs. cbn in HR.
      destruct (HR ((i1, o1) :: nil) s1'
                  (machine_trace_cons _ _ _ _ nil _ Hs (ExecutionEmpty _ _))) as (s2' & e2' & He).
      pose proof (execution_one e _ _ _ _ He) as Hst.
      exists s2', e2'. split; [ exact Hst |].
      intros io s1'' Hio.
      destruct (HR ((i1, o1) :: io) s1'' (machine_trace_cons _ _ _ _ _ _ Hs Hio))
        as (s2'' & e2'' & He'').
      exists s2'', e2''. exact (execution_rest e Hdet2 _ _ _ _ _ _ Hst He''). }
    exists e. split.
    - (* the real world refines the ideal one *)
      apply forward_simulation with (R := lifted_R e).
      split; [ exact Hinit | split ].
      + intros s1 i o s1' s2 HR Hstep.
        destruct s1 as [s1 | s1], s2 as [s2 | s2 e2]; cbn in HR; try contradiction;
          cbn in Hstep; inversion Hstep; subst.
        * (* first wire-level input *)
          match goal with Hm : step (mux M1) _ _ _ |- _ => inversion Hm; subst end.
          match goal with Hs : step M1 _ _ _ |- _ =>
            destruct (Hlow_start _ _ _ _ _ HR Hs) as (s2' & e2' & Hst & HR') end.
          exists (EmulatorLow s2' e2'). split; assumption.
        * (* spec-level operation *)
          match goal with Hd : dexec _ _ _ _ _ |- _ =>
            destruct (Hcorrect _ _ _ _ _ HR Hd) as (s2' & Hs2 & HR') end.
          exists (EmulatorHigh s2'). split; [| exact HR' ].
          apply EmulatorStepHighHigh. exact (MuxStepL _ _ M2 _ _ _ _ Hs2).
        * (* further wire-level input *)
          match goal with Hm : step (mux M1) _ _ _ |- _ => inversion Hm; subst end.
          match goal with Hs : step M1 _ _ _ |- _ =>
            destruct (Hlow_cont _ _ _ _ _ _ HR Hs) as (s2' & e2' & Hst & HR') end.
          exists (EmulatorLow s2' e2'). split; assumption.
        * (* back to spec level: both worlds reset first *)
          match goal with Hr : reset _ _ _ |- _ => apply Hrst1 in Hr; subst end.
          match goal with Hd : dexec _ _ _ _ _ |- _ =>
            destruct (Hcorrect _ _ _ _ _ Hinit Hd) as (s2' & Hs2 & HR') end.
          exists (EmulatorHigh s2'). split; [| exact HR' ].
          eapply EmulatorStepLowHigh; [ exact (Hrst2i s2) |]. exact (MuxStepL _ _ M2 _ _ _ _ Hs2).
      + intros s1 s1' s2 HR Hr.
        destruct s1 as [s1 | s1], s1' as [s1' | s1'], s2 as [s2 | s2 e2];
          cbn in HR, Hr; try contradiction;
          apply Hrst1 in Hr; subst;
          exists (EmulatorHigh M2.(init)); (split; [ exact (Hrst2i _) | exact Hinit ]).
    - (* the ideal world refines the real one *)
      apply forward_simulation with (R := fun s2 s1 => lifted_R e s1 s2).
      split; [ exact Hinit | split ].
      + intros s2 i o s2' s1 HR Hstep.
        destruct s2 as [s2 | s2 e2], s1 as [s1 | s1]; cbn in HR; try contradiction;
          cbn in Hstep; inversion Hstep; subst.
        * (* spec-level operation *)
          match goal with Hm : step (mux M2) _ _ _ |- _ => inversion Hm; subst end.
          match goal with Hs : step M2 _ _ _ |- _ => rename Hs into Hspec end.
          destruct (Hterm _ _ i2 HR) as (o2' & s1' & Hd).
          destruct (Hcorrect _ _ _ _ _ HR Hd) as (s2'' & Hs2 & HR').
          pose proof (Hdet2 _ _ _ _ Hspec Hs2) as E.
          inversion E; subst.
          exists (DriverHigh s1'). split; [| exact HR' ].
          apply DriverStepHighHigh. exact Hd.
        * (* first wire-level input *)
          destruct (Htot1 s1 i1) as ([o1' s1'] & Hs).
          destruct (Hlow_start _ _ _ _ _ HR Hs) as (s2'' & e2'' & Hst & HR').
          pose proof (ideal_low_deterministic e Hdet2 _ _ _ _ Hst Hstep) as E.
          inversion E; subst.
          exists (DriverLow s1'). split; [| exact HR' ].
          apply DriverStepHighLow. exact (MuxStepR _ _ M1 _ _ _ _ Hs).
        * (* back to spec level: both worlds reset first *)
          match goal with Hr : reset _ _ _ |- _ => apply Hrst2 in Hr; subst end.
          match goal with Hm : step (mux M2) _ _ _ |- _ => inversion Hm; subst end.
          match goal with Hs : step M2 _ _ _ |- _ => rename Hs into Hspec end.
          destruct (Hterm _ _ i2 Hinit) as (o2' & s1' & Hd).
          destruct (Hcorrect _ _ _ _ _ Hinit Hd) as (s2'' & Hs2 & HR').
          pose proof (Hdet2 _ _ _ _ Hspec Hs2) as E.
          inversion E; subst.
          exists (DriverHigh s1'). split; [| exact HR' ].
          eapply DriverStepLowHigh; [ exact (Hrst1i s1) | exact Hd ].
        * (* further wire-level input *)
          destruct (Htot1 s1 i1) as ([o1' s1'] & Hs).
          destruct (Hlow_cont _ _ _ _ _ _ HR Hs) as (s2'' & e2'' & Hst & HR').
          pose proof (ideal_low_deterministic e Hdet2 _ _ _ _ Hst Hstep) as E.
          inversion E; subst.
          exists (DriverLow s1'). split; [| exact HR' ].
          apply DriverStepLowLow. exact (MuxStepR _ _ M1 _ _ _ _ Hs).
      + intros s2 s2' s1 HR Hr.
        destruct s2 as [s2 | s2 e2], s2' as [s2' | s2' e2'], s1 as [s1 | s1];
          cbn in HR, Hr; try contradiction;
          apply Hrst2 in Hr; subst;
          exists (DriverHigh M1.(init)); (split; [ exact (Hrst1i _) | exact Hinit ]).
  Qed.

End Strategy.
