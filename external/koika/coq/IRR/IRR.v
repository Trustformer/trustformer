(*! Proving | Transformation of a schedule into a proof-friendly form !*)
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Program.Equality.
Require Import Coq.Strings.Ascii.
Require Import Coq.Wellfounded.Wellfounded.
Require Import Koika.BitsToLists.
Require Import Koika.Utils.Maps.
Require Import Koika.Primitives.
Require Import Koika.KoikaForm.Syntax.
Require Import Koika.IRR.Wt.
Require Import Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.IRR.Sact.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.KoikaForm.Desugaring.DesugaredSyntax.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(* When reasoning about a Kôika schedule, a lot of complex implicit mechanisms
   have to be considered explicitly (rules merging, cancellation, ...).
   Furthermore, performance issues related to abstract interpretation make
   reasoning about the behavior of some even moderately complex models (e.g.,
   the RISC-V processor example) impossible.

   This is what this simpler form, which we call an IRR (Intermediate
   Representation for Reasoning) aims to fix. For instance, it makes finding
   under which conditions the value of a register is updated or proving that the
   value of register x never reaches 5 much easier.

   The result of the interpretation of a model before or after its conversion
   to the form defined hereafter should be equal (in terms of the effects of a
   cycle on the final state of the registers and of the emitted extcalls,
   although the latter are not really considered in Kôika's pure semantics). *)
Open Scope positive.
Section IRR.
  Context {pos_t reg_t ext_fn_t rule_name_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {ext_fn_t_eq_dec: EqDec ext_fn_t}.
  Definition uact := @daction pos_t string string reg_t ext_fn_t.

  Variable REnv : Env reg_t.
  Variable r : env_t REnv (fun _ => val).
  Context {sigma : ext_fn_t -> val -> val}.
  Variable R: reg_t -> type.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  Context {
    wt_sigma: forall ufn vc,
    wt_val (arg1Sig (Sigma ufn)) vc
    -> wt_val (retSig (Sigma ufn)) (sigma ufn vc)}.

  Inductive sact :=
  | SVar (var: positive)
  | SConst (v:val)
  | SIf (cond: sact) (tbranch: sact) (fbranch: sact)
  | SUnop (ufn1: PrimUntyped.ufn1) (arg1: sact)
  | SBinop (ufn2: PrimUntyped.ufn2) (arg1: sact) (arg2: sact)
  | SExternalCall (ufn: ext_fn_t) (arg: sact)
  | SReg (idx: reg_t).

  Definition sumbool_to_bool {A B} (sb: {A} + {B}) : bool :=
    match sb with
    | left _ => true
    | right _ => false
    end.

  Fixpoint sact_beq (s1 s2: sact) : bool :=
  match s1, s2 with
  | SVar v1, SVar v2 => Pos.eqb v1 v2
  | SConst v1, SConst v2 => val_beq v1 v2
  | SIf c1 tb1 fb1, SIf c2 tb2 fb2 =>
    andb (andb (sact_beq c1 c2) (sact_beq tb1 tb2)) (sact_beq fb1 fb2)
  | SUnop ufn1 a1, SUnop ufn2 a2 =>
    andb (sact_beq a1 a2) (sumbool_to_bool (eq_dec ufn1 ufn2))
  | SBinop ufn1 a1 a'1, SBinop ufn2 a2 a'2 =>
    andb
      (andb (sact_beq a1 a2) (sumbool_to_bool (eq_dec ufn1 ufn2)))
      (sact_beq a'1 a'2)
  | SExternalCall ufn1 a1, SExternalCall ufn2 a2 =>
    andb (sact_beq a1 a2) (sumbool_to_bool (eq_dec ufn1 ufn2))
  | SReg idx1, SReg idx2 => sumbool_to_bool (eq_dec idx1 idx2)
  | _, _ => false
  end.

  Lemma sact_beq_iff_eq:
    forall s1 s2, sact_beq s1 s2 = true <-> s1 = s2.
  Proof.
    intros.
    split; intro.
    - generalize dependent s2. induction s1, s2; try discriminate; intro.
      + simpl in H. apply Pos.eqb_eq in H. subst. reflexivity.
      + simpl in H. apply val_beq_correct in H. subst. reflexivity.
      + simpl in H. rewrite ! andb_true_iff in H. destruct H. destruct H.
        apply IHs1_1 in H. apply IHs1_2 in H1. apply IHs1_3 in H0.
        subst. reflexivity.
      + unfold sact_beq in H.  rewrite ! andb_true_iff in H. destruct H.
        destruct (eq_dec ufn1 ufn0). 2: discriminate H0.
        apply IHs1 in H. subst. reflexivity.
      + unfold sact_beq in H. rewrite ! andb_true_iff in H. destruct H.
        destruct H.
        destruct (eq_dec ufn2 ufn0). 2: discriminate H1.
        apply IHs1_1 in H. apply IHs1_2 in H0. subst. reflexivity.
      + unfold sact_beq in H.  rewrite ! andb_true_iff in H. destruct H.
        destruct (eq_dec ufn ufn0). 2: discriminate H0.
        apply IHs1 in H. subst. reflexivity.
      + simpl in H. destruct (eq_dec idx idx0). 2: discriminate H.
        subst. reflexivity.
    - subst. induction s2.
      + simpl. rewrite Pos.eqb_eq. reflexivity.
      + simpl. rewrite val_beq_correct. reflexivity.
      + simpl. rewrite ! andb_true_iff. repeat split; auto.
      + unfold sact_beq. rewrite ! andb_true_iff. repeat split; auto.
        rewrite eq_dec_refl. auto.
      + unfold sact_beq. rewrite ! andb_true_iff. repeat split; auto.
        rewrite eq_dec_refl. auto.
      + unfold sact_beq. rewrite ! andb_true_iff. repeat split; auto.
        rewrite eq_dec_refl. auto.
      + simpl. rewrite eq_dec_refl. auto.
  Qed.

  Instance EqDec_sact : EqDec sact.
  Proof.
    econstructor. intros. destruct (sact_beq t1 t2) eqn:?.
    - apply sact_beq_iff_eq in Heqb. subst. left. reflexivity.
    - assert (sact_beq t1 t2 = true -> False).
      { rewrite Heqb. intro. discriminate H. }
      rewrite sact_beq_iff_eq in H. right. auto.
  Qed.

  Definition const_nil := SConst (Bits []).
  Definition const_true := SConst (Bits [true]).
  Definition const_false := SConst (Bits [false]).

  Definition uor (x y: sact) :=
    SBinop (PrimUntyped.UBits2 PrimUntyped.UOr) x y.
  Definition uand (x y: sact) :=
    SBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) x y.
  Definition unot (x: sact) := SUnop (PrimUntyped.UBits1 PrimUntyped.UNot) x.

  Definition schedule := scheduler pos_t rule_name_t.

  Inductive wt_sact (vt: PTree.t (type * sact)) : sact -> type -> Prop :=
  | wt_sact_var var t s: vt ! var = Some (t, s) -> wt_sact vt (SVar var) t
  | wt_sact_const v t: wt_val t v -> wt_sact vt (SConst v) t
  | wt_sact_if c bt bf t:
    wt_sact vt c (bits_t 1)
    -> wt_sact vt bt t
    -> wt_sact vt bf t
    -> wt_sact vt (SIf c bt bf) t
  | wt_sact_unop ufn a t t' :
    wt_sact vt a t -> wt_unop ufn t t' -> wt_sact vt (SUnop ufn a) t'
  | wt_sact_binop ufn a1 a2 t1 t2 t' :
    wt_sact vt a1 t1
    -> wt_sact vt a2 t2
    -> wt_binop ufn t1 t2 t'
    -> wt_sact vt (SBinop ufn a1 a2) t'
  | wt_sact_extcall ufn a:
    wt_sact vt a (arg1Sig (Sigma ufn))
    -> wt_sact vt (SExternalCall ufn a) (retSig (Sigma ufn))
  | wt_sact_reg idx: wt_sact vt (SReg idx) (R idx).

  Inductive interp_sact (vvs: PTree.t (type * sact)) : sact -> val -> Prop :=
  | interp_sact_var var t a v:
    vvs ! var = Some (t, a)
    -> interp_sact vvs a v
    -> interp_sact vvs (SVar var) v
  | interp_sact_const v: interp_sact vvs (SConst v) v
  | interp_sact_if c t f b v:
    interp_sact vvs c (Bits [b])
    -> interp_sact vvs (if b then t else f) v
    -> interp_sact vvs (SIf c t f) v
  | interp_sact_unop ufn a v v':
    interp_sact vvs a v
    -> UntypedSemantics.sigma1 ufn v = Some v'
    -> interp_sact vvs (SUnop ufn a) v'
  | interp_sact_binop ufn a1 a2 v1 v2 v' :
    interp_sact vvs a1 v1
    -> interp_sact vvs a2 v2
    -> UntypedSemantics.sigma2 ufn v1 v2 = Some v'
    -> interp_sact vvs (SBinop ufn a1 a2) v'
  | interp_sact_extcall ufn a v :
    interp_sact vvs a v -> interp_sact vvs (SExternalCall ufn a) (sigma ufn v)
  | interp_sact_reg idx: interp_sact vvs (SReg idx) (getenv REnv r idx).

  Lemma interp_sact_determ:
    forall vvs a v1,
    interp_sact vvs a v1 -> forall v2, interp_sact vvs a v2 -> v1 = v2.
  Proof.
    induction 1; simpl; intros ? IS; inv IS; eauto.
    - rewrite H in H2; inv H2. eauto.
    - apply IHinterp_sact1 in H5. inv H5.
      eauto.
    - apply IHinterp_sact in H3. subst. congruence.
    - apply IHinterp_sact1 in H5. subst.
      apply IHinterp_sact2 in H7. subst. congruence.
    - apply IHinterp_sact in H3. subst. congruence.
  Qed.

  (* Simple form and related structures *)
  Definition cond_log := list (reg_t * sact).
  Definition write_log_raw := list (reg_t * sact).
  Definition var_value_map := PTree.t (type * sact).

  Record rule_information_raw := mkRuleInformationRaw {
    rir_read0s: cond_log;
    rir_read1s: cond_log;
    rir_write0s: write_log_raw;
    rir_write1s: write_log_raw;
    rir_vars: var_value_map;
    rir_failure_cond: sact
  }.

  Instance etaRuleInformationRaw : Settable _ :=
    settable! mkRuleInformationRaw
      < rir_read0s; rir_read1s; rir_write0s; rir_write1s; rir_vars;
        rir_failure_cond >.
  Record IRR := mkIRR {
    final_values: list (reg_t * positive);
    read1_values: list (reg_t * positive);
    debug_log: list (rule_name_t * list (reg_t * sact) * list (reg_t * sact) * list (reg_t * sact) * list (reg_t * sact));
    vars: var_value_map
  }.
  #[export] Instance etaIRR : Settable _ :=
    settable! mkIRR < final_values; read1_values; debug_log; vars >.

  (* * rule_information extraction *)
  (* ** Addition of a new action into an existing rule_information *)
  (* *** Merger of failure conditions *)
  Definition or_conds (conds: list sact) := fold_left uor conds const_false.
  Definition merge_failures (f1 f2: sact) : sact := uor f1 f2.

  (* *** Merger of actions *)
  (* Remove Nones from list, turn rest from (Some x) to x. *)
  Definition list_options_to_list {A} (l: list (option A)) : list A :=
    filter_map id l.

  Definition merge_failures_list (action_cond: sact) (conds: list sact)
  : sact :=
    uand action_cond (or_conds conds).

  Definition add_read0 (rir: rule_information_raw) (grd: sact) (reg: reg_t)
    (* Returns modified rir *)
    : rule_information_raw :=
    let new_grd :=
      match list_assoc (rir_read0s rir) reg with
      | None => grd
      | Some cond' => uor cond' grd
      end in
    rir <| rir_read0s := list_assoc_set (rir_read0s rir) reg new_grd |>.

  Definition add_read1 (rir: rule_information_raw) (grd: sact) (reg: reg_t)
    (* Returns modified rule_information_raw *)
    : rule_information_raw :=
    let new_grd :=
      match list_assoc (rir_read1s rir) reg with
      | None => grd
      | Some cond' => uor cond' grd
      end in
    rir <| rir_read1s := list_assoc_set (rir_read1s rir) reg new_grd |>.

  Definition rir_has_write0 rir reg : sact :=
    match list_assoc (rir_write0s rir) reg with
    | None => const_false
    | Some gcond => gcond
    end.
  Definition rir_has_write1 rir reg : sact :=
    match list_assoc (rir_write1s rir) reg with
    | None => const_false
    | Some gcond => gcond
    end.
  Definition rir_has_read0 rir reg : sact :=
    match list_assoc (rir_read0s rir) reg with
    | None => const_false
    | Some (gcond) => gcond
    end.
  Definition rir_has_read1 rir reg : sact :=
    match list_assoc (rir_read1s rir) reg with
    | None => const_false
    | Some (gcond) => gcond
    end.

  Definition add_write0 (sched_rir: rule_information_raw)
    (rir: rule_information_raw) (grd: sact) (reg: reg_t) (v:sact)
  (* Returns modified rule_information_raw, failure conditions *)
  : rule_information_raw * sact :=
    let new_grd :=
      match list_assoc (rir_write0s rir) reg with
      | None => grd
      | Some c => uor c grd
      end in
    (
      (rir <| rir_write0s := list_assoc_set (rir_write0s rir) reg new_grd |>),
      merge_failures_list
        grd [
          rir_has_write0 rir reg; rir_has_read1 rir reg;
          rir_has_write1 rir reg; rir_has_write0 sched_rir reg;
          rir_has_read1 sched_rir reg; rir_has_write1 sched_rir reg
        ]).

  Definition add_write1
    sched_rir (rir: rule_information_raw) (grd: sact) (reg: reg_t) (v:sact)
  (* Returns modified rule_information_raw, failure conditions *)
  : rule_information_raw * sact :=
    let new_grd :=
      match list_assoc (rir_write1s rir) reg with
      | None => grd
      | Some c => uor c grd
      end in
    (rir <| rir_write1s := list_assoc_set (rir_write1s rir) reg new_grd |>,
     merge_failures_list
      grd [rir_has_write1 rir reg; rir_has_write1 sched_rir reg]
    ).

  (* ** Extraction of actions from rule *)
  Definition reduce t (ua: option (sact)) : sact :=
    match ua with
    | None => SConst (val_of_type t)
    | Some x => x
    end.

  Fixpoint merge_branches
    (vm_tb vm_fb: list (string*positive)) (vvs: PTree.t (type * sact))
    (nid: positive) (cond_name: positive)
  :=
    match vm_tb, vm_fb with
    | (str, n1)::vm_tb, (_, n2)::vm_fb =>
      let '(acc, vv', nid) := merge_branches vm_tb vm_fb vvs nid cond_name in
      if Pos.eq_dec n1 n2 then ((str, n1)::acc, vv', nid)
      else
        let t :=
          match vvs ! n1 with
          | Some (t, _) => t
          | None => bits_t 0
          end in
        ((str, nid)::acc,
         PTree.set nid (t, SIf (SVar cond_name) (SVar n1) (SVar n2)) vv',
         Pos.succ nid)
    | _, _ => ([], vvs, nid)
    end.

  Fixpoint merge_branches2
    (vm_tb vm_fb: list (string*positive)) (tsig: list (string * type))
    (vvs: PTree.t (type * sact)) (nid: positive) (cond_name: positive)
  :=
    match vm_tb, vm_fb, tsig with
    | (str, n1)::vm_tb, (_, n2)::vm_fb, (_,t)::tsig =>
        let '(acc, vv', nid) :=
          merge_branches2 vm_tb vm_fb tsig vvs nid cond_name in
        if Pos.eq_dec n1 n2 then ((str, n1)::acc, vv', nid)
        else
          ((str, nid)::acc,
           PTree.set nid (t, SIf (SVar cond_name) (SVar n1) (SVar n2)) vv',
           Pos.succ nid)
    | _, _, _ => ([], vvs, nid)
    end.

  Definition env_vvs
    (env: list (string * positive)) (vvs: PTree.t (type * sact))
    (tsig: tsig string)
  :=
    Forall2
      (fun '(var1, fv) '(var2, t) =>
        var1 = var2 /\ exists s, vvs ! fv = Some (t, s))
      env tsig.

  Lemma nodup_list_assoc_set:
    forall {K V: Type} {ed: EqDec K} (l: list (K * V)) k v,
    NoDup (map fst l) -> NoDup (map fst (list_assoc_set l k v)).
  Proof.
    induction l; simpl; intros; eauto. constructor. easy. auto. inv H. destr.
    destr; subst; simpl; econstructor; eauto.
    intros IN; apply H2. simpl.
    apply in_map_list_assoc_set_inv in IN. destruct IN; congruence.
  Qed.

  Lemma merge_branches2_nd:
    forall vm_tb vm_fb tsig vvs nid cond_name vm' vvs' nid',
    (forall x y, vvs ! x = Some y -> x < nid)
    -> merge_branches2 vm_tb vm_fb tsig vvs nid cond_name = (vm', vvs', nid')
    -> (forall x y, vvs' ! x = Some y -> x < nid').
  Proof.
    induction vm_tb; simpl; intros; eauto. inv H0. eauto.
    repeat (destr_in H0; [idtac]).
    destr_in H0. inv H0; eauto.
    destr_in H0. destr_in H0. inv H0; eauto.
    repeat (destr_in H0; [idtac]). subst.
    specialize (IHvm_tb _ _ _ _ _ _ _ _ H Heqp0).
    destr_in H0; inv H0. eauto.
    rewrite PTree.gsspec in H1. destr_in H1. inv H1. lia. apply IHvm_tb in H1.
    lia.
  Qed.

  Lemma merge_branches2_ok' :
    forall vm_tb vm_fb tsig vvs nid cond_name vm' vvs' nid',
    merge_branches2 vm_tb vm_fb tsig vvs nid cond_name = (vm', vvs', nid')
    -> (forall x y, vvs ! x = Some y -> x < nid)
    -> env_vvs vm_tb vvs tsig
    -> env_vvs vm_fb vvs tsig
    -> merge_branches vm_tb vm_fb vvs nid cond_name = (vm', vvs', nid').
  Proof.
    induction vm_tb; simpl; intros; eauto.
    - inv H1; inv H2. destruct a, x, y.
      do 2 destr_in H.
      eapply IHvm_tb in Heqp1. rewrite Heqp1.
      destr_in H.
      + inv H. eauto.
      + inv H. intros. destruct H5 as (? & ? & GET). rewrite GET. auto.
      + eauto.
      + eauto.
      + eauto.
  Qed.

  Lemma merge_branches2_ok:
    forall vm_tb vm_fb tsig vvs nid cond_name vm' vvs' nid',
    merge_branches2 vm_tb vm_fb tsig vvs nid cond_name = (vm', vvs', nid')
    -> (forall x y, vvs ! x = Some y -> x < nid)
    -> env_vvs vm_tb vvs tsig
    -> env_vvs vm_fb vvs tsig
    -> merge_branches vm_tb vm_fb vvs nid cond_name = (vm', vvs', nid').
  Proof. intros. eapply merge_branches2_ok'; eauto. Qed.

  Definition p2n pu :=
    match pu with
    | inl P0 => O
    | inl P1 => 1%nat
    | inr tt => 2%nat
    end.

  Context {finreg_t: FiniteType reg_t}.

  Definition rp2p (r: reg_t * (Port + unit)): positive :=
    Pos.of_nat (S (finite_index (fst r) * 3 + p2n (snd r))).

  Lemma rp2p_inj: forall r1 r2, rp2p r1 = rp2p r2 -> r1 = r2.
  Proof.
    unfold rp2p. intros.
    apply Pnat.Nat2Pos.inj_iff in H.
    apply Nat.succ_inj in H. 2-3: lia.
    cut (p2n (snd r1) < 3)%nat. cut (p2n (snd r2) < 3)%nat.
    intros.
    assert (finite_index (fst r1) = finite_index (fst r2)). nia.
    assert (p2n (snd r1) = p2n (snd r2)) by nia.
    apply finite_index_injective in H2.
    destruct r1, r2. simpl in *. subst.
    revert H3; unfold p2n.
    destruct s as [[|]|[]], s0 as [[|]|[]]; try congruence.
    unfold p2n. repeat destr; lia.
    unfold p2n. repeat destr; lia.
  Qed.

  Definition r2vtype := list (reg_t * (Port + unit) * positive).

  Fixpoint merge_reg2vars_reg2 (r1 r2: r2vtype) cond_name r vvs nid :=
    match r1, r2 with
    | ((reg,prt),v1)::r1, (_,v2)::r2 =>
      let '(r,vvs,nid) := merge_reg2vars_reg2 r1 r2 cond_name r vvs nid in
      if Pos.eq_dec v1 v2 then (((reg,prt), v1)::r, vvs, nid)
      else
        (((reg,prt), nid)::r,
         PTree.set nid (R reg, SIf (SVar cond_name) (SVar v1) (SVar v2)) vvs,
         Pos.succ nid)
    | _, _ => (r, vvs, nid)
    end.

  Definition merge_reg2vars2 (r1 r2: r2vtype) cond_name vvs nid :=
    merge_reg2vars_reg2 r1 r2 cond_name [] vvs nid.

  Definition reg2var_vvs (reg2var: r2vtype) (vvs: PTree.t (type * sact)) :=
    forall x, exists y,
    list_assoc reg2var x = Some y /\ exists z, vvs ! y = Some (R (fst x), z).

  Lemma same_regenv_refl: forall reg2var',
    Forall2 (fun x y : reg_t * (Port + unit) * positive => fst x = fst y)
      reg2var' reg2var' .
  Proof. induction reg2var' ; simpl; intros; eauto. Qed.

  Lemma same_regenv_trans: forall r1 r2,
    Forall2 (fun x y : reg_t * (Port + unit) * positive => fst x = fst y) r1 r2
    -> forall r3,
      Forall2 (fun x y : reg_t * (Port + unit) * positive => fst x = fst y) r2
      r3
    -> Forall2 (fun x y : reg_t * (Port + unit) * positive => fst x = fst y) r1
      r3.
  Proof.
    induction 1; simpl; intros; eauto. inv H1. econstructor; eauto. congruence.
  Qed.

  Lemma same_regenv_sym: forall r1 r2,
    Forall2 (fun x y : reg_t * (Port + unit) * positive => fst x = fst y) r1 r2
    -> Forall2 (fun x y : reg_t * (Port + unit) * positive => fst x = fst y) r2
      r1.
  Proof. induction 1; simpl; intros; eauto. Qed.

  Lemma merge_reg2vars_reg_same_structure:
    forall r1 r2, Forall2 (fun a b => fst a = fst b) r1 r2
    -> forall r cname vvs nid vvs' r' nid',
      merge_reg2vars_reg2 r1 r2 cname r vvs nid = (r', vvs', nid')
    -> Forall2 (fun a b => fst a = fst b) (r1++r) r' .
  Proof.
    induction 1; simpl; intros; eauto. inv H.
    - apply same_regenv_refl.
    - repeat (destr_in H1; [idtac]). apply IHForall2 in Heqp3.
      destr_in H1; inv H1; constructor; eauto.
  Qed.

  Lemma merge_reg2vars_same_structure:
    forall r1 r2, Forall2 (fun a b => fst a = fst b) r1 r2
    -> forall cname vvs nid vvs' r' nid',
      merge_reg2vars2 r1 r2 cname vvs nid = (r', vvs', nid')
    -> Forall2 (fun a b => fst a = fst b) r1 r'.
  Proof.
    intros.
    exploit merge_reg2vars_reg_same_structure.
    2 : apply H0. auto. rewrite app_nil_r. auto.
  Qed.

  Definition var_lt (v1 v2: positive) := v1 < v2.

  Lemma var_lt_gen_r: forall s n n', n <= n' -> var_lt s n -> var_lt s n'.
  Proof. unfold var_lt; intros; lia. Qed.

  Inductive var_in_sact : sact -> positive -> Prop :=
  | var_in_sact_var v: var_in_sact (SVar v) v
  | var_in_if_cond c t f v: var_in_sact c v -> var_in_sact (SIf c t f) v
  | var_in_if_true c t f v: var_in_sact t v -> var_in_sact (SIf c t f) v
  | var_in_if_false c t f v: var_in_sact f v -> var_in_sact (SIf c t f) v
  | var_in_sact_unop ufn a v: var_in_sact a v -> var_in_sact (SUnop ufn a) v
  | var_in_sact_binop_1 ufn a1 a2 v:
    var_in_sact a1 v -> var_in_sact (SBinop ufn a1 a2) v
  | var_in_sact_binop_2 ufn a1 a2 v:
    var_in_sact a2 v -> var_in_sact (SBinop ufn a1 a2) v
  | var_in_sact_external ufn a v:
    var_in_sact a v -> var_in_sact (SExternalCall ufn a) v.

  Definition vvs_smaller_variables (vvs: PTree.t (type * sact)) :=
    forall (v : positive) (t: type) (a : sact), vvs ! v = Some (t, a)
    -> forall v' : positive, var_in_sact a v'
    -> var_lt v' v.

  Definition vvs_grows (vvs1 vvs2: var_value_map) :=
    forall x y, vvs1 ! x = Some y -> vvs2 ! x = Some y.

  Lemma vvs_grows_refl: forall v, vvs_grows v v.
  Proof. red; auto. Qed.

  Lemma vvs_grows_trans:
    forall v1 v2, vvs_grows v1 v2
    -> forall v3, vvs_grows v2 v3
    -> vvs_grows v1 v3.
  Proof. unfold vvs_grows; intros; eauto. Qed.

  Definition wt_vvs (vvs: PTree.t (type * sact)) :=
    forall v s t, vvs ! v = Some (t, s) -> wt_sact vvs s t.

  Definition valid_name name nid := name < nid.

  Definition vvs_range (vvs: PTree.t (type * sact)) (nid: positive) :=
    forall x y, vvs ! x = Some y -> valid_name x nid.

  Lemma vvs_range_list_assoc_set:
    forall vvs n name v, vvs_range vvs n
    -> valid_name name n
    -> vvs_range (PTree.set name v vvs) n.
  Proof.
    unfold vvs_range; simpl; intros.
    rewrite PTree.gsspec in H1; destr_in H1; eauto. inv H1. auto.
  Qed.

  Lemma valid_name_incr:
    forall name n1 n2 (INCR: n1 <= n2),
    valid_name name n1 -> valid_name name n2.
  Proof. unfold valid_name. intros; lia. Qed.

  Lemma vvs_range_incr:
    forall vvs n1 n2 (INCR: n1 <= n2), vvs_range vvs n1 -> vvs_range vvs n2.
  Proof. unfold vvs_range; simpl; intros; eauto using valid_name_incr. Qed.

  Lemma wt_sact_vvs_set:
    forall vvs s t, wt_sact vvs s t
    -> forall k v n, vvs_range vvs n
    -> k >= n
    -> wt_sact (PTree.set k v vvs) s t.
  Proof.
    induction 1; simpl; intros; eauto.
    - econstructor. rewrite PTree.gso. eauto. apply H0 in H. red in H; lia.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor.
  Qed.

  Lemma wt_vvs_set:
    forall vvs n, wt_vvs vvs
    -> vvs_range vvs n
    -> forall k t v, wt_sact vvs v t
    -> k >= n
    -> wt_vvs (PTree.set k (t, v) vvs).
  Proof.
    red; intros. rewrite PTree.gsspec in H3.
    destr_in H3; eauto.
    inv H3.
    eapply wt_sact_vvs_set; eauto.
    eapply wt_sact_vvs_set; eauto.
  Qed.

  Lemma wt_sact_vvs_grows:
    forall vvs vvs', vvs_grows vvs vvs'
    -> forall s t, wt_sact vvs s t
    -> wt_sact vvs' s t.
  Proof.
    induction 2; simpl; intros; eauto.
    - eapply H in H0. econstructor; eauto.
    - constructor; auto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor.
  Qed.

  Lemma wt_sact_valid_vars:
    forall vvs n (WFS: vvs_range vvs n) a t (WTGUARD: wt_sact vvs a t) v,
    var_in_sact a v -> v < n.
  Proof.
    intros vvs n WFS.
    induction 1; simpl; intros; eauto.
    - inv H0. eapply WFS in H; eauto.
    - inv H0.
    - inv H; eauto.
    - inv H0; eauto.
    - inv H0; eauto.
    - inv H; eauto.
    - inv H.
  Qed.

  Lemma nodup_in_assoc:
    forall {K V: Type} {eqdec: EqDec K} (l: list (K*V)) k v,
    NoDup (map fst l) -> In (k,v) l -> list_assoc l k = Some v.
  Proof.
    induction l; simpl; intros; eauto.
    easy.
    inv H.
    destruct H0. subst. rewrite eq_dec_refl. auto.
    destr. simpl in *. destr. apply (in_map fst) in H. simpl in H; subst.
    congruence.
    eauto.
  Qed.

  Fixpoint size_sact (s: sact) : nat :=
    match s with
    | SVar _ => 1
    | SConst _ => 1
    | SIf c t f => 1 + size_sact c + size_sact t + size_sact f
    | SUnop _ a => 1 + size_sact a
    | SBinop _ a b => 1 + size_sact a + size_sact b
    | SExternalCall _ a => 1 + size_sact a
    | SReg _ => 1
    end.

  Definition order_sact :=
    Relation_Operators.lexprod
      positive (fun _ => sact)
      (fun s1 s2 => s1 < s2)
      (fun s s1 s2 => size_sact s1 < size_sact s2)%nat.

  Lemma wf_order_sact: well_founded (order_sact).
  Proof.
    apply wf_lexprod.
    - eapply well_founded_lt_compat with (f := Pos.to_nat).
      intros. rewrite <- Pnat.Pos2Nat.inj_lt. auto.
    - intros. apply wf_inverse_image. apply lt_wf.
  Qed.

  Hypothesis WTRENV: wt_renv R REnv r.

  Lemma wt_sact_interp':
    forall vvs, wt_vvs vvs
    -> vvs_smaller_variables vvs
    -> forall n a t, (forall v, var_in_sact a v -> v < n)
    -> wt_sact vvs a t
    -> exists v, interp_sact vvs a v /\ wt_val t v.
  Proof.
    intros vvs WTvvs VSV n a.
    change n with (projT1 (existT (fun _ => sact) n a)).
    change a with (projT2 (existT (fun _ => sact) n a)) at 1 3 4.
    generalize (existT (fun _ => sact) n a).
    clear n a. intro s. pattern s.
    eapply well_founded_induction.
    apply wf_order_sact. clear s.
    intros x IH t BELOW WTs.
    destruct x; simpl in *.
    inv WTs.
    - trim (BELOW var). constructor.
      generalize (VSV _ _ _ H). intros.
      edestruct (IH (existT _ var s0)) as (v & IS & WTv).
      + red. apply Relation_Operators.left_lex. simpl. auto.
      + simpl. eauto.
      + simpl. eapply WTvvs; eauto.
      + eexists; split. econstructor; eauto. auto.
    - eexists. split. econstructor. auto.
    - edestruct (IH) as (vc & ISc & WTvc); simpl; eauto.
      {
        red. apply Relation_Operators.right_lex. instantiate (1:=c). simpl; lia.
      }
      { simpl. intros; eapply BELOW. constructor. auto. }
      simpl. eauto. simpl in *.
      inv WTvc. destruct bs; simpl in H3; try lia.
      destruct bs; simpl in H3; try lia.
      edestruct (fun n => IH (existT _ n (if b then bt else bf)))
        as (vb & ISb & WTb); simpl; eauto.
      { red. apply Relation_Operators.right_lex. simpl; destruct b; lia. }
      {
        simpl. intros; eapply BELOW.
        destruct b. eapply var_in_if_true. eauto. eapply var_in_if_false; eauto.
      }
      destruct b; eauto. simpl in ISb.
      eexists; split. econstructor; eauto. auto.
    - edestruct (IH) as (vc & ISc & WTvc); simpl; eauto.
      {
        red. apply Relation_Operators.right_lex. instantiate (1:=a). simpl; lia.
      }
      { simpl. intros; eapply BELOW. constructor. auto. }
      simpl. eauto. simpl in *.
      edestruct wt_unop_interp as (v2 & SIG1); eauto.
      eexists; split. econstructor; eauto.
      eapply wt_unop_sigma1; eauto.
    - edestruct (fun n=> IH (existT _ n a1)) as (vc & ISc & WTvc); simpl; eauto.
      { red. apply Relation_Operators.right_lex. simpl; lia. }
      { simpl. intros; eapply BELOW. constructor. auto. }
      simpl. eauto. simpl in *.
      edestruct (fun n => IH (existT _ n a2))
        as (vc2 & ISc2 & WTvc2); simpl; eauto.
      { red. apply Relation_Operators.right_lex. simpl; lia. }
      { simpl. intros; eapply BELOW. eapply var_in_sact_binop_2; eauto. }
      simpl in *.
      edestruct wt_binop_interp as (v2 & SIG2); eauto.
      eexists; split. econstructor; eauto.
      eapply wt_binop_sigma1; eauto.
    - edestruct (IH) as (vc & ISc & WTvc); simpl; eauto.
      {
        red. apply Relation_Operators.right_lex. instantiate (1:=a). simpl; lia.
      }
      { simpl. intros; eapply BELOW. constructor. auto. }
      simpl. eauto. simpl in *.
      eexists; split. econstructor; eauto.
      eapply wt_sigma; eauto.
    - eexists; split. econstructor. apply WTRENV.
  Qed.

  Lemma wt_sact_interp:
    forall vvs, wt_vvs vvs
    -> vvs_smaller_variables vvs
    -> forall n a t, vvs_range vvs n
    -> wt_sact vvs a t
    -> exists v, interp_sact vvs a v /\ wt_val t v.
  Proof.
    intros.
    eapply wt_sact_interp'; eauto.
    eapply wt_sact_valid_vars; eauto.
  Qed.

  Lemma vvs_grows_interp_sact:
    forall v1 v2 a v, vvs_grows v1 v2
    -> interp_sact v1 a v
    -> interp_sact v2 a v.
  Proof. induction 2; simpl; intros; eauto; try now (econstructor; eauto). Qed.
  Lemma interp_sact_vvs_grows_inv:
    forall vvs vvs' a v t n, wt_vvs vvs
    -> vvs_smaller_variables vvs
    -> vvs_grows vvs vvs'
    -> vvs_range vvs n
    -> wt_sact vvs a t
    -> interp_sact vvs' a v
    -> interp_sact vvs a v.
  Proof.
    intros.
    edestruct wt_sact_interp as (vv & IS & WTv); eauto.
    exploit vvs_grows_interp_sact; eauto. intros.
    exploit interp_sact_determ. apply H4. apply H5. intros ->; eauto.
  Qed.

  Lemma interp_sact_vvs_grows_iff:
    forall (vvs vvs' : PTree.t (type * sact)) (a : sact) (v : val) (t : type)
      (n : positive),
    wt_vvs vvs
    -> vvs_smaller_variables vvs
    -> vvs_grows vvs vvs'
    -> vvs_range vvs n
    -> wt_sact vvs a t
    -> interp_sact vvs' a v <-> interp_sact vvs a v.
  Proof.
    intros; split.
    eapply interp_sact_vvs_grows_inv; eauto.
    eapply vvs_grows_interp_sact; eauto.
  Qed.

  Lemma vvs_grows_set:
    forall vvs n k l, vvs_range vvs n
    -> k >= n
    -> vvs_grows vvs (PTree.set k l vvs).
  Proof.
    red; intros.
    rewrite PTree.gso; eauto.
    eapply H in H1. red in H1. lia.
  Qed.

  Lemma merge_reg2vars_reg2_nd:
    forall r1 r2 cond_name vvs nid r r' vvs' nid' (RNG: vvs_range vvs nid)
      (NDr1: NoDup (map fst r1)) (NDr: NoDup (map fst r))
      (DISJ: forall k, In k (map fst r1) -> ~ In k (map fst r))
      (WTv: wt_vvs vvs) (VSV: vvs_smaller_variables vvs)
      (F2: Forall2 (fun x y => fst x = fst y) r1 r2)
      (R2V1: forall x y, In (x,y) r1 -> exists z, vvs !y = Some (R (fst x), z))
      (R2V2: forall x y, In (x,y) r2 -> exists z, vvs !y = Some (R (fst x), z))
      (R2VR: forall x y, In (x,y) r -> exists z, vvs !y = Some (R (fst x), z))
      (WTcond: wt_sact vvs (SVar cond_name) (bits_t 1)),
    merge_reg2vars_reg2 r1 r2 cond_name r vvs nid = (r', vvs', nid')
    -> vvs_range vvs' nid'
    /\ NoDup (map fst r')
    /\ (forall k, In k (map fst r') -> In k (map fst r) \/ In k (map fst r1))
    /\ vvs_grows vvs vvs' /\ nid <= nid' /\ wt_vvs vvs'
    /\ vvs_smaller_variables vvs'
    /\ (forall x y, In (x,y) r' -> exists z, vvs' ! y = Some (R (fst x), z))
    /\ (forall x y,
        list_assoc r' x = Some y
        -> list_assoc r x = Some y
        \/ exists y1 y2,
          list_assoc r1 x = Some y1
          /\ list_assoc r2 x = Some y2
          /\ forall b v,
            interp_sact vvs' (SVar cond_name) (Bits [b])
            -> interp_sact vvs' (SVar (if b then y1 else y2)) v
            <-> interp_sact vvs' (SVar y) v).
  Proof.
    Opaque list_assoc.
    induction r1; simpl; intros; eauto.
    - inv H; eauto. repeat refine (conj _ _); auto. apply vvs_grows_refl. lia.
    - inv F2. destr_in H.
      destr_in H.
      destr_in H.
      do 2 destr_in H.
      inv NDr1.
      eapply IHr1 in Heqp3; eauto.
      destruct Heqp3 as
        (RNG2 & ND2 & INCL & GROWS & LE & WTv2 & VSV2 & R2VR2 & EVAL).
      destr_in H; inv H; eauto.
      * repeat refine (conj _ _); eauto.
        -- simpl. constructor; eauto. intro IN; apply INCL in IN.
           destruct IN; eauto.
           apply DISJ in H. auto. left; auto.
        -- simpl. intros k [EQ|IN]; eauto. apply INCL in IN. destruct IN; auto.
        -- simpl; intros x y [EQ|IN]; eauto.
           inv EQ.
           edestruct R2V1. left; reflexivity.
           erewrite GROWS; eauto.
        -- intros x y GET; rewrite list_assoc_cons in GET. destr_in GET; eauto.
           ++ inv GET. right.
              do 2 eexists. split.
              rewrite list_assoc_cons. rewrite eq_dec_refl. eauto.
              split. rewrite list_assoc_cons. simpl in H2; subst.
              rewrite eq_dec_refl. eauto.
              intros b v INT. destr; tauto.
           ++ simpl in H2; subst.
              setoid_rewrite list_assoc_cons.
              rewrite Heqs1. eauto.
      * simpl.
        repeat refine (conj _ _); eauto.
        -- intros x y GET. rewrite PTree.gsspec in GET. destr_in GET. inv GET.
           red; lia.
           eapply RNG2 in GET. red in GET; red; lia.
        -- constructor; eauto.
           intro IN. apply INCL in IN. destruct IN; eauto.
           apply DISJ in H. auto. auto.
        -- intros k [EQ|IN]; eauto. apply INCL in IN; eauto. destruct IN; auto.
        -- eapply vvs_grows_trans. eauto. eapply vvs_grows_set. eauto. lia.
        -- lia.
        -- eapply wt_vvs_set; eauto.
           edestruct (R2V1 _ _ (or_introl eq_refl)) as (? & GET1).
           edestruct (R2V2 _ _ (or_introl eq_refl)) as (? & GET2).
           econstructor.
           eapply wt_sact_vvs_grows. 2: eauto. eauto.
           eapply wt_sact_vvs_grows. eauto. econstructor; eauto.
           simpl in H2. subst.
           eapply wt_sact_vvs_grows. eauto. econstructor; eauto. lia.
        -- red; simpl; intros x ? a GET. rewrite PTree.gsspec in GET.
           destr_in GET; eauto.
           inv GET. intros v' VIS.
           inv VIS; inv H7.
           eapply wt_sact_valid_vars in WTcond. 3: constructor. 2: eauto.
           red; lia.
           edestruct (R2V1 _ _ (or_introl eq_refl)) as (? & GET1).
           apply RNG in GET1; red in GET1. red; lia.
           edestruct (R2V2 _ _ (or_introl eq_refl)) as (? & GET2).
           apply RNG in GET2; red in GET2. red; lia.
        -- intros x y [EQ|IN]; eauto. rewrite PTree.gsspec. inv EQ.
           destr; try congruence. eauto.
           rewrite PTree.gsspec. destr; try congruence. simpl in H2. subst.
           apply R2VR2 in IN. destruct IN. apply RNG2 in H. red in H; lia.
           eauto.
        -- intros x y GET; rewrite list_assoc_cons in GET. destr_in GET; eauto.
           ++ inv GET. right.
              do 2 eexists. split.
              rewrite list_assoc_cons. rewrite eq_dec_refl. eauto.
              split. rewrite list_assoc_cons. simpl in H2; subst.
              rewrite eq_dec_refl. eauto.
              intros b v INT.
              Lemma interp_sact_var_cons:
                forall k v vvs x,
                interp_sact (PTree.set k v vvs) (SVar k) x
                <-> interp_sact (PTree.set k v vvs) (snd v) x.
              Proof.
                split.
                inversion 1; subst. rewrite PTree.gsspec in H1.
                destr_in H1; try congruence. inv H1. auto.
                destruct v. intros; econstructor.
                rewrite PTree.gss. eauto. auto.
              Qed.
              rewrite interp_sact_var_cons. simpl.
              Lemma interp_sact_iff:
                forall vvs c t f x b,
                interp_sact vvs c (Bits [b])
                -> interp_sact vvs (SIf c t f) x
                <-> interp_sact vvs (if b then t else f) x.
              Proof.
                split; intros.
                - inv H0. exploit interp_sact_determ. apply H. apply H5.
                  intro A; inv A. auto.
                - econstructor; eauto.
              Qed.
              rewrite interp_sact_iff; eauto. destr; tauto.

           ++ simpl in H2; subst.
              setoid_rewrite list_assoc_cons.
              rewrite Heqs1.

              assert (
                vvs_grows t (PTree.set p4 (R r2, SIf (SVar cond_name) (SVar p0)
                (SVar p2)) t)).
              {
                red; simpl; intros. rewrite PTree.gso. auto.
                apply RNG2 in H. red in H; lia.
              }
              edestruct EVAL. apply GET. auto.
              destruct H0 as (y1 & y2 & GET1 & GET2 & EVAL2).
              right; exists y1, y2. split; auto. split; auto. intros b v INT.
              setoid_rewrite (interp_sact_vvs_grows_iff t) in INT; eauto.
              destruct (R2VR2 _ _ (list_assoc_in _ _ _ GET)).
              destruct (R2V1 _ _ (or_intror (list_assoc_in _ _ _ GET1))).
              destruct (R2V2 _ _ (or_intror (list_assoc_in _ _ _ GET2))).
              setoid_rewrite (interp_sact_vvs_grows_iff t); eauto.
              econstructor. eapply GROWS.
              instantiate (1:=if b then x1 else x2). destr; eauto.
              econstructor. eauto.
              eapply wt_sact_vvs_grows. eauto. eauto.
      * intros; apply R2V2. right; auto.
  Qed.

  Lemma merge_reg2vars2_nd:
    forall r1 r2 cond_name vvs nid r' vvs' nid' (NDr: NoDup (map fst r1))
      (RNG: vvs_range vvs nid) (WTv: wt_vvs vvs)
      (VSV: vvs_smaller_variables vvs)
      (F2: Forall2 (fun x y => fst x = fst y) r1 r2)
      (R2V1: forall x y, In (x,y) r1 -> exists z, vvs !y = Some (R (fst x), z))
      (R2V2: forall x y, In (x,y) r2 -> exists z, vvs !y = Some (R (fst x), z))
      (WTcond: wt_sact vvs (SVar cond_name) (bits_t 1)),
    merge_reg2vars2 r1 r2 cond_name vvs nid = (r', vvs', nid')
    -> NoDup (map fst r')
    /\ (forall k, In k (map fst r') -> In k (map fst r1))
    /\ vvs_grows vvs vvs' /\ nid <= nid' /\ wt_vvs vvs'
    /\ vvs_smaller_variables vvs' /\ vvs_range vvs' nid'
    /\ (forall (x : reg_t * (Port + unit)) (y : positive),
      In (x, y) r' -> exists z : sact, vvs' ! y = Some (R (fst x), z))
    /\ (
      forall x y, list_assoc r' x = Some y
      -> exists y1 y2, list_assoc r1 x = Some y1
      /\ list_assoc r2 x = Some y2
      /\ forall b v, interp_sact vvs' (SVar cond_name) (Bits [b])
      -> interp_sact vvs' (SVar (if b then y1 else y2)) v
      <-> interp_sact vvs' (SVar y) v).
  Proof.
    unfold merge_reg2vars2. intros.
    edestruct merge_reg2vars_reg2_nd
      as (RNG2 & NDr2 & INCL & GROWS & LE & WTv2 & VSV2 & R2V & EVAL).
    12: eauto. all: eauto.
    constructor. simpl; easy. repeat refine (conj _ _); eauto.
    intros k IN. apply INCL in IN. simpl in IN. intuition auto with *.
    intros.
    edestruct EVAL; eauto. inv H1.
  Qed.
  Transparent list_assoc.

  Definition gria_list
    (guard: sact)
    (rec:
      uact -> (list (string * type)) -> list (string * positive) -> r2vtype
      -> var_value_map -> sact -> rule_information_raw -> rule_information_raw
      -> positive
      -> (
        option sact * list (string * positive) * r2vtype * PTree.t (type * sact)
        * sact * rule_information_raw * positive * type))
  :=
    fix gria_list (args: list uact) (tsig: list (string * type))
      (env: list (string * positive)) (reg2var : r2vtype)
      (vvs: PTree.t (type * sact)) (sched_rir: rule_information_raw)
      (rir: rule_information_raw) (nid: positive) names0 fail0
    : list (positive * type) * list (string * positive) * r2vtype
      * PTree.t (type * sact) * sact * rule_information_raw * positive
    :=
      match args with
      | [] => (names0, env, reg2var, vvs, fail0, rir, nid)
      | a::args =>
        let '(vc, vms, reg2var, vvs, failure, rir, nid, t) :=
          rec a tsig env reg2var vvs guard sched_rir rir nid
        in
        let arg_bind_name := nid in
        gria_list
          args tsig vms reg2var (PTree.set arg_bind_name (t, reduce t vc) vvs)
          sched_rir rir (Pos.succ nid) ((arg_bind_name, t) :: names0)
          (merge_failures failure fail0)
      end.

  (* This function extracts the actions for a given rule. *)
  (*
    - ua : the original action to simplify
    - tsig : the name and type of local variables
    - env : mapping from original var name to fresh variable
    - reg2var : mapping from register-port pair to fresh variable
    - vvs : for each fresh variable, its type and simple action (sact)
    - guard : a simple action denoting the path condition we're in
    - rir : information about reads and writes performed within this rule
    - nid : the next available fresh variable name

    Returns:
    - option sact : a simple action which evaluates equivalently to the original
      daction
    - list (string * positive) : updated env
    - list ((reg_t * Port) * positive) : updated reg2var
    - PTree.t (type * sact) : updated vvs
    - sact : the condition under which the action fails
    - rule_information_raw : updated rir
    - positive : updated nid
    - type : the type of the original action
  *)
  Fixpoint get_rule_information_aux
    (* No need to pass failures as these impact the whole rule - taking note of
    all of them and factoring the conditions in is enough. Conflicts between
    different actions are also dealt with here. *)
    (ua: uact) (tsig: list (string * type)) (env: list (string * positive))
    (reg2var: r2vtype) (vvs: PTree.t (type * sact)) (guard: sact)
    (sched_rir: rule_information_raw) (rir: rule_information_raw)
    (nid: positive)
    (* Returns value, env, var_values, failure condition, rule_information_raw,
       next_ids *)
    : option (sact) * list (string * positive) * r2vtype
      * (PTree.t (type * sact)) * sact * rule_information_raw * positive * type
    :=
    match ua with
    | DBind var val body =>
      let '(
        ret_val, vm_val, reg2var, vv_val, failures_val, rir_val, nid, tval
      ) :=
        get_rule_information_aux
          val tsig env reg2var vvs guard sched_rir rir nid
      in
      let name := nid in
      let '(
        ret_body, vm_body, reg2var, vv_body, failures_body, rir_body, nid, tbody
      ) :=
        get_rule_information_aux
          body ((var, tval)::tsig) ((var, name)::vm_val) reg2var
          (PTree.set name (tval,reduce tval ret_val) vv_val)
          guard sched_rir rir_val (Pos.succ nid) in
      (ret_body, skipn 1 vm_body (* var's binding goes out of scope *), reg2var,
        vv_body, merge_failures failures_val failures_body, rir_body, nid, tbody
      )
    | DAssign var val =>
      let '(ret_val, vm_val, reg2var, vv_val, failures_val, rir_val, nid, t) :=
        get_rule_information_aux
          val tsig env reg2var vvs guard sched_rir rir nid in
      let name := nid in
      (None, list_assoc_set vm_val var name, reg2var,
       PTree.set name (t, (reduce t ret_val)) vv_val, failures_val, rir_val,
       Pos.succ nid, bits_t 0)
    | DVar var =>
      match list_assoc env var, list_assoc tsig var with
      | Some x, Some t =>
        (Some (SVar x), env, reg2var, vvs, const_false, rir, nid, t)
      | _, _ => (* Unreachable assuming rule valid *)
        (None, env, reg2var, vvs, const_true, rir, nid, bits_t 0)
      end
    | DSeq a1 a2 =>
      let '(_, vm_a1, reg2var, vv_a1, failures_a1, rir_a1, nid_a1, _) :=
        get_rule_information_aux a1 tsig env reg2var vvs guard sched_rir rir nid
      in
      let '(ret_a2, vm_a2, reg2var, vv_a2, failures_a2, rir_a2, nid_a2, t) :=
        get_rule_information_aux
          a2 tsig vm_a1 reg2var vv_a1 guard sched_rir rir_a1 nid_a1
      in
      (ret_a2, vm_a2, reg2var, vv_a2, merge_failures failures_a1 failures_a2,
        rir_a2, nid_a2, t)
    | DIf cond tb fb =>
      let '(
        ret_cond, vm_cond, reg2var, vv_cond, failures_cond, rir_cond, nid, t
      ) :=
        get_rule_information_aux
          cond tsig env reg2var vvs guard sched_rir rir nid in
      let cond_name := nid in
      let guard_tb_name := Pos.succ nid in
      let guard_fb_name := Pos.succ guard_tb_name in
      let guard_tb := uand guard (SVar cond_name) in
      let guard_fb := uand guard (unot (SVar cond_name)) in
      let vv_cond :=
        PTree.set cond_name (bits_t 1, reduce (bits_t 1) ret_cond) vv_cond in
      let vv_cond := PTree.set guard_tb_name (bits_t 1, guard_tb) vv_cond in
      let vv_cond := PTree.set guard_fb_name (bits_t 1, guard_fb) vv_cond in
      let '(ret_tb, vm_tb, reg2var_tb, vv_tb, failures_tb, rir_tb, nid, t1) :=
        get_rule_information_aux
          tb tsig vm_cond reg2var vv_cond (SVar guard_tb_name) sched_rir
          rir_cond (Pos.succ guard_fb_name) in
      let '(ret_fb, vm_fb, reg2var_fb, vv_fb, failures_fb, rir_fb, nid, t2) :=
        (* We use rir_tb here even though we know that none of the actions added
           by the other branch can impact those from this branch (they are
           mutually exclusive). This way, we don't have to deal with
           rule_information_raw merging. However, this also means that the
           failure condition will contain some redundancy. *)
        get_rule_information_aux fb tsig vm_cond reg2var vv_tb
          (SVar guard_fb_name) sched_rir rir_tb nid in
      (* Merge var maps: if vm_tb and vm_fb disagree for some variable, generate
         a new variable reflecting the condition and update the variables map.
      *)
      let '(vm_merge, vvs, nid) :=
        merge_branches2 vm_tb vm_fb tsig vv_fb nid cond_name in
      let '(reg2var, vvs, nid) :=
        merge_reg2vars2 reg2var_tb reg2var_fb cond_name vvs nid in
      (Some
        (SIf
          (reduce (bits_t 1) ret_cond) (reduce t1 ret_tb) (reduce t2 ret_fb)),
          vm_merge, reg2var, vvs,
          uor failures_cond
            (uor
              (uand (reduce (bits_t 1) ret_cond) failures_tb)
              (uand (unot (reduce (bits_t 1) ret_cond)) failures_fb)),
            rir_fb, nid, t1)
    | DUnop ufn a =>
      let '(ret_a, vm_a, reg2var, vv_a, failures_a, rir_a, nid, t) :=
        get_rule_information_aux a tsig env reg2var vvs guard sched_rir rir nid
      in
      (Some (SUnop ufn (reduce t ret_a)), vm_a, reg2var, vv_a, failures_a,
       rir_a, nid, ret_type_unop ufn t)
    | DBinop ufn a1 a2 =>
      let '(ret_a1, vm_a1, reg2var, vvs, failures_a1, rir_a1, nid, t1) :=
        get_rule_information_aux a1 tsig env reg2var vvs guard sched_rir rir nid
      in
      let '(ret_a2, vm_a2, reg2var, vvs, failures_a2, rir_a2, nid, t2) :=
        get_rule_information_aux
          a2 tsig vm_a1 reg2var vvs guard sched_rir rir_a1 nid in
      (Some (SBinop ufn (reduce t1 ret_a1) (reduce t2 ret_a2)), vm_a2, reg2var,
       vvs, merge_failures failures_a1 failures_a2, rir_a2, nid,
       ret_type_binop ufn t1 t2)
    | DInternalCall ufn args =>
      let '(
        arg_names, vm_args, reg2var, vv_args, failure_args, rir_args, nid
      ) :=
        gria_list
          guard get_rule_information_aux args tsig env reg2var vvs sched_rir rir
          nid [] const_false in
      let vm_tmp :=
        combine
          (fst (split (rev (int_argspec ufn)))) (* Names from argspec *)
          (map fst arg_names) in
      let '(ret_ic, _, reg2var, vv_ic, failure_ic, rir_ic, nid, t) :=
        get_rule_information_aux
          (int_body ufn) (rev (int_argspec ufn)) vm_tmp reg2var vv_args guard
          sched_rir rir_args nid in
      (* We can forget vm_tmp which contained the temporary map for use in the
         called function. *)
      (ret_ic, vm_args, reg2var, vv_ic, merge_failures failure_ic failure_args,
        rir_ic, nid, t)
    | DAPos _ e =>
      get_rule_information_aux e tsig env reg2var vvs guard sched_rir rir nid
    | DRead port reg =>
      let failure :=
        match port with
        | P0 =>
          uor (rir_has_write0 sched_rir reg) (rir_has_write1 sched_rir reg)
        | P1 => rir_has_write1 sched_rir reg
        end in
      let modified_rir :=
        match port with
        | P0 => add_read0 rir guard reg
        | P1 => add_read1 rir guard reg
        end in
      match list_assoc reg2var (reg, inl port) with
      | Some v =>
        (Some (SVar v), env, reg2var, vvs, failure, modified_rir, nid, R reg)
      | None => (None, env, reg2var, vvs, const_true, modified_rir, nid, R reg)
      end
    | DWrite port reg val =>
      let '(ret_val, vm_val, reg2var, vvs, failures_val, rir, nid, t) :=
        get_rule_information_aux
          val tsig env reg2var vvs guard sched_rir rir nid in
      let '(rir_wr, failure_wr) :=
        match port with
        | P0 => add_write0 sched_rir rir guard reg (reduce t ret_val)
        | P1 => add_write1 sched_rir rir guard reg (reduce t ret_val)
        end in
      let v_read1 := nid in
      let nid := Pos.succ nid in
      let vvs := PTree.set v_read1 (t, reduce t ret_val) vvs in
      let reg2var :=
        match port with
        | P0 =>
          let reg2var := list_assoc_set reg2var (reg, inl P1) v_read1 in
          let reg2var := list_assoc_set reg2var (reg, inr tt) v_read1 in
          reg2var
        | P1 =>
          let reg2var := list_assoc_set reg2var (reg, inr tt) v_read1 in
          reg2var
        end in
      (None, vm_val, reg2var, vvs, merge_failures failures_val failure_wr,
       rir_wr, nid, bits_t 0)
    | DExternalCall ufn arg =>
      let '(ret_arg, vm_arg, reg2var, vv_arg, failures_arg, rir, nid, t) :=
        get_rule_information_aux
          arg tsig env reg2var vvs guard sched_rir rir nid in
      let name := nid in
      (Some (SVar name), vm_arg, reg2var,
       (PTree.set name (retSig (Sigma ufn),
        SExternalCall ufn (reduce t ret_arg)) vv_arg),
       failures_arg, rir, Pos.succ nid, retSig (Sigma ufn))
    | DError _ => (None, env, reg2var, vvs, const_true, rir, nid, bits_t 0)
    | DFail tau => (None, env, reg2var, vvs, const_true, rir, nid, tau)
    | DConst tau c =>
      (Some (SConst c), env, reg2var, vvs, const_false, rir, nid, tau)
    end.

  Definition same_env env1 env2 :=
    Forall2 (fun x y : string * positive => fst x = fst y) env1 env2.

  Lemma same_env_set_in:
    forall env' env (SAMEENV: same_env env env') v n
      (VARIN: In v (map fst env)),
    same_env env (list_assoc_set env' v n).
  Proof.
    Opaque eq_dec.
    induction env'; simpl; intros; eauto.
    - inv SAMEENV. simpl in *; easy.
    - inv SAMEENV. simpl in *. destr. simpl in *. subst.
      destr.
      + subst. simpl. constructor. reflexivity. auto.
      + constructor. reflexivity. eapply IHenv'. eauto.
        destruct VARIN; congruence.
  Qed.

  Lemma same_env_trans:
    forall l1 l2, same_env l1 l2 -> forall l3, same_env l2 l3 -> same_env l1 l3.
  Proof. eapply Forall2_trans. congruence. Qed.

  Lemma same_env_refl: forall (l: list (string * positive)), same_env l l.
  Proof. unfold same_env; induction l; simpl; intros; eauto. Qed.

  Lemma same_env_sym:
    forall (l1 l2: list (string * positive)), same_env l1 l2 -> same_env l2 l1.
  Proof. unfold same_env. induction 1; simpl; intros; eauto. Qed.

  Lemma merge_vms_preserve_same_env:
    forall
      (l2 l4: list (string*positive)) (F: same_env l2 l4)
      (l3: var_value_map) cname n1 env' vvs n2,
    merge_branches l2 l4 l3 n1 cname = (env', vvs, n2) -> same_env l2 env'.
  Proof.
    induction 1; simpl; intros; eauto.
    - inv H. constructor.
    - do 4 destr_in H0. apply IHF in Heqp1.
      destr_in H0. inv H0. constructor; auto.
      inv H0. constructor; auto.
  Qed.

  Lemma fst_split_map:
    forall {A B: Type} (l: list (A*B)), fst (split l) = map fst l.
  Proof.
    induction l; simpl; intros; eauto. repeat destr. subst. simpl. f_equal.
    simpl in IHl. auto.
  Qed.

  Lemma vvs_range_none:
    forall l n name, vvs_range l n -> ~ valid_name name n -> l ! name = None.
  Proof.
    unfold vvs_range; intros.
    destruct (l ! name) eqn:?; eauto. eapply H in Heqo; eauto. congruence.
  Qed.

  Lemma wt_sact_fold_uor:
    forall conds vvs, Forall (fun a => wt_sact vvs a (bits_t 1)) conds
    -> forall ci, wt_sact vvs ci (bits_t 1)
    -> wt_sact vvs (fold_left uor conds ci) (bits_t 1).
  Proof.
    induction 1; simpl; intros; eauto.
    apply IHForall. econstructor; eauto. constructor.
  Qed.

  Lemma wt_sact_or_conds:
    forall conds vvs, Forall (fun a => wt_sact vvs a (bits_t 1)) conds
    -> wt_sact vvs (or_conds conds) (bits_t 1).
  Proof.
    intros; eapply wt_sact_fold_uor; eauto.
    repeat constructor.
  Qed.

  Lemma env_vvs_ex:
    forall
      env vvs tsig (EV: env_vvs env vvs tsig) x v t
      (GET1: list_assoc env x = Some v) (GET2: list_assoc tsig x = Some t),
    exists s, vvs !v = Some (t, s).
  Proof.
    induction 1; simpl; intros; eauto. inv GET1.
    repeat destr_in H. subst.
    destruct H as (EQ & (ss & GET3)). subst.
    destr_in GET1. inv GET1; inv GET2. eauto.
    eauto.
  Qed.

  Lemma env_vvs_some_none:
    forall env vvs tsig, env_vvs env vvs tsig
    -> forall v n, list_assoc env v = Some n
    -> list_assoc tsig v = None
    -> False.
  Proof.
    induction 1; simpl; intros; eauto. easy.
    repeat destr_in H. destruct H as (? & ? & ?). subst.
    repeat destr_in H1. easy. eauto.
  Qed.

  Lemma env_vvs_set:
    forall env vvs tsig, env_vvs env vvs tsig
    -> forall v n t a, list_assoc tsig v = Some t
    -> vvs_range vvs n
    -> env_vvs (list_assoc_set env v n) (PTree.set n (t, a) vvs) tsig.
  Proof.
    induction 1; simpl; intros; eauto. easy.
    repeat destr_in H. destruct H as (EQ & ss & GET). subst.
    destr_in H1; inv H1.
    + constructor. split; auto. rewrite PTree.gss; eauto.
      eapply Forall2_impl. 2: eauto.
      simpl; intros; eauto.
      repeat destr_in H. destruct H as (? & ? & GET2). subst. split; eauto.
      rewrite PTree.gso; eauto.
      intro; subst.
      eapply H2 in GET2. red in GET2. lia.
    + constructor. split; auto. rewrite PTree.gso. eauto.
      eapply H2 in GET. red in GET. lia.
      eapply Forall2_impl. intros; auto.
      2: eapply IHForall2. 2-3: eauto.
      simpl; intros. destr. eauto.
  Qed.

  Lemma env_vvs_change_vvs:
    forall env vvs tsig, env_vvs env vvs tsig
    -> forall n k v, vvs_range vvs n
    -> k >= n
    -> env_vvs env (PTree.set k v vvs) tsig.
  Proof.
    induction 1; simpl; intros; eauto. constructor.
    repeat destr_in H. destruct H as (? & ? & ?). subst.
    constructor; eauto.
    - split; auto. rewrite PTree.gso. eauto.
      apply H1 in H3. red in H3. lia.
    - eapply IHForall2; eauto.
  Qed.

  Lemma env_vvs_vvs_grows:
    forall env vvs tsig, env_vvs env vvs tsig
    -> forall vvs', vvs_grows vvs vvs'
    -> env_vvs env vvs' tsig.
  Proof.
    induction 1; simpl; intros; eauto. constructor.
    repeat destr_in H. destruct H as (? & ? & ?). subst.
    constructor; eauto.
    eapply Forall2_impl; eauto. simpl. intros. destr. destruct b. destruct H.
    subst. split. auto. destruct H3. exists x. auto.
  Qed.

  Lemma vvs_smaller_variables_set:
    forall vvs, vvs_smaller_variables vvs
    -> forall n t a, (forall v, var_in_sact a v -> v < n)
    -> vvs_smaller_variables (PTree.set n (t, a) vvs).
  Proof.
    red; intros.
    rewrite PTree.gsspec in H1. destr_in H1. inv H1. red. eauto.
    eauto.
  Qed.

  Lemma wt_sact_reduce:
    forall vvs t o, (forall x, o = Some x -> wt_sact vvs x t)
    -> wt_sact vvs (reduce t o) t.
  Proof.
    intros.
    destruct o. simpl. eauto.
    simpl. constructor. apply wt_val_of_type.
  Qed.

  Lemma wt_sact_interp_bool:
    forall vvs, wt_vvs vvs
    -> vvs_smaller_variables vvs
    -> forall n a, vvs_range vvs n
    -> wt_sact vvs a (bits_t 1)
    -> exists b, interp_sact vvs a (Bits [b]).
  Proof.
    intros.
    edestruct wt_sact_interp as (v & Iv & WTv); eauto.
    apply wt_val_bool in WTv. destruct WTv. subst. eauto.
  Qed.

  Lemma wt_val_determ: forall v t1 t2, wt_val t1 v -> wt_val t2 v -> t1 = t2.
  Proof.
    induction v using val_ind'; simpl; intros; eauto.
    - inv H. inv H0. auto.
    - inv H. inv H0. auto.
    - inv H0. inv H1. auto.
    - inv H0. inv H1. auto.
  Qed.

  Lemma interp_sact_wt:
    forall vvs, wt_vvs vvs
    -> vvs_smaller_variables vvs
    -> forall (n : positive) (a : sact) (t : type), vvs_range vvs n
    -> wt_sact vvs a t
    -> forall v, interp_sact vvs a v
    -> wt_val t v.
  Proof.
    intros.
    edestruct wt_sact_interp as (x & IV & WTv); eauto.
    exploit interp_sact_determ. apply H3. apply IV. intros ->; auto.
  Qed.

  Lemma interp_sact_wt_bool:
    forall vvs, wt_vvs vvs
    -> vvs_smaller_variables vvs
    -> forall (n : positive) (a : sact), vvs_range vvs n
    -> wt_sact vvs a (bits_t 1)
    -> forall v, interp_sact vvs a v
    -> exists b, v = Bits [b].
  Proof.
    intros.
    eapply interp_sact_wt in H3; eauto. eapply wt_val_bool; eauto.
  Qed.

  Lemma interp_sact_list_assoc_set:
    forall vvs, wt_vvs vvs
    -> vvs_smaller_variables vvs
    -> forall n a x v, (forall v, var_in_sact a v -> v < n)
    -> forall m, n <= m
    -> interp_sact (PTree.set m x vvs) a v -> interp_sact vvs a v.
  Proof.
    intros vvs WTvvs VSV n a.
    change n with (projT1 (existT (fun _ => sact) n a)).
    change a with (projT2 (existT (fun _ => sact) n a)) at 1 4 5.
    generalize (existT (fun _ => sact) n a).
    clear n a. intro s. pattern s.
    eapply well_founded_induction.
    apply wf_order_sact. clear s.
    intros x IH t vv BELOW m LE INTERP.
    destruct x; simpl in *.
    inv INTERP.
    - trim (BELOW var). constructor. rewrite PTree.gso in H by lia.
      econstructor; eauto.
      generalize (VSV _ _ _ H). intros.
      eapply (IH (existT _ var a)). 4: simpl; eauto.
      + red. apply Relation_Operators.left_lex. auto.
      + simpl. eauto.
      + simpl. lia.
    - constructor.
    - exploit IH.
      + red. apply Relation_Operators.right_lex. instantiate (1:=c). simpl; lia.
      + simpl. intros; eapply BELOW. constructor. auto.
      + simpl. eauto.
      + simpl. eauto.
      + exploit (IH (existT _ x (if b then t0 else f))).
        * red. apply Relation_Operators.right_lex. simpl; destruct b; lia.
        * simpl. intros; eapply BELOW.
          destruct b. eapply var_in_if_true. eauto.
          eapply var_in_if_false; eauto.
        * simpl. eauto.
        * simpl. eauto.
        * simpl. intros.
          econstructor; eauto.
    - exploit IH.
      + red. apply Relation_Operators.right_lex. instantiate (1:=a). simpl; lia.
      + simpl. intros; eapply BELOW. constructor. auto.
      + simpl. eauto.
      + simpl in *. eauto.
      + simpl; auto. intros. econstructor; eauto.
    - exploit IH.
      + red. apply Relation_Operators.right_lex. instantiate (1:=a1).
        simpl; lia.
      + simpl. intros; eapply BELOW. constructor. auto.
      + simpl. eauto.
      + simpl in *. eauto.
      + exploit IH.
        * red. apply Relation_Operators.right_lex. instantiate (1:=a2).
          simpl; lia.
        * simpl. intros; eapply BELOW. eapply var_in_sact_binop_2; eauto.
        * simpl. eauto.
        * simpl in *. eauto.
        * simpl; auto. intros. econstructor; eauto.
    - exploit IH.
      + red. apply Relation_Operators.right_lex. instantiate (1:=a). simpl; lia.
      + simpl. intros; eapply BELOW. constructor. auto.
      + simpl. eauto.
      + simpl in *. eauto.
      + simpl; auto. intros. econstructor; eauto.
    - constructor.
  Qed.

  Lemma interp_sact_list_assoc_set':
    forall vvs, wt_vvs vvs
    -> vvs_smaller_variables vvs
    -> forall n a x v, vvs_range vvs n
    -> (forall v, var_in_sact a v -> v < n)
    -> interp_sact (PTree.set n x vvs) a v <-> interp_sact vvs a v.
  Proof.
    intros; split.
    eapply interp_sact_list_assoc_set; eauto. lia.
    intros; eapply vvs_grows_interp_sact; eauto.
    eapply vvs_grows_set; eauto. lia.
  Qed.

  Definition match_Gamma_env
    (Gamma: list (string * val)) (env: list (string * positive)) vvs
  :=
    Forall2 (
      fun x y => fst x = fst y /\ interp_sact vvs (SVar (snd y)) (snd x)
    ) Gamma env.

  Lemma merge_branches_grows:
    forall vm_tb vm_fb vvs nid cond_name vm' vvs' nid' tsig
      (MB: merge_branches vm_tb vm_fb vvs nid cond_name = (vm', vvs', nid'))
      (ENVVVS1: env_vvs vm_tb vvs tsig) (ENVVVS2: env_vvs vm_fb vvs tsig)
      (RNGVVS: vvs_range vvs nid) (VVSVALID: vvs_smaller_variables vvs)
      (VALIDCOND: valid_name cond_name nid)
      (WTCOND: wt_sact vvs (SVar cond_name) (bits_t 1)) (WTVVS: wt_vvs vvs),
    vvs_grows vvs vvs' /\ vvs_range vvs' nid' /\ env_vvs vm' vvs' tsig
    /\ nid <= nid' /\ vvs_smaller_variables vvs' /\ wt_vvs vvs'
    /\ Forall2
         (fun '(xt,xf) x =>
           forall b, interp_sact vvs' (SVar cond_name) (Bits [b])
           -> (
             forall v, interp_sact vvs' (SVar (snd (if b then xt else xf))) v
             <-> interp_sact vvs' (SVar (snd x)) v))
         (combine vm_tb vm_fb) vm'.
  Proof.
   induction vm_tb; simpl; intros; eauto.
    - inv MB. repeat split; eauto using vvs_grows_refl. lia.
    - repeat destr_in MB; inv MB. now auto.
       + inv ENVVVS1. inv ENVVVS2. destruct y.
        destruct H1 as ( ? & ? & GET1).
        destruct H4 as ( ? & ? & GET2). subst.
        edestruct IHvm_tb as (
          VVSGROWS3 & VVSRANGE3 & ENVVVS3 & NIDGROWS3 & VVSVALID3 & WTVVS3
          & EVAL3
        ); eauto.
        repeat split; auto.
        constructor; eauto.
        constructor; eauto.
        intros. destr; tauto.
      + inv ENVVVS1. inv ENVVVS2. destruct y.
        destruct H1 as ( ? & ? & GET1).
        destruct H4 as ( ? & ? & GET2). subst.
        edestruct IHvm_tb as (
          VVSGROWS3 & VVSRANGE3 & ENVVVS3 & NIDGROWS3 & VVSVALID3 & WTVVS3
          & EVAL3
        ); eauto.
        repeat split; auto.
        * eapply vvs_grows_trans; eauto. eapply vvs_grows_set; eauto. lia.
        * eapply vvs_range_list_assoc_set. eapply vvs_range_incr.
          2: eauto. lia. red; lia.
        * constructor. split; auto. rewrite PTree.gss.
          assert (t1 = t0) by congruence. subst; eauto.
          eapply env_vvs_change_vvs. eauto. eauto. lia.
        * lia.
        * eapply vvs_smaller_variables_set; eauto.
          intros v VIS. inv VIS.
          -- inv H4. red in VALIDCOND; lia.
          -- inv H4. apply RNGVVS in Heqo. red in Heqo. lia.
          -- inv H4. apply RNGVVS in GET2. red in GET2. lia.
        * eapply wt_vvs_set; eauto.
          rewrite GET1 in Heqo; inv Heqo.
          econstructor; eauto.
          eapply wt_sact_vvs_grows; eauto.
          econstructor. eapply VVSGROWS3; eauto.
          econstructor. eapply VVSGROWS3; eauto. lia.
        * constructor; eauto.
          -- intros.
             split; intros IS.
             ++ econstructor. rewrite PTree.gss. eauto.
                econstructor. eauto. destruct b; eauto.
             ++ simpl in IS. inv IS. rewrite PTree.gss in H1. inv H1.
                inv H2.
                exploit interp_sact_determ. apply H. apply H7. intro A; inv A.
                destruct b0; eauto.
          -- eapply Wt.Forall2_impl. eapply EVAL3. simpl; intros.
             repeat destr_in H1.
             intros.
             rewrite interp_sact_list_assoc_set' in H2; eauto.
             rewrite interp_sact_list_assoc_set'; eauto.
             rewrite interp_sact_list_assoc_set'; eauto.
             inversion 1; subst.
             exploit @Forall2_Forall. apply ENVVVS3.
             rewrite Forall_forall; intro F.
             destruct (F _ H0) as (yy & IN & EQ).
             repeat destr_in EQ. subst. destruct EQ as (? & ? & GET). subst.
             eapply VVSRANGE3 in GET. red in GET; simpl; lia.
             inversion 1; subst.
             destr.
             exploit @Forall2_Forall. apply H3.
             rewrite Forall_forall; intro F.
             destruct (F _ (in_combine_l _ _ _ _ H)) as ( yy & IN & EQ).
             repeat destr_in EQ. subst. destruct EQ as (? & ? & GET). subst.
             eapply RNGVVS in GET. red in GET; simpl; lia.
             exploit @Forall2_Forall. apply H6.
             rewrite Forall_forall; intro F.
             destruct (F _ (in_combine_r _ _ _ _ H)) as ( yy & IN & EQ).
             repeat destr_in EQ. subst. destruct EQ as (? & ? & GET). subst.
             eapply RNGVVS in GET. red in GET; simpl; lia.
             inversion 1; subst. red in VALIDCOND. lia.
      + inv ENVVVS1. destr_in H1. decompose [ex and] H1. congruence.
  Qed.

  Lemma reg2var_vvs_grows:
    forall r2v vvs1 vvs2, reg2var_vvs r2v vvs1
    -> vvs_grows vvs1 vvs2
    -> reg2var_vvs r2v vvs2.
  Proof.
    unfold reg2var_vvs; intros.
    edestruct H as (y & GET & z & GET2). eauto.
  Qed.

  Lemma reg2var_vvs_set:
    forall r2v vvs r v, reg2var_vvs r2v vvs
    -> (exists z : sact, vvs !v = Some (R (fst r), z))
    -> reg2var_vvs (list_assoc_set r2v r v) vvs.
  Proof.
    red; intros.
    rewrite list_assoc_spec.
    destr; eauto. subst. eexists; split; eauto.
  Qed.

  Definition do_read (sched_log action_log: Log REnv) reg prt :=
    match prt with
    | P0 => getenv REnv r reg
    | P1 =>
      match latest_write0 (V:=val) (log_app action_log sched_log) reg with
      | None => getenv REnv r reg
      | Some v => v
      end
    end.

  Record match_log_vvs
    (vvs: var_value_map) (rir: rule_information_raw) (log: Log REnv)
  := {
    mlv_read0:
      forall idx, log_existsb log idx is_read0 = false
      <-> interp_sact vvs (rir_has_read0 rir idx) (Bits [false]);
    mlv_read1:
      forall idx, log_existsb log idx is_read1 = false
      <-> interp_sact vvs (rir_has_read1 rir idx) (Bits [false]);
    mlv_write0:
      forall idx, log_existsb log idx is_write0 = false
      <-> interp_sact vvs (rir_has_write0 rir idx) (Bits [false]);
    mlv_write1:
      forall idx, log_existsb log idx is_write1 = false
      <-> interp_sact vvs (rir_has_write1 rir idx) (Bits [false]);
  }.

  Definition wt_cond_log vvs (cl: cond_log) :=
    forall i a, In (i, a) cl -> wt_sact vvs a (bits_t 1).

  Record wf_rir (r: rule_information_raw) (vvs: PTree.t (type * sact)) := {
    wf_rir_read0s: wt_cond_log vvs (rir_read0s r);
    wf_rir_read1s: wt_cond_log vvs (rir_read1s r);
    wf_rir_write0s: wt_cond_log vvs (rir_write0s r);
    wf_rir_write1s: wt_cond_log vvs (rir_write1s r);
    wf_fail_wt: wt_sact (rir_vars r) (rir_failure_cond r) (bits_t 1);
    wf_nodup_read0: NoDup (map fst (rir_read0s r));
    wf_nodup_read1: NoDup (map fst (rir_read1s r));
    wf_nodup_write0: NoDup (map fst (rir_write0s r));
    wf_nodup_write1: NoDup (map fst (rir_write1s r));
  }.

  Record wf_state tsig env reg2var vvs rir nid := {
    wfs_wt_vvs: wt_vvs vvs;
    wfs_env_vvs: env_vvs env vvs tsig;
    wfs_r2v_vvs: reg2var_vvs reg2var vvs;
    wfs_vvs_range: vvs_range vvs nid;
    wfs_vsv: vvs_smaller_variables vvs;
    wfs_rir: wf_rir rir vvs;
    wfs_ndr: NoDup (map fst reg2var);
  }.

  Lemma interp_sact_vvs_grows_iff':
    forall (vvs vvs' : PTree.t (type * sact)) (a : sact) (v : val) (t : type)
      (n : positive) env tsig r2v rir,
    wf_state tsig env r2v vvs rir n
    -> vvs_grows vvs vvs'
    -> wt_sact vvs a t -> interp_sact vvs' a v <-> interp_sact vvs a v.
  Proof. intros; inv H; eapply interp_sact_vvs_grows_iff; eauto. Qed.

  Lemma wt_rir_has_read0:
    forall rir vvs idx, wf_rir rir vvs
    -> wt_sact vvs (rir_has_read0 rir idx) (bits_t 1).
  Proof.
    intros.
    unfold rir_has_read0. destr. 2: repeat constructor.
    eapply H. eapply list_assoc_in; eauto.
  Qed.

  Lemma wt_rir_has_read1:
    forall rir vvs idx, wf_rir rir vvs
    -> wt_sact vvs (rir_has_read1 rir idx) (bits_t 1).
  Proof.
    intros.
    unfold rir_has_read1. destr. 2: repeat constructor.
    eapply list_assoc_in in Heqo. eapply H in Heqo; eauto.
  Qed.

  Lemma wt_rir_has_write0:
    forall rir vvs idx, wf_rir rir vvs
    -> wt_sact vvs (rir_has_write0 rir idx) (bits_t 1).
  Proof.
    intros.
    unfold rir_has_write0. destr. 2: repeat constructor.
    eapply list_assoc_in in Heqo. eapply H in Heqo; eauto.
  Qed.

  Lemma wt_rir_has_write1:
    forall rir vvs idx, wf_rir rir vvs
    -> wt_sact vvs (rir_has_write1 rir idx) (bits_t 1).
  Proof.
    intros.
    unfold rir_has_write1. destr. 2: repeat constructor.
    eapply list_assoc_in in Heqo. eapply H in Heqo; eauto.
  Qed.

  Lemma match_log_vvs_grows':
    forall vvs1 vvs2 rir log n, match_log_vvs vvs1 rir log
    -> vvs_grows vvs1 vvs2
    -> vvs_range vvs1 n
    -> vvs_smaller_variables vvs1
    -> wt_vvs vvs1
    -> wf_rir rir vvs1
    -> match_log_vvs vvs2 rir log.
  Proof.
    intros vvs1 vvs2 rir log n MLV VG VR VSV WT WFR.
    inv MLV.
    split; intros.
    - erewrite interp_sact_vvs_grows_iff. 4: eauto. all: eauto.
      eapply wt_rir_has_read0. apply WFR.
    - erewrite interp_sact_vvs_grows_iff. 4: eauto. all: eauto.
      eapply wt_rir_has_read1. apply WFR.
    - erewrite interp_sact_vvs_grows_iff. 4: eauto. all: eauto.
      eapply wt_rir_has_write0. apply WFR.
    - erewrite interp_sact_vvs_grows_iff. 4: eauto. all: eauto.
      eapply wt_rir_has_write1. apply WFR.
  Qed.

  Lemma match_log_vvs_grows:
    forall vvs1 vvs2 rir log tsig env r2v n, match_log_vvs vvs1 rir log
    -> vvs_grows vvs1 vvs2
    -> wf_state tsig env r2v vvs1 rir n
    -> match_log_vvs vvs2 rir log.
  Proof.
    intros vvs1 vvs2 rir log tsig env r2v n MLV VG WS.
    inv MLV.
    split; intros.
    - erewrite interp_sact_vvs_grows_iff'. 3: eauto. 2: eauto. auto.
      eapply wt_rir_has_read0. apply WS.
    - erewrite interp_sact_vvs_grows_iff'. 3: eauto. 2: eauto. auto.
      eapply wt_rir_has_read1. apply WS.
    - erewrite interp_sact_vvs_grows_iff'. 3: eauto. 2: eauto. auto.
      eapply wt_rir_has_write0. apply WS.
    - erewrite interp_sact_vvs_grows_iff'. 3: eauto. 2: eauto. auto.
      eapply wt_rir_has_write1. apply WS.
  Qed.

  Record match_logs_r2v (r2v: list (reg_t * (Port + unit) * positive))
    (vvs: var_value_map) sched_rir (rir: rule_information_raw)
    (sched_log action_log: Log REnv)
  := {
    mlr_read:
      forall reg prt n, list_assoc r2v (reg, prt) = Some n
      -> interp_sact
           vvs (SVar n)
           (match prt with
             | inl prt => do_read sched_log action_log reg prt
             | _ =>
               match latest_write (log_app action_log sched_log) reg with
               | Some v => v
               | None => getenv REnv r reg
               end
             end);
    mlr_mlv_sched: match_log_vvs vvs sched_rir sched_log;
    mlr_mlv_action: match_log_vvs vvs rir action_log;
  }.

  Lemma wt_cond_log_grows:
    forall r n1 n2, wt_cond_log n1 r
    -> vvs_grows n1 n2
    -> wt_cond_log n2 r.
  Proof. intros. red; eauto using wt_sact_vvs_grows. Qed.

  Lemma wf_rir_grows:
    forall r n1 n2, wf_rir r n1
    -> vvs_grows n1 n2
    -> wf_rir r n2.
  Proof.
    intros. inv H. split; eauto using wt_sact_vvs_grows, wt_cond_log_grows.
  Qed.

  Lemma vvs_range_set:
    forall vvs n v, vvs_range vvs n
    -> vvs_range (PTree.set n v vvs) (Pos.succ n).
  Proof.
    unfold vvs_range; simpl; intros.
    rewrite PTree.gsspec in H0; destr_in H0; eauto. inv H0. red; lia.
    apply H in H0. red in H0; red; lia.
  Qed.

  Lemma merge_reg2var_aux_grows:
    forall
      r2v_tb r2v_fb (F2: Forall2 (fun x y => fst x = fst y) r2v_tb r2v_fb)
      r2v vvs nid cond_name r2v' vvs' nid'
      (MB:
        merge_reg2vars_reg2 r2v_tb r2v_fb cond_name r2v vvs nid
        = (r2v', vvs', nid'))
      (ENVVVS1:
        Forall (fun '(x,y) => exists z, vvs !y = Some (R (fst x), z)) r2v_tb)
      (ENVVVS2:
        Forall (fun '(x,y) => exists z, vvs !y = Some (R (fst x), z)) r2v_fb)
      (ENVVVSR:
         Forall (fun '(x,y) => exists z, vvs !y = Some (R (fst x), z)) r2v)
      (DISJ: forall k, In k (map fst r2v_tb) -> ~ In k (map fst r2v))
      (RNGVVS: vvs_range vvs nid) (VVSVALID: vvs_smaller_variables vvs)
      (VALIDCOND: valid_name cond_name nid)
      (WTCOND: wt_sact vvs (SVar cond_name) (bits_t 1))
      (WT: wt_vvs vvs) (NDr: NoDup (map fst r2v))
      (NDrt: NoDup (map fst r2v_tb)),
    vvs_grows vvs vvs' /\ vvs_range vvs' nid'
    /\ (Forall (fun '(x,y) => exists z, vvs' ! y = Some (R (fst x), z)) r2v')
    /\ (incl (map fst r2v_tb) (map fst r2v')) /\ nid <= nid'
    /\ vvs_smaller_variables vvs' /\ wt_vvs vvs' /\ NoDup (map fst r2v')
    /\ forall sched_log action_log rir sched_rir
         (MLR: match_logs_r2v r2v vvs sched_rir rir sched_log action_log)
         (WFR: wf_rir rir vvs) (WFSR: wf_rir sched_rir vvs)
         (MLR2:
           forall (b : bool), interp_sact vvs (SVar cond_name) (Bits [b])
           -> match_logs_r2v (if b then r2v_tb else r2v_fb) vvs sched_rir rir
                sched_log action_log),
    match_logs_r2v r2v' vvs' sched_rir rir sched_log action_log.
  Proof.
    induction 1; simpl; intros; eauto.
    - inv MB. repeat refine (conj _ _); eauto using vvs_grows_refl. red; easy.
      lia.
    - do 5 destr_in MB.
      edestruct IHF2 as (
        VG2 & VR2 & EX2 & INCL2 & LT2 & VSV2 & WT2 & NDr2 & MLR2
      ); eauto using reg2var_vvs_grows.
      inv ENVVVS1; auto.
      inv ENVVVS2; auto.
      inv NDrt; auto.
      inv ENVVVS1.
      inv ENVVVS2.
      destruct H2, H4. simpl in *; subst.
      edestruct merge_reg2vars_reg2_nd as (VR3 & NDl0 & INl0 & _). 12: eauto.
      all: eauto. inv NDrt; auto.
      rewrite Forall_forall in H3; eauto.
      intros x1 y INN; apply H3 in INN. auto.
      rewrite Forall_forall in H5; eauto.
      intros x1 y INN; apply H5 in INN. auto.
      rewrite Forall_forall in ENVVVSR; eauto.
      intros x1 y INN; apply ENVVVSR in INN. auto.
      destr_in MB; inv MB; repeat refine (conj _ _); eauto.
      + simpl. unfold incl. intros a [EQ|IN]; simpl; eauto.
      + simpl. constructor; eauto. intro IN. inv NDrt; auto.
        apply INl0 in IN. destruct IN; eauto.
        eapply DISJ in H. auto. left; auto.
      + intros sl al rr sr MLR WFR WFS EVAL.
        exploit MLR2. eauto. auto. auto. intros b INT.
        exploit EVAL. apply INT. destr.
        * destruct 1; split; auto.
          intros reg prt n GET. eapply mlr_read0. simpl. destr; eauto.
          clear Heqs1. inv e.
          inv NDrt. apply list_assoc_in in GET. apply (in_map fst) in GET.
          simpl in GET; congruence.
        * destruct 1; split; auto.
          intros reg prt n GET. eapply mlr_read0. simpl. destr; eauto.
          clear Heqs1. inv e.
          inv NDrt. apply list_assoc_in in GET. apply (in_map fst) in GET.
          simpl in GET.
          Lemma same_regenv_map:
            forall (r1 r2: r2vtype)
              (F: Forall2 (fun x y => fst x = fst y) r1 r2),
            map fst r1 = map fst r2.
          Proof. induction 1; simpl; intros; eauto. congruence. Qed.
          eapply same_regenv_map in F2. congruence.
        * destruct 1; split; auto.
          intros. simpl in H. destr_in H; eauto. clear Heqs1. inv e. inv H.
          edestruct wt_sact_interp_bool. apply WT. apply VVSVALID. apply RNGVVS.
          eapply WTCOND.
          eapply EVAL in H. destruct H.
          eapply vvs_grows_interp_sact. eauto. apply mlr_read1.
          destr; simpl; destr.
      + eapply vvs_grows_trans. eauto. eapply vvs_grows_set; eauto. lia.
      + eapply vvs_range_set; eauto.
      + constructor. simpl. rewrite PTree.gss. eauto.
        eapply Forall_impl. 2: apply EX2. simpl. intros (rp & nn) (z & GET).
        exploit VR2. eauto. unfold valid_name; intros.
        rewrite PTree.gso by lia. eauto.
      + simpl. red; intros a [EQ|IN]; subst; simpl; eauto.
      + lia.
      + eapply vvs_smaller_variables_set. auto. intros v VIS.
        inv VIS; inv H7.
        red in VALIDCOND; lia.
        apply RNGVVS in H0; red in H0; lia.
        apply RNGVVS in H1; red in H1; lia.
      + eapply wt_vvs_set; eauto. 2: lia.
        eapply wt_sact_vvs_grows with (vvs:=vvs). eauto.
        econstructor; eauto. econstructor; eauto.
        econstructor; eauto.
      + simpl. constructor; eauto.
        intro IN. apply INl0 in IN. destruct IN; eauto.
        eapply DISJ in H. auto. left; auto.
        inv NDrt. auto.
      + intros sl al rr sr MLR WFR WFS EVAL.
        exploit MLR2. eauto. auto. auto. intros b INT.
        exploit EVAL. apply INT. destr.
        * destruct 1; split; auto.
          intros reg prt nn GET. eapply mlr_read0. simpl. destr; eauto.
          clear Heqs1. inv e.
          inv NDrt. apply list_assoc_in in GET. apply (in_map fst) in GET.
          simpl in GET; congruence.
        * destruct 1; split; auto.
          intros reg prt nn GET. eapply mlr_read0. simpl. destr; eauto.
          clear Heqs1. inv e.
          inv NDrt. apply list_assoc_in in GET. apply (in_map fst) in GET.
          simpl in GET.
          eapply same_regenv_map in F2. congruence.
        * destruct 1; split; auto.
          -- intros. simpl in H. destr_in H; eauto.
             ++ clear Heqs1. inv e. inv H.
                edestruct wt_sact_interp_bool. apply WT. apply VVSVALID.
                apply RNGVVS.
                eapply WTCOND.
                exploit EVAL. apply H. destruct 1.
                econstructor. rewrite PTree.gss; eauto.
                eapply vvs_grows_interp_sact with (v1:=vvs).
                eapply vvs_grows_trans. eauto. eapply vvs_grows_set; eauto. lia.
                econstructor. eauto.
                destruct x1; eapply mlr_read1. simpl. rewrite eq_dec_refl. auto.
                simpl. rewrite eq_dec_refl. auto.
             ++ eapply vvs_grows_interp_sact with (v1:=t).
                eapply vvs_grows_set; eauto. lia.
                eapply mlr_read0. auto.
          -- eapply match_log_vvs_grows'; eauto.
             eapply vvs_grows_set; eauto. lia.
             eapply wf_rir_grows; eauto.
          -- eapply match_log_vvs_grows'; eauto.
             eapply vvs_grows_set; eauto. lia.
             eapply wf_rir_grows; eauto.
  Qed.

  Lemma merge_reg2var_grows:
    forall r2v_tb r2v_fb vvs nid cond_name r2v' vvs' nid'
      (F2: Forall2 (fun x y => fst x = fst y) r2v_tb r2v_fb)
      (MB: merge_reg2vars2 r2v_tb r2v_fb cond_name vvs nid = (r2v', vvs', nid'))
      (ENVVVS1: reg2var_vvs r2v_tb vvs) (ENVVVS2: reg2var_vvs r2v_fb vvs)
      (RNGVVS: vvs_range vvs nid) (VVSVALID: vvs_smaller_variables vvs)
      (VALIDCOND: valid_name cond_name nid)
      (WTCOND: wt_sact vvs (SVar cond_name) (bits_t 1)) (WT: wt_vvs vvs)
      (ND2: NoDup (map fst r2v_tb)),
    vvs_grows vvs vvs' /\ vvs_range vvs' nid' /\ reg2var_vvs r2v' vvs'
    /\ nid <= nid' /\ vvs_smaller_variables vvs' /\ wt_vvs vvs'
    /\ NoDup (map fst r2v')
    /\ forall sched_log action_log sched_rir rir
         (WFR: wf_rir rir vvs) (WFSR: wf_rir sched_rir vvs)
         (MLR2:
           forall (b : bool), interp_sact vvs (SVar cond_name) (Bits [b])
           -> match_logs_r2v
                (if b then r2v_tb else r2v_fb) vvs sched_rir rir sched_log
                action_log),
       match_logs_r2v r2v' vvs' sched_rir rir sched_log action_log.
  Proof.
    unfold merge_reg2vars2. simpl; intros.
    edestruct merge_reg2var_aux_grows as (
      VG & VR & R2V1 & R2V2 & NG & VSV & WTVVS & NDr2 & EVAL
    ); eauto.
    rewrite Forall_forall; intros (x & y) IN. apply nodup_in_assoc in IN; auto.
    destruct (ENVVVS1 x) as (? & GET1 & ? & GET2).
    rewrite IN in GET1; inv GET1; eauto.
    rewrite Forall_forall; intros (x & y) IN. apply nodup_in_assoc in IN; auto.
    destruct (ENVVVS2 x) as (? & GET1 & ? & GET2).
    rewrite IN in GET1; inv GET1; eauto.
    exploit same_regenv_map; eauto. congruence.
    constructor.
    repeat refine (conj _ _); eauto.
    red; intros.
    edestruct ENVVVS1 as (? & GET1 & ? & GET2).
    apply list_assoc_in_keys in GET1. apply R2V2 in GET1.
    rewrite in_map_iff in GET1.
    destruct GET1 as (? & EQ & IN).
    destruct x2. simpl in *. subst.
    rewrite Forall_forall in R2V1.
    specialize (R2V1 _ IN). simpl in R2V1.
    apply nodup_in_assoc in IN. eauto. auto.
    intros; eapply EVAL; eauto.
    exploit wt_sact_interp_bool. 4: apply WTCOND. auto. auto.
    eauto. intros (b & INT).
    specialize (MLR2 _ INT). inv MLR2.
    split; eauto. simpl; easy.
  Qed.

  Lemma wf_rir_add_write0:
    forall sched_rir rir vvs guard v idx rir' fail (WFR: wf_rir rir vvs)
      (WFRS: wf_rir sched_rir vvs) (WTg: wt_sact vvs guard (bits_t 1))
      (WV: wt_vvs vvs) (VSV: vvs_smaller_variables vvs) n (VR: vvs_range vvs n)
      (AW: add_write0 sched_rir rir guard idx v = (rir', fail)),
    wf_rir rir' vvs /\ wt_sact vvs fail (bits_t 1).
  Proof.
    intros. unfold add_write0 in AW. inv AW.
    split. split; simpl; eauto.
    - apply WFR.
    - apply WFR.
    - intros i c IN.
      apply in_list_assoc_set_inv in IN.
      inv WFR.
      destruct IN; eauto.
      inv H.
      destr; eauto.
      econstructor; eauto. apply list_assoc_in in Heqo; eauto.
      constructor.
    - apply WFR.
    - apply WFR.
    - apply WFR.
    - apply WFR.
    - eapply nodup_list_assoc_set; eauto. apply WFR.
    - apply WFR.
    - econstructor. eauto. 2: constructor.
      apply wt_sact_or_conds.
      repeat constructor.
      eapply wt_rir_has_write0; eauto.
      eapply wt_rir_has_read1; eauto.
      eapply wt_rir_has_write1; eauto.
      eapply wt_rir_has_write0; eauto.
      eapply wt_rir_has_read1; eauto.
      eapply wt_rir_has_write1; eauto.
  Qed.

  Lemma wf_rir_add_write1:
    forall sched_rir rir vvs guard v idx rir' fail (WFR: wf_rir rir vvs)
      (WFRS: wf_rir sched_rir vvs) (WTg: wt_sact vvs guard (bits_t 1))
      (WV: wt_vvs vvs) (VSV: vvs_smaller_variables vvs) n (VR: vvs_range vvs n)
      (AW: add_write1 sched_rir rir guard idx v = (rir', fail)),
    wf_rir rir' vvs /\ wt_sact vvs fail (bits_t 1).
  Proof.
    intros. unfold add_write1 in AW. inv AW.
    split.
    split; simpl; eauto.
    - apply WFR.
    - apply WFR.
    - apply WFR.
    - intros i c IN.
      apply in_list_assoc_set_inv in IN.
      inv WFR. destruct IN; eauto.
      inv H. destr; eauto. econstructor; eauto.
      apply list_assoc_in in Heqo; eauto.
      constructor.
    - apply WFR.
    - apply WFR.
    - apply WFR.
    - apply WFR.
    - eapply nodup_list_assoc_set; eauto. apply WFR.
    - econstructor. eauto. 2: constructor.
      apply wt_sact_or_conds.
      repeat constructor.
      eapply wt_rir_has_write1; eauto.
      eapply wt_rir_has_write1; eauto.
  Qed.

 Lemma wf_rir_add_read0:
    forall rir vvs guard idx, wf_rir rir vvs
    -> wt_sact vvs guard (bits_t 1)
    -> wf_rir (add_read0 rir guard idx) vvs.
  Proof.
    intros. inv H. unfold add_read0. split; simpl; eauto.
    red; intros.
    edestruct @in_list_assoc_set_inv. eapply H.
    - inv H1. destr; eauto.
      econstructor; eauto. 2: constructor.
      eapply wf_rir_read0s0; eauto.
      apply list_assoc_in in Heqo. eauto.
    - eauto.
    - apply nodup_list_assoc_set. auto.
  Qed.

  Lemma wf_rir_add_read1:
    forall rir vvs guard idx, wf_rir rir vvs
    -> wt_sact vvs guard (bits_t 1)
    -> wf_rir (add_read1 rir guard idx) vvs.
  Proof.
    intros. inv H. unfold add_read1. split; simpl; eauto.
    red; intros.
    apply in_list_assoc_set_inv in H. destruct H.
    - inv H. destr; eauto.
      econstructor; eauto.
      apply list_assoc_in in Heqo. eauto.
      constructor.
    - eauto.
    - eapply nodup_list_assoc_set; eauto.
  Qed.

  Definition bool_sact_grows vvs1 c1 vvs2 c2 : Prop :=
    interp_sact vvs1 c1 (Bits [true]) -> interp_sact vvs2 c2 (Bits [true]).

  Definition cond_log_grows vvs1 (cl1: cond_log) vvs2 cl2 grd :=
    forall idx,
    let c :=
      match list_assoc cl1 idx with
      | Some c => c
      | None => const_false
      end in
    let c' :=
      match list_assoc cl2 idx with
      | Some c => c
      | None => const_false
      end in
    bool_sact_grows vvs1 c vvs2 c'
    /\ (
      interp_sact vvs2 grd (Bits [false])
      -> forall b, interp_sact vvs1 c b
      <-> interp_sact vvs2 c' b).

  Record rir_grows vvs1 r1 vvs2 r2 grd : Prop := {
    rir_grows_read0s:
      cond_log_grows vvs1 (rir_read0s r1) vvs2 (rir_read0s r2) grd;
    rir_grows_read1s:
      cond_log_grows vvs1 (rir_read1s r1) vvs2 (rir_read1s r2) grd;
    rir_grows_write0s:
      cond_log_grows vvs1 (rir_write0s r1) vvs2 (rir_write0s r2) grd;
    rir_grows_write1s:
      cond_log_grows vvs1 (rir_write1s r1) vvs2 (rir_write1s r2) grd;
    rir_vvs_grows: vvs_grows vvs1 vvs2;
    rir_wt_grd: wt_sact vvs2 grd (bits_t 1);
  }.

  Lemma rir_grows_interp_sact:
    forall r1 v1 r2 v2 a v grd, rir_grows v1 r1 v2 r2 grd
    -> interp_sact v1 a v
    -> interp_sact v2 a v.
  Proof. inversion 1; eapply vvs_grows_interp_sact; eauto. Qed.

  Lemma bool_sact_grows_refl: forall vvs c, bool_sact_grows vvs c vvs c.
  Proof. red; intros; eauto. Qed.

  Lemma cond_log_grows_refl:
    forall vvs cl grd, cond_log_grows vvs cl vvs cl grd.
  Proof. red; intros. repeat split; eauto using bool_sact_grows_refl. Qed.

  Lemma rir_grows_refl: forall vvs r grd,
    wt_sact vvs grd (bits_t 1) -> rir_grows vvs r vvs r grd.
  Proof.
    split; eauto using cond_log_grows_refl, vvs_grows_refl.
  Qed.

  Lemma wf_sact_interp:
    forall tsig env r2v vvs rir n a t, wt_sact vvs a t
    -> wf_state tsig env r2v vvs rir n
    -> exists v, interp_sact vvs a v /\ wt_val t v.
  Proof.
    intros tsig env r2v vvs rir n a t WTs WFs. inv WFs.
    eapply wt_sact_interp; eauto.
  Qed.

  Lemma bool_sact_grows_trans:
    forall vvs1 c1 vvs2 c2, bool_sact_grows vvs1 c1 vvs2 c2
    -> forall vvs3 c3, bool_sact_grows vvs2 c2 vvs3 c3
    -> bool_sact_grows vvs1 c1 vvs3 c3.
  Proof. red; intros. eapply H in H1. eapply H0 in H1. eauto. Qed.

  Lemma cond_log_grows_trans:
    forall vvs1 cl1 vvs2 cl2 grd tsig env r2v rir n, wt_sact vvs2 grd (bits_t 1)
    -> wf_state tsig env r2v vvs2 rir n
    -> cond_log_grows vvs1 cl1 vvs2 cl2 grd
    -> forall cl3 tsig' env' r2v' vvs3 rir' n' grd',
      wt_sact vvs3 grd' (bits_t 1)
    -> wf_state tsig' env' r2v' vvs3 rir' n'
    -> vvs_grows vvs2 vvs3
    -> cond_log_grows vvs2 cl2 vvs3 cl3 grd'
    -> cond_log_grows vvs1 cl1 vvs3 cl3 (uor grd grd').
  Proof.
    red.
    intros vvs1 cl1 vvs2 cl2 grd tsig env r2v rir n WTG1 WFS1 CLG1 cl3 tsig'
      env' r2v' vvs3 rir' n' grd' WTG2 WFS2 VG2 CLG2 idx.
    edestruct (CLG1 idx) as (BSG1 & INCR1); eauto.
    edestruct (CLG2 idx) as (BSG2 & INCR2); eauto.
    split.
    eauto using bool_sact_grows_trans.
    intros.
    edestruct (wf_sact_interp) with (a:=grd) as (vv & IS & WTV); eauto.
    edestruct wt_val_bool; eauto. clear WTV; subst.
    edestruct (wf_sact_interp) with (a:=grd') as (vv & IS' & WTV); eauto.
    edestruct wt_val_bool; eauto. clear WTV; subst.
    exploit vvs_grows_interp_sact; eauto. intro ISg.
    inv H.
    exploit interp_sact_determ. apply ISg. apply H3.
    exploit interp_sact_determ. apply IS'. apply H5. intros; subst.
    simpl in H6. inv H6. apply orb_false_iff in H0. destruct H0; subst.
    rewrite INCR1; eauto.
  Qed.

  Lemma rir_grows_trans:
    forall vvs1 r1 vvs2 r2 grd tsig env r2v rir n,
    wf_state tsig env r2v vvs2 rir n
    -> rir_grows vvs1 r1 vvs2 r2 grd
    -> forall vvs3 r3 grd' tsig' env' r2v' rir' n',
      wf_state tsig' env' r2v' vvs3 rir' n'
    -> rir_grows vvs2 r2 vvs3 r3 grd'
    -> rir_grows vvs1 r1 vvs3 r3 (uor grd grd').
  Proof.
    intros. inv H0; inv H2.
    split; eauto using incl_tran, cond_log_grows_trans, vvs_grows_trans.
    econstructor; eauto. eapply wt_sact_vvs_grows; eauto. constructor.
  Qed.

  Lemma rir_grows_add_read0:
    forall
      vvs rir grd idx tsig env r2v nid
      (WFS: wf_state tsig env r2v vvs rir nid)
      (WTG: wt_sact vvs grd (bits_t 1)),
    rir_grows vvs rir vvs (add_read0 rir grd idx) grd.
  Proof.
    unfold add_read0. intros.
    split; simpl; eauto using incl_refl, cond_log_grows_refl, vvs_grows_refl.
    red; intros.
    edestruct wf_sact_interp with (a:=grd) as (x & IV & WTv); eauto.
    apply wt_val_bool in WTv. destruct WTv; subst.
    split.
    - destr.
      + subst. rewrite list_assoc_spec. rewrite Heqo.
        destruct eq_dec.
        subst. rewrite Heqo.
        red; intros.
        econstructor; eauto.
        eauto using bool_sact_grows_refl.
      + rewrite list_assoc_spec. rewrite Heqo.
        destruct eq_dec.
        subst. rewrite Heqo.
        red; intros. inv H.
        eauto using bool_sact_grows_refl.
    - intros.
      exploit interp_sact_determ. apply IV. apply H. intro A; inv A.
      rewrite list_assoc_spec.
      destruct eq_dec; subst.
      + destr.
        split; intros. econstructor; eauto.
        exploit interp_sact_wt_bool. 5: apply H0. all: try apply WFS.
        apply list_assoc_in in Heqo.
        eapply wf_rir_read0s in Heqo. 2: apply WFS. auto.
        intros (b0 & ?); subst. simpl.
        simpl. rewrite orb_false_r; auto.
        inv H0. exploit interp_sact_determ. apply IV. apply H6. intros <-.
        exploit wf_rir_read0s. inv WFS; eauto. apply list_assoc_in. eauto.
        intro WTs.
        exploit interp_sact_wt_bool. 5: apply H4. 4: eauto.
        1-3: inv WFS; eauto.
        intros (? & ?). subst. simpl in H7. inv H7.
        rewrite orb_false_r. auto.
        split; intros. inv H0. auto.
        exploit interp_sact_determ. apply H0. apply IV. intros; subst.
        constructor.
      + destr. tauto. tauto.
  Qed.

  Lemma rir_grows_add_read1:
    forall
      vvs rir grd idx tsig env r2v nid
      (WFS: wf_state tsig env r2v vvs rir nid)
      (WTG: wt_sact vvs grd (bits_t 1)),
    rir_grows vvs rir vvs (add_read1 rir grd idx) grd.
  Proof.
    unfold add_read1. intros.
    split; simpl; eauto using incl_refl, cond_log_grows_refl, vvs_grows_refl.
    red; intros.
    edestruct wf_sact_interp with (a:=grd) as (x & IV & WTv); eauto.
    apply wt_val_bool in WTv. destruct WTv; subst.
    split.
    - destr.
      + subst. rewrite list_assoc_spec. rewrite Heqo.
        destruct eq_dec.
        subst. rewrite Heqo.
        red; intros.
        econstructor; eauto.
        eauto using bool_sact_grows_refl.
      + rewrite list_assoc_spec. rewrite Heqo.
        destruct eq_dec.
        subst. rewrite Heqo.
        red; intros. inv H.
        eauto using bool_sact_grows_refl.
    - intros.
      exploit interp_sact_determ. apply IV. apply H. intro A; inv A.
      rewrite list_assoc_spec.
      destruct eq_dec; subst.
      + destr.
        split; intros. econstructor; eauto.
        exploit interp_sact_wt_bool. 5: apply H0. all: try apply WFS.
        apply list_assoc_in in Heqo.
        eapply wf_rir_read1s in Heqo. 2: apply WFS. auto.
        intros (b0 & ?); subst. simpl.
        simpl. rewrite orb_false_r; auto.
        inv H0. exploit interp_sact_determ. apply IV. apply H6. intros <-.
        exploit wf_rir_read1s. inv WFS; eauto. apply list_assoc_in. eauto.
        intro WTs.
        exploit interp_sact_wt_bool. 5: apply H4. 4: eauto.
        1-3: inv WFS; eauto.
        intros (? & ?). subst. simpl in H7. inv H7.
        rewrite orb_false_r. auto.
        split; intros. inv H0. auto.
        exploit interp_sact_determ. apply H0. apply IV. intros; subst.
        constructor.
      + destr. tauto. tauto.
  Qed.

  Lemma interp_sact_change_vvs:
    forall a (vvs1: PTree.t (type * sact)) v (vvs2: PTree.t (type * sact)) n
      (VVSRANGE: vvs_range vvs1 n)
      (VVSGROWS:
        forall x, valid_name x n
        -> forall y, vvs1 ! x = Some y
        -> vvs2 ! x = Some y)
      (INF: interp_sact vvs1 a v),
    interp_sact vvs2 a v.
  Proof. induction 3; simpl; intros; eauto; try now (econstructor; eauto). Qed.

  Lemma cond_log_grows_change_vvs:
    forall vvs1 vvs2 n cl grd env tsig r2v rir, wf_state tsig env r2v vvs1 rir n
    -> vvs_range vvs1 n
    -> (forall x, valid_name x n
        -> forall y, vvs1 ! x = Some y -> vvs2 ! x = Some y)
    -> (forall i a, In (i, a) cl -> wt_sact vvs1 a (bits_t 1))
    -> cond_log_grows vvs1 cl vvs2 cl grd.
  Proof.
    red; intros. split.
    - red; simpl; intros. eapply vvs_grows_interp_sact; eauto.
      red; intros; eauto.
    - intros. destr. 2: split; inversion 1; econstructor; eauto.
      split; intros.
      eapply vvs_grows_interp_sact; eauto.
      red; intros; eauto.
      eapply interp_sact_vvs_grows_inv; eauto. inv H; eauto.
      inv H; eauto.
      red; intros; eapply H1; eauto.
      eapply H2; eauto. eapply list_assoc_in; eauto.
  Qed.

  Lemma rir_grows_change_vvs:
    forall vvs1 vvs2 rir n grd tsig env r2v, wf_state tsig env r2v vvs1 rir n
    -> (forall x, valid_name x n
        -> forall y, vvs1 ! x = Some y -> vvs2 ! x = Some y)
    -> wt_sact vvs2 grd (bits_t 1)
    -> rir_grows vvs1 rir vvs2 rir grd.
  Proof.
    intros. split; eauto using cond_log_grows_refl, incl_refl.
    - eapply cond_log_grows_change_vvs; eauto. inv H; auto.
      inv H. intros; eapply wf_rir_read0s; eauto.
    - eapply cond_log_grows_change_vvs; eauto. inv H; auto.
      inv H. intros; eapply wf_rir_read1s; eauto.
    - eapply cond_log_grows_change_vvs; eauto. inv H; auto.
      inv H. intros; eapply wf_rir_write0s; eauto.
    - eapply cond_log_grows_change_vvs; eauto. inv H; auto.
      inv H. intros; eapply wf_rir_write1s; eauto.
    - red; intros; eapply H0; eauto.
      eapply wfs_vvs_range in H2; eauto.
  Qed.

  Lemma rir_grows_set:
    forall vvs rir name n v tsig env r2v, wf_state tsig env r2v vvs rir n
    -> ~ valid_name name n
    -> rir_grows vvs rir (PTree.set name v vvs) rir const_false.
  Proof.
    intros; eapply rir_grows_change_vvs; eauto.
    intros; rewrite PTree.gso; eauto. congruence.
    eapply wt_sact_vvs_grows; eauto. eapply vvs_grows_set; eauto. apply H.
    repeat constructor.
  Qed.

  Lemma match_Gamma_env_vvs_grows:
    forall Gamma env vvs, match_Gamma_env Gamma env vvs
    -> forall vvs', vvs_grows vvs vvs'
    -> match_Gamma_env Gamma env vvs'.
  Proof.
    induction 1; simpl; intros; eauto.
    constructor.
    destruct H.
    constructor; eauto. split; eauto using vvs_grows_interp_sact.
    eapply Forall2_impl; eauto. simpl; intros; eauto.
    destruct H3; split; eauto using vvs_grows_interp_sact.
  Qed.

  Lemma match_logs_r2v_vvs_grows:
    forall r2v vvs sl al sched_rir rir vvs' n,
    match_logs_r2v r2v vvs sched_rir rir sl al
    -> vvs_grows vvs vvs'
    -> vvs_range vvs n
    -> vvs_smaller_variables vvs
    -> wt_vvs vvs
    -> wf_rir rir vvs
    -> wf_rir sched_rir vvs
    -> match_logs_r2v r2v vvs' sched_rir rir sl al.
  Proof.
    intros. inv H. split; intros; eauto.
    eapply vvs_grows_interp_sact; eauto.
    eapply match_log_vvs_grows'; eauto.
    eapply match_log_vvs_grows'; eauto.
  Qed.

  Lemma rir_grows_weaken_guard:
    forall vvs1 rir1 vvs2 rir2 grd1 grd2, rir_grows vvs1 rir1 vvs2 rir2 grd1
    -> (interp_sact vvs2 grd2 (Bits [false])
        -> interp_sact vvs2 grd1 (Bits [false]))
    -> wt_sact vvs2 grd2 (bits_t 1)
    -> rir_grows vvs1 rir1 vvs2 rir2 grd2.
  Proof.
    intros. inv H; split; eauto.
    - red; intros.
      edestruct (rir_grows_read0s0 idx). split. eauto.
      intros; eauto.
    - red; intros.
      edestruct (rir_grows_read1s0 idx). split. eauto.
      intros; eauto.
    - red; intros.
      edestruct rir_grows_write0s0; eauto.
    - red; intros.
      edestruct rir_grows_write1s0; eauto.
  Qed.

  Lemma wf_state_set:
    forall tsig env reg2var vvs rir n, wf_state tsig env reg2var vvs rir n
    -> forall t v vv, wt_sact vvs vv t
    -> list_assoc tsig v = Some t
    -> wf_state
         tsig (list_assoc_set env v n) reg2var (PTree.set n (t, vv) vvs) rir
         (Pos.succ n).
  Proof.
    intros tsig env reg2var vvs rir n WFS t v vv WTA GETt.
    inv WFS; split; eauto.
    + eapply wt_vvs_set; eauto. lia.
    + eapply env_vvs_set; auto.
    + eapply reg2var_vvs_grows. eauto. eapply vvs_grows_set; eauto. lia.
    + eapply vvs_range_set. eauto.
    + eapply vvs_smaller_variables_set; eauto.
      eapply wt_sact_valid_vars; eauto.
    + eapply wf_rir_grows; eauto.
      eapply vvs_grows_set; eauto. lia.
  Qed.

  Lemma wf_state_vvs_set:
    forall tsig env reg2var vvs rir n, wf_state tsig env reg2var vvs rir n
    -> forall t vv, wt_sact vvs vv t
    -> forall k, k >= n
    -> (forall v0, var_in_sact vv v0 -> v0 < k)
    -> forall m, m > k
    -> wf_state tsig env reg2var (PTree.set k (t,vv) vvs) rir m
    /\ vvs_grows vvs (PTree.set k (t,vv) vvs).
  Proof.
    intros tsig env reg2var vvs rir n WFS t vv WTA k GEk VARRES m GTk.
    inv WFS; split; [split|]; eauto.
    + eapply wt_vvs_set; eauto.
    + eapply env_vvs_vvs_grows; eauto. eapply vvs_grows_set; eauto.
    + eapply reg2var_vvs_grows. eauto. eapply vvs_grows_set; eauto.
    + eapply vvs_range_list_assoc_set. eapply vvs_range_incr. 2: eauto. lia.
      red; lia.
    + eapply vvs_smaller_variables_set; eauto.
    + eapply wf_rir_grows; eauto. eapply vvs_grows_set; eauto.
    + eapply vvs_grows_set; eauto.
  Qed.

  Lemma env_vvs_none_some:
    forall env vvs tsig, env_vvs env vvs tsig
    -> forall v n, list_assoc env v = None
    -> list_assoc tsig v = Some n
    -> False.
  Proof.
    induction 1; simpl; intros; eauto. easy.
    repeat destr_in H. destruct H as (? & ? & ?). subst.
    repeat destr_in H1. easy. eauto.
  Qed.

  Lemma wf_state_vvs_grows_incr:
    forall tsig env r2v vvs rir n rir' vvs' n' grd,
    wf_state tsig env r2v vvs rir n
    -> rir_grows vvs rir vvs' rir' grd
    -> wt_vvs vvs'
    -> vvs_range vvs' n'
    -> vvs_smaller_variables vvs'
    -> wf_rir rir' vvs'
    -> n <= n'
    -> wf_state tsig env r2v vvs' rir' n'.
  Proof.
    intros tsig env r2v vvs rir n rir' vvs' n' grd WFS RG WTV VR VSV WFR LE.
    inv WFS; split; eauto.
    eapply env_vvs_vvs_grows; eauto using rir_vvs_grows.
    eapply reg2var_vvs_grows; eauto using rir_vvs_grows.
  Qed.

  Lemma merge_branches_grows2 :
    forall vm_tb vm_fb vvs nid cond_name vm' vvs' nid' tsig r2v r2v' rir,
    merge_branches vm_tb vm_fb vvs nid cond_name = (vm', vvs', nid')
    -> wf_state tsig vm_tb r2v vvs rir nid
    -> wf_state tsig vm_fb r2v' vvs rir nid
    -> valid_name cond_name nid
    -> wt_sact vvs (SVar cond_name) (bits_t 1)
    -> vvs_grows vvs vvs'
    /\ nid <= nid' /\ wf_state tsig vm' r2v' vvs' rir nid'
    /\ Forall2
         (fun '(xt,xf) x =>
           forall b, interp_sact vvs' (SVar cond_name) (Bits [b])
           -> (
             forall v, interp_sact vvs' (SVar (snd (if b then xt else xf))) v
             <-> interp_sact vvs' (SVar (snd x)) v))
         (combine vm_tb vm_fb) vm'.
  Proof.
    intros. inv H0; inv H1.
    edestruct merge_branches_grows as (
      VVSGROWS4 & VVSRANGE4 & ENVVVS4 & NIDGROWS4 & VVSVALID4 & WTVVS4 & EVAL
    ); eauto.
    repeat refine (conj _ _); eauto.
    split; eauto.
    eapply reg2var_vvs_grows; eauto.
    eapply wf_rir_grows; eauto.
  Qed.

  Lemma merge_reg2var_grows2 :
    forall r2vt r2vf vvs nid cond_name r2v' vvs' nid' sched_rir rir env tsig
      env2
      (F2:
        Forall2
          (fun x y : reg_t * (Port + unit) * positive => fst x = fst y)
          r2vt r2vf
      ),
      merge_reg2vars2 r2vt r2vf cond_name vvs nid = (r2v', vvs', nid')
      -> wf_state tsig env2 r2vt vvs rir nid
      -> wf_state tsig env r2vf vvs rir nid
      -> wf_rir sched_rir vvs
      -> valid_name cond_name nid
      -> wt_sact vvs (SVar cond_name) (bits_t 1)
      -> vvs_grows vvs vvs' /\ nid <= nid'
      /\ wf_state tsig env r2v' vvs' rir nid'
      /\ (
        forall
          sched_log action_log
          (MLR:
            forall b : bool, interp_sact vvs (SVar cond_name) (Bits [b])
            -> match_logs_r2v (if b then r2vt else r2vf) vvs sched_rir rir
               sched_log action_log
          ),
          match_logs_r2v r2v' vvs' sched_rir rir sched_log action_log).
  Proof.
    intros. inv H0; inv H1.
    edestruct merge_reg2var_grows as (
      VVSGROWS4 & VVSRANGE4 & R2VVVS4 & NIDGROWS4 & VSV4 & WTVVS4 & NDr4 & EVAL4
    ); eauto.
    repeat (refine (conj _ _)); eauto.
    split; eauto.
    eapply env_vvs_vvs_grows; eauto.
    eapply wf_rir_grows; eauto.
  Qed.

  Lemma wf_state_cons:
    forall tsig env r2v vvs rir n, wf_state tsig env r2v vvs rir n
    -> forall v vv t, wt_sact vvs vv t
    -> (forall v0, var_in_sact vv v0 -> v0 < n)
    -> wf_state
      ((v,t)::tsig) ((v,n)::env) r2v (PTree.set n (t, vv) vvs) rir (Pos.succ n).
  Proof.
    intros tsig env r2v vvs rir n WFS v vv t WTs VIS.
    inv WFS; split; eauto.
    + eapply wt_vvs_set; eauto. lia.
    + constructor. split; auto. rewrite PTree.gss. eauto.
      eapply env_vvs_vvs_grows. eauto.
      eapply vvs_grows_set; eauto. lia.
    + eapply reg2var_vvs_grows. eauto.
      eapply vvs_grows_set; eauto. lia.
    + apply vvs_range_list_assoc_set. eapply vvs_range_incr. 2: eauto. lia.
      red. lia.
    + eapply vvs_smaller_variables_set; eauto.
    + eapply wf_rir_grows; eauto. eapply vvs_grows_set; eauto. lia.
  Qed.

  Lemma wf_state_tl:
    forall tsig env r2v vvs rir n, wf_state tsig env r2v vvs rir n
    -> wf_state (tl tsig) (tl env) r2v vvs rir n.
  Proof.
    intros tsig env r2v vvs rir n WFS.
    inv WFS; split; eauto.
    inv wfs_env_vvs0; simpl; eauto. constructor.
  Qed.

  Lemma wf_state_change_rir:
    forall tsig env r2v vvs rir nid, wf_state tsig env r2v vvs rir nid
    -> forall rir' grd, rir_grows vvs rir vvs rir' grd
    -> wf_rir rir' vvs
    -> wf_state tsig env r2v vvs rir' nid.
  Proof.
    intros tsig env r2v vvs rir nid H rir' grd H0 H1.
    inv H; split; eauto.
  Qed.

  Lemma wf_state_change_r2v:
    forall tsig env r2v vvs rir n,
    wf_state tsig env r2v vvs rir n
    -> forall r v, (exists z : sact, vvs !v = Some (R (fst r), z))
    -> wf_state tsig env (list_assoc_set r2v r v) vvs rir n.
  Proof.
    intros tsig env r2v vvs rir n H r0 v H0.
    inv H; split; eauto.
    eapply reg2var_vvs_set; eauto.
    eapply nodup_list_assoc_set; eauto.
  Qed.

  Lemma match_Gamma_env_ex:
    forall Gamma env vvs, match_Gamma_env Gamma env vvs
    -> forall tsig, env_vvs env vvs tsig
    -> forall var v, list_assoc Gamma var = Some v
    -> exists n t s, list_assoc env var = Some n
    /\ list_assoc tsig var = Some t /\ vvs !n = Some (t, s)
    /\ interp_sact vvs s v.
  Proof.
    induction 1; simpl; intros; eauto.
    easy.
    destruct H.
    inv H1.
    repeat destr_in H6. destruct H6 as (? & ? & ?). destruct x; simpl in *.
    subst.
    repeat destr_in H2; inv H2; eauto.
    exists p, t, x0; repeat split; eauto. inv H3.
    rewrite H4 in H1; inv H1; auto.
  Qed.

  Lemma match_Gamma_env_set:
    forall Gamma env vvs, match_Gamma_env Gamma env vvs
    -> forall v v1 n t0 o, vvs_range vvs n
    -> interp_sact vvs (reduce t0 o) v1
    -> match_Gamma_env
      (list_assoc_set Gamma v v1) (list_assoc_set env v n)
      (PTree.set n (t0, reduce t0 o) vvs).
  Proof.
    induction 1; simpl; intros; eauto.
    - constructor; simpl. split; auto.
      econstructor. rewrite PTree.gss. eauto.
      eapply vvs_grows_interp_sact; eauto. eapply vvs_grows_set; eauto. lia.
      constructor.
    - destruct H. inv H3. destruct x, y. simpl in *; subst.
      destr.
      + subst. constructor; simpl; eauto. split; auto.
        econstructor. rewrite PTree.gss. eauto.
        eapply vvs_grows_interp_sact; eauto. eapply vvs_grows_set; eauto. lia.
        eapply Forall2_impl.
        2: eapply H0. simpl; intros. destruct H; split; auto.
        inv H3.
        eapply vvs_grows_interp_sact; eauto. eapply vvs_grows_set; eauto. lia.
        econstructor; eauto.
      + constructor; simpl; eauto.
        split; auto.
        eapply vvs_grows_interp_sact; eauto. eapply vvs_grows_set; eauto. lia.
        econstructor; eauto. eapply IHForall2; eauto.
  Qed.

  Lemma wt_sact_below:
    forall tsig env reg2var vvs rir n, wf_state tsig env reg2var vvs rir n
    -> forall s t, wt_sact vvs s t
    -> forall v, var_in_sact s v
    -> v < n.
  Proof. intros; eapply wt_sact_valid_vars; eauto. apply H. Qed.

  Lemma mge_merge_branches:
    forall Gamma env1 env2 cond_name env' vvs (b: bool),
    Forall2 (fun x y => fst x = fst y) env1 env2
    -> Forall2 (fun x y => fst x = fst y) env1 env'
    -> match_Gamma_env Gamma (if b then env1 else env2) vvs
    -> interp_sact vvs (SVar cond_name) (Bits [b])
    -> Forall2
         (fun '(xt,xf) x =>
          forall b, interp_sact vvs (SVar cond_name) (Bits [b])
          -> (
            forall v, interp_sact vvs (SVar (snd (if b then xt else xf))) v
            <-> interp_sact vvs (SVar (snd x)) v))
         (combine env1 env2) env'
    -> match_Gamma_env Gamma env' vvs.
  Proof.
    induction Gamma; simpl; intros; eauto.
    - inv H1.
      destruct b; inv H; try congruence; inv H3; constructor.
    - inv H1. destruct H7. inv H.
      destruct b; congruence.
      assert (y = if b then x else y0) by (destruct b; congruence).
      assert (l' = if b then l else l'0) by (destruct b; congruence). clear H6.
      subst. simpl in H3. inv H0. inv H3.
      constructor; eauto.
      + split. rewrite H1. destr; congruence.
        eapply H10. eauto. auto.
      + eapply IHGamma. 3: eauto. all: eauto.
  Qed.

  Lemma match_logs_r2v_vvs_set:
    forall r2v vvs sl al n x sched_rir rir tsig env,
    match_logs_r2v r2v vvs sched_rir rir sl al
    -> wf_state tsig env r2v vvs rir n
    -> wf_rir sched_rir vvs
    -> match_logs_r2v r2v (PTree.set n x vvs) sched_rir rir sl al.
  Proof.
    intros; inv H0. eapply match_logs_r2v_vvs_grows; eauto.
    eapply vvs_grows_set; eauto. lia.
  Qed.

  Lemma Forall_iff:
    forall {A:Type} (P1 P2: A -> Prop) l (H: Forall (fun x => P1 x <-> P2 x) l),
    Forall P1 l <-> Forall P2 l.
  Proof.
    induction 1; simpl; intros; eauto.
    split; constructor.
    split; intro B; inv B; econstructor; eauto. apply H; auto. tauto.
    apply H; auto. tauto.
  Qed.

  Lemma match_logs_r2v_rir_grows:
    forall r2v vvs sl al rir vvs' rir' grd sr n n',
    match_logs_r2v r2v vvs sr rir sl al
    -> rir_grows vvs rir vvs' rir' grd
    -> vvs_range vvs n
    -> vvs_smaller_variables vvs
    -> wt_vvs vvs -> wf_rir rir vvs -> wf_rir sr vvs -> wf_rir rir' vvs'
    -> vvs_range vvs' n'
    -> vvs_smaller_variables vvs'
    -> wt_vvs vvs'
    -> interp_sact vvs' grd (Bits [false])
    -> match_logs_r2v r2v vvs' sr rir' sl al.
  Proof.
    intros. inv H. inv H0. split.
    intros; eapply vvs_grows_interp_sact; eauto.
    eapply match_log_vvs_grows'; eauto.
    inv mlr_mlv_action0. split.
    - intros idx. rewrite mlv_read2.
      edestruct (rir_grows_read0s0 idx). unfold rir_has_read0.
      eapply H0. eauto.
    - intros idx. rewrite mlv_read3.
      edestruct (rir_grows_read1s0 idx). unfold rir_has_read1.
      eapply H0. eauto.
    - intros idx. rewrite mlv_write2.
      edestruct (rir_grows_write0s0 idx). unfold rir_has_write0.
      eapply H0. eauto.
    - intros idx. rewrite mlv_write3.
      edestruct (rir_grows_write1s0 idx). unfold rir_has_write1.
      eapply H0. eauto.
  Qed.

  Lemma log_app_log_cons:
    forall (l1: Log REnv) idx x l2,
    log_app (log_cons idx x l1) l2 = log_cons idx x (log_app l1 l2).
  Proof.
    unfold log_app. unfold log_cons.
    simpl. intros.
    apply equiv_eq.
    red. intros.
    rewrite getenv_map2.
    rewrite getenv_map2.
    destruct (eq_dec idx k). subst.
    rewrite ! get_put_eq. simpl. auto.
    rewrite ! get_put_neq by congruence.
    rewrite getenv_map2. auto.
  Qed.

  Lemma latest_write0_log_cons_read:
    forall idx v (action_log: Log REnv) reg prt,
    latest_write0 (log_cons idx (LE Logs.LogRead prt v) action_log) reg
    = latest_write0 action_log reg.
  Proof.
    unfold latest_write0. unfold log_find, log_cons.
    intros. destruct (eq_dec reg idx).
    subst; rewrite get_put_eq. simpl. auto.
    rewrite get_put_neq. simpl. auto. auto.
  Qed.

  Lemma do_read_log_cons_read:
    forall sched_log action_log idx v reg p prt,
    do_read sched_log (log_cons idx (LE Logs.LogRead p v) action_log) reg prt
    = do_read sched_log action_log reg prt.
  Proof.
    unfold do_read. intros. destr; auto.
    rewrite log_app_log_cons.
    rewrite latest_write0_log_cons_read. eauto.
  Qed.

  Lemma interp_sact_fold_or_conds_false:
    forall vvs l, Forall (fun a => interp_sact vvs a (Bits [false])) l
    -> forall c0, interp_sact vvs c0 (Bits [false])
    -> interp_sact vvs (fold_left uor l c0) (Bits [false]).
  Proof.
    induction 1; simpl; intros; eauto.
    apply IHForall. econstructor; eauto.
  Qed.

  Lemma interp_sact_or_conds_false:
    forall vvs l, Forall (fun a => interp_sact vvs a (Bits [false])) l
    -> interp_sact vvs (or_conds l) (Bits [false]).
  Proof.
    intros; eapply interp_sact_fold_or_conds_false; eauto. constructor.
  Qed.

  Lemma log_existsb_log_cons:
    forall (l2: Log REnv) idx r e fn,
    log_existsb (log_cons r e l2) idx fn
    =
      (if eq_dec idx r then fn (kind e) (port e) else false)
      || log_existsb l2 idx fn.
  Proof.
    unfold log_existsb, log_cons.
    intros. destr. subst. rewrite get_put_eq. simpl. destr. simpl. auto. simpl.
    rewrite get_put_neq; auto.
  Qed.

  Lemma log_find_log_cons:
    forall {A: Type} (l2: Log REnv) idx r e (fn: _ -> option A),
    log_find (log_cons r e l2) idx fn
    = (
      if eq_dec idx r then
        match fn e with
        | Some x => Some x
        | None => log_find l2 idx fn
        end
      else log_find l2 idx fn).
  Proof.
    unfold log_find, log_cons.
    intros. destr. subst. rewrite get_put_eq. simpl. auto.
    rewrite get_put_neq; auto.
  Qed.

  Lemma log_existsb_log_app:
    forall (l1 l2: Log REnv) idx fn,
    log_existsb (log_app l1 l2) idx fn =
    log_existsb l1 idx fn || log_existsb l2 idx fn.
  Proof.
    unfold log_existsb, log_app. intros.
    rewrite getenv_map2.
    rewrite existsb_app. auto.
  Qed.

  Lemma match_logs_r2v_add_read0:
    forall r2v vvs sched_rir rir (sched_log action_log: Log REnv)
      (MLR : match_logs_r2v r2v vvs sched_rir rir sched_log action_log) idx
      guard (GOK: interp_sact vvs guard (Bits [true])),
    match_logs_r2v
      r2v vvs sched_rir (add_read0 rir guard idx) sched_log
      (log_cons idx (LE (V:=val) Logs.LogRead P0 (Bits [])) action_log).
  Proof.
    intros.
    inv MLR. unfold add_read0.
    split; intros; eauto.
    - eapply mlr_read0 in H. destr.
      rewrite do_read_log_cons_read; eauto.
      rewrite log_app_log_cons.
      revert H; unfold latest_write. rewrite log_find_log_cons. simpl.
      destruct eq_dec; destr.
    - split; intros; eauto.
      + rewrite log_existsb_log_cons. simpl.
        unfold rir_has_read0. simpl.
        destruct mlr_mlv_action0.
        destr. simpl. split. congruence. subst.
        rewrite list_assoc_gss.
        intros IS. destr_in IS. inv IS. simpl in H5.
        exploit interp_sact_determ. apply GOK. apply H4. intros <-.
        repeat destr_in H5; inv H5.
        destruct v; simpl in H0. congruence. inv H0. rewrite orb_true_r in H1.
        congruence.
        exploit interp_sact_determ. apply GOK. apply IS. congruence. simpl.
        rewrite mlv_read2. unfold rir_has_read0.
        rewrite list_assoc_gso. tauto. auto.
      + rewrite log_existsb_log_cons. simpl.
        unfold rir_has_read1. simpl.
        destruct mlr_mlv_action0.
        replace (if eq_dec idx0 idx then false else false) with false
          by (destr; eauto).
        simpl. rewrite mlv_read3.
        unfold rir_has_read1. tauto.
      + rewrite log_existsb_log_cons. simpl.
        unfold rir_has_write1. simpl.
        destruct mlr_mlv_action0.
        replace (if eq_dec idx0 idx then false else false) with false
          by (destr; eauto).
        simpl. rewrite mlv_write2.
        unfold rir_has_write1. tauto.
      + rewrite log_existsb_log_cons. simpl.
        unfold rir_has_write1. simpl.
        destruct mlr_mlv_action0.
        replace (if eq_dec idx0 idx then false else false) with false
          by (destr; eauto).
        simpl. rewrite mlv_write3.
        unfold rir_has_write1. tauto.
  Qed.

  Lemma match_logs_r2v_add_read1:
    forall
      r2v vvs sched_rir rir (sched_log action_log: Log REnv)
      (MLR : match_logs_r2v r2v vvs sched_rir rir sched_log action_log) idx
      guard (GOK: interp_sact vvs guard (Bits [true])),
    match_logs_r2v
      r2v vvs sched_rir (add_read1 rir guard idx) sched_log
      (log_cons idx (LE (V:=val) Logs.LogRead P1 (Bits [])) action_log).
  Proof.
    intros.
    inv MLR. unfold add_read0.
    split; intros; eauto.
    - exploit mlr_read0. eauto.
      destr. rewrite do_read_log_cons_read; eauto.
      rewrite log_app_log_cons.
      revert H; unfold latest_write. rewrite log_find_log_cons. simpl.
      destruct eq_dec; destr.
    - split; intros; eauto.
      + rewrite log_existsb_log_cons. simpl.
        unfold rir_has_read1. simpl.
        destruct mlr_mlv_action0.
        replace (if eq_dec idx0 idx then false else false) with false
          by (destr; eauto).
        simpl. rewrite mlv_read2.
        unfold rir_has_read1. tauto.
      + rewrite log_existsb_log_cons. simpl.
        unfold rir_has_read1. simpl.
        destruct mlr_mlv_action0.
        destr. simpl. split. congruence. subst.
        rewrite list_assoc_gss.
        intros IS. destr_in IS. inv IS. simpl in H5.
        exploit interp_sact_determ. apply GOK. apply H4. intros <-.
        repeat destr_in H5; inv H5.
        destruct v; simpl in H0. congruence. inv H0. rewrite orb_true_r in H1.
        congruence.
        exploit interp_sact_determ. apply GOK. apply IS. congruence. simpl.
        rewrite mlv_read3. unfold rir_has_read0.
        rewrite list_assoc_gso. tauto. auto.
      + rewrite log_existsb_log_cons. simpl.
        unfold rir_has_write1. simpl.
        destruct mlr_mlv_action0.
        replace (if eq_dec idx0 idx then false else false) with false
          by (destr; eauto).
        simpl. rewrite mlv_write2.
        unfold rir_has_write1. tauto.
      + rewrite log_existsb_log_cons. simpl.
        unfold rir_has_write1. simpl.
        destruct mlr_mlv_action0.
        replace (if eq_dec idx0 idx then false else false) with false
          by (destr; eauto).
        simpl. rewrite mlv_write3.
        unfold rir_has_write1. tauto.
  Qed.


  Lemma interp_uor_false:
    forall vvs n a v, wt_vvs vvs
    -> vvs_smaller_variables vvs
    -> vvs_range vvs n
    -> wt_sact vvs a (bits_t 1)
    -> interp_sact vvs (uor a const_false) v <-> interp_sact vvs a v.
  Proof.
    intros.
    exploit wt_sact_interp_bool; eauto. intros (? & ?).
    split; intros.
    inv H4. inv H10.
    exploit interp_sact_determ. apply H3. apply H8. intros; subst.
    simpl in H11. inv H11. rewrite orb_false_r; auto.
    exploit interp_sact_determ. apply H3. apply H4. intros; subst.
    econstructor; eauto. constructor. simpl. rewrite orb_false_r; auto.
  Qed.

  Lemma interp_uor_snd_false:
    forall vvs a b v n, wt_vvs vvs
    -> vvs_smaller_variables vvs
    -> vvs_range vvs n
    -> wt_sact vvs a (bits_t 1)
    -> wt_sact vvs b (bits_t 1)
    -> interp_sact vvs b (Bits [false])
    -> interp_sact vvs (uor a b) v <-> interp_sact vvs a v.
  Proof.
    intros.
    split; intros A. inv A.
    exploit interp_sact_determ. apply H10. apply H4. intros ->.
    edestruct interp_sact_wt_bool. 5: apply H8. all: eauto. subst.
    simpl in H11. inv H11.
    rewrite orb_false_r; auto.
    edestruct interp_sact_wt_bool. 5: apply A. all: eauto. subst.
    econstructor; eauto. simpl.
    rewrite orb_false_r; auto.
  Qed.

  Lemma rir_grows_add_write0:
    forall vvs sched_rir rir grd idx v rir' grd' tsig env r2v n,
    wt_sact vvs grd (bits_t 1)
    -> wf_state tsig env r2v vvs rir n
    -> add_write0 sched_rir rir grd idx v = (rir', grd')
    -> forall (WFSR: wf_rir sched_rir vvs) (WTv: wt_sact vvs v (R idx)),
      let vvs1 := PTree.set n (R idx, v) vvs in
      let r2v1 := list_assoc_set r2v (idx, inl P1) n in
      let r2v1 := list_assoc_set r2v1 (idx, inr tt) n in
      rir_grows vvs rir vvs1 rir' grd
      /\ wf_state tsig env r2v1 vvs1 rir' (n + 1)
      /\ wt_sact vvs1 grd' (bits_t 1).
  Proof.
    unfold add_write0. intros. inv H1.
    split; [|split].
    - split; simpl; eauto using incl_refl, cond_log_grows_refl, vvs_grows_refl.
      + eapply cond_log_grows_change_vvs. eauto. inv H0; eauto. intros.
        red in H1. repeat rewrite PTree.gso by lia. eauto.
        intros i a IN; eapply wf_rir_read0s in IN; eauto. inv H0; eauto.
      + eapply cond_log_grows_change_vvs. eauto. inv H0; eauto. intros.
        red in H1. repeat rewrite PTree.gso by lia. eauto.
        intros i a IN; eapply wf_rir_read1s in IN; eauto. inv H0; eauto.
      + red. intros; split; intros.
        * rewrite list_assoc_spec.
          destruct (eq_dec idx idx0).
          -- subst.
             red. intros EX.
             eapply vvs_grows_interp_sact. eapply vvs_grows_set. apply H0. lia.
             destr; eauto.
             exploit wt_sact_interp_bool. 4: apply H.
             1-3: apply H0. intros (?&?).
             econstructor; eauto. inv EX.
          -- eapply cond_log_grows_change_vvs. eauto. apply H0. apply H0.
             intros x V y; red in V. repeat rewrite PTree.gso by lia. eauto.
             apply H0.
        * rewrite list_assoc_spec.
          destr.
          exploit wf_rir_write0s. apply H0. apply list_assoc_in. eauto.
          intro WTs.
          rewrite interp_sact_vvs_grows_iff
            with (vvs':=PTree.set n (R idx, v) vvs).
          4: eapply vvs_grows_set. 2-4,6: apply H0. 2: lia.
          exploit wt_sact_interp_bool. 4: apply H. 1-3: apply H0. intros (?&?).
          exploit interp_sact_determ. apply H1. eapply vvs_grows_interp_sact.
          2: apply H2.
          eapply vvs_grows_set. apply H0. lia. intros A; inv A. clear H1.
          destruct (eq_dec idx idx0); [|tauto].
          subst. rewrite Heqo.
          rewrite interp_uor_snd_false. tauto. 1-3: apply H0. auto. auto. auto.
          destruct (eq_dec); subst. rewrite Heqo. econstructor; eauto.
          constructor. eauto.
          destruct (eq_dec); subst. rewrite Heqo.
          split; intros. inv H2. eauto.
          exploit interp_sact_determ. apply H1. apply H2.
          intros <-. constructor.
          split; intros A; inv A; constructor.
      + eapply cond_log_grows_change_vvs. eauto. inv H0; eauto. intros.
        red in H1. repeat rewrite PTree.gso by lia. eauto.
        intros i a IN; eapply wf_rir_write1s in IN; eauto. inv H0; eauto.
      + eapply vvs_grows_set. apply H0. lia.
      + eapply wt_sact_vvs_grows; eauto.
        eapply vvs_grows_set. apply H0. lia.
    - inv H0.
      assert (VG: vvs_grows vvs (PTree.set n (R idx, v) vvs)).
      { eapply vvs_grows_set. eauto. lia. }
      split.
      + eapply wt_vvs_set; eauto. lia.
      + eapply env_vvs_change_vvs; eauto. lia.
      + eapply reg2var_vvs_set.
        eapply reg2var_vvs_set.
        eapply reg2var_vvs_grows. eauto. eauto.
        simpl. rewrite PTree.gss; eauto.
        simpl. rewrite PTree.gss; eauto.
      + eapply vvs_range_list_assoc_set. eapply vvs_range_incr. 2: eauto. lia.
        red; lia.
      + eapply vvs_smaller_variables_set; eauto.
        eapply wt_sact_valid_vars; eauto.
      + eapply wf_rir_add_write0.
        7:{ unfold add_write0. simpl; eauto. }
        * eapply wf_rir_grows; eauto.
        * eapply wf_rir_grows; eauto.
        * eapply wt_sact_vvs_grows. 2: eauto. eauto.
        * eapply wt_vvs_set; eauto. lia.
        * eapply vvs_smaller_variables_set; eauto.
          eapply wt_sact_valid_vars; eauto.
        * eapply vvs_range_set. eauto.
      + eapply nodup_list_assoc_set; eauto.
        eapply nodup_list_assoc_set; eauto.
    - assert (VG: vvs_grows vvs (PTree.set n (R idx, v) vvs)).
      { inv H0. eapply vvs_grows_set; eauto. lia. }
      econstructor.
      eapply wt_sact_vvs_grows; eauto.
      eapply wt_sact_or_conds.
      repeat constructor.
      apply wt_rir_has_write0. eapply wf_rir_grows; eauto. all: try apply H0.
      apply wt_rir_has_read1. eapply wf_rir_grows; eauto. all: try apply H0.
      apply wt_rir_has_write1. eapply wf_rir_grows; eauto. all: try apply H0.
      apply wt_rir_has_write0. eapply wf_rir_grows; eauto. all: try apply H0.
      apply wt_rir_has_read1. eapply wf_rir_grows; eauto. all: try apply H0.
      apply wt_rir_has_write1. eapply wf_rir_grows; eauto. all: try apply H0.
      constructor.
      Unshelve. eauto.
  Qed.

  Lemma rir_grows_add_write1:
    forall vvs sched_rir rir grd idx v rir' grd' tsig env r2v n,
    wt_sact vvs grd (bits_t 1)
    -> wf_state tsig env r2v vvs rir n
    -> add_write1 sched_rir rir grd idx v = (rir', grd')
    -> forall (WFSR: wf_rir sched_rir vvs) (WTv: wt_sact vvs v (R idx)),
      let vvs1 := PTree.set n (R idx, v) vvs in
      let r2v1 := list_assoc_set r2v (idx, inr tt) n in
      rir_grows vvs rir vvs1 rir' grd
      /\ wf_state tsig env r2v1 vvs1 rir' (Pos.succ n)
      /\ wt_sact vvs1 grd' (bits_t 1).
  Proof.
    unfold add_write1. intros. inv H1.
    split; [|split].
    - split; simpl; eauto using incl_refl, cond_log_grows_refl, vvs_grows_refl.
      + eapply cond_log_grows_change_vvs. eauto. inv H0; eauto. intros.
        red in H1. repeat rewrite PTree.gso by lia. eauto.
        intros i a IN; eapply wf_rir_read0s in IN; eauto. inv H0; eauto.
      + eapply cond_log_grows_change_vvs. eauto. inv H0; eauto. intros.
        red in H1. repeat rewrite PTree.gso by lia. eauto.
        intros i a IN; eapply wf_rir_read1s in IN; eauto. inv H0; eauto.
      + eapply cond_log_grows_change_vvs. eauto. inv H0; eauto. intros.
        red in H1. repeat rewrite PTree.gso by lia. eauto.
        intros i a IN; eapply wf_rir_write0s in IN; eauto. inv H0; eauto.
      + red. intros; split; intros.
        * rewrite list_assoc_spec.
          destruct (eq_dec idx idx0).
          -- subst.
             red. intros EX.
             eapply vvs_grows_interp_sact. eapply vvs_grows_set. apply H0. lia.
             destr; eauto.
             exploit wt_sact_interp_bool. 4: apply H. 1-3: apply H0.
             intros (?&?). econstructor; eauto. inv EX.
          -- eapply cond_log_grows_change_vvs. eauto. apply H0. apply H0.
             intros x V y; red in V. repeat rewrite PTree.gso by lia. eauto.
             apply H0.
        * rewrite list_assoc_spec.
          destr.
          exploit wf_rir_write1s. 2: apply list_assoc_in; eauto. apply H0.
          intro WTs.
          rewrite interp_sact_vvs_grows_iff
            with (vvs':=PTree.set n (R idx, v) vvs).
          4: eapply vvs_grows_set. 2-4,6: apply H0. 2: lia.
          exploit wt_sact_interp_bool. 4: apply H. 1-3: apply H0. intros (?&?).
          exploit interp_sact_determ. apply H1. eapply vvs_grows_interp_sact.
          2: apply H2.
          eapply vvs_grows_set. apply H0. lia. intros A; inv A. clear H1.
          destruct (eq_dec idx idx0); [|tauto].
          subst. rewrite Heqo.
          rewrite interp_uor_snd_false. tauto. 1-3: apply H0. auto. auto. auto.
          destruct (eq_dec); subst. rewrite Heqo. econstructor; eauto.
          constructor. eauto.
          destruct (eq_dec); subst. rewrite Heqo.
          split; intros. inv H2. eauto.
          exploit interp_sact_determ. apply H1. apply H2. intros <-.
          constructor. split; intros A; inv A; constructor.
      + eapply vvs_grows_set. apply H0. lia.
      + eapply wt_sact_vvs_grows; eauto.
        eapply vvs_grows_set. apply H0. lia.
    - inv H0.
      assert (VG: vvs_grows vvs (PTree.set n (R idx, v) vvs)).
      { eapply vvs_grows_set. eauto. lia. }
      split.
      + eapply wt_vvs_set; eauto. lia.
      + eapply env_vvs_change_vvs; eauto. lia.
      + eapply reg2var_vvs_set.
        eapply reg2var_vvs_grows. eauto. eauto.
        simpl. rewrite PTree.gss; eauto.
      + eapply vvs_range_set. eauto.
      + red; intros.
        repeat rewrite PTree.gsspec in H0.
        red.
        repeat destr_in H0; subst; eauto. inv H0.
        eapply wt_sact_valid_vars; eauto.
        eapply wfs_vsv0 in H0; eauto. eapply H0; eauto.
      + eapply wf_rir_add_write1.
        7:{ unfold add_write1. simpl; eauto. }
        * eapply wf_rir_grows; eauto.
        * eapply wf_rir_grows; eauto.
        * eapply wt_sact_vvs_grows. 2: eauto. eauto.
        * eapply wt_vvs_set; eauto. lia.
        * eapply vvs_smaller_variables_set; eauto.
          eapply wt_sact_valid_vars; eauto.
        * eapply vvs_range_set. eauto.
      + eapply nodup_list_assoc_set; eauto.
    - assert (VG: vvs_grows vvs (PTree.set n (R idx, v) vvs)).
      { inv H0. eapply vvs_grows_set; eauto. lia. }
      econstructor.
      eapply wt_sact_vvs_grows; eauto.
      eapply wt_sact_or_conds.
      repeat constructor.
      apply wt_rir_has_write1. eapply wf_rir_grows; eauto. all: try apply H0.
      apply wt_rir_has_write1. eapply wf_rir_grows; eauto. all: try apply H0.
      constructor.
      Unshelve. eauto.
  Qed.

  Lemma add_write0_fail:
    forall
      sched_log action_log idx vvs sched_rir rir rir' fail_cond grd v tsig env
      r2v g',
    may_write sched_log action_log P0 idx = true
    -> wf_state tsig env r2v vvs rir g'
    -> match_logs_r2v r2v vvs sched_rir rir sched_log action_log
    -> add_write0 sched_rir rir grd idx v = (rir', fail_cond)
    -> interp_sact vvs grd (Bits [true])
    -> interp_sact vvs fail_cond (Bits [false]).
  Proof.
    intros sched_log action_log idx vvs sched_rir rir rir' fail_cond grd v tsig
      env r2v g' MW WR MLR AW GRD.
    unfold add_write0 in AW.
    unfold may_write in MW.
    rewrite ! andb_true_iff in MW.
    rewrite ! negb_true_iff in MW.
    destruct MW as ((A & B) & C). inv AW.
    econstructor. eauto.
    eapply interp_sact_or_conds_false. 2: reflexivity.
    rewrite log_existsb_log_app in A, B, C.
    rewrite orb_false_iff in A, B, C.
    destruct A, B, C.
    eapply mlv_read1 in H. 2: apply MLR.
    eapply mlv_read1 in H0. 2: apply MLR.
    eapply mlv_write0 in H1. 2: apply MLR.
    eapply mlv_write0 in H2. 2: apply MLR.
    eapply mlv_write1 in H3. 2: apply MLR.
    eapply mlv_write1 in H4. 2: apply MLR.
    repeat constructor; eauto.
  Qed.
  Lemma add_write1_fail:
    forall sched_log action_log idx vvs sched_rir rir rir' fail_cond grd v tsig
      env r2v g',
    may_write sched_log action_log P1 idx = true
    -> wf_state tsig env r2v vvs rir g'
    -> match_logs_r2v r2v vvs sched_rir rir sched_log action_log
    -> add_write1 sched_rir rir grd idx v = (rir', fail_cond)
    -> interp_sact vvs grd (Bits [true])
    -> interp_sact vvs fail_cond (Bits [false]).
  Proof.
    intros sched_log action_log idx vvs sched_rir rir rir' fail_cond grd v tsig
      env r2v g' MW WR MLR AW GRD.
    unfold add_write1 in AW.
    unfold may_write in MW.
    rewrite ! negb_true_iff in MW.
    inv AW.
    econstructor. eauto.
    eapply interp_sact_or_conds_false. 2: reflexivity.
    rewrite log_existsb_log_app in MW.
    rewrite orb_false_iff in MW.
    destruct MW.
    eapply mlv_write1 in H. 2: apply MLR.
    eapply mlv_write1 in H0. 2: apply MLR.
    repeat constructor; eauto.
  Qed.

  Lemma latest_write0_log_cons_write_other:
    forall idx v (action_log: Log REnv) reg prt, idx <> reg
    -> latest_write0 (log_cons idx (LE Logs.LogWrite prt v) action_log) reg
    = latest_write0 action_log reg.
  Proof.
    unfold latest_write0. unfold log_find, log_cons.
    intros. rewrite get_put_neq. simpl. auto. auto.
  Qed.

  Lemma do_read_log_cons_write_other:
    forall sched_log action_log idx v reg p prt, reg <> idx
    -> do_read
      sched_log (log_cons idx (LE Logs.LogWrite p v) action_log) reg prt
    = do_read sched_log action_log reg prt.
  Proof.
    unfold do_read. intros. destr; auto.
    rewrite log_app_log_cons.
    rewrite latest_write0_log_cons_write_other; eauto.
  Qed.

  Lemma match_logs_r2v_add_write0:
    forall r2v vvs sched_rir r0 sched_log action_log guard idx v rir' s0 n tsig
      env v',
    wf_state tsig env r2v vvs r0 n
    -> match_logs_r2v r2v vvs sched_rir r0 sched_log action_log
    -> add_write0 sched_rir r0 guard idx v = (rir', s0)
    -> may_write sched_log action_log P0 idx = true
    -> wt_sact vvs v (R idx)
    -> interp_sact vvs v v'
    -> wt_sact vvs guard (bits_t 1)
    -> interp_sact vvs guard (Bits [true])
    -> wf_rir sched_rir vvs
    -> match_logs_r2v
        (list_assoc_set (list_assoc_set r2v (idx, inl P1) n) (idx, inr tt) n)
        (PTree.set n (R idx, v) vvs) sched_rir rir' sched_log
        (log_cons idx (LE (V:=val) Logs.LogWrite P0 v') action_log).
  Proof.
    intros r2v vvs sched_rir r0 sched_log action_log guard idx v rir' s0 n tsig
      env v' WFS MLR AW MW VWT IV GWT GOK WFRS.
    inv MLR. unfold add_write0 in AW. inv AW.
    split.
    - intros reg prt n0 GET.
      rewrite ! list_assoc_spec in GET.
      repeat destr_in GET; eauto.
      + inv GET. clear Heqs. inv e.
        econstructor. rewrite PTree.gss. eauto.
        unfold do_read. rewrite log_app_log_cons. unfold latest_write.
        rewrite log_find_log_cons. rewrite eq_dec_refl. simpl.
        eapply vvs_grows_interp_sact. 2: eauto.
        eapply vvs_grows_set; eauto.
        apply WFS. lia.
      + inv GET. clear Heqs0. inv e.
        econstructor. rewrite PTree.gss. eauto.
        unfold do_read. rewrite log_app_log_cons. unfold latest_write0.
        rewrite log_find_log_cons. rewrite eq_dec_refl. simpl.
        eapply vvs_grows_interp_sact. 2: eauto.
        eapply vvs_grows_set; eauto.
        apply WFS. lia.
      + destruct (eq_dec idx reg). subst. destruct prt; try congruence.
        destruct p; try congruence.
        simpl.
        exploit mlr_read0. eauto. simpl.
        eapply vvs_grows_interp_sact; eauto. eapply vvs_grows_set; eauto.
        apply WFS. lia.
        destruct u; congruence.
        exploit mlr_read0. eauto. simpl.
        rewrite log_app_log_cons. unfold latest_write.
        rewrite log_find_log_cons. simpl.
        destruct (eq_dec reg idx); try congruence.
        simpl.
        destr.
        rewrite do_read_log_cons_write_other.
        eapply vvs_grows_interp_sact; eauto. eapply vvs_grows_set; eauto.
        apply WFS. lia. auto.
        eapply vvs_grows_interp_sact; eauto. eapply vvs_grows_set; eauto.
        apply WFS. lia.
    - eapply match_log_vvs_grows'. eauto.
      eapply vvs_grows_set; eauto. all: try apply WFS. lia. eauto.
    - eapply match_log_vvs_grows'. 2: eapply vvs_grows_set; eauto.
      all: try apply WFS.
      inv mlr_mlv_action0. split; simpl; intros; eauto.
      + rewrite log_existsb_log_cons. simpl.
        replace (if eq_dec idx0 idx then false else false) with false
          by (destr; eauto). simpl.
        rewrite mlv_read2. tauto.
      + rewrite log_existsb_log_cons. simpl.
        replace (if eq_dec idx0 idx then false else false) with false
          by (destr; eauto). simpl.
        rewrite mlv_read3. tauto.
      + rewrite log_existsb_log_cons. simpl.
        rewrite orb_false_iff.
        rewrite mlv_write2. unfold rir_has_write0. simpl.
        destr. subst. rewrite list_assoc_gss.
        split. intuition congruence. intros INTs. exfalso.
        destr_in INTs. inv INTs.
        exploit interp_sact_determ. apply GOK. clear GOK. eauto. intros <-.
        simpl in H5. repeat destr_in H5; inv H5.
        destruct v0; simpl in H0. congruence. inv H0. rewrite orb_true_r in H1.
        congruence.
        exploit interp_sact_determ. apply GOK. clear GOK. eauto. congruence.
        rewrite list_assoc_gso by auto. tauto.
      + rewrite log_existsb_log_cons. simpl.
        replace (if eq_dec idx0 idx then false else false) with false
          by (destr; eauto). simpl.
        rewrite mlv_write3. tauto.
      + lia.
      + eapply wf_rir_add_write0.
        7:{ unfold add_write0. simpl. eauto. }
        apply WFS. apply WFRS. all: eauto.
        all: apply WFS.
        Unshelve. eauto.
  Qed.

  Lemma match_logs_r2v_add_write1:
    forall r2v vvs sched_rir r0 sched_log action_log guard idx v rir' s0 n tsig
      env v',
    wf_state tsig env r2v vvs r0 n
    -> match_logs_r2v r2v vvs sched_rir r0 sched_log action_log
    -> add_write1 sched_rir r0 guard idx v = (rir', s0)
    -> may_write sched_log action_log P1 idx = true
    -> wt_sact vvs v (R idx)
    -> interp_sact vvs v v'
    -> wt_sact vvs guard (bits_t 1)
    -> interp_sact vvs guard (Bits [true])
    -> wf_rir sched_rir vvs
    -> match_logs_r2v
        (list_assoc_set r2v (idx, inr tt) n) (PTree.set n (R idx, v) vvs)
        sched_rir rir' sched_log
        (log_cons idx (LE (V:=val) Logs.LogWrite P1 v') action_log).
  Proof.
    intros r2v vvs sched_rir r0 sched_log action_log guard idx v rir' s0 n tsig
      env v' WFS MLR AW MW VWT IV GWT GOK WFRS.
    inv MLR. unfold add_write1 in AW. inv AW.
    split.
    - intros reg prt n0 GET.
      rewrite list_assoc_spec in GET. destr_in GET.
      + inv GET. clear Heqs. inv e.
        econstructor. rewrite PTree.gss. eauto.
        rewrite log_app_log_cons. unfold latest_write.
        rewrite log_find_log_cons. simpl. rewrite eq_dec_refl.
        eapply vvs_grows_interp_sact. 2: eauto. eapply vvs_grows_set. apply WFS.
        lia.
      + eapply vvs_grows_interp_sact. eapply vvs_grows_set. apply WFS. lia.
        exploit mlr_read0; eauto. destr.
        unfold do_read. destr. rewrite log_app_log_cons. unfold latest_write0.
        rewrite log_find_log_cons. simpl.
        destruct (eq_dec reg idx); auto.
        rewrite log_app_log_cons. unfold latest_write.
        rewrite log_find_log_cons. simpl.
        destruct u. destruct (eq_dec reg idx). congruence. eauto.
    - eapply match_log_vvs_grows'; eauto. eapply vvs_grows_set. apply WFS. lia.
      apply WFS. apply WFS. apply WFS.
    - eapply match_log_vvs_grows'. 2: eapply vvs_grows_set; eauto.
      all: try apply WFS.
      inv mlr_mlv_action0. split; simpl; intros; eauto.
      + rewrite log_existsb_log_cons. simpl.
        replace (if eq_dec idx0 idx then false else false) with false
          by (destr; eauto). simpl.
        rewrite mlv_read2. unfold rir_has_read0. simpl. tauto.
      + rewrite log_existsb_log_cons. simpl.
        replace (if eq_dec idx0 idx then false else false) with false
          by (destr; eauto). simpl.
        rewrite mlv_read3. tauto.
      + rewrite log_existsb_log_cons. simpl.
        replace (if eq_dec idx0 idx then false else false) with false
          by (destr; eauto). simpl.
        rewrite mlv_write2. tauto.
      + rewrite log_existsb_log_cons. simpl.
        rewrite orb_false_iff.
        rewrite mlv_write3. unfold rir_has_write1. simpl.
        destr. subst. rewrite list_assoc_gss.
        split. intuition congruence. intros INTs. exfalso.
        destr_in INTs. inv INTs.
        exploit interp_sact_determ. apply GOK. clear GOK. eauto. intros <-.
        simpl in H5.
        repeat destr_in H5; inv H5.
        destruct v0; simpl in H0. congruence. inv H0. rewrite orb_true_r in H1.
        congruence.
        exploit interp_sact_determ. apply GOK. clear GOK. eauto. congruence.
        rewrite list_assoc_gso by auto. tauto.
      + lia.
      + eapply wf_rir_add_write1.
        7:{ unfold add_write1. eauto. } apply WFS. apply WFRS. all: eauto.
        all: apply WFS.
        Unshelve. eauto.
  Qed.

  Lemma gria_list_grows2:
    forall
      rec args tsig
      (F:
        Forall
          (fun u =>
            forall env r2v guard sched_rir rir nid v env' r2v' vvs fail_cond
              rir' nid' vvs0 t t0,
            wt_daction pos_t string string tsig (R:=R) (Sigma:=Sigma) u t0
            -> rec u tsig env r2v vvs0 guard sched_rir rir nid
               = (v, env', r2v', vvs, fail_cond, rir', nid', t)
            -> wf_state tsig env r2v vvs0 rir nid
            -> wt_sact vvs0 guard (bits_t 1)
            -> wf_rir sched_rir vvs0
            -> same_env env env' /\ Forall2 (fun x y => fst x = fst y) r2v r2v'
            /\ rir_grows vvs0 rir vvs rir' guard
            /\ wf_state tsig env' r2v' vvs rir' nid'
            /\ wt_sact vvs guard (bits_t 1) /\ wt_sact vvs fail_cond (bits_t 1)
            /\ nid <= nid' /\ wt_sact vvs (reduce t v) t /\ t = t0
            /\ forall Gamma sched_log action_log (WTRENV: wt_renv R REnv r)
                 (WTG: wt_env _ tsig Gamma) (WTLA: wt_log R REnv action_log)
                 (WTLS: wt_log R REnv sched_log)
                 (GE: match_Gamma_env Gamma env vvs0)
                 (MLR:
                   match_logs_r2v r2v vvs0 sched_rir rir sched_log action_log)
                 (GUARDOK: interp_sact vvs0 guard (Bits [true])),
               (forall action_log' vret Gamma'
                  (INTERP:
                     interp_daction r sigma Gamma sched_log action_log u
                     = Some (action_log', vret, Gamma')),
                interp_sact vvs (reduce t v) vret
                /\ interp_sact vvs fail_cond (Bits [false])
                /\ match_Gamma_env Gamma' env' vvs
                /\ match_logs_r2v r2v' vvs sched_rir rir' sched_log action_log'
                /\ wt_log R REnv action_log' /\ wt_env _ tsig Gamma')
            /\ (forall
              (INTERP:
                 interp_daction r sigma Gamma sched_log action_log u = None),
              interp_sact vvs fail_cond (Bits [true]))) args)
        lt
        (WTargs:
          Forall2 (wt_daction (R:=R) (Sigma:=Sigma) pos_t string string tsig)
          args lt)
        guard env r2v vvs0 sched_rir rir nid names0 fail0 names env' r2v' vvs
        fail1 rir' nid'
      (WTg: wt_sact vvs0 guard (bits_t 1)) (WTf: wt_sact vvs0 fail0 (bits_t 1))
      (WFR: wf_rir sched_rir vvs0) (WFS: wf_state tsig env r2v vvs0 rir nid)
      (GRIA:
        gria_list guard rec args tsig env r2v vvs0 sched_rir rir nid names0
        fail0 = (names, env', r2v', vvs, fail1, rir', nid'))
      lt0
      (NAMES:
        Forall2
          (fun '(var1, t1) t2 =>
            t1 = t2 /\ exists s, vvs0 ! var1 = Some (t1, s)) names0 lt0),
    same_env env env'
    /\ Forall2 (fun x y => fst x = fst y) r2v r2v'
    /\ rir_grows vvs0 rir vvs rir' guard
    /\ wf_state tsig env' r2v' vvs rir' nid'
    /\ wt_sact vvs guard (bits_t 1)
    /\ (Forall2
         (fun '(var1, t1) t2 => t1 = t2 /\ exists s, vvs !var1 = Some (t1, s))
         names (rev lt ++ lt0))
    /\ (List.length names = List.length names0 + List.length args)%nat
    /\ wt_sact vvs fail1 (bits_t 1)
    /\ nid <= nid'
    /\ (interp_sact vvs0 fail0 (Bits [true])
        -> interp_sact vvs fail1 (Bits [true]))
    /\ forall Gamma sched_log action_log (WTRENV: wt_renv R REnv r)
         (WTG: wt_env _ tsig Gamma) (WTLA: wt_log R REnv action_log)
         (WTLS: wt_log R REnv sched_log) (GE: match_Gamma_env Gamma env vvs0)
         (MLR: match_logs_r2v r2v vvs0 sched_rir rir sched_log action_log) lv0
         (INIT:
          Forall2 (fun '(n,t) v => interp_sact vvs0 (SVar n) v) names0 lv0)
         (INITFAIL: interp_sact vvs0 fail0 (Bits [false]))
         (GUARDOK: interp_sact vvs0 guard (Bits [true])),
       (forall action_log' Gamma' lv
          (INTERP: fold_left
             (fun acc a0 =>
                let/opt3 action_log0, l, Gamma0 := acc in (
                  let/opt3 action_log1, v, Gamma1 :=
                    interp_daction r sigma Gamma0 sched_log action_log0 a0
                  in Some (action_log1, v :: l, Gamma1))
             ) args
             (Some (action_log, lv0, Gamma)) = Some (action_log', lv, Gamma')),
        Forall2 (fun '(n,t) v => interp_sact vvs (SVar n) v) names lv
        /\ interp_sact vvs fail1 (Bits [false])
        /\ match_Gamma_env Gamma' env' vvs
        /\ match_logs_r2v r2v' vvs sched_rir rir' sched_log action_log'
        /\ wt_log R REnv action_log'
        /\ wt_env _ tsig Gamma')
       /\ (forall
        (INTERP:
          fold_left
            (fun acc a0 =>
               let/opt3 action_log0, l, Gamma0 := acc in (
                 let/opt3 action_log1, v, Gamma1 :=
                   interp_daction r sigma Gamma0 sched_log action_log0 a0
                 in Some (action_log1, v :: l, Gamma1)))
            args
            (Some (action_log, lv0, Gamma))
          = None),
      interp_sact vvs fail1 (Bits [true])).
  Proof.
    induction 1; simpl; intros; eauto.
    - inv GRIA. repeat refine (conj _ _); eauto.
      apply same_env_refl. apply same_regenv_refl. apply rir_grows_refl. auto.
      inv WTargs. simpl. eauto. lia.
      intros. split; intros. inv INTERP. repeat refine (conj _ _); eauto.
      inv INTERP.
    - repeat destr_in GRIA. subst. inv WTargs.
      eapply H in Heqp; eauto.
      destruct Heqp as (
        P12 & F2 & P22 & I12 & I22 & WTa & NIDGROWS2 & WTf0 & TEQ & INTERPHYP
      ). clear H.
      subst.
      generalize GRIA; intro GRIASAVE.
      eapply IHF in GRIA; eauto.
      destruct GRIA as (
        Pgria1 & F3 & Pgria2 & Igria1 & Igria2 & NAMES1 & LENNAMES & WTf2
        & NIDGROWS & FAILGROWS& INTERPHYP2
       ).
      repeat refine (conj _ _); eauto.
      + eapply same_env_trans; eauto.
      + eapply same_regenv_trans; eauto.
      + eapply rir_grows_weaken_guard. eapply rir_grows_trans.
        2: eauto. 3: eapply rir_grows_trans. 6: eauto.
        eauto. eauto.
        eapply wf_state_vvs_set with (m:=Pos.succ p1); eauto. lia.
        eapply wt_sact_valid_vars; eauto.
        apply I12. lia.
        eapply rir_grows_set; eauto. unfold valid_name; lia. eauto.
        intros. repeat econstructor; eauto. reflexivity. reflexivity. eauto.
      + simpl. rewrite <- app_assoc. apply NAMES1.
      + simpl in LENNAMES; lia.
      + lia.
      + intros; apply FAILGROWS.
        clear INTERPHYP2. clear INTERPHYP.
        exploit wt_sact_interp_bool. 4: apply WTa. 1-3: apply I12.
        intros (b & INTs).
        econstructor.
        eapply vvs_grows_interp_sact. 2: apply INTs.
        eapply vvs_grows_set. apply I12. lia.
        eapply vvs_grows_interp_sact. 2: apply H.
        eapply vvs_grows_trans. eauto using rir_vvs_grows.
        eapply vvs_grows_set. apply I12. lia.
        simpl. rewrite orb_true_r. auto.
      + intros.
        specialize (INTERPHYP Gamma sched_log action_log).
        trim INTERPHYP. eauto. trim INTERPHYP. eauto. trim INTERPHYP. eauto.
        trim INTERPHYP. eauto. trim INTERPHYP. eauto. trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        destruct INTERPHYP as (INTERPHYPOK & INTERHYPKO).
        destruct (interp_daction r sigma Gamma sched_log action_log x) eqn:?.
        destruct p as ((? & ?) & ?). simpl.
        Ltac dihyp H :=
          let iv := fresh "INTERPVAL" in
          let ig := fresh "INTERPFAIL" in
          let mge := fresh "MGE" in
          let mlr := fresh "MLR" in
          let wtl := fresh "WTL" in
          let wte := fresh "WTE" in
          edestruct H as (iv & ig & mge & mlr & wtl & wte); eauto.
        dihyp INTERPHYPOK.
        specialize (INTERPHYP2 l3 sched_log l2).
        trim INTERPHYP2. eauto.
        trim INTERPHYP2. eauto.
        trim INTERPHYP2. eauto.
        trim INTERPHYP2. eauto.
        trim INTERPHYP2.
        {
          eapply match_Gamma_env_vvs_grows; eauto.
          eapply vvs_grows_set. apply I12. lia.
        }
        trim INTERPHYP2.
        {
          eapply match_logs_r2v_vvs_grows; eauto. eapply vvs_grows_set.
          apply I12. lia. apply I12. apply I12. apply I12. apply I12.
          eapply wf_rir_grows. eauto. eauto using rir_vvs_grows.
        }
        trim (INTERPHYP2 (v::lv0)).
        {
          constructor. econstructor. rewrite PTree.gss. eauto.
          eapply vvs_grows_interp_sact; eauto using vvs_grows_set.
          eapply vvs_grows_set. apply I12. lia.
          eapply Forall2_impl. 2: eauto. simpl; intros.
          destr. eapply vvs_grows_interp_sact. 2: eauto.
          eapply vvs_grows_trans. 2: eapply vvs_grows_set.
          eapply rir_vvs_grows. eauto. apply I12. lia.
        }
        trim INTERPHYP2.
        {
          eapply vvs_grows_interp_sact. eapply vvs_grows_set. apply I12. lia.
          econstructor; eauto.
          eapply vvs_grows_interp_sact; eauto using rir_vvs_grows. reflexivity.
        }
        trim INTERPHYP2.
        {
          eapply vvs_grows_interp_sact. 2: eauto.
          eapply vvs_grows_trans. 2: eapply vvs_grows_set.
          eauto using rir_vvs_grows. apply I12. lia.
        }
        destruct INTERPHYP2 as (INTERPHYP2OK & INTERPHYP2KO).
        split; intros.
        dihyp INTERPHYP2OK. eauto.
        split; intros.
        simpl in INTERP.
        rewrite fold_left_none in INTERP. congruence. simpl. auto.
        eapply FAILGROWS.
        econstructor.
        eapply vvs_grows_interp_sact. 2: apply INTERHYPKO.
        eapply vvs_grows_set. apply I12. eauto. lia. eauto.
        eapply vvs_grows_interp_sact. 2: apply INITFAIL.
        eapply vvs_grows_trans. eauto using rir_vvs_grows.
        eapply vvs_grows_set. apply I12. lia. eauto.
      + eapply wt_sact_vvs_grows. 2: eauto.
        eapply vvs_grows_set. apply I12. lia.
      + econstructor. eapply wt_sact_vvs_grows. 2: eauto. eapply vvs_grows_set.
        apply I12. lia.
        eapply wt_sact_vvs_grows. 2: eauto.
        eapply vvs_grows_trans. eapply rir_vvs_grows; eauto.
        eapply vvs_grows_set. apply I12. lia.
        constructor.
      + eapply wf_rir_grows. eauto.
        eapply vvs_grows_trans. 2: eapply vvs_grows_set.
        eauto using rir_vvs_grows. apply I12. lia.
        all: apply WFS.
      + simpl. inv I12. constructor; auto.
        eapply wt_vvs_set; eauto. lia.
        eapply env_vvs_change_vvs; eauto. lia.
        eapply reg2var_vvs_grows; eauto. eapply vvs_grows_set; eauto. lia.
        eapply vvs_range_set. eauto.
        eapply vvs_smaller_variables_set. eauto. eapply wt_sact_valid_vars.
        eauto. eauto.
        eapply wf_rir_grows; eauto.
        eapply vvs_grows_set. eauto using rir_vvs_grows. lia.
      + simpl. constructor; eauto. split; auto.
        rewrite PTree.gss; eauto.
        eapply Forall2_impl. 2: apply NAMES. simpl.
        intros (n0 & ?) t1 (EQ & s0 & GET). subst. split; auto.
        rewrite PTree.gso; eauto.
        eapply rir_vvs_grows in GET. 2: eauto. eauto.
        eapply wfs_vvs_range in GET. 2: eauto. red in GET. lia.
  Qed.

  Lemma vvs_grows_same_r:
    forall vvs1 vvs2 vvs2' (VG: vvs_grows vvs1 vvs2)
      (SAME: forall k, vvs2' ! k = vvs2 ! k),
    vvs_grows vvs1 vvs2'.
  Proof.
    intros. eapply vvs_grows_trans. eauto.
    red. intros; rewrite SAME; eauto.
  Qed.

  Lemma wt_sact_same_vvs:
    forall vvs vvs' (SAME: forall k, vvs' ! k = vvs !k) a t
      (WT: wt_sact vvs a t),
    wt_sact vvs' a t.
  Proof.
    induction 2; simpl; intros; eauto.
    rewrite <- SAME in H; econstructor; eauto.
    constructor; auto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    constructor.
  Qed.

  Lemma interp_sact_same_vvs:
    forall vvs vvs' (SAME: forall k, vvs' ! k = vvs !k) a t
      (INTERP: interp_sact vvs a t),
    interp_sact vvs' a t.
  Proof.
    induction 2; simpl; intros; eauto.
    rewrite <- SAME in H; econstructor; eauto.
    constructor; auto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    constructor.
  Qed.

  Lemma interp_sact_same_vvs_iff:
    forall vvs vvs' (SAME: forall k, vvs' ! k = vvs !k) a t,
    interp_sact vvs a t <-> interp_sact vvs' a t.
  Proof.
    split; intros; eapply interp_sact_same_vvs. 2: eauto. auto. 2: eauto. auto.
  Qed.

  Lemma wf_rir_same_r:
    forall vvs vvs' rir (SAME: forall k, vvs' ! k = vvs !k), wf_rir rir vvs
    -> wf_rir rir vvs'.
  Proof.
    intros. inv H. split; auto.
    red; intros; eapply wt_sact_same_vvs; eauto.
    red; intros; eapply wt_sact_same_vvs; eauto.
    red; intros; eapply wt_sact_same_vvs; eauto.
    red; intros; eapply wt_sact_same_vvs; eauto.
  Qed.

  Lemma wf_state_same_r:
    forall tsig env r2v vvs vvs' rir nid (SAME: forall k, vvs' ! k = vvs !k),
    wf_state tsig env r2v vvs rir nid
    -> wf_state tsig env r2v vvs' rir nid.
  Proof.
    intros. destruct H.
    split; auto.
    red; intros. rewrite SAME in H. eapply wt_sact_same_vvs.
    2: eapply wfs_wt_vvs0; eauto. auto.
    red; intros. eapply Forall2_impl. 2: apply wfs_env_vvs0. simpl; intros.
    repeat destr_in H.
    destruct H as (? & ? & GET).
    rewrite <- SAME in GET; eauto.
    red; intros. setoid_rewrite SAME. eauto.
    red; intros. rewrite SAME in H; eauto.
    red; intros. rewrite SAME in H; eauto.
    eapply wf_rir_same_r; eauto.
  Qed.

  Lemma merge_branches2_grows2 :
    forall vm_tb vm_fb vvs nid cond_name vm' vvs' nid' tsig r2v r2v' rir,
    merge_branches2 vm_tb vm_fb tsig vvs nid cond_name = (vm', vvs', nid')
    -> wf_state tsig vm_tb r2v vvs rir nid
    -> wf_state tsig vm_fb r2v' vvs rir nid
    -> valid_name cond_name nid
    -> wt_sact vvs (SVar cond_name) (bits_t 1)
    -> vvs_grows vvs vvs'
    /\ nid <= nid' /\ wf_state tsig vm' r2v' vvs' rir nid'
    /\ Forall2
         (fun '(xt,xf) x =>
            forall b, interp_sact vvs' (SVar cond_name) (Bits [b])
            -> (
              forall v, interp_sact vvs' (SVar (snd (if b then xt else xf))) v
              <-> interp_sact vvs' (SVar (snd x)) v))
         (combine vm_tb vm_fb) vm'.
  Proof.
    intros.
    exploit merge_branches2_ok. eauto. apply H0. apply H0. apply H1.
    intros MB.
    edestruct (merge_branches_grows2) as (VG & LE & WFS & F2); eauto.
  Qed.

  Lemma get_rule_information_aux_env_grows:
    forall (ua: uact) tsig (env: list (string * positive)) reg2var (guard: sact)
      sched_rir (rir: rule_information_raw) (nid: positive)
         v env' reg2var' vvs fail_cond rir' nid' t vvs0
         (GRIA:
           get_rule_information_aux
             ua tsig env reg2var vvs0 guard sched_rir rir nid
           = (v, env', reg2var', vvs, fail_cond, rir', nid', t))
         tret
         (WT:
           BitsToLists.wt_daction
             pos_t string string (R:=R) (Sigma:=Sigma) tsig ua tret)
         (WFS: wf_state tsig env reg2var vvs0 rir nid)
         (WFRS: wf_rir sched_rir vvs0) (WTGUARD: wt_sact vvs0 guard (bits_t 1)),
      wf_state tsig env' reg2var' vvs rir' nid'
      /\ Forall2 (fun x y => fst x = fst y) reg2var reg2var'
      /\ rir_grows vvs0 rir vvs rir' guard /\ wf_rir sched_rir vvs
      /\ wt_sact vvs (reduce t v) t /\ wt_sact vvs fail_cond (bits_t 1)
      /\ nid <= nid' /\ same_env env env' /\ tret = t
      /\ forall Gamma sched_log action_log (WTRENV: wt_renv R REnv r)
           (WTG: wt_env _ tsig Gamma) (WTLA: wt_log R REnv action_log)
           (WTLS: wt_log R REnv sched_log) (GE: match_Gamma_env Gamma env vvs0)
           (MLR: match_logs_r2v reg2var vvs0 sched_rir rir sched_log action_log)
           (GUARDOK: interp_sact vvs0 guard (Bits [true])),
         (forall action_log' vret Gamma'
            (INTERP:
              interp_daction r sigma Gamma sched_log action_log ua
              = Some (action_log', vret, Gamma')),
          interp_sact vvs (reduce t v) vret
          /\ interp_sact vvs fail_cond (Bits [false])
          /\ match_Gamma_env Gamma' env' vvs
          /\ match_logs_r2v reg2var' vvs sched_rir rir' sched_log action_log'
          /\ wt_log R REnv action_log'
          /\ wt_env _ tsig Gamma')
          /\ (forall
                (INTERP:
                   interp_daction r sigma Gamma sched_log action_log ua = None),
              interp_sact vvs fail_cond (Bits [true])).
  Proof.
    Opaque skipn.
    intros ua; pattern ua; eapply daction_ind'; simpl; intros; eauto.
    all: repeat destr_in GRIA; inv GRIA; eauto; try now (intuition congruence).
    - inv WT.
    - inv WT.
      intuition try congruence. eapply same_regenv_refl. eapply rir_grows_refl.
      auto.
      apply wt_sact_reduce. easy. repeat constructor. lia. apply same_env_refl.
      constructor.
    - inv WT.
      repeat refine (conj _ _); eauto.
      + eapply same_regenv_refl.
      + eapply rir_grows_refl. auto.
      + simpl; intros. edestruct env_vvs_ex; eauto. inv WFS; eauto.
        econstructor; eauto.
      + repeat constructor.
      + lia.
      + apply same_env_refl.
      + inv H1.
        eapply assoc_list_assoc in H. congruence.
      + simpl. split; intros. unfold opt_bind in INTERP.
        repeat destr_in INTERP; inv INTERP.
        edestruct match_Gamma_env_ex as (
          ? & tt & s & GET1 & GET2 & GET3 & GET4
        ); eauto.
        inv WFS; eauto. rewrite GET1 in Heqo; inv Heqo.
        rewrite GET2 in Heqo0; inv Heqo0.
        repeat refine (conj _ _); eauto.
        econstructor; eauto. econstructor; eauto.
        unfold opt_bind in INTERP.
        repeat destr_in INTERP; inv INTERP.
        Lemma mge_some_none:
          forall g e vvs var n,
            match_Gamma_env g e vvs
            -> list_assoc e var = Some n
            -> list_assoc g var = None
            -> False.
        Proof.
          induction 1. easy. simpl. repeat destr.
          subst. intros A; inv A. intuition auto with *. eauto.
        Qed.
        edestruct mge_some_none; eauto.
    - exfalso; eapply env_vvs_some_none; eauto.
      inv WFS; eauto.
    - inv WT. inv H1.
      apply assoc_list_assoc in H.
      edestruct env_vvs_none_some. inv WFS; eauto. eauto. eauto.
    - intuition try congruence. eapply same_regenv_refl. eapply rir_grows_refl.
    auto.
      simpl. econstructor. inv WT. auto.
      repeat constructor. lia.
      apply same_env_refl.
      inv WT. auto.
      inv INTERP.
      simpl; econstructor. constructor. inv INTERP; eauto.
    - inv WT.
      Ltac dhyp H :=
        let wfs := fresh "WFS" in
        let wfrs := fresh "WFRsched" in
        let sre := fresh "SAMEREGENV" in
        let rg := fresh "RIRGROWS" in
        let wt := fresh "WTRES" in
        let vvs := fresh "FAILWT" in
        let ng := fresh "NIDGROWS" in
        let se := fresh "SAMEENV" in
        let teq := fresh "TEQ" in
        let interp := fresh "INTERPHYP" in
        edestruct H as (
          wfs & sre & rg & wfrs & wt & vvs & ng & se & teq & interp
        ); eauto.
      dhyp H.
      subst.
      inversion H5; subst. eapply assoc_list_assoc in H0.
      exploit wf_state_set. 3: eauto. 2: eauto. eauto.
      intros WFS2.
      assert (RG:
        rir_grows vvs0 rir (PTree.set p1 (projT1 tm, reduce (projT1 tm) o) t1)
        rir' (uor guard const_false)
      ).
      {
        eapply rir_grows_trans. 4: eapply rir_grows_set; eauto. eauto. 2: eauto.
        auto. unfold valid_name; lia.
      }
      repeat (refine (conj _ _)); eauto.
      + eapply rir_grows_weaken_guard; eauto.
        intros; econstructor; eauto. constructor. simpl. auto.
        inv RG. inv rir_wt_grd0. inv H9. auto.
      + eapply wf_rir_grows. 2: apply RG. eauto. all: try apply WFS.
      + eapply wt_sact_reduce; eauto. easy.
      + eapply wt_sact_vvs_grows. 2: eauto.
        eapply vvs_grows_set. inv WFS0; eauto. lia.
      + lia.
      + eapply same_env_set_in; eauto.
        destruct (list_assoc env v)eqn:?.
        eapply list_assoc_in_keys; eauto.
        edestruct env_vvs_none_some. inv WFS; eauto. eauto. eauto.
      + simpl; intros.
        specialize (INTERPHYP Gamma sched_log action_log).
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        destruct INTERPHYP as (INTERPHYPOK & INTERPHYPKO).
        split; intros.
        {
          unfold opt_bind in INTERP.
          repeat destr_in INTERP; inv INTERP.
          dihyp INTERPHYPOK.
          repeat (refine (conj _ _)); eauto.
          * econstructor.
          * eapply vvs_grows_interp_sact; eauto.
            eapply vvs_grows_set. inv WFS0; eauto. lia.
          * eapply match_Gamma_env_set; eauto. inv WFS0; eauto.
          * eapply match_logs_r2v_vvs_set; eauto.
          * eapply wt_env_set; eauto.
            edestruct (wt_sact_interp) with (a:=reduce (projT1 tm) o)
              as (vv & IS & WTV); eauto.
            1-3: inv WFS0; eauto.
            exploit interp_sact_determ. apply IS. apply INTERPVAL.
            intros ->; eauto.
        }
        {
          unfold opt_bind in INTERP.
          repeat destr_in INTERP; inv INTERP.
          eapply vvs_grows_interp_sact; eauto.
          eapply vvs_grows_set. inv WFS0; eauto. lia.
        }
    - inv WT.
      dhyp H. subst.
      dhyp H0.
      eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
      subst.
      repeat refine (conj _ _); eauto.
      + eapply same_regenv_trans; eauto.
      + eapply rir_grows_weaken_guard.
        eapply rir_grows_trans. 2,4: eauto. all: eauto.
        intros; econstructor; eauto.
        eapply wt_sact_vvs_grows. 2: eauto.
        eauto using vvs_grows_trans, rir_vvs_grows.
      + econstructor; eauto.
        eapply wt_sact_vvs_grows; eauto using rir_vvs_grows.
        constructor.
      + lia.
      + eapply same_env_trans; eauto.
      + simpl; intros.
        specialize (INTERPHYP Gamma sched_log action_log).
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        destruct INTERPHYP as (INTERPHYPOK & INTERPHYPKO).
        split; intros.
        intros.
        unfold opt_bind in INTERP. repeat destr_in INTERP; inv INTERP.
        dihyp INTERPHYPOK.
        specialize (INTERPHYP0 l0 sched_log l1).
        trim INTERPHYP0. eauto.
        trim INTERPHYP0. eauto.
        trim INTERPHYP0. eauto.
        trim INTERPHYP0. eauto.
        trim INTERPHYP0. eauto.
        trim INTERPHYP0. eauto.
        trim INTERPHYP0.
        eapply vvs_grows_interp_sact. 2: eauto.
        eauto using vvs_grows_trans, rir_vvs_grows.
        destruct INTERPHYP0 as (INTERPHYP0OK & INTERPHYP0KO).
        dihyp INTERPHYP0OK.
        repeat refine (conj _ _); eauto.
        econstructor.
        eapply vvs_grows_interp_sact. 2: eauto. eapply rir_vvs_grows; eauto.
        eauto. reflexivity. unfold opt_bind in INTERP.
        repeat destr_in INTERP; inv INTERP. dihyp INTERPHYPOK.
        specialize (INTERPHYP0 l0 sched_log l1).
        trim INTERPHYP0. eauto.
        trim INTERPHYP0. eauto.
        trim INTERPHYP0. eauto.
        trim INTERPHYP0. eauto.
        trim INTERPHYP0. eauto.
        trim INTERPHYP0. eauto.
        trim INTERPHYP0.
        eapply vvs_grows_interp_sact. 2: eauto.
        eauto using vvs_grows_trans, rir_vvs_grows.
        destruct INTERPHYP0 as (INTERPHYP0OK & INTERPHYP0KO).
        econstructor.
        eapply vvs_grows_interp_sact. 2: eauto.
        eauto using vvs_grows_trans, rir_vvs_grows.
        apply INTERPHYP0KO. auto. reflexivity.
        exploit wt_sact_interp_bool. 4: apply FAILWT0. 1-3: apply WFS1.
        intros (b & INTs). econstructor.
        eapply vvs_grows_interp_sact. 2: apply INTERPHYPKO.
        eauto using rir_vvs_grows. auto.
        eauto. simpl. auto.
    - inv WT. dhyp H. subst.
      assert (WFS2:
        wf_state ((v, t0) :: tsig) ((v, p1) :: l) r1
        (PTree.set p1 (t0, reduce t0 o) t1) r0 (Pos.succ p1)).
      {
        eapply wf_state_cons; eauto. intros.
        eapply wt_sact_below in H1; eauto.
      }
      assert (VG: vvs_grows vvs0 (PTree.set p1 (t0, reduce t0 o) t1)).
      {
        eapply rir_vvs_grows.
        eapply rir_grows_trans. 2: eauto. eauto.
        2: eapply rir_grows_set; eauto. eauto.
        unfold valid_name; lia.
      }
      dhyp H0.
      + eapply wf_rir_grows. apply WFRS. eauto. all: apply WFS.
      + eapply wt_sact_vvs_grows; eauto using rir_vvs_grows.
      + subst. inv SAMEENV0. simpl in H3. subst.
        change (skipn 1 (y::l')) with l'.
        assert (WFS3: wf_state tsig l' reg2var' vvs rir' nid').
        apply wf_state_tl in WFS1. simpl in WFS1. eauto.
        assert (RG3:
          rir_grows t1 r0 (PTree.set p1 (t0, reduce t0 o) t1) r0 const_false).
        {
          eapply rir_grows_set. eauto. unfold valid_name; lia.
        }
        repeat (refine (conj _ _)); eauto.
        * eapply same_regenv_trans; eauto.
        * eapply rir_grows_weaken_guard.
          eapply rir_grows_trans. 2: eauto. eauto.
          2: eapply rir_grows_trans. 3: eauto. eauto. eauto. eauto. eauto.
          intros; repeat econstructor; eauto. simpl. eauto.
          simpl; eauto.
          eapply wt_sact_vvs_grows. 2: eauto.
          eapply vvs_grows_trans; eauto using rir_vvs_grows, vvs_grows_trans.
        * econstructor.
          -- eapply wt_sact_vvs_grows. 2: eauto.
             eapply vvs_grows_trans; eauto using rir_vvs_grows.
          -- eauto.
          -- econstructor.
        * lia.
        * eapply same_env_trans; eauto.
        * intros.
          specialize (INTERPHYP Gamma sched_log action_log).
          trim INTERPHYP. eauto.
          trim INTERPHYP. eauto.
          trim INTERPHYP. eauto.
          trim INTERPHYP. eauto.
          trim INTERPHYP. eauto.
          trim INTERPHYP. eauto.
          trim INTERPHYP. eauto.
          destruct INTERPHYP as (INTERPHYPOK & INTERPHYPKO).
          destruct (interp_daction r sigma Gamma sched_log action_log ex) eqn:?.
          destruct p. destruct p. simpl.
          dihyp INTERPHYPOK.
          specialize (INTERPHYP0 ((fst y, v)::l0) sched_log l1).
          trim INTERPHYP0. eauto.
          trim INTERPHYP0.
          eapply wt_env_cons; eauto.
          inv WFS0.
          edestruct (wt_sact_interp) with (a:=reduce t0 o)
            as (vv & IS & WTV); eauto.
          exploit interp_sact_determ. apply IS. apply INTERPVAL.
          intros ->; eauto.
          trim INTERPHYP0. eauto.
          trim INTERPHYP0. eauto.
          trim INTERPHYP0.
          constructor. split; auto. simpl. econstructor. rewrite PTree.gss.
          eauto.
          eapply vvs_grows_interp_sact. 2: eauto. eapply vvs_grows_set.
          eapply wfs_vvs_range; eauto. lia.
          eapply match_Gamma_env_vvs_grows; eauto.
          eapply vvs_grows_set. eapply wfs_vvs_range; eauto. lia.
          trim INTERPHYP0.
          eapply match_logs_r2v_vvs_grows; eauto.
          eapply vvs_grows_set. eapply wfs_vvs_range; eauto. lia.
          1-4: apply WFS0.
          trim INTERPHYP0.
          eapply vvs_grows_interp_sact. 2: eauto.
          eauto using vvs_grows_trans, rir_vvs_grows.
          destruct INTERPHYP0 as (INTERPHYP0OK & INTERPHYP0KO).
          split; intros.
          unfold opt_bind in INTERP. repeat destr_in INTERP; inv INTERP.
          dihyp INTERPHYP0OK.
          repeat (refine (conj _ _)); eauto.
          econstructor; eauto.
          eapply vvs_grows_interp_sact. 2: eauto.
          eapply vvs_grows_trans; eauto. eapply vvs_grows_set.
          eapply wfs_vvs_range; eauto.
          2: eauto using rir_vvs_grows. lia. reflexivity.
          inv MGE0. simpl. eauto.
          inv WTE0. simpl. eauto.
          unfold opt_bind in INTERP. repeat destr_in INTERP; inv INTERP.
          econstructor; eauto.
          eapply vvs_grows_interp_sact. 2: eauto.
          eapply vvs_grows_trans; eauto. eapply vvs_grows_set.
          eapply wfs_vvs_range; eauto.
          2: eauto using rir_vvs_grows. lia. reflexivity.
          simpl. split; intros. congruence.
          exploit wt_sact_interp_bool. 4: apply FAILWT0. 1-3: apply WFS1.
          intros (b & INTs). econstructor.
          eapply vvs_grows_interp_sact. 2: apply INTERPHYPKO.
          eauto using vvs_grows_trans, rir_vvs_grows. auto.
          eauto. simpl. auto.
    - inv WT.
      dhyp H. subst.
      set (ll1 := PTree.set p1 (bits_t 1, reduce (bits_t 1) o) t1).
      set (ll2 := PTree.set (Pos.succ p1) (bits_t 1, uand guard (SVar p1)) ll1).
      set (
        ll3 := (
          PTree.set
            (Pos.succ (Pos.succ p1))
            (bits_t 1, uand guard (unot (SVar p1)))
            ll2)).
      fold ll1 ll2 ll3 in Heqp1.
      assert (WFSl1:
        wf_state tsig l r1 ll1 r0 (Pos.succ p1) /\ vvs_grows t1 ll1).
      {
        eapply wf_state_vvs_set; eauto. lia. intros.
        eapply wt_sact_below in H2; eauto. lia.
      }
      destruct WFSl1 as (WFSl1 & VG1).
      assert (WFSl2:
        wf_state tsig l r1 ll2 r0 (Pos.succ (Pos.succ p1))
        /\ vvs_grows ll1 ll2).
      {
        eapply wf_state_vvs_set; eauto.
        econstructor. eapply wt_sact_vvs_grows. 2: eauto.
        eapply vvs_grows_trans; eauto using rir_vvs_grows.
        econstructor. unfold ll1. rewrite PTree.gss. eauto.
        constructor. lia. simpl.
        intros v VIS. inv VIS.
        eapply wt_sact_below in H7; eauto. eapply wt_sact_vvs_grows. 2: eauto.
        eauto using vvs_grows_trans, rir_vvs_grows.
        inv H7. lia.
        lia.
      }
      destruct WFSl2 as (WFSl2 & VG2).
      assert (WFSl3:
        wf_state tsig l r1 ll3 r0 (Pos.succ (Pos.succ (Pos.succ p1)))
        /\ vvs_grows ll2 ll3).
      {
        eapply wf_state_vvs_set; eauto.
        econstructor. eapply wt_sact_vvs_grows. 2: eauto.
        eapply vvs_grows_trans; eauto using rir_vvs_grows.
        eapply vvs_grows_trans; eauto using rir_vvs_grows.
        econstructor. econstructor. unfold ll2, ll1.
        rewrite PTree.gso by lia.
        rewrite PTree.gss. eauto.
        constructor. constructor. lia. simpl.
        intros v VIS. inv VIS.
        eapply wt_sact_below in H7; eauto. eapply wt_sact_vvs_grows. 2: eauto.
        eauto using vvs_grows_trans, rir_vvs_grows.
        inv H7. inv H5. lia.
        lia.
      }
      destruct WFSl3 as (WFSl3 & VG3).
      dhyp H0.
      eapply wf_rir_grows. eauto.
      eauto using vvs_grows_trans.
      econstructor.
      unfold ll3. rewrite PTree.gso by lia.
      unfold ll2. rewrite PTree.gss; eauto.
      subst.
      dhyp H1.
      inv WFS1; eapply wf_state_vvs_grows_incr; eauto.
      econstructor. eapply rir_vvs_grows. eauto.
      unfold ll3; rewrite PTree.gss. eauto.
      subst.
      assert (WTcond: wt_sact t5 (SVar p1) (bits_t 1)).
      {
        eapply wt_sact_vvs_grows.
        eapply vvs_grows_trans. 2: eapply rir_vvs_grows; eauto.
        eapply rir_vvs_grows; eauto. econstructor.
        unfold ll3, ll2, ll1.
        rewrite PTree.gso by lia.
        rewrite PTree.gso by lia.
        rewrite PTree.gss. eauto.
      }
      edestruct merge_branches2_grows2
        as (VVSGROWS4 & NIDGROWS4 & WFS4 & EVAL4); eauto.
      inv WFS2; eapply wf_state_vvs_grows_incr; eauto.
      red; lia.
      assert (RG4: rir_grows t3 r2 t6 rir' (SVar (Pos.succ (Pos.succ p1)))).
      {
        eapply rir_grows_weaken_guard.
        - eapply rir_grows_trans. 2: eauto. all: eauto.
          eapply rir_grows_change_vvs with (grd:=const_false); eauto.
          repeat constructor.
        - intros; econstructor; eauto. repeat constructor. reflexivity.
        - eapply wt_sact_vvs_grows.
          eapply vvs_grows_trans. 2: eauto using rir_vvs_grows.
          eapply vvs_grows_trans. 2: eauto using rir_vvs_grows.
          eauto using rir_vvs_grows.
          econstructor. unfold ll3. setoid_rewrite PTree.gss. eauto.
      }
      edestruct merge_reg2var_grows2 as (VVSGROWS5 & NIDGROWS5 & WFS5 & EVAL5).
      2: eauto.
      eapply same_regenv_trans; eauto.
      eapply same_regenv_sym; eauto.
      eapply wf_state_vvs_grows_incr; eauto. 1-4: inv WFS4; eauto. lia.
      apply WFS4.
      eauto.
      eapply wf_rir_grows. apply WFRsched1. auto.
      red; lia.
      eapply wt_sact_vvs_grows; eauto.
      assert (rir_grows t3 r2 vvs rir' (SVar (Pos.succ (Pos.succ p1)))).
      {
        eapply rir_grows_weaken_guard.
        - eapply rir_grows_trans. 2: eauto. all: eauto.
          eapply rir_grows_change_vvs with (grd:=const_false); eauto.
          repeat constructor.
        - intros; econstructor; eauto. repeat constructor. reflexivity.
        - eapply wt_sact_vvs_grows.
          eapply vvs_grows_trans. 2: eauto.
          eapply vvs_grows_trans. 2: eauto.
          eapply vvs_grows_trans. 2: eauto using rir_vvs_grows.
          eauto using rir_vvs_grows.
          econstructor. unfold ll3. setoid_rewrite PTree.gss. eauto.
      }
      assert (rir_grows t1 r0 ll3 r0 const_false).
      {
        eapply rir_grows_change_vvs. eauto.
        intros; eauto using vvs_grows_trans.
        repeat constructor.
      }
      assert (rir_grows t1 r0 vvs rir' guard).
      {
        eapply rir_grows_weaken_guard.
        eapply rir_grows_trans. 2: eauto. eauto. eauto.
        eapply rir_grows_trans. 4: eauto. all: eauto.
        intros.
        assert (interp_sact ll3 guard (Bits [false])).
        {
          eapply interp_sact_vvs_grows_inv. 6: eauto. all: inv WFSl3; eauto.
          eapply vvs_grows_trans; eauto using rir_vvs_grows.
          eapply wt_sact_vvs_grows. 2: eauto.
          eapply vvs_grows_trans; eauto using rir_vvs_grows.
        }
        assert (exists b, interp_sact ll3 (SVar p1) (Bits [b])).
        {
          edestruct wt_sact_interp as (vv & IS & WTv).
          4: apply WTRES. 1-3: inv WFS0; eauto.
          eapply wt_val_bool in WTv. destruct WTv; subst.
          exists x; econstructor.
          unfold ll3; rewrite PTree.gso by lia.
          unfold ll2; rewrite PTree.gso by lia.
          unfold ll1; rewrite PTree.gss. eauto.
          eapply vvs_grows_interp_sact. 2: eauto.
          eauto using rir_vvs_grows.
        } destruct H7.
        assert (interp_sact ll3 (SVar (Pos.succ p1)) (Bits [false])).
        {
          econstructor.
          unfold ll3; rewrite PTree.gso by lia.
          unfold ll2; rewrite PTree.gss. eauto.
          econstructor; eauto.
        }
        assert (interp_sact ll3 (SVar (Pos.succ (Pos.succ p1))) (Bits [false])).
        {
          econstructor.
          unfold ll3; rewrite PTree.gss. eauto.
          econstructor; eauto.
          econstructor; eauto. simpl. eauto. simpl. auto.
        }
        eapply vvs_grows_interp_sact with (v1:=ll3).
        eapply vvs_grows_trans; eauto using rir_vvs_grows.
        econstructor. repeat econstructor; eauto.
        econstructor. eauto. eauto. simpl. reflexivity. simpl. reflexivity.
        eapply wt_sact_vvs_grows. eapply rir_vvs_grows. apply H2.
        eapply wt_sact_vvs_grows. eapply rir_vvs_grows. eauto.
        eapply wt_sact_vvs_grows. eauto.
        eapply wt_sact_vvs_grows. eauto.
        eapply wt_sact_vvs_grows. eauto.
        eapply wt_sact_vvs_grows. eauto using rir_vvs_grows. eauto.
      }
      assert (rir_grows vvs0 rir vvs rir' guard).
      {
        eapply rir_grows_weaken_guard.
        eapply rir_grows_trans. 2: eauto. 1,2: eauto. eauto.
        intros. econstructor; eauto.
        eapply wt_sact_vvs_grows. eauto using rir_vvs_grows.
        eapply wt_sact_vvs_grows. 2: eauto.
        eapply vvs_grows_trans; eauto using rir_vvs_grows.
        eapply vvs_grows_trans; eauto using rir_vvs_grows.
        eapply vvs_grows_trans; eauto using rir_vvs_grows.
        eapply vvs_grows_trans; eauto using rir_vvs_grows.
        eapply vvs_grows_trans; eauto using rir_vvs_grows.
      }
      repeat (refine (conj _ _)); auto.
      + eapply same_regenv_trans; eauto.
        eapply same_regenv_trans. apply SAMEREGENV0.
        eapply merge_reg2vars_same_structure; eauto.
        eapply same_regenv_trans; eauto.
        eapply same_regenv_sym; eauto.
      + eapply wf_rir_grows. 2: apply H5. eauto. all: apply WFS.
      + simpl. econstructor.
        * eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
        * eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
        * eapply wt_sact_vvs_grows. 2: eauto.
          eapply vvs_grows_trans; eauto.
      + econstructor.
        * eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
        * econstructor.
          econstructor. eapply wt_sact_vvs_grows. 2: eauto.
          eauto using rir_vvs_grows.
          eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
          constructor.
          econstructor. econstructor.
          eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
          constructor.
          eapply wt_sact_vvs_grows. 2: eauto.
          eapply vvs_grows_trans; eauto. constructor. constructor.
        * constructor.
      + lia.
      +

  Lemma merge_vms2_preserve_same_env:
    forall (l2 l4: list (string*positive)) (F: same_env l2 l4) tsig P
      (F2: Forall2 P l2 tsig) (l3: var_value_map) cname n1 env' vvs n2,
    merge_branches2 l2 l4 tsig l3 n1 cname = (env', vvs, n2)
    -> same_env l2 env'.
  Proof.
    induction 1; simpl; intros; eauto.
    - inv H. constructor.
    - inv F2. do 5 destr_in H0. eapply IHF in Heqp2; eauto.
      destr_in H0; inv H0; constructor; auto.
  Qed.
    exploit merge_vms2_preserve_same_env. 3: eauto. 2: apply WFS1.
    eapply same_env_trans. apply same_env_sym; eauto. auto. intro SAMEENV3.
    eapply same_env_trans; eauto.
    eapply same_env_trans. 2: eauto. eauto.

  + intros.
    specialize (INTERPHYP Gamma sched_log action_log).
    trim INTERPHYP. eauto.
    trim INTERPHYP. eauto.
    trim INTERPHYP. eauto.
    trim INTERPHYP. eauto.
    trim INTERPHYP. eauto.
    trim INTERPHYP. eauto.
    trim INTERPHYP. eauto.
    destruct INTERPHYP as (INTERPHYPOK & INTERPHYPKO).
    destruct (
      interp_daction r sigma Gamma sched_log action_log cond
    ) eqn:?; simpl.
    destruct p. destruct p. simpl.
    dihyp INTERPHYPOK.
    exploit interp_sact_wt_bool. 5: apply INTERPVAL. 4: now eauto.
    1-3: apply WFS0. intros (?&?); subst. 2: split; [intros; congruence |].
    specialize (INTERPHYP0 l2 sched_log l3).
    trim INTERPHYP0. eauto.
    trim INTERPHYP0. eauto.
    trim INTERPHYP0. eauto.
    trim INTERPHYP0. eauto.
    trim INTERPHYP0.
    eapply match_Gamma_env_vvs_grows. eauto.
    eauto using vvs_grows_trans.
    trim INTERPHYP0.
    eapply match_logs_r2v_vvs_grows; eauto.
    eauto using vvs_grows_trans.
    1-4:apply WFS0.
    specialize (INTERPHYP1 l2 sched_log l3).
    trim INTERPHYP1. eauto.
    trim INTERPHYP1. eauto.
    trim INTERPHYP1. eauto.
    trim INTERPHYP1. eauto.
    trim INTERPHYP1.
    eapply match_Gamma_env_vvs_grows. eauto.
    eapply vvs_grows_trans. apply VG1.
    eapply vvs_grows_trans; eauto.
    eapply vvs_grows_trans; eauto.
    eauto using vvs_grows_trans, rir_vvs_grows.
    Ltac trim_assert H cond :=
      match type of H with
      | ?a -> ?b =>
        let x := fresh "H" in
        assert (x: forall (Hcond: cond), a); [
        | let HH := fresh in
          assert (HH: cond -> b);[
            let X := fresh in intro X; apply x in X; apply (H X)
            | clear H; clear x; rename HH into H
          ]
        ]
      end.
    trim_assert INTERPHYP1 (x = false).
    intros. eapply match_logs_r2v_rir_grows; eauto.
    eapply rir_grows_trans. 4: eauto. 2: eauto. eauto. eauto.
    1-4: apply WFS0. 1-4: apply WFS1.
    eapply vvs_grows_interp_sact. eauto using rir_vvs_grows.
    edestruct wt_sact_interp as (vg & ISG & WTGv).
    4: apply WTGUARD. 1-3: inv WFS; eauto.
    apply wt_val_bool in WTGv. destruct WTGv as (? & WTGv). subst.
    econstructor. constructor. econstructor.
    unfold ll3. rewrite PTree.gso by lia.
    unfold ll2; rewrite PTree.gss. eauto.
    econstructor.
    eapply vvs_grows_interp_sact. 2: apply ISG.
    eauto using vvs_grows_trans, rir_vvs_grows.
    econstructor.
    unfold ll3, ll2, ll1.
    repeat rewrite PTree.gso by lia.
    rewrite PTree.gss. eauto.
    eapply vvs_grows_interp_sact. 2: apply INTERPVAL.
    eauto using vvs_grows_trans, rir_vvs_grows.
    simpl; eauto. simpl; eauto. rewrite andb_false_r; auto.
    trim_assert INTERPHYP0 (x=true).
    {
      intros; subst. econstructor. unfold ll3. rewrite PTree.gso by lia.
      unfold ll2; rewrite PTree.gss. eauto.
      econstructor.
      eapply vvs_grows_interp_sact. 2: eauto.
      eauto using vvs_grows_trans, rir_vvs_grows.
      econstructor. unfold ll3, ll2, ll1.
      repeat rewrite PTree.gso by lia. rewrite PTree.gss. eauto.
      eapply vvs_grows_interp_sact. 2: eauto.
      eauto using vvs_grows_trans, rir_vvs_grows.
      reflexivity.
    }
    Ltac swaphyps H :=
      match type of H with
      | ?a -> ?b -> ?c => specialize (fun B A => H A B)
      end.
    swaphyps INTERPHYP1.
    trim_assert INTERPHYP1 (x=false).
    {
      intros; subst.
      eapply vvs_grows_interp_sact. eauto using rir_vvs_grows.
      econstructor. unfold ll3; repeat rewrite PTree.gso by lia.
      rewrite PTree.gss. eauto.
      econstructor.
      eapply vvs_grows_interp_sact. 2: eauto.
      eauto using vvs_grows_trans, rir_vvs_grows.
      econstructor.
      econstructor. unfold ll3, ll2, ll1.
      repeat rewrite PTree.gso by lia. rewrite PTree.gss. eauto.
      eapply vvs_grows_interp_sact. 2: eauto.
      eauto using vvs_grows_trans, rir_vvs_grows.
      reflexivity. reflexivity.
    }
    split; intros.
    destr_in INTERP.
    * destruct INTERPHYP0 as (INTERPHYP0OK & INTERPHYP0KO). auto.
      dihyp INTERPHYP0OK.
      repeat refine (conj _ _); eauto.
      -- econstructor.
         eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
         simpl.
         eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
      -- econstructor.
         eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
         instantiate (1:=Bits [false]).
         econstructor. econstructor.
         eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
         eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
         simpl. reflexivity.
         instantiate (1:=Bits [false]).
         edestruct wt_sact_interp with (a:=s1) as (? & IV & WTv). 4: eauto.
         1-3: inv WFS2; eauto.
         econstructor. econstructor.
         eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
         reflexivity.
         eapply vvs_grows_interp_sact. 2: eauto. eauto using vvs_grows_trans.
         eapply wt_val_bool in WTv. destruct WTv. subst. simpl. reflexivity.
         reflexivity.
         reflexivity.
      -- assert (match_Gamma_env Gamma' env' t6).
        {
          eapply mge_merge_branches.
          4: {
            econstructor. eapply VVSGROWS4. eapply rir_vvs_grows; eauto.
            eapply rir_vvs_grows; eauto.
            unfold ll3, ll2, ll1. rewrite PTree.gso.
            rewrite PTree.gso.
            rewrite PTree.gss. eauto. lia. lia.
            eapply vvs_grows_interp_sact. 2: eauto.
            eapply vvs_grows_trans. 2: eauto.
                eapply vvs_grows_trans. apply VG1.
                eapply vvs_grows_trans; eauto.
                eapply vvs_grows_trans; eauto.
                eapply vvs_grows_trans; eauto using rir_vvs_grows.
              }
              3: simpl; eauto. 4: eauto.
              eapply same_env_trans.
              apply same_env_sym. eauto. eauto.
              eapply merge_vms2_preserve_same_env. 3: eauto.
              eapply same_env_trans.
              apply same_env_sym. eauto. eauto.
              apply WFS1.
              eapply match_Gamma_env_vvs_grows. apply MGE0.
              eauto using rir_vvs_grows.
            }
            eapply match_Gamma_env_vvs_grows. apply H7. auto.
          -- apply EVAL5.
             intros.
             assert (b = true).
             exploit vvs_grows_interp_sact.
             eapply vvs_grows_trans. 2: apply VVSGROWS4.
             eapply vvs_grows_trans. 2: eauto using rir_vvs_grows.
             eauto using rir_vvs_grows.
             2: intro IS; exploit interp_sact_determ.
             2: apply H7. 2: apply IS.
             econstructor. unfold ll3, ll2, ll1.
             repeat rewrite PTree.gso by lia.
             rewrite PTree.gss. eauto.
             eapply vvs_grows_interp_sact. 2: eauto.
             eauto using vvs_grows_trans. intro A; inv A. auto.
             subst.
             eapply match_logs_r2v_rir_grows. eauto. eauto.
             1-4: apply WFS1. eauto.
             eapply wf_rir_grows. apply WFS2. eauto.
             1-3: apply WFS4.
             eapply vvs_grows_interp_sact with (v1:=ll3).
             eauto using vvs_grows_trans, rir_vvs_grows.
             unfold ll3,ll2,ll1.
             econstructor.
             rewrite PTree.gss. eauto.
             edestruct wt_sact_interp as (vg & ISG & WTGv).
             4: apply WTGUARD. 1-3: inv WFS; eauto.
             apply wt_val_bool in WTGv. destruct WTGv as (? & WTGv). subst.
             econstructor. eapply vvs_grows_interp_sact. 2: eauto.
             eauto using vvs_grows_trans, rir_vvs_grows.
             econstructor.
             eapply interp_sact_vvs_grows_inv. 6: now eauto.
             apply WFSl3.
             apply WFSl3.
             eauto using vvs_grows_trans, rir_vvs_grows.
             apply WFSl3.
             econstructor. rewrite PTree.gso by lia.
             rewrite PTree.gso by lia.
             rewrite PTree.gss. eauto.
             simpl; eauto.
             simpl; eauto. rewrite andb_false_r. auto.
        * destruct INTERPHYP1 as (INTERPHYP1OK & INTERPHYP1KO). auto. auto.
          dihyp INTERPHYP1OK.
          -- repeat refine (conj _ _); eauto.
             ++ econstructor.
                eapply vvs_grows_interp_sact. 2: eauto.
                eauto using vvs_grows_trans, rir_vvs_grows.
                simpl.
                eapply vvs_grows_interp_sact. 2: eauto.
                eauto using vvs_grows_trans, rir_vvs_grows.
             ++ edestruct wt_sact_interp with (a:=s0) as (? & IV & WTv).
                4: eauto.  1-3: inv WFS1; eauto.
                destruct (wt_val_bool _ WTv); subst.
                econstructor.
                eapply vvs_grows_interp_sact. 2: eauto.
                eauto using rir_vvs_grows.
                econstructor. econstructor.
                eapply vvs_grows_interp_sact.
                2: eauto. eauto using rir_vvs_grows.
                eapply vvs_grows_interp_sact. 2: eauto.
                eauto using rir_vvs_grows. simpl. reflexivity.
                econstructor. econstructor.
                eapply vvs_grows_interp_sact. 2: eauto.
                eauto using rir_vvs_grows. reflexivity.
                eapply vvs_grows_interp_sact. 2: eauto.
                eauto using vvs_grows_trans.
                simpl. eauto. simpl; eauto. reflexivity.
             ++ assert (match_Gamma_env Gamma' env' t6).
                {
                  eapply mge_merge_branches.
                  4: {
                    econstructor. eapply VVSGROWS4. eapply rir_vvs_grows; eauto.
                    eapply rir_vvs_grows; eauto.
                    unfold ll3, ll2, ll1.
                    rewrite PTree.gso.
                    rewrite PTree.gso.
                    rewrite PTree.gss. eauto. lia. lia.
                    eapply vvs_grows_interp_sact. 2: eauto.
                    eapply vvs_grows_trans. 2: eauto.
                    eapply vvs_grows_trans. apply VG1.
                    eapply vvs_grows_trans; eauto.
                    eapply vvs_grows_trans; eauto.
                    eapply vvs_grows_trans; eauto using rir_vvs_grows.
                  }
                  3: simpl; eauto. 4: eauto.
                  eapply same_env_trans.
                  apply same_env_sym. eauto. eauto.
                  eapply merge_vms2_preserve_same_env. 3: eauto.
                  eapply same_env_trans.
                  apply same_env_sym. eauto. eauto. apply WFS1.
                  eapply match_Gamma_env_vvs_grows. apply MGE0.
                  eauto using rir_vvs_grows.
                }
                eapply match_Gamma_env_vvs_grows. apply H7. auto.
             ++ apply EVAL5.
                intros.
                assert (b = false).
                exploit vvs_grows_interp_sact.
                eapply vvs_grows_trans. 2: apply VVSGROWS4.
                eapply vvs_grows_trans. 2: eauto using rir_vvs_grows.
                eauto using rir_vvs_grows.
                2: intro IS; exploit interp_sact_determ.
                2: apply H7. 2: apply IS.
                econstructor.
                unfold ll3, ll2, ll1.
                repeat rewrite PTree.gso by lia.
                rewrite PTree.gss; eauto.
                eapply vvs_grows_interp_sact. 2: eauto.
                eauto using vvs_grows_trans. intro A; inv A. auto.
                subst.
                eapply match_logs_r2v_vvs_grows; eauto.
                all: apply WFS2.
        * econstructor.
          eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
          instantiate (1:=Bits [true]).
          destr_in INTERP.
          -- destruct INTERPHYP0 as (_ & FAIL0). auto.
             edestruct wt_sact_interp_bool with (a:=s1). 4: eauto.
             1-3: apply WFS2.
             econstructor. econstructor.
             eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
             eapply vvs_grows_interp_sact. 2: apply FAIL0.
             eauto using rir_vvs_grows. auto.
             reflexivity.
             econstructor. econstructor.
             eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
             reflexivity.
             eapply vvs_grows_interp_sact. 2: apply H7.
             eauto using vvs_grows_trans, rir_vvs_grows.
             reflexivity. reflexivity.
          -- destruct INTERPHYP1 as (_ & FAIL0). auto. auto.
             edestruct wt_sact_interp_bool with (a:=s0). 4: eauto.
             1-3: apply WFS1.
             econstructor. econstructor.
             eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
             eapply vvs_grows_interp_sact.
             2: apply H7. eauto using rir_vvs_grows.
             reflexivity. econstructor. econstructor.
             eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
             reflexivity.
             eapply vvs_grows_interp_sact. 2: apply FAIL0.
             eauto using vvs_grows_trans, rir_vvs_grows.
             auto. reflexivity.
             reflexivity.
          -- simpl. reflexivity.
        * intros.
          edestruct wt_sact_interp_bool with (
            a := (
              uor
                (uand (reduce (bits_t 1) o) s0)
                (uand (unot (reduce (bits_t 1) o)) s1)
            )
          ).
          1-3: apply WFS5.
          econstructor. econstructor.
          eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
          eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
          constructor.
          econstructor. econstructor.
          eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
          constructor.
          eapply wt_sact_vvs_grows. 2: eauto.
          eauto using vvs_grows_trans, rir_vvs_grows.
          constructor. constructor.
          econstructor; eauto.
          eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
          reflexivity.
    - repeat (refine (conj _ _)); eauto.
      + exploit wt_sact_interp; eauto. 1-3: inv WFS; eauto.
        intros (v & IS & WTg). destruct (wt_val_bool _ WTg). subst.
        eapply wf_state_change_rir; eauto. eapply rir_grows_add_read0; eauto.
        eapply wf_rir_add_read0; eauto. inv WFS; eauto.
      + apply same_regenv_refl.
      + exploit wt_sact_interp; eauto. 1-3: inv WFS; eauto.
        intros (v & IS & WTg). destruct (wt_val_bool _ WTg). subst.
        eapply rir_grows_add_read0; eauto.
      + simpl.
        edestruct wfs_r2v_vvs as (? & GET & ? & GET2); eauto.
        setoid_rewrite Heqo in GET. inv GET. eauto.
        econstructor; eauto.
      + econstructor. eapply wt_rir_has_write0; eauto.
        eapply wt_rir_has_write1; eauto. constructor.
      + lia.
      + apply same_env_refl.
      + inv WT. auto.
      + split; intros;
        destr_in INTERP; inv INTERP.
        {
          inv WT.
          repeat (refine (conj _ _)); eauto.
          * exploit mlr_read. eauto. eauto. eauto.
          * unfold may_read in Heqb.
            rewrite andb_true_iff in Heqb.
            rewrite ! negb_true_iff in Heqb. destruct Heqb.
            inv MLR. inv mlr_mlv_sched0.
            rewrite mlv_write2 in H.
            rewrite mlv_write3 in H0.
            econstructor; eauto.
          * eapply match_logs_r2v_add_read0. eauto. eauto.
          * eapply wt_log_cons; eauto. simpl. congruence.
        }
        {
          simpl in Heqb.
          rewrite andb_false_iff in Heqb.
          rewrite ! negb_false_iff in Heqb.
          inv MLR. inv mlr_mlv_sched0.
          exploit wt_rir_has_write0. apply WFRS.
          exploit wt_rir_has_write1. apply WFRS.
          intros HW1 HW0.
          exploit wt_sact_interp_bool. 4: apply HW0. 1-3: apply WFS.
          exploit wt_sact_interp_bool. 4: apply HW1. 1-3: apply WFS.
          intros (?&?) (?&?).
          econstructor. eauto. eauto. simpl.
          destruct x, x0; auto.
          rewrite <- mlv_write2 in H0.
          rewrite <- mlv_write3 in H.
          destruct Heqb; congruence.
        }
    - repeat (refine (conj _ _)); eauto.
      + exploit wt_sact_interp; eauto. 1-3: inv WFS; eauto.
        intros (v & IS & WTg). apply wt_val_bool in WTg. inv WTg.
        eapply wf_state_change_rir; eauto. eapply rir_grows_add_read1; eauto.
        eapply wf_rir_add_read1; inv WFS; eauto.
      + apply same_regenv_refl.
      + exploit wt_sact_interp; eauto. 1-3: inv WFS; eauto.
        intros (v & IS & WTg). apply wt_val_bool in WTg. inv WTg.
        eapply rir_grows_add_read1; eauto.
      + simpl.
        edestruct wfs_r2v_vvs as (? & GET & ? & GET2); eauto.
        setoid_rewrite Heqo in GET. inv GET. eauto.
        econstructor; eauto.
      + eapply wt_rir_has_write1; eauto.
      + lia.
      + apply same_env_refl.
      + inv WT. auto.
      + split; intros;
        destr_in INTERP; inv INTERP.
        {
          inv WT.
          repeat (refine (conj _ _)); eauto.
          * exploit mlr_read. eauto. eauto. eauto.
          * unfold may_read in Heqb. apply negb_true_iff in Heqb.
            eapply mlv_write1 in Heqb. eauto. apply MLR.
          * eapply match_logs_r2v_add_read1; eauto.
          * eapply wt_log_cons; eauto. simpl. congruence.
        }
        {
          simpl in Heqb.
          rewrite ! negb_false_iff in Heqb.
          inv MLR. inv mlr_mlv_sched0.
          exploit wt_rir_has_write1. apply WFRS.
          intros HW1.
          exploit wt_sact_interp_bool. 4: apply HW1. 1-3: apply WFS.
          intros (?&?).
          destruct x; eauto.
          rewrite <- mlv_write3 in H. congruence.
        }
    - edestruct wfs_r2v_vvs as (? & GET & ? & GET2); eauto.
      setoid_rewrite Heqo in GET. inv GET.
    - edestruct wfs_r2v_vvs as (? & GET & ? & GET2); eauto.
      setoid_rewrite Heqo in GET. inv GET.
    - inv WT.
      dhyp H. subst.
      exploit rir_grows_add_write0. 3: eauto.
      eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
      all: eauto. simpl. intros (RG1 & WFS1 & WTfail).
      repeat (refine (conj _ _)); eauto.
      rewrite <- Pos.add_1_r. auto.
      + eapply same_regenv_trans; eauto.
        Lemma reg2var_vvs_add_write_same_regenv:
          forall (r1: r2vtype) k v,
            In k (map fst r1)
            -> Forall2 (fun x y => fst x = fst y) r1 (list_assoc_set r1 k v).
        Proof.
          induction r1; simpl; intros; eauto. easy.
          destruct a. simpl in *. destruct H.
          - subst. rewrite eq_dec_refl. constructor; auto.
            apply same_regenv_refl.
          - destr. subst. constructor; auto. apply same_regenv_refl.
            constructor; auto.
        Qed.
        eapply same_regenv_trans.
        2: apply reg2var_vvs_add_write_same_regenv.
        apply reg2var_vvs_add_write_same_regenv.
        edestruct (wfs_r2v_vvs) as (? & GET & _). apply WFS0.
        apply list_assoc_in in GET.
        apply in_map with (f:=fst) in GET. apply GET.
        edestruct (wfs_r2v_vvs) as (? & GET & _). apply WFS0.
        apply list_assoc_in in GET.
        apply in_map with (f:=fst) in GET.
        eapply list_assoc_set_key_stays_in.
        apply GET.
      + eapply rir_grows_weaken_guard.
        eapply rir_grows_trans. 2: eauto. all: eauto.
        intros.
        econstructor; eauto.
        eapply wt_sact_vvs_grows. 2: eauto.
        eauto using vvs_grows_trans, rir_vvs_grows.
      + eapply wf_rir_grows. eauto. apply RG1. all: apply WFS0.
      + simpl. constructor. constructor. reflexivity.
      + econstructor; eauto. 2: constructor.
        eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
      + lia.
      + intros.
        trim (INTERPHYP Gamma sched_log action_log). eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        destruct INTERPHYP as (INTERPHYPOK & INTERPHYPKO).
        split; intros.
        unfold opt_bind in INTERP.
        repeat destr_in INTERP; inv INTERP.
        dihyp INTERPHYPOK.
        repeat (refine (conj _ _)); eauto.
        * repeat constructor.
        * econstructor.
          eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
          -- eapply vvs_grows_interp_sact. eauto using rir_vvs_grows.
             eapply add_write0_fail; eauto.
             eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
          -- reflexivity.
        * eapply match_Gamma_env_vvs_grows; eauto. eauto using rir_vvs_grows.
        * eapply match_logs_r2v_add_write0; eauto.
          eapply wt_sact_vvs_grows; eauto. apply RIRGROWS.
          eapply vvs_grows_interp_sact; eauto. apply RIRGROWS.
        * eapply wt_log_cons; eauto. simpl.
          eapply wt_daction_preserves_wt_env in Heqo0.
          intros; apply Heqo0. all: eauto.
        * unfold opt_bind in INTERP.
          repeat destr_in INTERP; inv INTERP.
          dihyp INTERPHYPOK.
          {
            unfold may_write in Heqb.
            unfold add_write0, add_write1 in Heqp1. inv Heqp1.
            rewrite ! log_existsb_log_app in Heqb.
            rewrite ! negb_orb in Heqb.
            rewrite ! andb_false_iff in Heqb.
            rewrite ! negb_false_iff in Heqb.
            econstructor. eapply vvs_grows_interp_sact. 2: eauto.
            eauto using rir_vvs_grows.
            econstructor. eapply vvs_grows_interp_sact. 2: eauto.
            eauto using vvs_grows_trans, rir_vvs_grows.
            instantiate(1:=Bits [true]).
            exploit wt_sact_interp_bool. 4: eapply wt_rir_has_write0.
            4: apply WFRS. 1-3: apply WFS.
            exploit wt_sact_interp_bool. 4: eapply wt_rir_has_write1.
            4: apply WFRS. 1-3: apply WFS.
            exploit wt_sact_interp_bool. 4: eapply wt_rir_has_read1.
            4: apply WFRS. 1-3: apply WFS.
            exploit wt_sact_interp_bool. 4: eapply wt_rir_has_write0.
            4: apply WFS0. 1-3: apply WFS0.
            exploit wt_sact_interp_bool. 4: eapply wt_rir_has_write1.
            4: apply WFS0. 1-3: apply WFS0.
            exploit wt_sact_interp_bool. 4: eapply wt_rir_has_read1.
            4: apply WFS0. 1-3: apply WFS0.
            intros (?&?) (?&?) (?&?) (?&?) (?&?) (?&?).
            eapply vvs_grows_interp_sact with (v1:=t1).
            eauto using vvs_grows_trans, rir_vvs_grows.
            repeat econstructor; eauto.
            4: eapply vvs_grows_interp_sact; [|now eauto];
              eauto using vvs_grows_trans, rir_vvs_grows.
            5: eapply vvs_grows_interp_sact; [|now eauto];
              eauto using vvs_grows_trans, rir_vvs_grows.
            6: eapply vvs_grows_interp_sact; [|now eauto];
              eauto using vvs_grows_trans, rir_vvs_grows.
            all: simpl; eauto.
            all: simpl; eauto.
            inv MLR. inv mlr_mlv_sched0.
            rewrite <-! not_false_iff_true in Heqb.
            rewrite (mlv_read3 idx) in Heqb.
            rewrite (mlv_write2 idx) in Heqb.
            rewrite (mlv_write3 idx) in Heqb.
            inv MLR0. inv mlr_mlv_action1.
            revert Heqb.
            rewrite mlv_read5, mlv_write4, mlv_write5. intros.
            destruct x, x0, x1, x2, x3, x4; simpl; auto.
            intuition auto with *.
          }
          exploit wt_sact_interp_bool. 4: apply WTfail. 1-3: apply WFS1.
          intros (?&?).
          econstructor; eauto. eapply vvs_grows_interp_sact. 2: eauto.
          eauto using vvs_grows_trans, rir_vvs_grows. reflexivity.
    - inv WT.
      dhyp H. subst.
      exploit rir_grows_add_write1. 3: eauto.
      eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
      all: eauto. simpl. intros (RG1 & WFS1 & WTfail).
      repeat (refine (conj _ _)); eauto.
      + eapply same_regenv_trans; eauto.
        apply reg2var_vvs_add_write_same_regenv.
        edestruct (wfs_r2v_vvs) as (? & GET & _).
        apply WFS0. apply list_assoc_in in GET.
        apply in_map with (f:=fst) in GET. apply GET.
      + eapply rir_grows_weaken_guard.
        eapply rir_grows_trans. 2: eauto. all: eauto.
        intros. econstructor; eauto.
        eapply wt_sact_vvs_grows. 2: eauto.
        eauto using vvs_grows_trans, rir_vvs_grows.
      + eapply wf_rir_grows. eauto. apply RG1. all: apply WFS0.
      + simpl. constructor. constructor. reflexivity.
      + econstructor; eauto. 2: constructor.
        eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
      + lia.
      + intros.
        trim (INTERPHYP Gamma sched_log action_log). eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        destruct INTERPHYP as (INTERPHYPOK & INTERPHYPKO).
        split; intros.
        unfold opt_bind in INTERP.
        repeat destr_in INTERP; inv INTERP.
        dihyp INTERPHYPOK.
        repeat (refine (conj _ _)); eauto.
        * repeat constructor.
        * econstructor.
          eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
          -- eapply vvs_grows_interp_sact. eauto using rir_vvs_grows.
             eapply add_write1_fail; eauto.
             eapply vvs_grows_interp_sact. 2: eauto. eauto using rir_vvs_grows.
          -- reflexivity.
        * eapply match_Gamma_env_vvs_grows; eauto. eauto using rir_vvs_grows.
        * eapply match_logs_r2v_add_write1; eauto.
          eapply wt_sact_vvs_grows; eauto. apply RIRGROWS.
          eapply vvs_grows_interp_sact; eauto. apply RIRGROWS.
        * eapply wt_log_cons; eauto. simpl.
          eapply wt_daction_preserves_wt_env in Heqo0. intros; apply Heqo0.
          all: eauto.
        * unfold opt_bind in INTERP.
          repeat destr_in INTERP; inv INTERP.
          dihyp INTERPHYPOK.
          {
            unfold may_write in Heqb.
            unfold add_write0, add_write1 in Heqp1. inv Heqp1.
            rewrite ! log_existsb_log_app in Heqb.
            rewrite ! negb_orb in Heqb.
            rewrite ! andb_false_iff in Heqb.
            rewrite ! negb_false_iff in Heqb.
            econstructor. eapply vvs_grows_interp_sact. 2: eauto.
            eauto using rir_vvs_grows.
            econstructor. eapply vvs_grows_interp_sact. 2: eauto.
            eauto using vvs_grows_trans, rir_vvs_grows.
            instantiate(1:=Bits [true]).
            exploit wt_sact_interp_bool. 4: eapply wt_rir_has_write1.
            4: apply WFRS. 1-3: apply WFS.
            exploit wt_sact_interp_bool. 4: eapply wt_rir_has_write1.
            4: apply WFS0. 1-3: apply WFS0.
            intros (?&?) (?&?).
            eapply vvs_grows_interp_sact with (v1:=t1).
            eauto using vvs_grows_trans, rir_vvs_grows.
            repeat econstructor; eauto.
            2: eapply vvs_grows_interp_sact;[|now eauto];
              eauto using vvs_grows_trans, rir_vvs_grows.
            all: simpl; eauto.
            all: simpl; eauto.
            inv MLR. inv mlr_mlv_sched0.
            rewrite <-! not_false_iff_true in Heqb.
            rewrite (mlv_write3 idx) in Heqb.
            inv MLR0. inv mlr_mlv_action1.
            revert Heqb.
            rewrite mlv_write5. intros.
            move H0 at bottom.
            move H1 at bottom.
            destruct x, x0; simpl; auto.
            intuition auto with *.
          }
          exploit wt_sact_interp_bool.
          4: apply WTfail. 1-3: apply WFS1. intros (?&?).
          econstructor; eauto. eapply vvs_grows_interp_sact.
          2: eauto. eauto using vvs_grows_trans, rir_vvs_grows. reflexivity.
    - assert (
        exists t1,
        wt_daction (R:=R) (Sigma:=Sigma) pos_t string string tsig arg1 t1
        /\ wt_unop ufn1 t1 tret
      ).
      { inv WT; eexists; split; simpl; eauto; try (econstructor; eauto). }
      destruct H0 as (t1 & WTa & EQ).
      dhyp H. subst.
      repeat (refine (conj _ _)); eauto.
      + simpl. intros. econstructor. eauto.
        exploit wt_unop_type_unop_ret; eauto. congruence.
      + eapply wt_unop_type_unop_ret; eauto.
      + intros.
        trim (INTERPHYP Gamma sched_log action_log). eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        destruct INTERPHYP as (INTERPHYPOK & INTERPHYPKO).
        split; intros;
        unfold opt_bind in INTERP;
        repeat destr_in INTERP; inv INTERP.
        dihyp INTERPHYPOK.
        repeat (refine (conj _ _)); eauto.
        simpl. econstructor. eauto. eauto.
        exploit wt_unop_interp. eauto.
        eapply wt_daction_preserves_wt_env in Heqo0. apply Heqo0. all: eauto.
        intros (? & ?); congruence.
    - assert (
        exists t1 t2,
        wt_daction (R:=R) (Sigma:=Sigma) pos_t string string tsig arg1 t1
        /\ wt_daction (R:=R) (Sigma:=Sigma) pos_t string string tsig arg2 t2
        /\ wt_binop ufn2 t1 t2 tret
      ).
      {
        inv WT; do 2 eexists; repeat split; simpl; eauto;
          try (econstructor; eauto).
      }
      destruct H1 as (tt1 & tt2 & WTa & WTb & EQ).
      dhyp H. subst.
      dhyp H0.
      + eapply wt_sact_vvs_grows; eauto. eapply rir_vvs_grows; eauto.
      + repeat (refine (conj _ _)); eauto.
        * eapply same_regenv_trans; eauto.
        * eapply rir_grows_weaken_guard. eapply rir_grows_trans.
        2,4:eauto. all: eauto.
          intros; econstructor; eauto.
          eapply wt_sact_vvs_grows; eauto.
          eauto using vvs_grows_trans, rir_vvs_grows.
        * simpl. subst.
          econstructor. eapply wt_sact_vvs_grows; eauto using rir_vvs_grows.
          eauto.
          exploit wt_binop_type_binop_ret; eauto. congruence.
        * econstructor.
          eapply wt_sact_vvs_grows. 2: eauto. eauto using rir_vvs_grows.
          eauto. constructor.
        * lia.
        * eapply same_env_trans; eauto.
        * subst. eapply wt_binop_type_binop_ret; eauto.
        * intros.
          trim (INTERPHYP Gamma sched_log action_log). eauto.
          trim INTERPHYP. eauto.
          trim INTERPHYP. eauto.
          trim INTERPHYP. eauto.
          trim INTERPHYP. eauto.
          trim INTERPHYP. eauto.
          trim INTERPHYP. eauto.
          destruct INTERPHYP as (INTERPHYPOK & INTERPHYPKO).
          destruct (
            interp_daction r sigma Gamma sched_log action_log arg1
          ) eqn:?; simpl.
          destruct p; destruct p.
          dihyp INTERPHYPOK.
          trim (INTERPHYP0 l0 sched_log l1). eauto.
          trim INTERPHYP0. eauto.
          trim INTERPHYP0. eauto.
          trim INTERPHYP0. eauto.
          trim INTERPHYP0. eauto.
          trim INTERPHYP0. eauto.
          trim INTERPHYP0.
          eapply vvs_grows_interp_sact; eauto using rir_vvs_grows.
          destruct INTERPHYP0 as (INTERPHYP0OK & INTERPHYP0KO).
          split; intros;
            unfold opt_bind in INTERP;
            repeat destr_in INTERP; inv INTERP.
          dihyp INTERPHYP0OK.
          repeat (refine (conj _ _)); eauto.
          -- simpl. econstructor. eapply vvs_grows_interp_sact. 2: eauto.
             eauto using vvs_grows_trans, rir_vvs_grows.
             eauto. auto.
          -- simpl. econstructor. eapply vvs_grows_interp_sact. 2: eauto.
             eauto using vvs_grows_trans, rir_vvs_grows.
             eauto. auto.
          -- exploit wt_binop_interp. eauto.
             eapply wt_daction_preserves_wt_env in Heqo1.
             apply Heqo1. all: eauto.
             eapply wt_daction_preserves_wt_env in Heqo0.
             apply Heqo0. all: eauto.
             intros (? & ?); congruence.
          -- dihyp INTERPHYPOK.
             econstructor. eapply vvs_grows_interp_sact. 2: eauto.
             eauto using rir_vvs_grows.
             eauto. reflexivity.
          -- split; intros. easy.
             exploit wt_sact_interp_bool. 4: apply FAILWT0.
             1-3: apply WFS1. intros (?&?).
             econstructor. eapply vvs_grows_interp_sact. 2: eauto.
             eauto using rir_vvs_grows.
             eauto. reflexivity.
    - inv WT. dhyp H. subst.
      assert (
        rir_grows t1 rir'
          (PTree.set p1 (retSig (Sigma ufn),
           SExternalCall ufn (reduce (arg1Sig (Sigma ufn)) o)) t1)
          rir' guard).
      {
        eapply rir_grows_change_vvs. eauto.
        intros.
        red in H0.
        rewrite ! PTree.gso by lia. auto.
        eapply wt_sact_vvs_grows; eauto.
        eapply vvs_grows_trans. eauto using rir_vvs_grows. eapply vvs_grows_set.
        inv WFS0; eauto. lia.
      }
      edestruct wf_state_vvs_set with (k:= p1) (m := Pos.succ p1). apply WFS0.
      apply wt_sact_extcall. apply WTRES. lia.
      intros. inv H1. eapply wt_sact_below in H6; eauto. lia.
      repeat (refine (conj _ _)); eauto.
      * eapply rir_grows_weaken_guard. eapply rir_grows_trans. 2,4: eauto.
        all: eauto.
        intros; econstructor; eauto.
        eapply wt_sact_vvs_grows. 2: eauto.
        eauto using vvs_grows_trans, rir_vvs_grows.
      * eapply wf_rir_grows. eauto. auto. all: apply WFS0.
      * simpl. econstructor. rewrite PTree.gss. eauto.
      * eapply wt_sact_vvs_grows. 2: eauto. auto.
      * intros.
        lia.
      * intros. specialize (INTERPHYP Gamma sched_log action_log).
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        destruct INTERPHYP as (INTERPHYPOK & INTERPHYPKO).
        split; simpl; intros; unfold opt_bind in INTERP;
        repeat destr_in INTERP; inv INTERP.
        dihyp INTERPHYPOK.
        repeat (refine (conj _ _)); eauto.
        -- simpl. econstructor. rewrite PTree.gss. eauto.
           econstructor.
           eapply vvs_grows_interp_sact. 2: eauto. auto.
        -- simpl. eapply vvs_grows_interp_sact. 2: eauto. auto.
        -- eapply match_Gamma_env_vvs_grows; eauto.
        -- eapply match_logs_r2v_vvs_grows; eauto.
           all: apply WFS0.
        -- eapply vvs_grows_interp_sact. 2: apply INTERPHYPKO.
           eauto. auto.
    - inv WT.
      eapply gria_list_grows2 in Heqp.
      2: {
        eapply Forall_impl.
        2: apply H0. simpl; intros.
        dhyp H1. subst. repeat refine (conj _ _); eauto.
        eapply wt_sact_vvs_grows; eauto using rir_vvs_grows.
      }
      destruct Heqp as (
        SAMEENV1 & SAMEREGENV1 & RIRGROWS1 & WFS1 & WTGUARD1 & NAMES & LENNAMES
        & WTS1 & NID1 & FG & INTERP1); eauto.
      all: eauto.
      2: repeat constructor.
      clear H0.
      simpl in LENNAMES.
      assert (
        env_vvs (combine (fst (split (rev (int_argspec ufn)))) (map fst l)) t0
          (rev (int_argspec ufn))).
      {
        rewrite app_nil_r in NAMES.
        revert NAMES.
        rewrite fst_split_map.
        rewrite <- ! map_rev.
        generalize l.
        generalize (rev (int_argspec ufn)).
        induction l0; simpl; intros; eauto. constructor.
        inv NAMES. simpl.
        repeat destr_in H3. destruct H3 as (? & ? & GET). subst. simpl.
        constructor; eauto.
        destr. simpl. split; eauto.
        eapply IHl0. eauto.
      }
      dhyp H.
      inv WFS1; split; eauto.
      eapply wf_rir_grows. eauto. apply RIRGROWS1.
      subst.
      repeat refine(conj _ _); eauto.
      + inv WFS1; inv WFS0; split; eauto.
        eapply env_vvs_vvs_grows; eauto. eapply rir_vvs_grows; eauto.
      + eapply same_regenv_trans; eauto.
      + eapply rir_grows_weaken_guard.
        eapply rir_grows_trans. 2,4: now eauto. all: eauto.
        intros; econstructor; eauto.
        eapply wt_sact_vvs_grows; eauto.
        eauto using vvs_grows_trans, rir_vvs_grows.
      + econstructor. eauto.
        eapply wt_sact_vvs_grows. 2: eauto.
        eauto using vvs_grows_trans, rir_vvs_grows.
        constructor.
      + lia.
      + intros.
        trim (INTERP1 Gamma sched_log action_log). eauto.
        trim INTERP1. eauto.
        trim INTERP1. eauto.
        trim INTERP1. eauto.
        trim INTERP1. eauto.
        trim INTERP1. eauto.
        trim (INTERP1 []). constructor.
        trim INTERP1. constructor.
        trim INTERP1. eauto.
        destruct INTERP1 as (INTERP1OK & INTERP1KO).
        destruct (fold_left
         (fun (acc : option (Log REnv * list val * list (string * val)))
            (a : daction) =>
            let/opt3 action_log0, l2, Gamma0 := acc in (
              let/opt3 action_log1, v0, Gamma1 :=
                interp_daction r sigma Gamma0 sched_log action_log0 a in
              Some (action_log1, v0 :: l2, Gamma1))
            ) args
            (Some (action_log, [], Gamma))) eqn:?; simpl.
            destruct p. destruct p.
        edestruct INTERP1OK as (EQv & FAIL & MGE' & MLR' & WTL' & WTE'); eauto.
        trim (
          INTERPHYP
            (map
              (fun '(name, _, v0) => (name, v0))
              (combine (rev (int_argspec ufn)) l3))
            sched_log l2).
        eauto.
        trim INTERPHYP.
        {
          revert EQv NAMES.
          rewrite app_nil_r. rewrite <- map_rev.
          generalize (rev (int_argspec ufn)).
          generalize l l3.
          intros l4 l5 l6 F; revert F l6.

          induction 1; simpl; intros; eauto.
          destruct l6; simpl in *. constructor. inv NAMES.
          destruct l6; simpl in *. inv NAMES. inv NAMES.
          destr. destr_in H7. destruct H7 as (? & ? & ?). subst.
          constructor. eauto. simpl in H3.
          inv H1. rewrite H3 in H5; inv H5.
          eapply interp_sact_wt. 5: apply H7. apply WFS1.
          apply WFS1. apply WFS1.
          eapply wfs_wt_vvs. 2: eauto. eauto.
        }
        trim INTERPHYP. eauto.
        trim INTERPHYP. eauto.
        trim INTERPHYP.
        {
          revert EQv NAMES.
          rewrite app_nil_r. rewrite <- map_rev.
          rewrite fst_split_map.
          generalize (rev (int_argspec ufn)).
          generalize l l3.
          intros l4 l5 l6 F; revert F l6.
          induction 1; simpl; intros; eauto.
          destruct l6; simpl in *. constructor. inv NAMES.
          destruct l6; simpl in *. inv NAMES. inv NAMES.
          destr. destr_in H7. destruct H7 as (? & ? & ?). subst.
          constructor. eauto. apply IHF. eauto.
        }
        trim INTERPHYP. eauto.
        trim INTERPHYP.
        eapply vvs_grows_interp_sact. 2: eauto.
        eauto using vvs_grows_trans, rir_vvs_grows.
        destruct INTERPHYP as (INTERPHYPOK & INTERPHYPKO).
        split; intros; unfold opt_bind in INTERP;
          repeat destr_in INTERP; inv INTERP.
        dihyp INTERPHYPOK.
        repeat refine (conj _ _); eauto.
        -- econstructor. eauto. eapply vvs_grows_interp_sact. 2: eauto.
           eauto using vvs_grows_trans, rir_vvs_grows. reflexivity.
        -- eapply match_Gamma_env_vvs_grows. eauto.
           eauto using vvs_grows_trans, rir_vvs_grows.
        -- econstructor. eauto. eapply vvs_grows_interp_sact. 2: eauto.
           eauto using vvs_grows_trans, rir_vvs_grows. reflexivity.
        -- split; intros. congruence.
           exploit wt_sact_interp_bool. 4: apply FAILWT.
           1-3: apply WFS0. intros (?&?).
           econstructor. eauto. eapply vvs_grows_interp_sact. 2: eauto.
           eauto using rir_vvs_grows.
           destruct x; reflexivity.
    - inv WT.
      dhyp H.
  Qed.

  Definition init_rir := {|
    rir_read0s := []; rir_read1s := []; rir_write0s := []; rir_write1s := [];
    rir_vars := PTree.empty (type*sact); rir_failure_cond := const_false
  |}.

  Definition get_rule_information (ua: uact) (nid: positive) r2v vvs sched_rir
  : rule_information_raw * r2vtype * positive :=
    let '(vret, env, r2v, vvs, failure, rir, nid', t) :=
      get_rule_information_aux ua [] [] r2v vvs const_true sched_rir init_rir
        nid
    in (rir <| rir_failure_cond := failure |> <| rir_vars := vvs|>, r2v, nid').

  Lemma get_rule_information_ok:
    forall
      (ua: uact) (nid: positive) rir' nid' sched_rir sched_log r2v vvs r2v'
      (GRI: get_rule_information ua nid r2v vvs sched_rir = (rir', r2v', nid'))
      tret
      (WT:
        BitsToLists.wt_daction pos_t string string (R:=R) (Sigma:=Sigma) [] ua
        tret)
      (WTL: wt_log R REnv sched_log) (WTR: wt_renv R REnv r)
      (WFRS: wf_rir sched_rir vvs) (WFS: wf_state [] [] r2v vvs init_rir nid)
      (MLR: match_logs_r2v r2v vvs sched_rir init_rir sched_log log_empty),
    wf_state [] [] r2v' (rir_vars rir') rir' nid'
    /\ Forall2
         (fun x y : reg_t * (Port + unit) * positive => fst x = fst y) r2v r2v'
    /\ rir_grows vvs init_rir (rir_vars rir') rir' const_true /\ nid <= nid'
    /\ (
      forall
        action_log' vret Gamma'
        (INTERP:
          interp_daction r sigma [] sched_log log_empty ua
          = Some (action_log', vret, Gamma')),
      interp_sact (rir_vars rir') (rir_failure_cond rir') (Bits [false])
      /\ wt_env _ [] Gamma'
      /\ match_logs_r2v
           r2v' (rir_vars rir') sched_rir rir' sched_log action_log')
    /\ (
      forall (INTERP: interp_daction r sigma [] sched_log log_empty ua = None),
      interp_sact (rir_vars rir') (rir_failure_cond rir') (Bits [true])).
  Proof.
    intros.
    unfold get_rule_information in GRI.
    repeat destr_in GRI. inv GRI.
    dhyp get_rule_information_aux_env_grows; eauto.
    repeat constructor. subst.
    repeat refine (conj _ _); eauto.
    - inv SAMEENV. simpl. inv WFS0. split; simpl; eauto.
      inv wfs_rir0; split; simpl; eauto.
    - simpl. inv RIRGROWS. split; eauto.
    - intros.
      edestruct (INTERPHYP [] sched_log log_empty) as (INTERPOK & INTERPKO).
      eauto. constructor.
      unfold wt_log, log_empty. intros idx le. rewrite getenv_create. easy.
      eauto. repeat constructor.
      eauto. repeat constructor. simpl.
      edestruct INTERPOK as (RES & FAIL & MGE & MLR' & WL & WE); eauto.
      repeat refine (conj _ _); eauto.
      simpl. inv MLR'; split; simpl; eauto.
      inv mlr_mlv_action0; split; simpl; eauto.
    - intros.
      edestruct (INTERPHYP [] sched_log log_empty) as (INTERPOK & INTERPKO).
      eauto. constructor.
      unfold wt_log, log_empty. intros idx le. rewrite getenv_create. easy.
      eauto. repeat constructor.
      eauto. repeat constructor. simpl. eauto.
  Qed.

  Lemma fold_left_induction:
    forall {A B: Type} (f : A -> B -> A) (P: A -> Prop) (l: list B) (acc0: A),
    P acc0
    -> (forall x acc, In x l -> P acc -> P (f acc x))
    -> P (fold_left f l acc0).
  Proof.
    induction l; simpl; intros; eauto.
    eapply IHl. eapply H0. eauto. eauto. intros; eauto.
  Qed.

  Definition list_assoc_modify
    {K V: Type} {eqdec: EqDec K} (l: (list (K*V))) k vdef (f: V -> V)
  :=
    let newv :=
      match list_assoc l k with
      | None => vdef
      | Some v => f v
      end in
    list_assoc_set l k newv.

  Fixpoint merge_cond_logs (cl1 cl2: cond_log) (cond2: sact) :=
    match cl2 with
    | [] => cl1
    | (idx, c)::cl2 =>
      let c := uand (unot cond2) c in
      merge_cond_logs
        (list_assoc_modify cl1 idx c (fun c1 => uor c1 c)) cl2 cond2
    end.

  Definition merge_rirs rir rir' conflict_name vvs := {|
    rir_read0s :=
      merge_cond_logs (rir_read0s rir) (rir_read0s rir') (SVar conflict_name);
    rir_read1s :=
      merge_cond_logs (rir_read1s rir) (rir_read1s rir') (SVar conflict_name);
    rir_write0s :=
      merge_cond_logs (rir_write0s rir) (rir_write0s rir') (SVar conflict_name);
    rir_write1s :=
      merge_cond_logs (rir_write1s rir) (rir_write1s rir') (SVar conflict_name);
    rir_vars := vvs;
    rir_failure_cond := uor (rir_failure_cond rir) (rir_failure_cond rir')
  |}.

  Lemma Exists_map:
    forall {A B: Type} (P: A -> Prop) (f: B -> A) l,
    Exists (fun x => P (f x)) l <-> Exists P (map f l).
  Proof.
    induction l; simpl; intros; eauto.
    split; inversion 1.
    rewrite ! Exists_cons. tauto.
  Qed.

  Lemma Forall_map:
    forall {A B: Type} (P: A -> Prop) (f: B -> A) l,
    Forall (fun x => P (f x)) l <-> Forall P (map f l).
  Proof.
    induction l; simpl; intros; eauto.
    split; constructor.
    split; inversion 1; econstructor; eauto.
    subst. tauto. tauto.
  Qed.

  Lemma Forall_list_assoc_modify:
    forall {K V: Type} {eqdec: EqDec K} (P: K * V -> Prop) l (P0: Forall P l) k
      def f (Pk: P (k, def)) (Pi: forall v, P (k,v) -> P (k, f v)),
    Forall P (list_assoc_modify l k def f).
  Proof.
    induction 1; simpl; intros; eauto.
    - unfold list_assoc_modify. simpl. constructor; auto.
    - unfold list_assoc_modify. simpl. destr. destr.
      subst; constructor; eauto.
      constructor; eauto.
  Qed.

  Lemma wt_merge_cond_logs:
    forall
      vvs cond rl2 (F2: Forall (fun '(idx,c) => wt_sact vvs c (bits_t 1)) rl2)
      rl1 (F1: Forall (fun '(idx,c) => wt_sact vvs c (bits_t 1)) rl1) i a,
    wt_sact vvs cond (bits_t 1)
    -> In (i, a) (merge_cond_logs rl1 rl2 cond)
    -> wt_sact vvs a (bits_t 1).
  Proof.
    induction 1; simpl; intros; eauto.
    rewrite Forall_forall in F1; apply F1 in H0; eauto.
    destr_in H1.
    eapply IHF2 in H1. auto.
    eapply Forall_list_assoc_modify. eauto.
    econstructor; eauto.
    econstructor; eauto.
    constructor. constructor.
    intros; econstructor; eauto. econstructor; eauto.
    econstructor; eauto. constructor. constructor.
    constructor. eauto.
  Qed.

  Context `{Show_rule: Show rule_name_t}.

  Fixpoint get_rir_scheduler'
    (sched_rir: rule_information_raw) r2v (rules: rule_name_t -> uact) nid
    (s: scheduler pos_t rule_name_t) {struct s}
  :=
    let interp_cons rl s :=
      let '(rir', r2v', nid) :=
        get_rule_information (rules rl) nid r2v (rir_vars sched_rir) sched_rir
      in
      let conflict : sact :=
        SUnop
          (PrimUntyped.UConv (PrimUntyped.UId ("conflict_" ++ show rl)))
          (rir_failure_cond rir')
      in
      let conflict_name := nid in
      let vvs := PTree.set conflict_name (bits_t 1, conflict) (rir_vars rir') in
      let nid := nid + 1 in
      let '(r2v2, vvs, nid) := merge_reg2vars2 r2v r2v' conflict_name vvs nid in
      let rir2 := merge_rirs sched_rir rir' conflict_name vvs in
      let conf := (SConst (Bits [true])) in
      (* let conf := (unot (SVar conflict_name)) in *)
      let lr := (rl,
                  map (fun '(reg, sa) => (reg, uand sa conf)) (rir_read0s rir'),
                  map (fun '(reg, sa) => (reg, uand sa conf)) (rir_read1s rir'),
                  map (fun '(reg, sa) => (reg, uand sa conf)) (rir_write0s rir'),
                  map (fun '(reg, sa) => (reg, uand sa conf)) (rir_write1s rir')
                ) in
      let '(rir, r2v, nid, l) := get_rir_scheduler' rir2 r2v2 rules nid s in
      (rir, r2v, nid, lr :: l)
    in
    match s with
    | Done => (sched_rir, r2v, nid, [])
    | Cons r s => interp_cons r s
    | Try r s1 s2 =>   (sched_rir,r2v,nid, [])       (* Ignored for now *)
    | SPos _ s => get_rir_scheduler' sched_rir r2v rules nid s
    end.

  Inductive good_scheduler: scheduler pos_t rule_name_t -> Prop :=
  | good_scheduler_done: good_scheduler Done
  | good_scheduler_cons r s: good_scheduler s -> good_scheduler (Cons r s)
  | good_scheduler_pos p s: good_scheduler s -> good_scheduler (SPos p s).

  Lemma wf_state_vvs_grows:
    forall tsig env r2v vvs1 vvs2 rir n n2 r2v2 rir2,
    wf_state tsig env r2v vvs1 rir n
    -> vvs_grows vvs1 vvs2
    -> wf_state tsig env r2v2 vvs2 rir2 n2
    -> wf_state tsig env r2v vvs2 rir2 n2.
  Proof.
    intros. inv H; inv H1.
    split; eauto.
    eapply reg2var_vvs_grows; eauto.
  Qed.

  Lemma nodup_merge_cond_logs:
    forall cond c2 c1, NoDup (map fst c1)
    -> NoDup (map fst (merge_cond_logs c1 c2 cond)).
  Proof.
    induction c2; simpl; intros; eauto. destr.
    eapply IHc2. unfold list_assoc_modify.
    apply nodup_list_assoc_set. auto.
  Qed.

  Lemma wf_state_merge_rirs:
    forall (nid: positive) (rir: rule_information_raw) (r2v: r2vtype)
      (n: positive) (r1: rule_information_raw) (l: r2vtype) (n0: positive)
      (l0: r2vtype) (l1: PTree.t (type * sact)) i
      (SAMEREGENV:
        Forall2 (fun x y : reg_t * (Port + unit) * positive => fst x = fst y)
        r2v l),
    wf_state [] [] r2v (rir_vars rir) rir nid
    -> wf_state [] [] l (rir_vars r1) r1 n
    -> vvs_grows (rir_vars rir) (rir_vars r1)
    -> wt_sact (rir_vars r1) (rir_failure_cond r1) (bits_t 1)
    -> merge_reg2vars2
         r2v l n
         (PTree.set n
           (bits_t 1,
            SUnop (PrimUntyped.UConv (PrimUntyped.UId i)) (rir_failure_cond r1)
           )
           (rir_vars r1)) (n + 1)
       = (l0, l1, n0)
    -> wf_state [] [] l0 l1 (merge_rirs rir r1 n l1) n0.
  Proof.
    intros nid rir r2v n r1 l n0 l0 l1 i. intros.
    exploit merge_reg2var_grows2. 2: eauto. auto.
    2: replace (n+1) with (Pos.succ n) by lia; eapply wf_state_vvs_set; eauto.
    eapply wf_state_vvs_grows. eauto.
    eapply vvs_grows_trans. eauto. eapply vvs_grows_set. apply H0. lia.
    eapply wf_state_vvs_grows_incr. apply H0.
    eapply rir_grows_set. apply H0. unfold valid_name; lia.
    eapply wt_vvs_set. apply H0. apply H0.
    econstructor. eauto. constructor.
    lia.
    eapply vvs_range_list_assoc_set.
    eapply vvs_range_incr. 2: eapply H0. lia. red; lia.
    eapply vvs_smaller_variables_set. apply H0.
    { intros. inv H4. eapply wt_sact_valid_vars in H8. eauto. apply H0. eauto. }
    eapply wf_rir_grows; eauto. apply H0.
    eapply vvs_grows_set; eauto.
    apply H0. lia. lia.
    econstructor. eauto. constructor. lia.
    { intros. inv H4. eapply wt_sact_valid_vars in H8. eauto. apply H0. eauto. }
    lia.
    eapply wf_rir_grows. apply H0. eapply vvs_grows_set; eauto. apply H0.
    lia. red; lia.
    econstructor. rewrite PTree.gss. eauto.
    intros (VG2 & NID2 & WFS2 & INTERP2).
    inv WFS2; split; eauto.
    inv H. inv wfs_rir1; inv wfs_rir0; split; simpl.
    red; intros; eapply wt_merge_cond_logs. 4: eauto.
    rewrite Forall_forall; intros (?&?) IN; now eauto.
    rewrite Forall_forall; intros (?&?) IN.
    eapply wt_sact_vvs_grows. 2: now eauto. eapply vvs_grows_trans; eauto.
    eapply vvs_grows_trans; eauto. eapply vvs_grows_set; eauto. apply H0. lia.
    econstructor.
    eapply VG2. rewrite PTree.gss. eauto.
    red; intros; eapply wt_merge_cond_logs. 4: eauto.
    rewrite Forall_forall; intros (?&?) IN; now eauto.
    rewrite Forall_forall; intros (?&?) IN.
    eapply wt_sact_vvs_grows. 2: now eauto. eapply vvs_grows_trans; eauto.
    eapply vvs_grows_trans; eauto. eapply vvs_grows_set; eauto. apply H0. lia.
    econstructor.
    eapply VG2. rewrite PTree.gss. eauto.
    red; intros; eapply wt_merge_cond_logs. 4: eauto.
    rewrite Forall_forall; intros (?&?) IN. eapply wf_rir_write0s1; eauto.
    rewrite Forall_forall; intros (?&?) IN.
    eapply wt_sact_vvs_grows. 2: eapply wf_rir_write0s0; eauto.
    eapply vvs_grows_trans; eauto.
    eapply vvs_grows_trans; eauto. eapply vvs_grows_set; eauto. apply H0. lia.
    econstructor.
    eapply VG2. rewrite PTree.gss. eauto.
    red; intros; eapply wt_merge_cond_logs. 4: eauto.
    rewrite Forall_forall; intros (?&?) IN. eapply wf_rir_write1s1; eauto.
    rewrite Forall_forall; intros (?&?) IN.
    eapply wt_sact_vvs_grows. 2: eapply wf_rir_write1s0; eauto.
    eapply vvs_grows_trans; eauto.
    eapply vvs_grows_trans; eauto. eapply vvs_grows_set; eauto. apply H0. lia.
    econstructor.
    eapply VG2. rewrite PTree.gss. eauto.
    econstructor.
    eapply wt_sact_vvs_grows. 2: eauto. eapply vvs_grows_trans. eauto.
    eapply vvs_grows_trans. 2: eauto. eapply vvs_grows_set; eauto.
    eapply H0. lia.
    eapply wt_sact_vvs_grows. 2: eauto.
    eapply vvs_grows_trans. 2: eauto. eapply vvs_grows_set; eauto.
    eapply H0. lia.
    constructor.
    eapply nodup_merge_cond_logs; eauto.
    eapply nodup_merge_cond_logs; eauto.
    eapply nodup_merge_cond_logs; eauto.
    eapply nodup_merge_cond_logs; eauto.
  Qed.

  Lemma log_app_empty:
    forall (l: Log REnv), log_app (REnv:=REnv) log_empty l = l.
  Proof.
    unfold log_app, log_empty; intros.
    rewrite <- (create_getenv_id _ (map2 _ _ _ _)).
    rewrite <- (create_getenv_id _ l) at 2.
    apply create_funext.
    intros.
    rewrite getenv_map2.
    rewrite getenv_create. reflexivity.
  Qed.

  Definition list_assoc_def
    {K V: Type} {eqdec: EqDec K} (l: (list (K*V))) k vdef
  :=
    match list_assoc l k with
    | None => vdef
    | Some v => v
    end.

  Lemma interp_uor_commut:
    forall vvs n a b v, wt_vvs vvs
    -> vvs_smaller_variables vvs
    -> vvs_range vvs n
    -> wt_sact vvs a (bits_t 1)
    -> wt_sact vvs b (bits_t 1)
    -> interp_sact vvs (uor a b) v <-> interp_sact vvs (uor b a) v.
  Proof.
    intros.
    split; intro A; inv A; econstructor; eauto.
    edestruct interp_sact_wt_bool. 5: apply H7. all: eauto.
    edestruct interp_sact_wt_bool. 5: apply H9. all: eauto. subst. simpl in *.
    inv H10.
    rewrite orb_comm. auto.
    edestruct interp_sact_wt_bool. 5: apply H7. all: eauto.
    edestruct interp_sact_wt_bool. 5: apply H9. all: eauto. subst. simpl in *.
    inv H10.
    rewrite orb_comm. auto.
  Qed.

  Lemma merge_cond_logs_interp:
    forall idx g vvs cond (WTvvs: wt_vvs vvs) (VSV: vvs_smaller_variables vvs) n
      (VR: vvs_range vvs n) (WTcond: wt_sact vvs cond (bits_t 1)) c2 c1
      (WT1: forall (i : reg_t) (a : sact),
        In (i, a) c1 -> wt_sact vvs a (bits_t 1))
      (WT2: forall (i : reg_t) (a : sact),
        In (i, a) c2 -> wt_sact vvs a (bits_t 1))
      (ND: NoDup (map fst c2)),
    list_assoc (merge_cond_logs c1 c2 cond) idx = Some g
    -> let v1 :=
         match list_assoc c1 idx with
         | Some g1 => g1
         | _ => const_false
         end in
       let v2 :=
         match list_assoc c2 idx with
         | Some g2 => uand (unot cond) g2
         | _ => const_false
         end in
       forall v, interp_sact vvs g v <-> interp_sact vvs (uor v1 v2) v.
  Proof.
    induction c2; simpl; intros; eauto.
    - rewrite H.
      exploit wt_sact_interp_bool. 1-3: eauto. eapply WT1. apply list_assoc_in.
      eauto.
      intros (? & ?).
      exploit wt_sact_interp_bool. 1-3: eauto. eapply WTcond.
      intros (? & ?).
      split; intros.
      exploit interp_sact_determ. apply H2. apply H0. intros ->.
      econstructor; eauto. econstructor; eauto. simpl. rewrite orb_false_r.
      auto.
      inv H2. inv H8.
      exploit interp_sact_determ. apply H6. apply H0. intros ->.
      simpl in H9. inv H9. rewrite orb_false_r; auto.
    - destr_in H.
      eapply IHc2 in H.
      2: {
        intros.
        apply in_list_assoc_set_inv in H0. destruct H0; eauto. inv H0.
        destr; econstructor; eauto. eapply WT1. apply list_assoc_in; eauto.
        econstructor; eauto. econstructor; eauto. constructor. constructor.
        constructor. econstructor; eauto. constructor. constructor.
      }
      2: now eauto.
      2: inv ND; auto.
      rewrite H. clear H. clear IHc2.
      unfold list_assoc_modify.
      rewrite list_assoc_spec.
      destruct eq_dec.
      + subst. rewrite eq_dec_refl.
        rewrite (list_assoc_unknown_key c2). 2: inv ND; auto. destr.
        eapply interp_uor_false; eauto.
        repeat econstructor; eauto. eapply WT1. apply list_assoc_in; eauto.
        eapply interp_uor_commut; eauto.
        repeat econstructor; eauto.
        repeat econstructor; eauto.
      + destruct eq_dec; try congruence. tauto.
  Qed.

  Lemma merge_cond_logs_interp_none:
    forall c2 c1 cond idx, list_assoc (merge_cond_logs c1 c2 cond) idx = None
    -> list_assoc c1 idx = None /\ list_assoc c2 idx = None.
  Proof.
    induction c2; simpl; intros; eauto.
    destr_in H.
    exploit IHc2. eauto. intros (A & B).
    clear H IHc2.
    unfold list_assoc_modify in A. rewrite list_assoc_spec in A.
    destr_in A; inv A. destr; subst. congruence. intuition auto with *.
    congruence.
  Qed.

  Lemma log_existsb_if:
    forall (l1 l2: Log REnv) (b: bool) reg fn,
    log_existsb (if b then l1 else l2) reg fn
    = if b then log_existsb l1 reg fn else log_existsb l2 reg fn.
  Proof. intros; destr. Qed.

  Lemma if_eq_distr:
    forall {A:Type} (b: bool) (x y a: A),
    (if b then x else y) = a <-> (if b then x = a else y = a).
  Proof. intros. destr; tauto. Qed.

  Lemma log_existsb_empty:
    forall idx fn, log_existsb (log_empty: Log REnv) idx fn = false.
  Proof.
    unfold log_empty, log_existsb. intros. rewrite getenv_create; reflexivity.
  Qed.

  Lemma if_prop:
    forall (b: bool) (P1 P2: Prop),
    (if b then P1 else P2) <-> ((b = true -> P1) /\ (b = false -> P2)).
  Proof. intros. destruct b; split; intuition auto with *. Qed.

  Lemma wf_init_rir vvs: wf_rir init_rir vvs.
  Proof.
    split; simpl; intros.
    red; easy.
    red; easy.
    red; easy.
    red; easy.
    repeat constructor.
    constructor.
    constructor.
    constructor.
    constructor.
  Qed.

  Lemma interp_uor_false2:
    forall vvs a b, interp_sact vvs a (Bits [false])
    -> interp_sact vvs b (Bits [false])
    -> interp_sact vvs (uor a b) (Bits [false]).
  Proof. intros; econstructor; eauto. Qed.

  Lemma interp_uand_false:
    forall vvs a b ba bb, interp_sact vvs a (Bits [ba])
    -> interp_sact vvs b (Bits [bb])
    -> ba = false \/ bb = false
    -> interp_sact vvs (uand a b) (Bits [false]).
  Proof.
    intros; econstructor; eauto.
    destruct ba, bb; simpl; auto. intuition congruence.
  Qed.

 Lemma has_merge_rir:
   forall rir1 rir2 n vvs reg v b vn (WTV: wt_vvs vvs)
     (VSV: vvs_smaller_variables vvs) (VR: vvs_range vvs vn)
     (WTn: wt_sact vvs (SVar n) (bits_t 1))
     (f: rule_information_raw -> cond_log) (ND: NoDup (map fst (f rir2)))
     (has: rule_information_raw -> reg_t -> sact)
     (HAS:
       forall rir r, has rir r
       = match list_assoc (f rir) r with
         | Some c => c
         | _ => const_false
         end)
     (fmerge:
        forall rir1 rir2 n vvs, f (merge_rirs rir1 rir2 n vvs)
        = merge_cond_logs (f rir1) (f rir2) (SVar n)),
   interp_sact vvs (SVar n) (Bits [b])
   -> wt_cond_log vvs (f rir1)
   -> wt_cond_log vvs (f rir2)
   -> interp_sact vvs (has (merge_rirs rir1 rir2 n vvs) reg) v
   <-> interp_sact
     vvs (uor (has rir1 reg) (uand (unot (SVar n)) (has rir2 reg))) v.
  Proof.
    intros. rewrite ! HAS. rewrite fmerge.
    destruct (list_assoc (merge_cond_logs _ _ _) _) eqn:?.
    - eapply merge_cond_logs_interp in Heqo. rewrite Heqo. clear Heqo.
      all: eauto.
      split.
      + intros. inv H2. econstructor. eauto.
        destr_in H8. eauto.
        inv H8. econstructor; eauto.
        econstructor; eauto. simpl; eauto. constructor. simpl.
        rewrite andb_false_r. auto. auto.
      + intro A; inv A.
        econstructor; eauto.
        inv H7. inv H6.
        exploit interp_sact_determ. apply H4. apply H. intros ->. simpl in H9.
        inv H9. destr.
        exploit interp_sact_wt_bool. 5: apply H10. 1-3: eauto.
        eapply H1. apply list_assoc_in; eauto. intros (?&?). subst.
        simpl in H11. inv H11.
        econstructor. econstructor; eauto. simpl; reflexivity. eauto. simpl.
        auto. inv H10. simpl in H11. inv H11. rewrite andb_false_r.
        constructor.
    - exploit merge_cond_logs_interp_none. eauto. intros (A & B). rewrite A, B.
      intuition auto with *.
      inv H2. repeat (econstructor; eauto). simpl. rewrite andb_false_r; auto.
      inv H2. inv H6. inv H8. inv H7. inv H5.
      exploit interp_sact_determ. apply H4. apply H. intros ->.
      simpl in H7; inv H7. simpl in H10; inv H10. simpl in H9; inv H9.
      rewrite andb_false_r; constructor.
  Qed.

  Lemma has_merge_rir2:
    forall rir1 rir2 n vvs reg b vn (WTV: wt_vvs vvs)
      (VSV: vvs_smaller_variables vvs) (VR: vvs_range vvs vn)
      (WTn: wt_sact vvs (SVar n) (bits_t 1))
      (f: rule_information_raw -> cond_log) (ND: NoDup (map fst (f rir2)))
      (has: rule_information_raw -> reg_t -> sact)
      (HAS:
        forall rir r,
        has rir r
        = match list_assoc (f rir) r with
          | Some c => c
          | _ => const_false end)
      (fmerge: forall rir1 rir2 n vvs,
        f (merge_rirs rir1 rir2 n vvs)
        = merge_cond_logs (f rir1) (f rir2) (SVar n)) ,
    interp_sact vvs (SVar n) (Bits [b])
    -> wt_cond_log vvs (f rir1)
    -> wt_cond_log vvs (f rir2)
    -> interp_sact vvs (has (merge_rirs rir1 rir2 n vvs) reg) (Bits [false])
    <-> (interp_sact vvs (has rir1 reg) (Bits [false])
        /\ (b = true \/ interp_sact vvs (has rir2 reg) (Bits [false]))).
  Proof.
    intros.
    erewrite has_merge_rir; eauto.
    assert (WThas1: forall r, wt_sact vvs (has rir1 r) (bits_t 1)).
    {
      intros; rewrite HAS. destr; eauto. apply list_assoc_in in Heqo; eauto.
      repeat constructor.
    }
    assert (WThas2: forall r, wt_sact vvs (has rir2 r) (bits_t 1)).
    {
      intros; rewrite HAS. destr; eauto. apply list_assoc_in in Heqo; eauto.
      repeat constructor.
    }
    split; intros.
    - inv H2.
      edestruct interp_sact_wt_bool. 5: apply H6. all: eauto. subst.
      inv H8.
      edestruct interp_sact_wt_bool. 5: apply H10. all: eauto. subst.
      inv H5.
      exploit interp_sact_determ. apply H4. apply H. intros ->.
      simpl in H8; inv H8.
      simpl in H11; inv H11. simpl in H9; inv H9.
      rewrite orb_false_iff in H3.
      rewrite andb_false_iff in H3.
      rewrite negb_false_iff in H3.
      destruct H3; subst. simpl.
      destruct H3; subst; split; auto.
      rewrite andb_false_r; auto.
      rewrite andb_false_r; auto.
    - destruct H2.
      exploit wt_sact_interp_bool. 1-3: eauto. apply (WThas2 reg). intros (?&?).
      econstructor; eauto.
      econstructor. econstructor. eauto. simpl; eauto. eauto. simpl. eauto.
      simpl. destruct b; auto.
      destruct H3. congruence. exploit interp_sact_determ. apply H3. apply H4.
      intros A; inv A.
      reflexivity.
  Qed.

  Lemma iff_cond:
    forall (cond A B: Prop), (cond -> A <-> B)
    -> (cond -> A) <-> (cond -> B).
  Proof. tauto. Qed.

  Lemma match_logs_merge:
    forall r2v l r1 n l0 l1 n0 sched_rir nid l2 i
      (Heqp1:
         merge_reg2vars2 r2v l n
         (PTree.set
           n
           (bits_t 1,
            SUnop (PrimUntyped.UConv (PrimUntyped.UId i)) (rir_failure_cond r1)
           )
           (rir_vars r1)
         )
         (n + 1) = (l0, l1, n0))
      (SAMEREGENV:
         Forall2
           (fun x y : reg_t * (Port + unit) * positive => fst x = fst y)
           r2v l)
      (sched_log: Log REnv)
      (WFS: wf_state [] [] r2v (rir_vars sched_rir) sched_rir nid)
      (MLR:
         match_logs_r2v r2v (rir_vars sched_rir) sched_rir init_rir sched_log
         log_empty)
      (WFS1: wf_state [] [] l (rir_vars r1) r1 n)
      (RG1: rir_grows (rir_vars sched_rir) init_rir (rir_vars r1) r1 const_true)
      b (IF1: interp_sact (rir_vars r1) (rir_failure_cond r1) (Bits [b]))
      (MLR1:
        b = false
        -> match_logs_r2v l (rir_vars r1) sched_rir r1 sched_log l2),
    match_logs_r2v l0 l1 (merge_rirs sched_rir r1 n l1) init_rir
      (log_app (if b then log_empty else l2) sched_log) log_empty.
  Proof.
    intros.
    edestruct merge_reg2vars2_nd as (
      NDr' & INCL & VG & LE & WTV & VSV & RNG2 & R2V & EVAL
    ).
    9 : eauto. all: eauto. apply WFS.
    apply vvs_range_list_assoc_set. 2: red; lia.
    eapply vvs_range_incr. 2: apply WFS1. lia.
    eapply wt_vvs_set. apply WFS1. apply WFS1.
    econstructor. apply WFS1. constructor. lia.
    eapply vvs_smaller_variables_set. apply WFS1.
    eapply wt_sact_below. eauto. econstructor. apply WFS1. constructor.
    {
      intros x y IN.
      edestruct wfs_r2v_vvs as (? & GET1 & ? & GET2). apply WFS.
      apply nodup_in_assoc in IN; auto.
      rewrite IN in GET1; inv GET1.
      rewrite PTree.gso.
      erewrite rir_vvs_grows. eauto. eauto. eauto.
      eapply rir_vvs_grows in GET2; eauto.
      eapply wfs_vvs_range in GET2. 2: eauto. red in GET2. lia.
      apply WFS.
    }
    {
      intros x y IN.
      edestruct wfs_r2v_vvs as (? & GET1 & ? & GET2). apply WFS1.
      apply nodup_in_assoc in IN; auto.
      rewrite IN in GET1; inv GET1.
      rewrite PTree.gso. eauto.
      eapply wfs_vvs_range in GET2. 2: eauto. red in GET2. lia.
      apply WFS1.
    }
    econstructor. rewrite PTree.gss. eauto.
    assert (RV2:
      forall x y, list_assoc l0 x = Some y
      -> exists y1 y2,
      list_assoc r2v x = Some y1
      /\ list_assoc l x = Some y2
      /\ (
        forall v,
        interp_sact l1 (SVar (if b then y1 else y2)) v
        <-> interp_sact l1 (SVar y) v)
    ).
    {
      intros.
      edestruct (EVAL _ _ H) as (y1 & y2 & GET1 & GET2 & INTERP).
      eexists; eexists; split; eauto. split; eauto. intros. apply INTERP.
      eapply vvs_grows_interp_sact. eauto.
      econstructor. rewrite PTree.gss; eauto.
      eapply vvs_grows_interp_sact. 2: eauto.
      eapply vvs_grows_set. apply WFS1. lia.
      econstructor. eauto. reflexivity.
    }
    clear EVAL.
    rename RV2 into RV.
    eapply match_logs_r2v_vvs_grows with (vvs':=l1) in MLR.
    3-5: apply WFS.
    2: {
      eapply vvs_grows_trans. 2: eauto.
      eapply vvs_grows_trans. eauto using rir_vvs_grows.
      eapply vvs_grows_set. apply WFS1. lia.
    }
    2: apply wf_init_rir.
    2: apply WFS.
    assert (MLR2: b = false -> match_logs_r2v l l1 sched_rir r1 sched_log l2).
    {
      intros; eapply match_logs_r2v_vvs_grows. eauto.
      2-4: apply WFS1.
      eapply vvs_grows_trans. 2: eauto.
      eapply vvs_grows_set. apply WFS1. lia.
      apply WFS1.
      eapply wf_rir_grows. apply WFS.
      eauto using rir_vvs_grows.
    }
    clear MLR1. rename MLR2 into MLR1.
    assert (WFr1: wf_rir r1 l1).
    {
      eapply wf_rir_grows. apply WFS1.
      eapply vvs_grows_trans. 2: eauto.
      eapply vvs_grows_set. apply WFS1. lia.
    }
    assert (WFrir: wf_rir sched_rir l1).
    {
      eapply wf_rir_grows. apply WFS.
      eapply vvs_grows_trans. eauto using rir_vvs_grows.
      eapply vvs_grows_trans. 2: eauto.
      eapply vvs_grows_set. apply WFS1. lia.
    }
    assert (INTn: interp_sact l1 (SVar n) (Bits [b])).
    {
      eapply vvs_grows_interp_sact. apply VG.
      econstructor. rewrite PTree.gss. eauto.
      eapply vvs_grows_interp_sact. 2: eauto.
      eapply vvs_grows_set. apply WFS1. lia.
      econstructor. eauto. reflexivity.
    }
    assert (WTn: wt_sact l1 (SVar n) (bits_t 1)).
    {
      eapply wt_sact_vvs_grows. apply VG.
      econstructor. rewrite PTree.gss; eauto.
    }
    clear Heqp1 WFS WFS1 RG1 VG LE IF1.
    split.
    - intros reg prt n1 GET.
      edestruct RV as (y1 & y2 & GET1 & GET2 & INTERP). eauto.
      rewrite <- INTERP.
      destruct b.
      exploit mlr_read. apply MLR. eauto.
      rewrite ! log_app_empty. auto.
      exploit mlr_read. apply MLR1. auto. eauto.
      unfold do_read.
      rewrite ! log_app_empty. auto.
    - split.
      + intros. rewrite log_existsb_log_app. rewrite orb_false_iff.
        rewrite log_existsb_if. rewrite log_existsb_empty.
        rewrite if_eq_distr. rewrite if_prop.
        erewrite (iff_cond (b = false)).
        2: intros; eapply mlv_read0; apply MLR1; auto.
        erewrite mlv_read0 with (log:=sched_log). 2: apply MLR.
        erewrite has_merge_rir2 with (f:=rir_read0s) ; eauto.
        destruct b; intuition try congruence.
        apply WFr1. apply WFrir. apply WFr1.
      + intros. rewrite log_existsb_log_app. rewrite orb_false_iff.
        rewrite log_existsb_if.
        rewrite log_existsb_empty.
        rewrite if_eq_distr. rewrite if_prop.
        erewrite (iff_cond (b = false)).
        2: intros; eapply mlv_read1; apply MLR1.
        erewrite mlv_read1 with (log:=sched_log). 2: apply MLR.
        erewrite has_merge_rir2 with (f:=rir_read1s) ; eauto.
        destruct b; intuition try congruence.
        apply WFr1. apply WFrir. apply WFr1. auto.
      + intros. rewrite log_existsb_log_app. rewrite orb_false_iff.
        rewrite log_existsb_if. rewrite log_existsb_empty.
        rewrite if_eq_distr. rewrite if_prop.
        erewrite (iff_cond (b = false)).
        2: intros; eapply mlv_write0; apply MLR1.
        erewrite mlv_write0 with (log:=sched_log). 2: apply MLR.
        erewrite has_merge_rir2 with (f:=rir_write0s) ; eauto.
        destruct b; intuition try congruence.
        apply WFr1. apply WFrir. apply WFr1. auto.
      + intros. rewrite log_existsb_log_app. rewrite orb_false_iff.
        rewrite log_existsb_if. rewrite log_existsb_empty.
        rewrite if_eq_distr. rewrite if_prop.
        erewrite (iff_cond (b = false)).
        2: intros; eapply mlv_write1; apply MLR1.
        erewrite mlv_write1 with (log:=sched_log). 2: apply MLR.
        erewrite has_merge_rir2 with (f:=rir_write1s) ; eauto.
        destruct b; intuition try congruence.
        apply WFr1. apply WFrir. apply WFr1. auto.
   - split; intros;
       unfold log_existsb, log_empty, rir_has_read0, rir_has_read1,
         rir_has_write0, rir_has_write1;
       simpl; rewrite getenv_create; simpl; (split; [repeat constructor|auto]).
  Qed.

  Lemma match_logs_merge_false:
    forall r2v l r1 n l0 l1 n0 sched_rir nid l2 i
      (Heqp1:
        merge_reg2vars2
          r2v l n
          (PTree.set
            n
            (bits_t 1,
             SUnop (PrimUntyped.UConv (PrimUntyped.UId i))(rir_failure_cond r1))
            (rir_vars r1)
          )
          (n + 1) = (l0, l1, n0))
      (F2:
        Forall2 (fun x y : reg_t * (Port + unit) * positive => fst x = fst y)
        r2v l)
      (sched_log : Log REnv)
      (WFS: wf_state [] [] r2v (rir_vars sched_rir) sched_rir nid)
      (MLR:
        match_logs_r2v r2v (rir_vars sched_rir) sched_rir init_rir sched_log
        log_empty)
      (WFS1: wf_state [] [] l (rir_vars r1) r1 n)
      (RG1: rir_grows (rir_vars sched_rir) init_rir (rir_vars r1) r1 const_true)
      (IF1: interp_sact (rir_vars r1) (rir_failure_cond r1) (Bits [false]))
      (MLR1: match_logs_r2v l (rir_vars r1) sched_rir r1 sched_log l2),
      match_logs_r2v l0 l1 (merge_rirs sched_rir r1 n l1) init_rir
        (log_app l2 sched_log) log_empty.
  Proof. intros. exploit match_logs_merge; eauto. Qed.

  Lemma merge_reg2var_nid:
    forall r2v1 r2v2 n vvs m r2v3 vvs2 m2,
    merge_reg2vars2 r2v1 r2v2 n vvs m = (r2v3, vvs2, m2)
    -> Forall2 (fun x y : reg_t * (Port + unit) * positive => fst x = fst y)
         r2v1 r2v2
    -> m <= m2.
  Proof.
    unfold merge_reg2vars2.
    intros r2v1.
    generalize (@nil (reg_t * (Port+unit) * positive)).
    induction r2v1; simpl; intros; eauto.
    inv H. lia.
    inv H0.
    repeat (destr_in H; [idtac]).
    apply IHr2v1 in Heqp3; auto.
    repeat destr_in H; inv H; lia.
  Qed.

  Lemma match_logs_merge_true:
    forall r2v l r1 n l0 l1 n0 sched_rir nid i
      (Heqp1:
        merge_reg2vars2
          r2v l n
          (PTree.set n
            (bits_t 1,
             SUnop
              (PrimUntyped.UConv (PrimUntyped.UId i))
              (rir_failure_cond r1)
             )
             (rir_vars r1))
          (n + 1)
        = (l0, l1, n0))
      (F2:
        Forall2
          (fun x y : reg_t * (Port + unit) * positive => fst x = fst y) r2v l)
      (sched_log: Log REnv)
      (WFS: wf_state [] [] r2v (rir_vars sched_rir) sched_rir nid)
      (MLR:
        match_logs_r2v
          r2v (rir_vars sched_rir) sched_rir init_rir sched_log log_empty)
      (WFS1: wf_state [] [] l (rir_vars r1) r1 n)
      (RG1: rir_grows (rir_vars sched_rir) init_rir (rir_vars r1) r1 const_true)
      (IF1: interp_sact (rir_vars r1) (rir_failure_cond r1) (Bits [true])),
      match_logs_r2v l0 l1 (merge_rirs sched_rir r1 n l1) init_rir sched_log
        log_empty.
  Proof.
    intros.
    exploit match_logs_merge; eauto. congruence. simpl.
    rewrite log_app_empty. eauto.
    Unshelve. eauto.
  Qed.

  Lemma get_rir_scheduler_ok:
    forall (rules: rule_name_t -> uact) s (GS: good_scheduler s) (nid: positive)
      sched_rir r2v rir' r2v' nid' l
      (GRI: get_rir_scheduler' sched_rir r2v rules nid s = (rir', r2v', nid', l))
      (WT:
        forall r, exists tret,
        BitsToLists.wt_daction
          pos_t string string (R:=R) (Sigma:=Sigma) [] (rules r) tret)
      sched_log
      (WTL: wt_log R REnv sched_log) (WTR: wt_renv R REnv r)
      (WFS: wf_state [] [] r2v (rir_vars sched_rir) sched_rir nid)
      (MLR:
        match_logs_r2v
          r2v (rir_vars sched_rir) sched_rir init_rir sched_log log_empty),
    wf_state [] [] r2v' (rir_vars rir') rir' nid' /\ nid <= nid'
    /\ forall sched_log'
         (INTERP: interp_dscheduler' rules r sigma sched_log s = sched_log'),
       match_logs_r2v r2v' (rir_vars rir') rir' init_rir sched_log' log_empty.
  Proof.
    induction 1; simpl; intros; eauto.
    - inv GRI. repeat refine (conj _ _); eauto.
      lia. intros; subst; eauto.
    - edestruct (WT r0) as (tret & WTr). repeat destr_in GRI.
      exploit get_rule_information_ok; eauto.
      + inv WFS. auto.
      + inv WFS.
        split; eauto.
        split; simpl; try easy. repeat constructor.
        constructor. constructor. constructor. constructor.
      + intros (WFS1 & F2 & RG1 & NID & INTERPOK & INTERPKO).
        destr.
        * unfold interp_drule in Heqo. repeat destr_in Heqo; inv Heqo.
          edestruct INTERPOK as (IF1 & _ & MLR1). eauto.
          clear INTERPOK INTERPKO.
          edestruct IHGS as (WFS2 & NID2 & INTERP2). eauto. eauto.
          instantiate (1:=log_app l2 sched_log). eapply wt_log_app.
          {
            generalize (
                wt_daction_preserves_wt_env
                  pos_t string string R Sigma REnv r sigma wt_sigma (rules r0) []
                  l3 tret [] sched_log log_empty l2 v
              ). intro WDPWE.
            eapply WDPWE; auto. constructor.
            red. intros idx le. unfold log_empty. rewrite getenv_create. easy.
          }
          eauto. eauto. simpl.
          eapply wf_state_merge_rirs.
          6: now eauto. now eauto. now eauto. now eauto. now apply RG1. now apply WFS1.
          simpl.
          now eapply match_logs_merge_false; eauto.
          inv GRI. repeat refine (conj _ _).
          eauto.
          eapply merge_reg2var_nid in Heqp0. lia. auto.
          intros. eauto.
        * unfold interp_drule in Heqo. repeat destr_in Heqo; inv Heqo.
          edestruct IHGS as (WFS2 & NID2 & INTERP2). eauto. eauto.
          eauto. eauto.
          eapply wf_state_merge_rirs.
          6: eauto. eauto. eauto. eauto. apply RG1. apply WFS1.
          eapply match_logs_merge_true; eauto.
          inv GRI. repeat refine (conj _ _). now eauto.
          eapply merge_reg2var_nid in Heqp0. lia.
          auto. intros. eauto.
  Qed.

  Definition init_reg r2v vvs (nid: positive) (idx: reg_t)
    : r2vtype * PTree.t (type * sact) * positive :=
    let r2v := list_assoc_set r2v (idx,inl P0) nid in
    let r2v := list_assoc_set r2v (idx,inl P1) nid in
    let r2v := list_assoc_set r2v (idx,inr tt) nid in
    let vvs := PTree.set nid (R idx, SReg idx) vvs in
    (r2v, vvs, Pos.succ nid).

  Definition init_regs r2v vvs (nid: positive) (l: list reg_t)
  : r2vtype * PTree.t (type * sact) * positive :=
    fold_left
      (fun '(r2v,vvs,nid) idx => init_reg r2v vvs nid idx)
      l (r2v,vvs,nid).

  Definition init_r2v nid :=
    init_regs [] (PTree.empty (type*sact)) nid (finite_elements).

  Lemma init_reg_wt_vvs:
    forall r2v vvs nid idx r2v' vvs' nid',
    init_reg r2v vvs nid idx = (r2v', vvs', nid')
    -> wt_renv R REnv r
    -> wt_vvs vvs
    -> (forall x y, list_assoc r2v x = Some y
      -> vvs !y = Some (R (fst x), SReg (fst x)))
    -> vvs_range vvs nid
    -> vvs_smaller_variables vvs
    -> wt_vvs vvs'
    /\ (forall x y, list_assoc r2v' x = Some y
      -> vvs' ! y = Some (R (fst x), SReg (fst x)))
    /\ vvs_range vvs' nid'
    /\ vvs_smaller_variables vvs'
    /\ nid <= nid'
    /\ forall i p, In (i,p) (map fst r2v) \/ i = idx
      -> In (i,p) (map fst r2v').
  Proof.
    intros r2v vvs nid idx r2v' vvs' nid' IR WTR WT R2V VR VSV.
    unfold init_reg in IR. inv IR.
    repeat refine (conj _ _).
    - eapply wt_vvs_set; eauto.
      constructor. lia.
    - intros.
      rewrite ! list_assoc_spec in H.
      rewrite ! PTree.gsspec.
      repeat destr_in H.
      + inv H. destr; try congruence. eauto.
      + inv H. destr; try congruence. eauto.
      + inv H. destr; try congruence. eauto.
      + destr; eauto. subst.
        exploit R2V; eauto. intro H0.
        eapply VR in H0. red in H0; lia.
    - eapply vvs_range_set. auto.
    - eapply vvs_smaller_variables_set; eauto.
      inversion 1.
    - lia.
    - intros.
      destruct H.
      apply list_assoc_set_key_stays_in.
      apply list_assoc_set_key_stays_in.
      apply list_assoc_set_key_stays_in.
      eauto.
      subst.
      destruct p. destruct p.
      apply list_assoc_set_key_stays_in.
      apply list_assoc_set_key_stays_in.
      apply list_assoc_set_key_in.
      apply list_assoc_set_key_stays_in.
      apply list_assoc_set_key_in.
      destruct u. apply list_assoc_set_key_in.
  Qed.

  Lemma init_regs_wt_vvs:
    forall l r2v vvs nid r2v' vvs' nid',
    init_regs r2v vvs nid l = (r2v', vvs', nid')
    -> wt_renv R REnv r
    -> wt_vvs vvs
    -> (forall x y, list_assoc r2v x = Some y
      -> vvs !y = Some (R (fst x), SReg ((fst x))))
    -> vvs_range vvs nid
    -> vvs_smaller_variables vvs
    -> NoDup (map fst r2v)
    -> wt_vvs vvs'
    /\ (forall x y, list_assoc r2v' x = Some y
      -> vvs' ! y = Some (R (fst x), SReg ((fst x))))
    /\ vvs_range vvs' nid'
    /\ vvs_smaller_variables vvs'
    /\ NoDup (map fst r2v')
    /\ nid <= nid'
    /\ forall i p, In (i,p) (map fst r2v) \/ In i l
      -> In (i,p) (map fst r2v').
  Proof.
    unfold init_regs.
    induction l; simpl; intros; eauto.
    - inv H. repeat refine (conj _ _); eauto. lia. intuition auto with *.
    - destruct (init_reg r2v vvs nid a) eqn:?.
      destruct p.
      edestruct init_reg_wt_vvs as (WTvvs' & R2V' & VR' & VSV' & LE & INCL);
        eauto.
      eapply IHl in H; eauto.
      intuition auto with *.
      lia.
      unfold init_reg in Heqp. inv Heqp.
      repeat apply nodup_list_assoc_set. auto.
  Qed.

  Definition get_rir_scheduler rules s :=
    let '(r2v, vvs, n) := init_r2v xH in
    get_rir_scheduler' (init_rir <| rir_vars := vvs|>) r2v rules n s.

  Lemma wfs_init_r2v:
    forall n0 r2v vvs n,
      init_r2v n0 = (r2v,vvs,n)
      -> wt_renv R REnv r
      -> wf_state [] [] r2v vvs init_rir n
      /\ n0 <= n
      /\ match_logs_r2v r2v vvs init_rir init_rir log_empty log_empty.
  Proof.
    intros n0 r2v vvs n IR WTR. simpl.
    unfold init_r2v in IR.
    edestruct init_regs_wt_vvs
      as (WTvvs' & R2V' & VR' & VSV' & NDr & LE & INCL); eauto.
    red. setoid_rewrite PTree.gempty. easy.
    simpl; easy.
    red. setoid_rewrite PTree.gempty. easy.
    red. setoid_rewrite PTree.gempty. easy.
    constructor.
    split. split; eauto. constructor.
    red; intros.
    simpl in INCL.
    generalize (finite_surjective (fst x)). intro NTH.
    apply nth_error_In in NTH. destruct x. simpl in *.
    edestruct @in_keys_list_assoc_ex. eapply INCL. right; eauto. rewrite H.
    eexists; split. eauto. exploit R2V'; eauto.
    split; simpl; try easy.
    repeat constructor.
    constructor. constructor. constructor. constructor.
    split. lia.
    split; simpl; try congruence.
    intros.
    econstructor. eapply R2V'. eauto.
    unfold do_read, latest_write0, latest_write. rewrite log_app_empty.
    unfold log_find, log_empty.
    rewrite getenv_create. simpl. repeat destr; econstructor.
    split; simpl; unfold log_existsb, log_empty; simpl; intros idx;
      rewrite getenv_create; simpl; split; auto; intros.
    unfold rir_has_read0. simpl. constructor.
    unfold rir_has_read1. simpl. constructor.
    unfold rir_has_write0. simpl. constructor.
    unfold rir_has_write1. simpl. constructor.
    split; simpl; unfold log_existsb, log_empty; simpl;
      intros idx; rewrite getenv_create; simpl; split; auto; intros.
    unfold rir_has_read0. simpl. constructor.
    unfold rir_has_read1. simpl. constructor.
    unfold rir_has_write0. simpl. constructor.
    unfold rir_has_write1. simpl. constructor.
  Qed.

  Lemma get_rir_scheduler2_ok:
    forall (rules: rule_name_t -> uact) s (GS: good_scheduler s) rir' r2v' nid' l
      (GRI: get_rir_scheduler rules s = (rir', r2v', nid', l))
      (WT:
        forall r, exists tret,
        BitsToLists.wt_daction
          pos_t string string (R:=R) (Sigma:=Sigma) [] (rules r) tret)
      (WTR: wt_renv R REnv r),
    wf_state [] [] r2v' (rir_vars rir') rir' nid'
    /\ match_logs_r2v
         r2v' (rir_vars rir') rir' init_rir
         (interp_dscheduler rules r sigma s) log_empty.
  Proof.
    intros.
    unfold get_rir_scheduler in GRI.
    repeat destr_in GRI.
    exploit wfs_init_r2v. eauto. eauto.
    intros (WFS & _ & MLR).
    edestruct get_rir_scheduler_ok
      with (sched_log:=log_empty (REnv:=REnv) (reg_t:=reg_t) (V:=val))
      as (WFS2 & _ & INTERP2). 2: eauto. all: eauto.
    red; unfold log_empty; intros idx le; rewrite getenv_create; easy.
    simpl.
    {
      clear - WFS.
      inv WFS; split; eauto.
      inv wfs_rir0; split; eauto. simpl. repeat constructor.
    } simpl.
    inv MLR; split; auto.
    inv mlr_mlv_sched0; split; auto.
  Qed.

  Lemma mlr_latest_write:
  forall r2v rir nid sched_log,
    wf_state [] [] r2v (rir_vars rir) rir nid
    -> match_logs_r2v r2v (rir_vars rir) rir init_rir sched_log log_empty
    -> forall idx,
       let v := match latest_write sched_log idx with
       | Some v => v
       | None => getenv REnv r idx
       end in
    forall n, list_assoc r2v (idx, inr tt) = Some n
    -> interp_sact (rir_vars rir) (SVar n) v.
  Proof.
    intros. inv H0.
    exploit mlr_read0. eauto. unfold v. rewrite log_app_empty. tauto.
  Qed.

  Definition schedule_to_IRR rules s :=
    let '(rir, r2v, nid, l) := get_rir_scheduler rules s in {|
      final_values :=
        filter_map
          (fun '(r,p,n) =>
             match p with
             | inr tt => Some (r,n)
             | inl _ => None
             end)
          r2v;
      read1_values :=
        filter_map
          (fun '(r,p,n) =>
             match p with
             | inl P1 => Some (r,n)
             | _ => None
             end)
          r2v;
      debug_log := l;
      vars := rir_vars rir;
    |}.

  Lemma list_assoc_filter_map:
    forall {K1 K2 V: Type} {eqdec: EqDec K1} {eqdec: EqDec K2}
      (f: (K1*V) -> option (K2*V)) (l: list (K1*V)) idx idx' v,
    list_assoc l idx = Some v
    -> f (idx, v) = Some (idx', v)
    -> (forall k1 k2 v1 v2, f (k1,v1) = Some (k2, v2) -> v1 = v2)
    -> (forall k1 k2 k3 v1 v2 v3 v4,
        f (k1,v1) = Some (k3, v3) -> f (k2,v2) = Some (k3, v4) -> k1 = k2)
    -> list_assoc (filter_map f l) idx' = Some v.
  Proof.
    induction l; simpl; intros; eauto.
    repeat destr_in H.
    - inv H. rewrite H0. simpl. rewrite eq_dec_refl. auto.
    - destr.
      + destruct p. exploit H1. apply Heqo. intros ->. simpl.
        destr. subst.
        exploit H2. apply Heqo. apply H0. intro; subst. congruence.
        eauto.
      + eauto.
  Qed.

  Lemma schedule_to_IRR_ok:
    forall (rules: rule_name_t -> uact) s (GS: good_scheduler s) sf
      (GRI: schedule_to_IRR rules s = sf)
      (WT:
        forall r, exists tret,
        BitsToLists.wt_daction
          pos_t string string (R:=R) (Sigma:=Sigma) [] (rules r) tret)
      (WTR: wt_renv R REnv r),
    wt_vvs (vars sf)
    /\ vvs_smaller_variables (vars sf)
    /\ (forall idx, In idx (map fst (final_values sf)))
    /\ (forall idx, exists n,
           list_assoc (final_values sf) idx = Some n
           /\ wt_sact (vars sf) (SVar n) (R idx))
    /\ forall idx,
       let v :=
         match latest_write (interp_dscheduler rules r sigma s) idx with
         | Some v => v
         | None => getenv REnv r idx
         end in
       exists n,
       list_assoc (final_values sf) idx = Some n
    /\ interp_sact (vars sf) (SVar n) v.
  Proof.
    intros.
    unfold schedule_to_IRR in GRI. repeat destr_in GRI. subst. simpl.
    edestruct get_rir_scheduler2_ok as (WFS & MLR); eauto.
    repeat refine (conj _ _).
    - apply WFS.
    - apply WFS.
    - inv WFS. red in wfs_r2v_vvs0. intro idx.
      destruct (wfs_r2v_vvs0 (idx, inr tt)) as (y & GET1 & z & GET2).
      rewrite in_map_iff. setoid_rewrite filter_map_In.
      apply list_assoc_in in GET1. eexists; split.
      2: eexists; split. 3: apply GET1. 2: simpl; reflexivity. reflexivity.
    - intro idx. inv WFS. red in wfs_r2v_vvs0.
      destruct (wfs_r2v_vvs0 (idx, inr tt)) as (y & GET1 & z & GET2).
      erewrite list_assoc_filter_map. 2: eauto.
      eexists; split. eauto.
      econstructor. rewrite GET2. simpl. eauto. simpl. auto.
      intros. repeat destr_in H; inv H. auto.
      intros. repeat destr_in H; inv H. repeat destr_in H0; inv H0. auto.
    - intro idx. inv WFS. red in wfs_r2v_vvs0.
      destruct (wfs_r2v_vvs0 (idx, inr tt)) as (y & GET1 & z & GET2).
      inv MLR. exploit mlr_read0. apply GET1. simpl. rewrite log_app_empty.
      intro INT.
      erewrite list_assoc_filter_map. 2: eauto.
      eexists; split. eauto. eauto. simpl. auto.
      intros. repeat destr_in H; inv H. auto.
      intros. repeat destr_in H; inv H. repeat destr_in H0; inv H0. auto.
  Qed.
End IRR.
Close Scope positive.
