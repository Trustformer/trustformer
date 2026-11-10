Require Import Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.IRR.Interpretation.
Require Import Koika.IRR.Direction.
Require Import Koika.IRR.Operations.
Require Import Koika.IRR.Simplifications.Simplify.
Require Import Koika.BitsToLists.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.KoikaForm.Types.
Require Import Koika.IRR.IRR.
Require Import Koika.Utils.EqDec.
Require Import Koika.Utils.Maps.
Require Import Koika.Utils.Environments.
Require Import Coq.Logic.FunctionalExtensionality.
Require Operations.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section SimplifyTargeted.
  Context {reg_t ext_fn_t rule_name_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {ext_fn_t_eq_dec: EqDec ext_fn_t}.
  Context {REnv: Env reg_t}.
  Context (R: reg_t -> type).
  Context (Sigma: ext_fn_t -> ExternalSignature).
  Local Definition ext_funs_defs := forall f: ext_fn_t, val -> val.
  Local Definition UREnv := REnv.(env_t) (fun _ => val).
  Context (r: UREnv).
  Context (sigma: ext_funs_defs).
  Local Definition sact := sact (ext_fn_t := ext_fn_t) (reg_t := reg_t).
  Local Definition eval_sact := eval_sact r sigma.
  Local Definition wf_sf := wf_sf (rule_name_t := rule_name_t) R Sigma.
  Hypothesis WTRENV: Wt.wt_renv R REnv r.
  Context {
    wt_sigma:
    forall ufn vc, wt_val (arg1Sig (Sigma ufn)) vc
    -> wt_val (retSig (Sigma ufn)) (sigma ufn vc)
  }.

  Definition exempted (pos: position) (exemptions: list position) :=
    List.existsb (position_beq pos) exemptions.

  Fixpoint simplify_sact_targeted_aux
    (ua: sact) (e: list position) (pos: position)
  : sact :=
    match ua with
    | SIf cond tb fb =>
      let cond' :=
        simplify_sact_targeted_aux cond e (branch1::pos) in
      if (exempted pos e) then
        SIf
          cond'
          (simplify_sact_targeted_aux tb e (branch2::pos))
          (simplify_sact_targeted_aux fb e (branch3::pos))
      else
        match cond' with
        | SConst (Bits [true]) => simplify_sact_targeted_aux tb e (branch2::pos)
        | SConst (Bits [false]) =>
          simplify_sact_targeted_aux fb e (branch3::pos)
        | _ =>
          SIf
            cond' (simplify_sact_targeted_aux tb e (branch2::pos))
            (simplify_sact_targeted_aux fb e (branch3::pos))
        end
    | SBinop ufn a1 a2 =>
      if (exempted pos e) then
        SBinop
          ufn (simplify_sact_targeted_aux a1 e (branch1::pos))
          (simplify_sact_targeted_aux a2 e (branch2::pos))
      else
        let a1' := simplify_sact_targeted_aux a1 e (branch1::pos) in
        let a2' := simplify_sact_targeted_aux a2 e (branch2::pos) in
        match ufn with
        | PrimUntyped.UBits2 PrimUntyped.UAnd =>
          match a1', a2' with
          | SConst (Bits [false]), _ => const_false
          | SConst (Bits [true]), _ => a2'
          | _, SConst (Bits [false]) => const_false
          | _, SConst (Bits [true]) => a1'
          | _, _ => SBinop ufn a1' a2'
          end
        | PrimUntyped.UBits2 PrimUntyped.UOr =>
          match a1', a2' with
          | SConst (Bits [true]), _ => const_true
          | SConst (Bits [false]), _ => a2'
          | _, SConst (Bits [true]) => const_true
          | _, SConst (Bits [false]) => a1'
          | _, _ => SBinop ufn a1' a2'
          end
        | fn =>
          match a1', a2' with
          | SConst x, SConst y =>
            match sigma2 fn x y with
            | Some r => SConst r
            | None => SBinop ufn a1' a2'
            end
          | _, _ => SBinop ufn a1' a2'
          end
        end
    | SUnop ufn a =>
      if (exempted pos e) then
        SUnop ufn (simplify_sact_targeted_aux a e (branch1::pos))
      else
        let a := simplify_sact_targeted_aux a e (branch1::pos) in
        match a with
        | SConst x =>
          match sigma1 ufn x with
          | Some r => SConst r
          | None => SUnop ufn a
          end
        | _ => SUnop ufn a
        end
    | SExternalCall ufn a =>
      SExternalCall ufn (simplify_sact_targeted_aux a e (branch1::pos))
    | SVar _ | SReg _ | SConst _ => ua
    end.

  Definition simplify_sact_targeted (ua: sact) (exemptions: list position)
  : sact :=
    simplify_sact_targeted_aux ua exemptions [].


  (* Lemma simplify_targeted_no_exemptions_pos_irrelevant: *)
  (*   forall a p1 p2, *)
  (*   simplify_sact_targeted_aux a [] p1 = simplify_sact_targeted_aux a [] p2. *)
  (* Proof. *)
  (*   induction a; simpl; intros; eauto. *)
  (*   - rewrite IHa1 with (p2:=branch1::p2). *)
  (*     rewrite IHa2 with (p2:=branch2::p2). *)
  (*     rewrite IHa3 with (p2:=branch3::p2). auto. *)
  (*   - rewrite IHa with (p2:=branch1::p2). auto. *)
  (*   - rewrite IHa1 with (p2:=branch1::p2). *)
  (*     rewrite IHa2 with (p2:=branch2::p2). auto. *)
  (*   - rewrite IHa with (p2:=branch1::p2). auto. *)
  (* Qed. *)

  (* Lemma sact_simplify_targeted_no_exemptions_eq_simplify : *)
  (*   forall a, *)
  (*   simplify_sact_targeted a [] = simplify_sact r sigma a. *)
  (* Proof. *)
  (*   induction a; eauto. *)
  (*   - unfold simplify_sact_targeted in *. simpl. *)
  (*     erewrite simplify_targeted_no_exemptions_pos_irrelevant in IHa1. *)
  (*     erewrite simplify_targeted_no_exemptions_pos_irrelevant in IHa2. *)
  (*     erewrite simplify_targeted_no_exemptions_pos_irrelevant in IHa3. *)
  (*     rewrite IHa1, IHa2, IHa3. eauto. *)
  (*   - unfold simplify_sact_targeted in *. simpl. *)
  (*     erewrite simplify_targeted_no_exemptions_pos_irrelevant in IHa. *)
  (*     rewrite IHa. eauto. *)
  (*   - unfold simplify_sact_targeted in *. simpl. *)
  (*     erewrite simplify_targeted_no_exemptions_pos_irrelevant in IHa1. *)
  (*     erewrite simplify_targeted_no_exemptions_pos_irrelevant in IHa2. *)
  (*     rewrite IHa1, IHa2. eauto. *)
  (*   - unfold simplify_sact_targeted in *. simpl. *)
  (*     erewrite simplify_targeted_no_exemptions_pos_irrelevant in IHa. *)
  (*     rewrite IHa. eauto. *)
  (* Qed. *)

  (* Lemma simplify_targeted_no_exemptions_eq_simplify : *)
  (*   forall sf, *)
  (*   simplify_sf_targeted sf [] = simplify_sf r sigma sf. *)
  (* Proof. *)
  (*   intros. *)
  (*   destruct sf. *)
  (*   unfold simplify_sf, simplify_sf_targeted. *)
  (*   simpl. f_equal. *)
  (*   unfold simplify_vars. *)
  (*   rewrite PTree.fold_spec. simpl. *)

  (*   f_equal. *)
  (*   (* apply functional_extensionality; intro. *) *)
  (*   (* apply functional_extensionality; intro. *) *)
  (*   (* destruct x0. simpl. *) *)
  (*   (* f_equal. *) *)
  (*   (* destruct (Pos.to_nat x); *) *)
  (*   (*   apply sact_simplify_targeted_no_exemptions_eq_simplify. *) *)
  (* Admitted. *)

  (* Lemma simplify_unop_targeted_cases: *)
  (*   forall e p ufn a a', *)
  (*   simplify_sact_targeted_aux (SUnop ufn a) e p = a' *)
  (*   -> forall ta tr vss, wt_unop ufn ta tr *)
  (*   -> wt_sact (Sigma:=Sigma) R vss a ta *)
  (*   -> ( *)
  (*     exists b x, *)
  (*     eval_sact_no_vars *)
  (*       r sigma (simplify_sact_targeted_aux a e (branch1 :: p)) *)
  (*     = Some b *)
  (*     /\ sigma1 ufn b = Some x *)
  (*     /\ a' = SConst x) *)
  (*   \/ a' = SUnop ufn (simplify_sact_targeted_aux a e (branch1 :: p)). *)
  (* Proof. *)
  (*   simpl. intros. *)
  (*   destr_in H; subst. right; auto. *)
  (*   destr. 2: right; auto. *)
  (*   destr. left; do 2 eexists; repeat split; eauto. *)
  (*   right; auto. *)
  (* Qed. *)

  (* Lemma simplify_bnop_targeted_cases: *)
  (*   forall ufn a1 a2 a' e p, *)
  (*   simplify_sact_targeted_aux (SBinop ufn a1 a2) e p = a' *)
  (*   -> a' = SBinop ufn (simplify_sact_targeted_aux a1 e (branch1 :: p)) (simplify_sact_targeted_aux a2 e (branch2 :: p)) *)
  (*   \/ (ufn = PrimUntyped.UBits2 PrimUntyped.UAnd *)
  (*     /\ ((eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (branch1 :: p)) = Some (Bits [true]) *)
  (*       /\ a' = simplify_sact_targeted_aux a2 e (branch2 :: p)) *)
  (*       \/ (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (branch1 :: p)) = Some (Bits [false]) *)
  (*         /\ a' = const_false) *)
  (*       \/ (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a2 e (branch2 :: p)) = Some (Bits [true]) *)
  (*           /\ a' = simplify_sact_targeted_aux a1 e (branch1 :: p)) *)
  (*       \/ (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a2 e (branch2 :: p)) = Some (Bits [false]) *)
  (*           /\ a' = const_false))) *)
  (*   \/ (ufn = PrimUntyped.UBits2 PrimUntyped.UOr *)
  (*       /\ ((eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (branch1 :: p)) = Some (Bits [true]) *)
  (*            /\ a' = const_true) *)
  (*           \/ (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (branch1 :: p)) = Some (Bits [false]) *)
  (*               /\ a' = simplify_sact_targeted_aux a2 e (branch2 :: p)) *)
  (*           \/ (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a2 e (branch2 :: p)) = Some (Bits [true]) *)
  (*               /\ a' = const_true) *)
  (*           \/ (eval_sact_no_vars r sigma (simplify_sact_targeted_aux a2 e (branch2 :: p)) = Some (Bits [false]) *)
  (*               /\ a' = simplify_sact_targeted_aux a1 e (branch1 :: p)))) *)
  (* \/ ( *)
  (*   exists v1 v2 v, *)
  (*   eval_sact_no_vars r sigma (simplify_sact_targeted_aux a1 e (branch1 :: p)) = Some v1 *)
  (*   /\ eval_sact_no_vars r sigma (simplify_sact_targeted_aux a2 e (branch2 :: p)) = Some v2 *)
  (*   /\ sigma2 ufn v1 v2 = Some v *)
  (*   /\ a' = SConst v). *)
  (* Proof. *)
  (*   simpl. intros. *)
  (*   destr_in H; subst. auto. *)
  (*   destr. *)
  (*   destr; try destr; try destr; auto. (repeat right; do 3 eexists; repeat split; eauto; auto). *)
  (*   destr. *)
  (*   repeat destr; intuition eauto. *)
  (*   repeat destr; intuition eauto. *)
  (*   { *)
  (*   repeat destr; intuition eauto. *)
  (*   (repeat right; do 3 eexists; repeat split; eauto; auto). *)
  (*   } *)
  (*   repeat destr; intuition eauto;     (repeat right; do 3 eexists; repeat split; eauto; auto). *)
  (*   repeat destr; intuition eauto;     (repeat right; do 3 eexists; repeat split; eauto; auto). *)
  (*   repeat destr; intuition eauto;     (repeat right; do 3 eexists; repeat split; eauto; auto). *)
  (*   repeat destr; intuition eauto;     (repeat right; do 3 eexists; repeat split; eauto; auto). *)
  (*   repeat destr; intuition eauto;     (repeat right; do 3 eexists; repeat split; eauto; auto). *)
  (*   repeat destr; intuition eauto;     (repeat right; do 3 eexists; repeat split; eauto; auto). *)
  (*   repeat destr; intuition eauto;     (repeat right; do 3 eexists; repeat split; eauto; auto). *)
  (*   repeat destr; intuition eauto;     (repeat right; do 3 eexists; repeat split; eauto; auto). *)
  (*   repeat destr; intuition eauto;     (repeat right; do 3 eexists; repeat split; eauto; auto). *)
  (*   repeat destr; intuition eauto;     (repeat right; do 3 eexists; repeat split; eauto; auto). *)
  (*   repeat destr; intuition eauto;     (repeat right; do 3 eexists; repeat split; eauto; auto). *)
  (*   repeat destr; intuition eauto;     (repeat right; do 3 eexists; repeat split; eauto; auto). *)
  (*   repeat destr; intuition eauto;     (repeat right; do 3 eexists; repeat split; eauto; auto). *)
  (* Qed. *)

  Definition eval_sact_no_vars_bool (ex: bool) a :=
    if ex then None else
    match eval_sact_no_vars r sigma a with
    | Some (Bits [true]) => Some true
    | Some (Bits [false]) => Some false
    | _ => None
    end.

  Inductive ssta : sact -> list position -> position -> sact -> Prop :=
  | ssta_if_true:
    forall c tb fb e pos tc ttb,
      ssta c e (branch1 :: pos) tc ->
      eval_sact_no_vars r sigma tc = Some (Bits [true]) ->
      ssta tb e (branch2 :: pos) ttb ->
      ssta (SIf c tb fb) e pos ttb
  | ssta_if_false:
    forall c tb fb e pos tc tfb,
      ssta c e (branch1 :: pos) tc ->
      eval_sact_no_vars r sigma tc = Some (Bits [false]) ->
      ssta fb e (branch3 :: pos) tfb ->
      ssta (SIf c tb fb) e pos tfb
  | ssta_if_exempted:
    forall c tb fb e pos tc ttb tfb,
      ssta c e (branch1 :: pos) tc ->
      ssta tb e (branch2 :: pos) ttb ->
      ssta fb e (branch3 :: pos) tfb ->
      ssta (SIf c tb fb) e pos (SIf tc ttb tfb)
  | ssta_unop:
    forall ufn a e pos ta v v1,
      ssta a e (branch1 :: pos) ta ->
      eval_sact_no_vars r sigma ta = Some v ->
      sigma1 ufn v = Some v1 ->
      ssta (SUnop ufn a) e pos (SConst v1)
  | ssta_unop_exempted:
    forall ufn a e pos ta,
      ssta a e (branch1 :: pos) ta ->
      ssta (SUnop ufn a) e pos (SUnop ufn ta)
  | ssta_binop_and_true_:
    forall a e pos ta b tb,
      ssta a e (branch1::pos) ta ->
      eval_sact_no_vars r sigma ta = Some (Bits [true]) ->
      ssta b e (branch2::pos) tb ->
      ssta (SBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) a b) e pos tb
  | ssta_binop_and_false_:
    forall a e pos ta b,
      ssta a e (branch1::pos) ta ->
      eval_sact_no_vars r sigma ta = Some (Bits [false]) ->
      ssta (SBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) a b) e pos const_false
  | ssta_binop_and__true:
    forall a e pos ta b tb,
      ssta a e (branch1::pos) ta ->
      ssta b e (branch2::pos) tb ->
      eval_sact_no_vars r sigma tb = Some (Bits [true]) ->
      ssta (SBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) a b) e pos ta
  | ssta_binop_and__false:
    forall a e pos b tb,
      ssta b e (branch2::pos) tb ->
      eval_sact_no_vars r sigma tb = Some (Bits [false]) ->
      ssta (SBinop (PrimUntyped.UBits2 PrimUntyped.UAnd) a b) e pos const_false
  | ssta_binop_or_false_:
    forall a e pos ta b tb,
      ssta a e (branch1::pos) ta ->
      eval_sact_no_vars r sigma ta = Some (Bits [false]) ->
      ssta b e (branch2::pos) tb ->
      ssta (SBinop (PrimUntyped.UBits2 PrimUntyped.UOr) a b) e pos tb
  | ssta_binop_or_true_:
    forall a e pos ta b,
      ssta a e (branch1::pos) ta ->
      eval_sact_no_vars r sigma ta = Some (Bits [true]) ->
      ssta (SBinop (PrimUntyped.UBits2 PrimUntyped.UOr) a b) e pos const_true
  | ssta_binop_or__false:
    forall a e pos ta b tb,
      ssta a e (branch1::pos) ta ->
      ssta b e (branch2::pos) tb ->
      eval_sact_no_vars r sigma tb = Some (Bits [false]) ->
      ssta (SBinop (PrimUntyped.UBits2 PrimUntyped.UOr) a b) e pos ta
  | ssta_binop_or__true:
    forall a e pos b tb,
      ssta b e (branch2::pos) tb ->
      eval_sact_no_vars r sigma tb = Some (Bits [true]) ->
      ssta (SBinop (PrimUntyped.UBits2 PrimUntyped.UOr) a b) e pos const_true
  | ssta_binop_sigma:
    forall ufn a e pos ta b tb va vb v,
      ssta a e (branch1::pos) ta ->
      ssta b e (branch2::pos) tb ->
      eval_sact_no_vars r sigma ta = Some va ->
      eval_sact_no_vars r sigma tb = Some vb ->
      sigma2 ufn va vb = Some v ->
      ssta (SBinop ufn a b) e pos
           (SConst v)
  | ssta_binop_exempted:
    forall ufn a e pos ta b tb,
      ssta a e (branch1::pos) ta ->
      ssta b e (branch2::pos) tb ->
      ssta (SBinop ufn a b) e pos
           (SBinop ufn ta tb)
  | ssta_external_all_exempted:
    forall ufn a e pos ta,
      ssta a e (branch1::pos) ta ->
      ssta (SExternalCall ufn a) e pos
        (SExternalCall ufn ta)
  | ssta_id: forall s e pos, ssta s e pos s
  .

  Lemma ssta_f:
    forall a e p,
      ssta a e p (simplify_sact_targeted_aux a e p).
  Proof.
    induction a; simpl; intros; eauto.
    - constructor.
    - constructor.
    - destr.
      constructor; eauto.
  Admitted.
  (*     destr. 2: constructor; eauto. *)
  (*     destr; try now (constructor; eauto). *)
  (*     destr; try now (constructor; eauto). *)
  (*     repeat destr; try now (constructor; eauto). *)
  (*     eapply ssta_if_true; eauto. *)
  (*     eapply ssta_if_false; eauto. *)
  (*   - destr. *)
  (*     eapply ssta_unop_exempted; eauto. *)
  (*     repeat destr; try now (constructor; eauto). *)
  (*     econstructor; eauto. *)
  (*   - destr. econstructor; eauto. *)
  (*     destr. *)
  (*     repeat destr; try now (constructor; eauto). *)
  (*     eapply ssta_binop_sigma; eauto. *)
  (*     destr; try now (constructor; eauto). *)
  (*     + repeat destr; try now (econstructor; eauto). *)
  (*     + repeat destr; try now (econstructor; eauto). *)
  (*     + repeat destr; try now (econstructor; eauto). *)
  (*     + repeat destr; try now (econstructor; eauto). *)
  (*     + repeat destr; try now (econstructor; eauto). *)
  (*     + repeat destr; try now (econstructor; eauto). *)
  (*     + repeat destr; try now (econstructor; eauto). *)
  (*     + repeat destr; try now (econstructor; eauto). *)
  (*     + repeat destr; try now (econstructor; eauto). *)
  (*     + repeat destr; try now (econstructor; eauto). *)
  (*     + repeat destr; try now (econstructor; eauto). *)
  (*     + repeat destr; try now (econstructor; eauto). *)
  (*     + repeat destr; try now (econstructor; eauto). *)
  (*     + repeat destr; try now (econstructor; eauto). *)
  (*     + repeat destr; try now (econstructor; eauto). *)
  (*     + repeat destr; try now (econstructor; eauto). *)
  (*   - econstructor; eauto. *)
  (*   - econstructor; eauto. *)
  (* Qed. *)

  Lemma wt_simplify_sact_targeted:
    forall vss a t,
      wt_sact R (Sigma:=Sigma) vss a t ->
      forall ta e p,
        ssta a e p ta ->
        wt_sact R (Sigma:=Sigma) vss ta t.
  Proof.
    induction 1; simpl; intros; eauto.
    - inv H0. econstructor; eauto.
    - inv H0. econstructor; eauto.
    - inv H2. eauto. eauto. econstructor; eauto. econstructor; eauto.
    - inv H1.
      + constructor. eapply Wt.wt_unop_sigma1; eauto.
        eapply eval_sact_no_vars_wt. 4: eauto. all: eauto.
      + econstructor; eauto.
      + econstructor; eauto.
    - inv H2; try (inv H1; [idtac]); eauto.
      + eapply eval_sact_no_vars_wt in H10; eauto. inv H10.
        simpl. repeat constructor.
      + eapply eval_sact_no_vars_wt in H10; eauto. inv H10.
        simpl. repeat constructor.
      + eapply eval_sact_no_vars_wt in H10; eauto. inv H10.
        simpl. repeat constructor.
      + eapply eval_sact_no_vars_wt in H10; eauto. inv H10.
        simpl. repeat constructor.
      + constructor. eapply Wt.wt_binop_sigma1; eauto.
        eapply eval_sact_no_vars_wt. 4: eauto. all: eauto.
        eapply eval_sact_no_vars_wt. 4: eauto. all: eauto.
      + econstructor; eauto.
      + econstructor; eauto.
    - inv H0; econstructor; eauto.
    - inv H; econstructor; eauto.
  Qed.

  Lemma simplify_sact_targeted_correct:
    forall vvs (WTV: wt_vvs R (Sigma:=Sigma) vvs) a e p ta
           (SSTA: ssta a e p ta)
           n res t
           (WTa: wt_sact (Sigma:=Sigma) R vvs a t)
           (EVAL: eval_sact vvs a n = Some res),
      eval_sact vvs ta n = Some res.
  Proof.
    induction 2; simpl; intros; eauto.
    - inv WTa.
      destruct n; simpl in EVAL;
        unfold opt_bind in EVAL;
        repeat destr_in EVAL; try congruence.
      eapply IHSSTA2; eauto.
      eapply Operations.eval_sact_more_fuel; eauto.
      eapply eval_sact_eval_sact_no_vars in H; eauto. congruence.
    - inv WTa.
      destruct n; simpl in EVAL;
        unfold opt_bind in EVAL;
        repeat destr_in EVAL; try congruence.
      eapply eval_sact_eval_sact_no_vars in H; eauto. congruence.
      eapply IHSSTA2; eauto.
      eapply Operations.eval_sact_more_fuel; eauto.
    - inv WTa.
      destruct n; simpl in EVAL;
        unfold opt_bind in EVAL;
        repeat (destr_in EVAL; try congruence; [idtac]).
      congruence.
      simpl.
      erewrite IHSSTA1; eauto. simpl. destr; eauto.
    - inv WTa.
      destruct n; simpl in EVAL;
        unfold opt_bind in EVAL;
        repeat (destr_in EVAL; try congruence; [idtac]).
      congruence.
      simpl.
      eapply eval_sact_eval_sact_no_vars in H; eauto. congruence.
    - inv WTa.
      destruct n; simpl in EVAL;
        unfold opt_bind in EVAL;
        repeat (destr_in EVAL; try congruence; [idtac]).
      congruence.
      simpl.
      erewrite IHSSTA; eauto.
    - inv WTa.
      destruct n; simpl in EVAL;
        unfold opt_bind in EVAL;
        repeat (destr_in EVAL; try congruence; [idtac]).
      congruence. inv EVAL.
      eapply IHSSTA1 in Heqo; eauto.
      eapply eval_sact_eval_sact_no_vars in Heqo; eauto. inv Heqo.
      erewrite IHSSTA2; eauto.
      eapply eval_sact_no_vars_wt in H; eauto. 2: eapply wt_simplify_sact_targeted. 3: eauto.
      2: eauto. inv H. inv H6.
      eapply eval_sact_wt in Heqo0 as WTv2; eauto. inv WTv2.
      destruct v2; simpl in H1; try congruence.
      destruct v2; simpl in H1; try congruence.
      simpl bitwise.
      eapply Operations.eval_sact_more_fuel. eauto. auto.
    - inv WTa.
      destruct n; simpl in EVAL;
        unfold opt_bind in EVAL;
        repeat (destr_in EVAL; try congruence; [idtac]).
      congruence. inv EVAL.
      eapply IHSSTA in Heqo; eauto.
      eapply eval_sact_eval_sact_no_vars in Heqo; eauto. inv Heqo.
      eapply eval_sact_no_vars_wt in H; eauto. 2: eapply wt_simplify_sact_targeted. 3: eauto.
      2: eauto. inv H. inv H6.
      eapply eval_sact_wt in Heqo0 as WTv2; eauto. inv WTv2.
      destruct v2; simpl in H1; try congruence.
      destruct v2; simpl in H1; try congruence.
      simpl bitwise.
      reflexivity.
    - inv WTa.
      destruct n; simpl in EVAL;
        unfold opt_bind in EVAL;
        repeat (destr_in EVAL; try congruence; [idtac]).
      congruence. inv EVAL.
      eapply IHSSTA2 in Heqo0; eauto.
      eapply eval_sact_eval_sact_no_vars in Heqo0; eauto. inv Heqo0.
      erewrite IHSSTA1; eauto.
      eapply eval_sact_no_vars_wt in H; eauto. 2: eapply wt_simplify_sact_targeted. 3: eauto.
      2: eauto. inv H. inv H6.
      eapply eval_sact_wt in Heqo as WTv1; eauto. inv WTv1.
      destruct v1; simpl in H1; try congruence.
      destruct v1; simpl in H1; try congruence.
      simpl bitwise. rewrite andb_true_r.
      eapply Operations.eval_sact_more_fuel. eauto. auto.
    - inv WTa.
      destruct n; simpl in EVAL;
        unfold opt_bind in EVAL;
        repeat (destr_in EVAL; try congruence; [idtac]).
      congruence. inv EVAL.
      eapply IHSSTA in Heqo0; eauto.
      eapply eval_sact_eval_sact_no_vars in Heqo0; eauto. inv Heqo0.
      eapply eval_sact_no_vars_wt in H; eauto. 2: eapply wt_simplify_sact_targeted. 3: eauto.
      2: eauto. inv H. inv H6.
      eapply eval_sact_wt in Heqo as WTv1; eauto. inv WTv1.
      destruct v1; simpl in H1; try congruence.
      destruct v1; simpl in H1; try congruence.
      simpl bitwise. rewrite andb_false_r.
      reflexivity.
    - inv WTa.
      destruct n; simpl in EVAL;
        unfold opt_bind in EVAL;
        repeat (destr_in EVAL; try congruence; [idtac]).
      congruence. inv EVAL.
      eapply IHSSTA1 in Heqo; eauto.
      eapply eval_sact_eval_sact_no_vars in Heqo; eauto. inv Heqo.
      erewrite IHSSTA2; eauto.
      eapply eval_sact_no_vars_wt in H; eauto. 2: eapply wt_simplify_sact_targeted. 3: eauto.
      2: eauto. inv H. inv H6.
      eapply eval_sact_wt in Heqo0 as WTv2; eauto. inv WTv2.
      destruct v2; simpl in H1; try congruence.
      destruct v2; simpl in H1; try congruence.
      simpl bitwise.
      eapply Operations.eval_sact_more_fuel. eauto. auto.
    - inv WTa.
      destruct n; simpl in EVAL;
        unfold opt_bind in EVAL;
        repeat (destr_in EVAL; try congruence; [idtac]).
      congruence. inv EVAL.
      eapply IHSSTA in Heqo; eauto.
      eapply eval_sact_eval_sact_no_vars in Heqo; eauto. inv Heqo.
      eapply eval_sact_no_vars_wt in H; eauto. 2: eapply wt_simplify_sact_targeted. 3: eauto.
      2: eauto. inv H. inv H6.
      eapply eval_sact_wt in Heqo0 as WTv2; eauto. inv WTv2.
      destruct v2; simpl in H1; try congruence.
      destruct v2; simpl in H1; try congruence.
      simpl bitwise.
      reflexivity.
    - inv WTa.
      destruct n; simpl in EVAL;
        unfold opt_bind in EVAL;
        repeat (destr_in EVAL; try congruence; [idtac]).
      congruence. inv EVAL.
      eapply IHSSTA2 in Heqo0; eauto.
      eapply eval_sact_eval_sact_no_vars in Heqo0; eauto. inv Heqo0.
      erewrite IHSSTA1; eauto.
      eapply eval_sact_no_vars_wt in H; eauto. 2: eapply wt_simplify_sact_targeted. 3: eauto.
      2: eauto. inv H. inv H6.
      eapply eval_sact_wt in Heqo as WTv1; eauto. inv WTv1.
      destruct v1; simpl in H1; try congruence.
      destruct v1; simpl in H1; try congruence.
      simpl bitwise. rewrite orb_false_r.
      eapply Operations.eval_sact_more_fuel. eauto. auto.
    - inv WTa.
      destruct n; simpl in EVAL;
        unfold opt_bind in EVAL;
        repeat (destr_in EVAL; try congruence; [idtac]).
      congruence. inv EVAL.
      eapply IHSSTA in Heqo0; eauto.
      eapply eval_sact_eval_sact_no_vars in Heqo0; eauto. inv Heqo0.
      eapply eval_sact_no_vars_wt in H; eauto. 2: eapply wt_simplify_sact_targeted. 3: eauto.
      2: eauto. inv H. inv H6.
      eapply eval_sact_wt in Heqo as WTv1; eauto. inv WTv1.
      destruct v1; simpl in H1; try congruence.
      destruct v1; simpl in H1; try congruence.
      simpl bitwise. rewrite orb_true_r.
      reflexivity.
    - inv WTa.
      destruct n; simpl in EVAL;
        unfold opt_bind in EVAL;
        repeat (destr_in EVAL; try congruence; [idtac]).
      congruence. inv EVAL.
      eapply IHSSTA1 in Heqo; eauto.
      eapply IHSSTA2 in Heqo0; eauto.
      eapply eval_sact_eval_sact_no_vars in Heqo; eauto.
      eapply eval_sact_eval_sact_no_vars in Heqo0; eauto. subst. simpl. congruence.
    - inv WTa.
      destruct n; simpl in EVAL;
        unfold opt_bind in EVAL;
        repeat (destr_in EVAL; try congruence; [idtac]).
      congruence.
      eapply IHSSTA1 in Heqo; eauto.
      eapply IHSSTA2 in Heqo0; eauto.
      simpl. rewrite Heqo, Heqo0. simpl. auto.
    - inv WTa.
      destruct n; simpl in EVAL;
        unfold opt_bind in EVAL;
        repeat (destr_in EVAL; try congruence; [idtac]).
      congruence. inv EVAL.
      simpl.
      erewrite IHSSTA; eauto.
      simpl; auto.
  Qed.

  (* Lemma simpl_sact_targeted_aux_some_p1_p2: *)
  (*   forall e a p1 ta1 (SSTA1: ssta a e p1 ta1) *)
  (*          p2 ta2 (SSTA2: ssta a e p2 ta2) v1 v2, *)
  (*   eval_sact_no_vars r sigma ta1 = Some v1 *)
  (*   -> eval_sact_no_vars r sigma ta2 = Some v2 *)
  (*   -> v1 = v2. *)
  (* Proof. *)
  (*   induction 1; simpl; intros; eauto. *)
  (* Qed. *)

  Lemma simplify_sact_wt_sact_targeted_ok':
    forall vvs a t (WTS: wt_sact (Sigma := Sigma) R vvs a t) e,
    wt_sact (Sigma := Sigma) R vvs (simplify_sact_targeted a e) t.
  Proof. intros. eapply wt_simplify_sact_targeted. eauto. eapply ssta_f. Qed.

  Lemma simplify_sact_targeted_reachable_vars_ok:
    forall vvs v s e p ts (SSTA: ssta s e p ts)
           (RV: reachable_var vvs ts v),
    reachable_var vvs s v.
  Proof.
    induction 1; intros; simpl in *; eauto.
    - eapply reachable_var_if_true; eauto.
    - eapply reachable_var_if_false; eauto.
    - inv RV.
      eapply reachable_var_if_cond; eauto.
      eapply reachable_var_if_true; eauto.
      eapply reachable_var_if_false; eauto.
    - inv RV.
    - inv RV; econstructor; eauto.
    - eapply reachable_var_binop2; eauto.
    - inv RV.
    - eapply reachable_var_binop1; eauto.
    - inv RV.
    - eapply reachable_var_binop2; eauto.
    - inv RV.
    - eapply reachable_var_binop1; eauto.
    - inv RV.
    - inv RV.
    - inv RV.
      eapply reachable_var_binop1; eauto.
      eapply reachable_var_binop2; eauto.
    - inv RV; econstructor; eauto.
  Qed.

  Lemma simplify_sact_targeted_interp_sact_ok':
    forall a v vvs (WTVVS: wt_vvs (Sigma := Sigma) R vvs) t e
      (WTS: wt_sact (Sigma := Sigma) R vvs a t)
      (VVSSV: vvs_smaller_variables vvs),
    interp_sact (sigma := sigma) REnv r vvs a v
    -> interp_sact (sigma := sigma) REnv r vvs (simplify_sact_targeted a e) v.
  Proof.
    intros.
    eapply interp_sact_do_eval_sact in H; eauto.
    unfold do_eval_sact in H.
    eapply eval_sact_interp_sact.
    unfold simplify_sact_targeted.
    erewrite simplify_sact_targeted_correct; eauto.
    eapply ssta_f.
  Qed.

  Lemma simplify_sact_targeted_var_in_sact_ok':
    forall s e p ts (SSTA: ssta s e p ts) v
           (VIS: var_in_sact ts v),
    var_in_sact s v.
  Proof.
    induction 1; intros; simpl in *; eauto.
    - eapply var_in_if_true; eauto.
    - eapply var_in_if_false; eauto.
    - inv VIS.
      eapply var_in_if_cond; eauto.
      eapply var_in_if_true; eauto.
      eapply var_in_if_false; eauto.
    - inv VIS.
    - inv VIS; econstructor; eauto.
    - eapply var_in_sact_binop_2; eauto.
    - inv VIS.
    - eapply var_in_sact_binop_1; eauto.
    - inv VIS.
    - eapply var_in_sact_binop_2; eauto.
    - inv VIS.
    - eapply var_in_sact_binop_1; eauto.
    - inv VIS.
    - inv VIS.
    - inv VIS.
      eapply var_in_sact_binop_1; eauto.
      eapply var_in_sact_binop_2; eauto.
    - inv VIS; econstructor; eauto.
  Qed.

  Lemma simplify_sact_targeted_interp_sact_ok:
    forall
      vvs (WTVVS: wt_vvs (Sigma := Sigma) R vvs)
      (VVSSV: vvs_smaller_variables vvs) a e p ta
      (SSTA: ssta a e p ta) v
      (EV_INIT:
        interp_sact (sigma := sigma) REnv r vvs ta v)
      t (WTS: wt_sact (Sigma := Sigma) R vvs a t),
    interp_sact (sigma := sigma) REnv r vvs a v.
  Proof.
    induction 3; simpl; intros; (try (inv WTS; [idtac])); eauto.
    - econstructor; eauto.
      eapply eval_sact_no_vars_interp in H; eauto.
      simpl. eauto.
    - econstructor; eauto.
      eapply eval_sact_no_vars_interp in H; eauto.
      simpl. eauto.
    - inv EV_INIT. econstructor; eauto.
      destr; eauto.
    - inv EV_INIT. econstructor; eauto.
      eapply eval_sact_no_vars_interp in H; eauto.
    - inv EV_INIT. econstructor; eauto.
    - eapply eval_sact_no_vars_interp in H; eauto.
      econstructor; eauto.
      eapply interp_sact_wt in H; eauto. 3: eapply wt_simplify_sact_targeted. 4: eauto. 3: eauto.
      inv H. inv H6.
      eapply interp_sact_wt in EV_INIT; eauto. 3: eapply wt_simplify_sact_targeted. 4: eauto. 3: eauto.
      destruct (Sact.wt_val_bool _ EV_INIT). subst. simpl. reflexivity.
      apply vvs_range_max_var.
      apply vvs_range_max_var.
    - inv EV_INIT.
      exploit @eval_sact_no_vars_wt. 4: apply H. 1-2: eauto. eapply wt_simplify_sact_targeted. 2: eauto. eauto.
      intro A; inv A. inv H6. simpl in *.
      edestruct (@wt_sact_interp) as (? & IS & WTv). 6: apply H5. all: eauto. apply vvs_range_max_var.
      econstructor; eauto.
      eapply IHSSTA.
      eapply eval_sact_no_vars_interp; eauto. eauto.
      destruct (Sact.wt_val_bool _ WTv). subst. simpl. reflexivity.
    - eapply eval_sact_no_vars_interp in H; eauto.
      econstructor; eauto.
      eapply interp_sact_wt in H; eauto. 3: eapply wt_simplify_sact_targeted. 4: eauto. 3: eauto.
      inv H. inv H6.
      eapply interp_sact_wt in EV_INIT; eauto. 3: eapply wt_simplify_sact_targeted. 4: eauto. 3: eauto.
      destruct (Sact.wt_val_bool _ EV_INIT). subst. simpl. rewrite andb_true_r; reflexivity.
      apply vvs_range_max_var.
      apply vvs_range_max_var.
    - inv EV_INIT.
      exploit @eval_sact_no_vars_wt. 4: apply H. 1-2: eauto. eapply wt_simplify_sact_targeted. 2: eauto. eauto.
      intro A; inv A. inv H6. simpl in *.
      edestruct (@wt_sact_interp) as (? & IS & WTv). 6: apply H3. all: eauto. apply vvs_range_max_var.
      econstructor; eauto.
      eapply IHSSTA.
      eapply eval_sact_no_vars_interp; eauto. eauto.
      destruct (Sact.wt_val_bool _ WTv). subst. simpl. rewrite andb_false_r. reflexivity.
    - eapply eval_sact_no_vars_interp in H; eauto.
      econstructor; eauto.
      eapply interp_sact_wt in H; eauto. 3: eapply wt_simplify_sact_targeted. 4: eauto. 3: eauto.
      inv H. inv H6.
      eapply interp_sact_wt in EV_INIT; eauto. 3: eapply wt_simplify_sact_targeted. 4: eauto. 3: eauto.
      destruct (Sact.wt_val_bool _ EV_INIT). subst. simpl. reflexivity.
      apply vvs_range_max_var.
      apply vvs_range_max_var.
    - inv EV_INIT.
      exploit @eval_sact_no_vars_wt. 4: apply H. 1-2: eauto. eapply wt_simplify_sact_targeted. 2: eauto. eauto.
      intro A; inv A. inv H6. simpl in *.
      edestruct (@wt_sact_interp) as (? & IS & WTv). 6: apply H5. all: eauto. apply vvs_range_max_var.
      econstructor; eauto.
      eapply IHSSTA.
      eapply eval_sact_no_vars_interp; eauto. eauto.
      destruct (Sact.wt_val_bool _ WTv). subst. simpl. reflexivity.
    - eapply eval_sact_no_vars_interp in H; eauto.
      econstructor; eauto.
      eapply interp_sact_wt in H; eauto. 3: eapply wt_simplify_sact_targeted. 4: eauto. 3: eauto.
      inv H. inv H6.
      eapply interp_sact_wt in EV_INIT; eauto. 3: eapply wt_simplify_sact_targeted. 4: eauto. 3: eauto.
      destruct (Sact.wt_val_bool _ EV_INIT). subst. simpl. rewrite orb_false_r; reflexivity.
      apply vvs_range_max_var.
      apply vvs_range_max_var.
    - inv EV_INIT.
      exploit @eval_sact_no_vars_wt. 4: apply H. 1-2: eauto. eapply wt_simplify_sact_targeted. 2: eauto. eauto.
      intro A; inv A. inv H6. simpl in *.
      edestruct (@wt_sact_interp) as (? & IS & WTv). 6: apply H3. all: eauto. apply vvs_range_max_var.
      econstructor; eauto.
      eapply IHSSTA.
      eapply eval_sact_no_vars_interp; eauto. eauto.
      destruct (Sact.wt_val_bool _ WTv). subst. simpl. rewrite orb_true_r. reflexivity.
    - eapply eval_sact_no_vars_interp in H; eauto.
      eapply eval_sact_no_vars_interp in H0; eauto.
      eapply IHSSTA1 in H; eauto.
      eapply IHSSTA2 in H0; eauto.
      inv EV_INIT. econstructor; eauto.
    - inv EV_INIT. econstructor; eauto.
    - inv EV_INIT. econstructor; eauto.
  Qed.

  Definition simplify_sf_targeted
    (sf: IRR (rule_name_t := rule_name_t)) (exemptions: PTree.t (list position))
  :=
    sf <|
      vars :=
        PTree.map (fun k '(t, s) =>
                     let exs :=
                       match PTree.get k exemptions with
                         Some l => l
                       | _ => []
                       end in
                     (t, simplify_sact_targeted s exs)
          )
          (vars sf)
    |>.

  Lemma sf_eq_simplify_sf_targeted sf:
    forall e,
    wf_sf sf -> sf_eq R Sigma r sigma sf (simplify_sf_targeted sf e).
  Proof.
    intros.
    eapply sf_eq_mapi.
    - intros. eapply simplify_sact_targeted_interp_sact_ok; eauto. eapply ssta_f.
    - intros; eapply simplify_sact_targeted_interp_sact_ok'; eauto.
    - intros; eapply simplify_sact_wt_sact_targeted_ok'; eauto.
    - intros; eapply simplify_sact_targeted_var_in_sact_ok'; eauto. eapply ssta_f.
    - eauto.
  Qed.

  Lemma wf_sf_simplify_sf_targeted:
    forall sf, wf_sf sf -> forall e, wf_sf (simplify_sf_targeted sf e).
  Proof.
    intros.
    eapply wf_fi; eauto.
    - intros; eapply simplify_sact_wt_sact_targeted_ok'; eauto.
    - intros; eapply simplify_sact_targeted_var_in_sact_ok'; eauto. eapply ssta_f.
  Qed.

  Lemma simplify_sf_targeted_interp_cycle_ok:
    forall reg sf e,
    wf_sf sf
    -> getenv REnv (interp_cycle r sigma sf) reg
    = getenv REnv (interp_cycle r sigma (simplify_sf_targeted sf e)) reg.
  Proof.
    intros.
    eapply sf_eq_interp_cycle_ok; eauto.
    - apply wf_sf_simplify_sf_targeted; auto.
    - apply sf_eq_simplify_sf_targeted. auto.
  Qed.
End SimplifyTargeted.
