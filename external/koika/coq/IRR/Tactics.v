Require Import Koika.BitsToLists.
Require Import Koika.Utils.Environments.
Require Import Koika.IRR.Direction.
Require Import Koika.IRR.IRR.
Require Import Koika.IRR.Operations.
Require Import Koika.IRR.Simplifications.Simplifications.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.IRR.Wt.
Require Import Koika.IRR.Interpretation.
Require Import Koika.IRR.Operations.

Ltac update_wfsf :=
  let wfsf_tmp := fresh "wfsf" in
  lazymatch goal with
  | RV: getenv ?REnv ?ctx ?rg = ?vl, WTRENV: Wt.wt_renv ?R ?REnv ?ctx,
    WFSF': wf_sf ?R ?ext_Sigma ?sf'
    |-
      getenv ?REnv (interp_cycle ?ctx ?ext_sigma (replace_reg ?sf' ?rg ?vl)) _
      = _
    =>
    assert (wf_sf R ext_Sigma (replace_reg sf' rg vl)) as wfsf_tmp by
    (eapply (wf_sf_replace_reg R ext_Sigma ctx WTRENV rg vl sf' RV WFSF'));
    clear WFSF'
  | VS: var_simpl ?R ?ext_Sigma ?ctx ?ext_sigma (vars ?sf) ?var ?newv,
    WTRENV: Wt.wt_renv ?R ?REnv ?ctx, WFSF': wf_sf ?R ?ext_Sigma ?sf'
    |-
      getenv ?REnv (interp_cycle ?ctx ?ext_sigma (replace_var ?sf' ?var ?newv))
        _
      = _
    =>
    assert (wf_sf R ext_Sigma (replace_var sf' var newv)) as wfsf_tmp by
    (eapply
      (wf_sf_replace_var R ext_Sigma ctx ext_sigma var newv sf' VS WFSF'));
    clear WFSF'
  | SO: subact_ok ?R ?ext_Sigma ?ctx ?ext_sigma (vars ?sf) ?positions ?needle
          ?rep,
    WTRENV: Wt.wt_renv ?R ?REnv ?ctx,
    WFSF': wf_sf ?R ?ext_Sigma ?sf'
    |-
      getenv
        ?REnv
        (interp_cycle ?ctx ?ext_sigma (replace_subact ?sf' ?positions ?rep)) _
      = _
    =>
    assert (wf_sf R ext_Sigma (replace_subact sf' positions rep)) as wfsf_tmp by
    (eapply
      (wf_sf_replace_subact' R ext_Sigma ctx ext_sigma sf' positions needle rep
        SO WFSF'));
    clear WFSF'
  | FV: get_field (getenv ?REnv ?ctx ?str) ?f = Some ?fv,
    WTRENV: Wt.wt_renv ?R ?REnv ?ctx, WFSF': wf_sf ?R ?ext_Sigma ?sf',
    WTSIGMA:
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)
    |-
      getenv
        ?REnv (interp_cycle ?ctx ?ext_sigma (replace_field ?str ?sf' ?f ?fv)) _
      = _
    =>
    assert (wf_sf R ext_Sigma (replace_field str sf' f fv)) as wfsf_tmp by (
    eapply (
      wf_sf_replace_field
        (wt_sigma := WTSIGMA) R ext_Sigma ctx ext_sigma WTRENV sf' str f fv FV
        WFSF'
    )); clear WFSF'
  | WTRENV: Wt.wt_renv ?R ?REnv ?ctx, WFSF': wf_sf ?R ?ext_Sigma ?sf',
    WT_SIGMA:
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)
    |- getenv
        ?REnv (interp_cycle ?ctx ?ext_sigma (simplify_sf ?ctx ?ext_sigma ?sf'))
        ?rg
       = _
    =>
    assert (wf_sf R ext_Sigma (simplify_sf ctx ext_sigma sf')) as wfsf_tmp by
    (intros; eapply (
       wf_sf_simplify_sf
         (wt_sigma := WT_SIGMA) (REnv := REnv) R ext_Sigma ctx ext_sigma WTRENV
         sf' WFSF'
    ); eauto); clear WFSF'
  | WTRENV: Wt.wt_renv ?R ?REnv ?ctx, WFSF': wf_sf ?R ?ext_Sigma ?sf',
    WT_SIGMA:
      forall (ufn : ?ext_fn_t) (vc : val), wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)
    |- getenv
         ?REnv
         (interp_cycle
           ?ctx ?ext_sigma (SyntacticSimplifications.simplify_sifs_sf ?sf')) ?rg
       = _
    =>
    assert (wf_sf R ext_Sigma (SyntacticSimplifications.simplify_sifs_sf sf'))
      as wfsf_tmp
      by (
        intros; eapply (
          SyntacticSimplifications.wf_sf_simplify_sifs_sf R ext_Sigma sf' WFSF'
        ); eauto
      );
    clear WFSF'
  | WTRENV: Wt.wt_renv ?R ?REnv ?ctx, WFSF': wf_sf ?R ?ext_Sigma ?sf',
    WT_SIGMA:
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)
    |- getenv
         ?REnv (interp_cycle ?ctx ?ext_sigma (simplify_sf_targeted ?sf' ?e)) ?rg
       = _
    =>
    assert (
      wf_sf R ext_Sigma (simplify_sf_targeted sf' e)
    ) as wfsf_tmp by (
      apply (
        wf_sf_simplify_sf_targeted
          (wt_sigma := WT_SIGMA) (REnv := REnv) R ext_Sigma ctx ext_sigma WTRENV
          sf' WFSF' e
      )
    ); clear WFSF'
  | WTRENV: Wt.wt_renv ?R ?REnv ?ctx, WFSF': wf_sf ?R ?ext_Sigma ?sf'
    |- getenv ?REnv (interp_cycle ?ctx ?ext_sigma (collapse_sf ?sf')) ?rg = _
    =>
    assert (wf_sf R ext_Sigma (collapse_sf sf')) as wfsf_tmp by (
      eapply (wf_collapse_sf R ext_Sigma sf' WFSF')
    ); clear WFSF'
  | WTRENV: Wt.wt_renv ?R ?REnv ?ctx, WFSF': wf_sf ?R ?ext_Sigma ?sf'
    |- getenv ?REnv
         (interp_cycle ?ctx ?ext_sigma (prune_irrelevant_aux ?sf' ?rg ?l)) ?rg
       = _
    =>
    let lassoc := fresh "lassoc" in
    assert (list_assoc (final_values sf') rg = Some l)
      as lassoc by (vm_compute list_assoc; reflexivity);
    assert (wf_sf R ext_Sigma (prune_irrelevant_aux sf' rg l)) as wfsf_tmp
    by (eapply (wf_sf_prune_irrelevant_aux R ext_Sigma sf' rg l lassoc WFSF'));
    clear WFSF'; clear lassoc
  | WTRENV: Wt.wt_renv ?R ?REnv ?ctx, WFSF': wf_sf ?R ?ext_Sigma ?sf'
    |- getenv ?REnv (interp_cycle ?ctx ?ext_sigma (prune_irrelevant_l ?sf' ?lr))
         ?rg
       = _
    =>
    assert (wf_sf R ext_Sigma (prune_irrelevant_l sf' lr)) as wfsf_tmp
      by (eapply (wf_sf_prune_irrelevant_l R ext_Sigma sf' lr WFSF'));
    clear WFSF'
  end; try move wfsf_tmp at top; try rename wfsf_tmp into wfsf.

Ltac exploit_reg H :=
  match goal with
  | WTRENV : Wt.wt_renv ?R ?REnv ?ctx,
    wt_sigma : (
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
    |- _ =>
      rewrite
        (replace_reg_interp_cycle_ok (wt_sigma := wt_sigma) _ _ _ _ WTRENV H);
        eauto; update_wfsf
  end.
Ltac exploit_regs :=
  repeat (match goal with
  | H: getenv ?REnv ?ctx ?reg = _,
    WTRENV : Wt.wt_renv ?R ?REnv ?ctx,
    wt_sigma : (
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
    |- _ =>
      rewrite
        (replace_reg_interp_cycle_ok (wt_sigma := wt_sigma) _ _ _ _ WTRENV H);
        eauto; update_wfsf; clear H
  end).

Ltac exploit_field H :=
  match goal with
  | WTRENV : Wt.wt_renv ?R ?REnv ?ctx,
    WFSF: wf_sf ?R ?ext_Sigma ?sf,
    wt_sigma : (
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
    |- _ =>
      rewrite
        (replace_field_interp_cycle_ok
          (wt_sigma := wt_sigma) _ _ _ _ WTRENV WFSF H);
      eauto; update_wfsf
  end.
Ltac exploit_fields :=
  (* TODO Manage imbricated fields *)
  repeat (match goal with
  | H: get_field (getenv ?REnv ?ctx ?reg) ?name = _,
    WTRENV : Wt.wt_renv ?R ?REnv ?ctx,
    WFSF: wf_sf ?R ?ext_Sigma ?sf,
    wt_sigma : (
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
    |- _ =>
      rewrite
        (replace_field_interp_cycle_ok
          (wt_sigma := wt_sigma) _ _ _ _ WTRENV WFSF H);
      eauto; update_wfsf; clear H
  end).

Ltac exploit_hypotheses := exploit_regs; exploit_fields.

Ltac simplify := erewrite simplify_sf_interp_cycle_ok; eauto; update_wfsf.
Ltac simplify_sifs :=
  erewrite SyntacticSimplifications.simplify_sifs_sf_interp_cycle_ok; eauto;
    update_wfsf.
Ltac prune :=
  erewrite prune_irrelevant_interp_cycle_ok;
    try (unfold prune_irrelevant; vm_compute list_assoc); eauto; update_wfsf.
Ltac collapse := erewrite collapse_interp_cycle_ok; eauto; update_wfsf.

Ltac exploit_var idx newv :=
  lazymatch goal with
  | WTRENV : Wt.wt_renv ?R ?REnv ?ctx,
    WFSF: wf_sf ?R ?ext_Sigma ?sf,
    wt_sigma : (
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
    |- _ =>
    let vs := fresh "VS" in
    assert (vs: var_simpl R ext_Sigma ctx ext_sigma (vars sf) idx newv);
    [| rewrite (
         replace_var_interp_cycle_ok (wt_sigma:=wt_sigma) _ _ _ _ WTRENV WFSF vs
       );
       update_wfsf ]
  end.

Ltac exploit_subact :=
  match goal with
  | WTRENV : Wt.wt_renv ?R ?REnv ?ctx,
    WFSF: wf_sf ?R ?ext_Sigma ?sf,
    SO: subact_ok
        ?R ?ext_Sigma ?ctx ?ext_sigma (vars ?sf) ?positions ?needle ?rep,
    wt_sigma : (
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
    |- _ =>
      rewrite (
        replace_subact_interp_cycle_ok'
          (wt_sigma:=wt_sigma) _ _ _ _ WTRENV _ WFSF _ _ _ SO
      ); update_wfsf
  end.

Ltac finish :=
  simplify; eapply getenv_interp;
  lazymatch goal with
  | |- list_assoc _ _ = _ => vm_compute list_assoc; reflexivity
  | |- Maps.PTree.get _ _ = _ => vm_compute Maps.PTree.get; reflexivity
  | |- _ => eauto
  end.

Ltac isolate_sf :=
  let name := fresh "sf" in
  lazymatch goal with
  | old_sf: IRR.IRR, wfsf: wf_sf _ _ _
    |- getenv _ (interp_cycle _ _ ?x) _ = _ =>
    set (name := x); fold name in wfsf; subst old_sf;
    vm_compute in name; rename name into old_sf
  | wfsf: wf_sf _ _ _ |- getenv _ (interp_cycle _ _ ?x) _ = _ =>
    set (name := x); fold name in wfsf
  end.

Ltac isolate_sf_named name :=
  lazymatch goal with
  | |- getenv _ (interp_cycle _ _ ?x) _ = _ => set (name := x)
  end.

Ltac full_pass := simplify; prune; collapse.
Ltac crusher strength :=
  exploit_hypotheses; isolate_sf;
  lazymatch strength with
  | 0 => idtac | 1 => do 1 full_pass | 2 => do 2 full_pass | 3 => do 3 full_pass
  | 4 => do 4 full_pass | 5 => do 5 full_pass | 6 => do 6 full_pass
  | 7 => do 7 full_pass | 8 => do 8 full_pass | 9 => do 9 full_pass
  | 10 => do 10 full_pass | 11 => do 11 full_pass | 12 => do 12 full_pass
  | 13 => do 13 full_pass | 14 => do 14 full_pass | 15 => do 15 full_pass
  | 16 => do 16 full_pass | 17 => do 17 full_pass | 18 => do 18 full_pass
  | 19 => do 19 full_pass | 20 => do 20 full_pass
  | _ => fail "max strength = 20"
  end;
  finish.

Ltac simplify_careful := isolate_sf; simplify_careful_t; update_wfsf.

Ltac full_pass_c := simplify_careful; collapse; prune; isolate_sf.
Ltac crusher_c strength :=
  exploit_hypotheses;
  lazymatch strength with
  | 0 => idtac | 1 => do 1 full_pass_c | 2 => do 2 full_pass_c
  | 3 => do 3 full_pass_c | 4 => do 4 full_pass_c | 5 => do 5 full_pass_c
  | 6 => do 6 full_pass_c | 7 => do 7 full_pass_c | 8 => do 8 full_pass_c
  | 9 => do 9 full_pass_c | 10 => do 10 full_pass_c | 11 => do 11 full_pass_c
  | 12 => do 12 full_pass_c | 13 => do 13 full_pass_c | 14 => do 14 full_pass_c
  | 15 => do 15 full_pass_c | 16 => do 16 full_pass_c | 17 => do 17 full_pass_c
  | 18 => do 18 full_pass_c | 19 => do 19 full_pass_c | 20 => do 20 full_pass_c
  | _ => fail "max strength = 20"
  end;
  finish.

Ltac search_subterm needle haystack pos orig_haystack Ppos :=
  lazymatch haystack with
  | needle => eval vm_compute in (ssprop_one pos needle orig_haystack Ppos)
  | SBinop _ ?a ?b =>
    let p1 :=
      search_subterm needle a (Direction.branch1 :: pos) orig_haystack
      (subact_at_pos_binop1 _ _ _ _ _ Ppos)
    in
    let p2 :=
      search_subterm needle b (Direction.branch2 :: pos) orig_haystack
      (subact_at_pos_binop2 _ _ _ _ _ Ppos)
    in
    eval vm_compute in
      (existT _ _ (sprop_binop needle pos _ _ _ (projT2 p1) (projT2 p2)))
  | SConst _ => eval vm_compute in (ssprop_nil needle orig_haystack pos)
  | SUnop _ ?a =>
    let p :=
      search_subterm
        needle a (Direction.branch1 :: pos) orig_haystack
        (subact_at_pos_unop1 _ _ _ _ Ppos)
    in
    eval vm_compute in (existT _ _ (sprop_unop needle pos _ _ (projT2 p)))
  | SVar _ => eval vm_compute in (ssprop_nil needle orig_haystack pos)
  | SIf ?a ?b ?c =>
    let p1 :=
      search_subterm needle a (Direction.branch1 :: pos) orig_haystack
        (subact_at_pos_if1 _ _ _ _ _ Ppos)
    in
    let p2 :=
      search_subterm needle b (Direction.branch2 :: pos) orig_haystack
        (subact_at_pos_if2 _ _ _ _ _ Ppos)
    in
    let p3 :=
      search_subterm needle c (Direction.branch3 :: pos) orig_haystack
        (subact_at_pos_if3 _ _ _ _ _ Ppos)
    in
    eval vm_compute in
      (existT _ _
        (sprop_if needle pos _ _ _ _ (projT2 p1) (projT2 p2) (projT2 p3)))
  | SReg _ => eval vm_compute in (ssprop_nil needle orig_haystack pos)
  | SExternalCall _ ?a =>
    let p :=
      search_subterm needle a (Direction.branch1 :: pos) orig_haystack
      (subact_at_pos_extcall1 _ _ _ _ Ppos)
    in
    eval vm_compute in (existT _ _ (sprop_unop needle pos _ _ (projT2 p)))
  end.

Ltac ssearch needle haystack :=
  let hs := eval vm_compute in haystack in
  let res :=
    search_subterm
      needle hs ([]: list Direction.direction) hs (subact_at_pos_rev_refl hs) in
  res.

Ltac ssearch_in_elems needle l :=
  lazymatch l with
  | [] => eval vm_compute in (ssearch_in_elemsT_nil needle)
  | (?kk, (?tt, ?x))::?r =>
    let ps := ssearch needle x in
    let pss := ssearch_in_elems needle r in
    eval vm_compute in (ssearch_in_elemsT_cons needle r kk tt _ _ pss ps)
  end.

Ltac ssearch_in_vars needle t H :=
  let vars := eval vm_compute in (Maps.PTree.elements t) in
  let res := ssearch_in_elems needle vars in
  let res := eval vm_compute in res in
  let x := eval vm_compute in (projT1 res) in
  let P := eval vm_compute in (projT2 res) in
  let positions := fresh "positions" in
  set (positions := x);
  assert (H :
    Forall2 (
      fun '(k, (ty, a)) '(k1, ps) =>
        k = k1 /\
        (fun '(_, a) ps =>
          ReplaceSubact.search_subterm_propP needle a [] ps) (ty, a) ps
    ) (Maps.PTree.elements t) positions) by exact P.

Ltac get_subact_ok needle vars rep t :=
  match goal with
  | WTRENV : Wt.wt_renv ?R ?REnv ?ctx,
    WFSF: wf_sf ?R ?ext_Sigma ?sf,
    wt_sigma : (forall (ufn : ?ext_fn_t) (vc : val),
    wt_val (arg1Sig (?ext_Sigma ufn)) vc
    -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
    |- _ =>
      let H := fresh in
      ssearch_in_vars needle vars H;
      generalize (
        ReplaceSubact.subact_ok_ltac
          (REnv:=REnv) R ext_Sigma ctx ext_sigma _ _ _ H rep t
      ); clear H
  end.

Ltac ssearch_in_var needle t k rep ty :=
  match goal with
  | WTRENV : Wt.wt_renv ?R ?REnv ?ctx,
    WFSF: wf_sf ?R ?ext_Sigma ?sf,
    wt_sigma : (
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
    |- _ =>
      let res := eval vm_compute in (Maps.PTree.get k t) in
      match res with
      | Some (?itt, ?ix) =>
        let res := ssearch needle ix in
        let x := eval vm_compute in (projT1 res) in
        let P := eval vm_compute in (projT2 res) in
        let positions := fresh "positions" in
        set (positions := x);
        set (HP := P);
        generalize (
          fun pf =>
            ReplaceSubact.subact_ok_ltac_1var
              (REnv:=REnv) R ext_Sigma ctx ext_sigma t _ k itt _ positions pf HP
              rep ty
        ); clear HP
      end
  end.
