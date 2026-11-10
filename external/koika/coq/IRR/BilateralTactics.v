Require Import Koika.BitsToLists.
Require Import Koika.Utils.Environments.
Require Import Koika.IRR.Direction.
Require Import Koika.IRR.IRR.
Require Import Koika.IRR.Operations.
Require Import Koika.IRR.Simplifications.Simplifications.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.IRR.Tactics.
Require Import Koika.IRR.Wt.
Require Import Koika.IRR.Interpretation.
Require Import Koika.IRR.Operations.

Ltac update_wfsf_bl :=
  let wfsfa_tmp := fresh "wfsfa" in
  let wfsfb_tmp := fresh "wfsfb" in
  lazymatch goal with
  | WTRENVA: Wt.wt_renv ?R ?REnv ?ctxa, WTRENVB: Wt.wt_renv ?R ?REnv ?ctxb,
    WFSFA: wf_sf ?R ?ext_Sigma ?sfa, WFSFB: wf_sf ?R ?ext_Sigma ?sfb,
    RVA: getenv ?REnv ?ctxa ?rga = ?vla, RVB: getenv ?REnv ?ctxb ?rgb = ?vlb
    |-
      getenv
        ?REnv (interp_cycle ?ctxa ?ext_sigma (replace_reg ?sfa ?rga ?vla)) _
      =
      getenv
        ?REnv (interp_cycle ?ctxb ?ext_sigma (replace_reg ?sfb ?rgb ?vlb)) _
    =>
    assert (wf_sf R ext_Sigma (replace_reg sfa rga vla)) as wfsfa_tmp by
    (eapply (wf_sf_replace_reg R ext_Sigma ctxa WTRENVA rga vla sfa RVA WFSFA));
    assert (wf_sf R ext_Sigma (replace_reg sfb rgb vlb)) as wfsfb_tmp by
    (eapply (wf_sf_replace_reg R ext_Sigma ctxb WTRENVB rgb vlb sfb RVB WFSFB));
    clear WFSFA; clear WFSFB
  | WTRENVA: Wt.wt_renv ?R ?REnv ?ctxa, WTRENVB: Wt.wt_renv ?R ?REnv ?ctxb,
    WFSFA: wf_sf ?R ?ext_Sigma ?sfa, WFSFB: wf_sf ?R ?ext_Sigma ?sfb,
    VSA: var_simpl ?R ?ext_Sigma ?ctxa ?ext_sigma (vars ?sfa) ?vara ?newva,
    VSB: var_simpl ?R ?ext_Sigma ?ctxb ?ext_sigma (vars ?sfb) ?varb ?newvb
    |-
      getenv
        ?REnv (interp_cycle ?ctxa ?ext_sigma (replace_var ?sfa ?vara ?newva)) _
      =
      getenv
        ?REnv (interp_cycle ?ctxb ?ext_sigma (replace_var ?sfb ?varb ?newvb)) _
    =>
    assert (wf_sf R ext_Sigma (replace_var sfa vara newva)) as wfsfa_tmp by
    (eapply
      (wf_sf_replace_var R ext_Sigma ctxa ext_sigma vara newva sfa VSA WFSFA));
    assert (wf_sf R ext_Sigma (replace_var sfb varb newvb)) as wfsfb_tmp by
    (eapply
      (wf_sf_replace_var R ext_Sigma ctxb ext_sigma varb newvb sfb VSB WFSFB));
    clear WFSFA; clear WFSFB
  | WTRENVA: Wt.wt_renv ?R ?REnv ?ctxa, WTRENVB: Wt.wt_renv ?R ?REnv ?ctxb,
    WFSFA: wf_sf ?R ?ext_Sigma ?sfa, WFSFB: wf_sf ?R ?ext_Sigma ?sfb,
    SOA: subact_ok ?R ?ext_Sigma ?ctxa ?ext_sigma (vars ?sfa) ?positionsa
           ?needlea ?repa,
    SOB: subact_ok ?R ?ext_Sigma ?ctxb ?ext_sigma (vars ?sfb) ?positionsb
           ?needleb ?repb
    |-
      getenv
        ?REnv
        (interp_cycle ?ctxa ?ext_sigma (replace_subact ?sfa ?positionsa ?repa))
        _
      =
      getenv
        ?REnv
        (interp_cycle ?ctxb ?ext_sigma (replace_subact ?sfb ?positionsb ?repb))
        _
    =>
    assert (wf_sf R ext_Sigma (replace_subact sfa positionsa repa)) as wfsfa_tmp
    by (eapply (wf_sf_replace_subact'
      R ext_Sigma ctxa ext_sigma sfa positionsa needlea repa SOA WFSFA)
    );
    assert (wf_sf R ext_Sigma (replace_subact sfb positionsb repb)) as wfsfb_tmp
    by (eapply (wf_sf_replace_subact'
      R ext_Sigma ctxb ext_sigma sfb positionsb needleb repb SOB WFSFB)
    );
    clear WFSFA; clear WFSFB
  | WTRENVA: Wt.wt_renv ?R ?REnv ?ctxa, WTRENVB: Wt.wt_renv ?R ?REnv ?ctxb,
    WFSFA: wf_sf ?R ?ext_Sigma ?sfa, WFSFB: wf_sf ?R ?ext_Sigma ?sfb,
    FVA: get_field (getenv ?REnv ?ctxa ?stra) ?fa = Some ?fva,
    FVB: get_field (getenv ?REnv ?ctxb ?strb) ?fb = Some ?fvb,
    WTSIGMA:
      forall (ufn : ?ext_fn_t) (vc : val), wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)
    |-
      getenv
        ?REnv
        (interp_cycle ?ctxa ?ext_sigma (replace_field ?stra ?sfa ?fa ?fva))
        _
      =
      getenv
        ?REnv
        (interp_cycle ?ctxb ?ext_sigma (replace_field ?strb ?sfb ?fb ?fvb))
        _
    =>
    assert (wf_sf R ext_Sigma (replace_field stra sfa fa fva)) as wfsfa_tmp by
    (eapply (
      wf_sf_replace_field
        (wt_sigma := WTSIGMA) R ext_Sigma ctxa ext_sigma WTRENVA sfa stra fa fva
        FVA WFSFA
    ));
    assert (wf_sf R ext_Sigma (replace_field strb sfb fb fvb)) as wfsfb_tmp by
    (eapply (
      wf_sf_replace_field
        (wt_sigma := WTSIGMA) R ext_Sigma ctxb ext_sigma WTRENVB sfb strb fb fvb
        FVB WFSFB
    ));
    clear WFSFA; clear WFSFB
  | WTRENVA: Wt.wt_renv ?R ?REnv ?ctxa, WTRENVB: Wt.wt_renv ?R ?REnv ?ctxb,
    WFSFA: wf_sf ?R ?ext_Sigma ?sfa, WFSFB: wf_sf ?R ?ext_Sigma ?sfb,
    WT_SIGMA:
      forall (ufn : ?ext_fn_t) (vc : val), wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)
    |- getenv
         ?REnv
         (interp_cycle ?ctxa ?ext_sigma (simplify_sf ?ctxa ?ext_sigma ?sfa))
         ?rga
       =
       getenv
         ?REnv
         (interp_cycle ?ctxb ?ext_sigma (simplify_sf ?ctxb ?ext_sigma ?sfb))
         ?rgb
    =>
    assert (wf_sf R ext_Sigma (simplify_sf ctxa ext_sigma sfa)) as wfsfa_tmp by
    (intros; eapply (
       wf_sf_simplify_sf
         (wt_sigma := WT_SIGMA) (REnv := REnv) R ext_Sigma ctxa ext_sigma
         WTRENVA sfa WFSFA
    ); eauto);
    assert (wf_sf R ext_Sigma (simplify_sf ctxb ext_sigma sfb)) as wfsfb_tmp by
    (intros; eapply (
       wf_sf_simplify_sf
         (wt_sigma := WT_SIGMA) (REnv := REnv) R ext_Sigma ctxb ext_sigma
         WTRENVB sfb WFSFB
    ); eauto);
    clear WFSFA; clear WFSFB
  | WTRENVA: Wt.wt_renv ?R ?REnv ?ctxa, WTRENVB: Wt.wt_renv ?R ?REnv ?ctxb,
    WFSFA: wf_sf ?R ?ext_Sigma ?sfa, WFSFB: wf_sf ?R ?ext_Sigma ?sfb,
    WT_SIGMA:
      forall (ufn : ?ext_fn_t) (vc : val), wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)
    |- getenv
         ?REnv (interp_cycle ?ctxa ?ext_sigma (simplify_sf_targeted ?sfa ?ea))
         ?rga
       =
       getenv
         ?REnv (interp_cycle ?ctxb ?ext_sigma (simplify_sf_targeted ?sfb ?eb))
         ?rgb
    =>
    assert (wf_sf R ext_Sigma (simplify_sf_targeted sfa ea)) as wfsfa_tmp
    by (apply (
      wf_sf_simplify_sf_targeted
        (wt_sigma := WT_SIGMA) (REnv := REnv) R ext_Sigma ctxa ext_sigma WTRENVA
        sfa WFSFA ea
    ));
    assert (wf_sf R ext_Sigma (simplify_sf_targeted sfb eb)) as wfsfb_tmp
    by (apply (
      wf_sf_simplify_sf_targeted
        (wt_sigma := WT_SIGMA) (REnv := REnv) R ext_Sigma ctxb ext_sigma WTRENVB
        sfb WFSFB eb
    ));
    clear WFSFA; clear WFSFB
  | WTRENVA: Wt.wt_renv ?R ?REnv ?ctxa, WTRENVB: Wt.wt_renv ?R ?REnv ?ctxb,
    WFSFA: wf_sf ?R ?ext_Sigma ?sfa, WFSFB: wf_sf ?R ?ext_Sigma ?sfb
    |- getenv ?REnv (interp_cycle ?ctxa ?ext_sigma (collapse_sf ?sfa)) ?rga
       = getenv ?REnv (interp_cycle ?ctxa ?ext_sigma (collapse_sf ?sfb)) ?rgb
    =>
    assert (wf_sf R ext_Sigma (collapse_sf sfa)) as wfsfa_tmp by (
      eapply (wf_collapse_sf R ext_Sigma sfa WFSFA)
    );
    assert (wf_sf R ext_Sigma (collapse_sf sfb)) as wfsfb_tmp by (
      eapply (wf_collapse_sf R ext_Sigma sfb WFSFB)
    );
    clear WFSFA; clear WFSFB
  | WTRENVA: Wt.wt_renv ?R ?REnv ?ctxa, WTRENVB: Wt.wt_renv ?R ?REnv ?ctxb,
    WFSFA: wf_sf ?R ?ext_Sigma ?sfa, WFSFB: wf_sf ?R ?ext_Sigma ?sfb
    |- getenv
         ?REnv
         (interp_cycle ?ctxa ?ext_sigma (prune_irrelevant_aux ?sfa ?rga ?la))
         ?rga
       =
       getenv
         ?REnv
         (interp_cycle ?ctxb ?ext_sigma (prune_irrelevant_aux ?sfb ?rgb ?lb))
         ?rgb
    =>
    let lassoca := fresh "lassoca" in
    assert (list_assoc (final_values sfa) rga = Some la)
      as lassoca by (vm_compute list_assoc; reflexivity);
    assert (wf_sf R ext_Sigma (prune_irrelevant_aux sfa rga la)) as wfsfa_tmp
    by (eapply (wf_sf_prune_irrelevant_aux R ext_Sigma sfa rga la lassoca WFSFA));
    assert (list_assoc (final_values sfb) rgb = Some lb)
      as lassocb by (vm_compute list_assoc; reflexivity);
    assert (wf_sf R ext_Sigma (prune_irrelevant_aux sfb rgb lb)) as wfsfb_tmp
    by (
      eapply (wf_sf_prune_irrelevant_aux R ext_Sigma sfb rgb lb lassocb WFSFB)
    );
    clear WFSFA; clear lassoca; clear WFSFB; clear lassocb
  (* From here on, we repeat the above cases but we assume that the sfs are
     shared *)
  | WTRENVA: Wt.wt_renv ?R ?REnv ?ctxa, WTRENVB: Wt.wt_renv ?R ?REnv ?ctxb,
    WFSF: wf_sf ?R ?ext_Sigma ?sf,
    RVA: getenv ?REnv ?ctxa ?rga = ?vla, RVB: getenv ?REnv ?ctxb ?rgb = ?vlb
    |-
      getenv ?REnv (interp_cycle ?ctxa ?ext_sigma (replace_reg ?sf ?rga ?vla)) _
      =
      getenv ?REnv (interp_cycle ?ctxb ?ext_sigma (replace_reg ?sf ?rgb ?vlb)) _
    =>
    assert (wf_sf R ext_Sigma (replace_reg sf rga vla)) as wfsfa_tmp by
    (eapply (wf_sf_replace_reg R ext_Sigma ctxa WTRENVA rga vla sf RVA WFSF));
    assert (wf_sf R ext_Sigma (replace_reg sf rgb vlb)) as wfsfb_tmp by
    (eapply (wf_sf_replace_reg R ext_Sigma ctxb WTRENVB rgb vlb sf RVB WFSF));
    clear WFSF; clear WFSF
  | WTRENVA: Wt.wt_renv ?R ?REnv ?ctxa, WTRENVB: Wt.wt_renv ?R ?REnv ?ctxb,
    WFSF: wf_sf ?R ?ext_Sigma ?sf,
    VSA: var_simpl ?R ?ext_Sigma ?ctxa ?ext_sigma (vars ?sf) ?vara ?newva,
    VSB: var_simpl ?R ?ext_Sigma ?ctxb ?ext_sigma (vars ?sf) ?varb ?newvb
    |-
      getenv
        ?REnv (interp_cycle ?ctxa ?ext_sigma (replace_var ?sf ?vara ?newva)) _
      =
      getenv
        ?REnv (interp_cycle ?ctxb ?ext_sigma (replace_var ?sf ?varb ?newvb)) _
    =>
    assert (wf_sf R ext_Sigma (replace_var sf vara newva)) as wfsfa_tmp by
    (eapply
      (wf_sf_replace_var R ext_Sigma ctxa ext_sigma vara newva sf VSA WFSF));
    assert (wf_sf R ext_Sigma (replace_var sf varb newvb)) as wfsfb_tmp by
    (eapply
      (wf_sf_replace_var R ext_Sigma ctxb ext_sigma varb newvb sf VSB WFSF));
    clear WFSF; clear WFSF
  | WTRENVA: Wt.wt_renv ?R ?REnv ?ctxa, WTRENVB: Wt.wt_renv ?R ?REnv ?ctxb,
    WFSF: wf_sf ?R ?ext_Sigma ?sf,
    SOA: subact_ok ?R ?ext_Sigma ?ctxa ?ext_sigma (vars ?sf) ?positionsa
           ?needlea ?repa,
    SOB: subact_ok ?R ?ext_Sigma ?ctxb ?ext_sigma (vars ?sf) ?positionsb
           ?needleb ?repb
    |-
      getenv
        ?REnv
        (interp_cycle ?ctxa ?ext_sigma (replace_subact ?sf ?positionsa ?repa))
        _
      =
      getenv
        ?REnv
        (interp_cycle ?ctxb ?ext_sigma (replace_subact ?sf ?positionsb ?repb))
        _
    =>
    assert (wf_sf R ext_Sigma (replace_subact sf positionsa repa)) as wfsfa_tmp
    by (eapply (wf_sf_replace_subact'
      R ext_Sigma ctxa ext_sigma sf positionsa needlea repa SOA WFSF)
    );
    assert (wf_sf R ext_Sigma (replace_subact sf positionsb repb)) as wfsfb_tmp
    by (eapply (wf_sf_replace_subact'
      R ext_Sigma ctxb ext_sigma sf positionsb needleb repb SOB WFSF)
    );
    clear WFSF; clear WFSF
  | WTRENVA: Wt.wt_renv ?R ?REnv ?ctxa, WTRENVB: Wt.wt_renv ?R ?REnv ?ctxb,
    WFSF: wf_sf ?R ?ext_Sigma ?sf,
    FVA: get_field (getenv ?REnv ?ctxa ?stra) ?fa = Some ?fva,
    FVB: get_field (getenv ?REnv ?ctxb ?strb) ?fb = Some ?fvb,
    WTSIGMA:
      forall (ufn : ?ext_fn_t) (vc : val), wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)
    |-
      getenv
        ?REnv
        (interp_cycle ?ctxa ?ext_sigma (replace_field ?stra ?sf ?fa ?fva))
        _
      =
      getenv
        ?REnv
        (interp_cycle ?ctxb ?ext_sigma (replace_field ?strb ?sf ?fb ?fvb))
        _
    =>
    assert (wf_sf R ext_Sigma (replace_field stra sf fa fva)) as wfsfa_tmp by
    (eapply (
      wf_sf_replace_field
        (wt_sigma := WTSIGMA) R ext_Sigma ctxa ext_sigma WTRENVA sf stra fa fva
        FVA WFSF
    ));
    assert (wf_sf R ext_Sigma (replace_field strb sf fb fvb)) as wfsfb_tmp by
    (eapply (
      wf_sf_replace_field
        (wt_sigma := WTSIGMA) R ext_Sigma ctxb ext_sigma WTRENVB sf strb fb fvb
        FVB WFSF
    ));
    clear WFSF; clear WFSF
  | WTRENVA: Wt.wt_renv ?R ?REnv ?ctxa, WTRENVB: Wt.wt_renv ?R ?REnv ?ctxb,
    WFSF: wf_sf ?R ?ext_Sigma ?sf,
    WT_SIGMA:
      forall (ufn : ?ext_fn_t) (vc : val), wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)
    |- getenv
         ?REnv
         (interp_cycle ?ctxa ?ext_sigma (simplify_sf ?ctxa ?ext_sigma ?sf))
         ?rga
       =
       getenv
         ?REnv
         (interp_cycle ?ctxb ?ext_sigma (simplify_sf ?ctxb ?ext_sigma ?sf))
         ?rgb
    =>
    assert (wf_sf R ext_Sigma (simplify_sf ctxa ext_sigma sf)) as wfsfa_tmp by
    (intros; eapply (
       wf_sf_simplify_sf
         (wt_sigma := WT_SIGMA) (REnv := REnv) R ext_Sigma ctxa ext_sigma
         WTRENVA sf WFSF
    ); eauto);
    assert (wf_sf R ext_Sigma (simplify_sf ctxb ext_sigma sf)) as wfsfb_tmp by
    (intros; eapply (
       wf_sf_simplify_sf
         (wt_sigma := WT_SIGMA) (REnv := REnv) R ext_Sigma ctxb ext_sigma
         WTRENVB sf WFSF
    ); eauto);
    clear WFSF
  | WTRENVA: Wt.wt_renv ?R ?REnv ?ctxa, WTRENVB: Wt.wt_renv ?R ?REnv ?ctxb,
    WFSF: wf_sf ?R ?ext_Sigma ?sf,
    WT_SIGMA:
      forall (ufn : ?ext_fn_t) (vc : val), wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)
    |- getenv
         ?REnv (interp_cycle ?ctxa ?ext_sigma (simplify_sf_targeted ?sf ?ea))
         ?rga
       =
       getenv
         ?REnv (interp_cycle ?ctxb ?ext_sigma (simplify_sf_targeted ?sf ?eb))
         ?rgb
    =>
    assert (wf_sf R ext_Sigma (simplify_sf_targeted sf ea)) as wfsfa_tmp
    by (apply (
      wf_sf_simplify_sf_targeted
        (wt_sigma := WT_SIGMA) (REnv := REnv) R ext_Sigma ctxa ext_sigma WTRENVA
        sf WFSF ea
    ));
    assert (wf_sf R ext_Sigma (simplify_sf_targeted sf eb)) as wfsfb_tmp
    by (apply (
      wf_sf_simplify_sf_targeted
        (wt_sigma := WT_SIGMA) (REnv := REnv) R ext_Sigma ctxb ext_sigma WTRENVB
        sf WFSF eb
    ));
    clear WFSF
  | WTRENVA: Wt.wt_renv ?R ?REnv ?ctxa, WTRENVB: Wt.wt_renv ?R ?REnv ?ctxb,
    WFSF: wf_sf ?R ?ext_Sigma ?sf
    |- getenv ?REnv (interp_cycle ?ctxa ?ext_sigma (collapse_sf ?sf)) ?rga
       = getenv ?REnv (interp_cycle ?ctxa ?ext_sigma (collapse_sf ?sf)) ?rgb
    =>
    assert (wf_sf R ext_Sigma (collapse_sf sf)) as wfsfa_tmp by (
      eapply (wf_collapse_sf R ext_Sigma sf WFSF)
    );
    assert (wf_sf R ext_Sigma (collapse_sf sf)) as wfsfb_tmp by (
      eapply (wf_collapse_sf R ext_Sigma sf WFSF)
    );
    clear WFSF
  | WTRENVA: Wt.wt_renv ?R ?REnv ?ctxa, WTRENVB: Wt.wt_renv ?R ?REnv ?ctxb,
    WFSF: wf_sf ?R ?ext_Sigma ?sf
    |- getenv
         ?REnv
         (interp_cycle ?ctxa ?ext_sigma (prune_irrelevant_aux ?sf ?rga ?la))
         ?rga
       =
       getenv
         ?REnv
         (interp_cycle ?ctxb ?ext_sigma (prune_irrelevant_aux ?sf ?rgb ?lb))
         ?rgb
    =>
    let lassoca := fresh "lassoca" in
    assert (list_assoc (final_values sf) rga = Some la)
      as lassoca by (vm_compute list_assoc; reflexivity);
    assert (wf_sf R ext_Sigma (prune_irrelevant_aux sf rga la)) as wfsfa_tmp
    by (eapply (wf_sf_prune_irrelevant_aux R ext_Sigma sf rga la lassoca WFSF));
    assert (list_assoc (final_values sf) rgb = Some lb)
      as lassocb by (vm_compute list_assoc; reflexivity);
    assert (wf_sf R ext_Sigma (prune_irrelevant_aux sf rgb lb)) as wfsfb_tmp
    by (
      eapply (wf_sf_prune_irrelevant_aux R ext_Sigma sf rgb lb lassocb WFSF)
    );
    clear WFSF; clear lassoca; clear lassocb
  end;
  try move wfsfa_tmp at top; try rename wfsfa_tmp into wfsfa;
  try move wfsfb_tmp at top; try rename wfsfb_tmp into wfsfb.

Ltac exploit_reg_bl HA HB :=
  match goal with
  | WTRENVA : Wt.wt_renv ?R ?REnv ?ctxa,
    WTRENVB : Wt.wt_renv ?R ?REnv ?ctxb,
    wt_sigma : (
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
    |- getenv ?REnv (interp_cycle ?ctxa ?ext_sigma ?sfa) ?rga
       = getenv ?REnv (interp_cycle ?ctxb ?ext_sigma ?sfb) ?rgb
    =>
      rewrite
        (replace_reg_interp_cycle_ok (wt_sigma := wt_sigma) _ _ _ _ WTRENVA HA);
      eauto; symmetry;
      rewrite
        (replace_reg_interp_cycle_ok (wt_sigma := wt_sigma) _ _ _ _ WTRENVB HB);
      eauto; symmetry; update_wfsf_bl
  end.
Ltac exploit_regs_bl :=
  repeat (
    match goal with
    | WTRENVA : Wt.wt_renv ?R ?REnv ?ctxa, HA: getenv ?REnv ?ctxa ?rega = _,
      wt_sigma : (
        forall (ufn : ?ext_fn_t) (vc : val),
        wt_val (arg1Sig (?ext_Sigma ufn)) vc
        -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
      |- getenv ?REnv (interp_cycle ?ctxa ?ext_sigma ?sfa) ?rga = _ =>
        rewrite
          (replace_reg_interp_cycle_ok
            (wt_sigma := wt_sigma) _ _ _ _ WTRENVA HA);
        match goal with
        | |- getenv _ _ _ = _ => idtac
        | _ => auto
        end; update_wfsf; clear HA
    end
  );
  symmetry;
  repeat (
    match goal with
    | WTRENVA : Wt.wt_renv ?R ?REnv ?ctxa, HA: getenv ?REnv ?ctxa ?rega = _,
      wt_sigma : (
        forall (ufn : ?ext_fn_t) (vc : val),
        wt_val (arg1Sig (?ext_Sigma ufn)) vc
        -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
      |- getenv ?REnv (interp_cycle ?ctxa ?ext_sigma ?sfa) ?rga = _ =>
        rewrite
          (replace_reg_interp_cycle_ok
            (wt_sigma := wt_sigma) _ _ _ _ WTRENVA HA);
        match goal with
        | |- getenv _ _ _ = _ => idtac
        | _ => auto
        end; update_wfsf; clear HA
    end
  );
  symmetry.

Ltac exploit_field_bl HA HB :=
  match goal with
  | WTRENVA: Wt.wt_renv ?R ?REnv ?ctxa, WTRENVB: Wt.wt_renv ?R ?REnv ?ctxb,
    WFSFA: wf_sf ?R ?ext_Sigma ?sfa, WFSFB: wf_sf ?R ?ext_Sigma ?sfb,
    wt_sigma: (
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)
    )
    |- getenv ?REnv (interp_cycle ?ctxa ?ext_sigma ?sfa) ?rga
       = getenv ?REnv (interp_cycle ?ctxb ?ext_sigma ?sfb) ?rgb
    =>
      rewrite
        (replace_field_interp_cycle_ok
          (wt_sigma := wt_sigma) _ _ _ _ WTRENVA WFSFA HA);
      eauto; symmetry;
      rewrite
        (replace_field_interp_cycle_ok
          (wt_sigma := wt_sigma) _ _ _ _ WTRENVB WFSFB HB);
      eauto; symmetry; update_wfsf_bl
  end.
Ltac exploit_fields_bl :=
  (* TODO Manage imbricated fields. Splitting into bits works but can lead to
          performance issues. *)
  repeat (match goal with
  | WTRENVA : Wt.wt_renv ?R ?REnv ?ctxa, WFSFA: wf_sf ?R ?ext_Sigma ?sfa,
    HA: get_field (getenv ?REnv ?ctxa ?rega) ?namea = _,
    wt_sigma : (
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
    |- getenv ?REnv (interp_cycle ?ctxa ?ext_sigma ?sfa) ?rga = _ =>
      rewrite
        (replace_field_interp_cycle_ok
          (wt_sigma := wt_sigma) _ _ _ _ WTRENVA WFSFA HA);
      auto; update_wfsf; clear HA
  end);
  symmetry;
  repeat (match goal with
  | WTRENVA : Wt.wt_renv ?R ?REnv ?ctxa, WFSFA: wf_sf ?R ?ext_Sigma ?sfa,
    HA: get_field (getenv ?REnv ?ctxa ?rega) ?namea = _,
    wt_sigma : (
      forall (ufn : ?ext_fn_t) (vc : val),
      wt_val (arg1Sig (?ext_Sigma ufn)) vc
      -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc))
    |- getenv ?REnv (interp_cycle ?ctxa ?ext_sigma ?sfa) ?rga = _ =>
      rewrite
        (replace_field_interp_cycle_ok
          (wt_sigma := wt_sigma) _ _ _ _ WTRENVA WFSFA HA);
      auto; update_wfsf; clear HA
  end);
  symmetry.

Ltac exploit_hypotheses_bl := exploit_regs_bl; exploit_fields_bl.

Ltac simplify_bl :=
  erewrite simplify_sf_interp_cycle_ok; eauto; symmetry;
  erewrite simplify_sf_interp_cycle_ok; eauto; symmetry;
  update_wfsf_bl.
Ltac prune_bl :=
  erewrite prune_irrelevant_interp_cycle_ok;
  match goal with
  | |- prune_irrelevant _ _ = _ =>
       unfold Prune.prune_irrelevant; vm_compute list_assoc; eauto
  | |- getenv _ _ _ = _ => idtac
  | |- _ => eauto
  end;
  symmetry;
  erewrite prune_irrelevant_interp_cycle_ok;
  match goal with
  | |- prune_irrelevant _ _ = _ =>
       unfold Prune.prune_irrelevant; vm_compute list_assoc; eauto
  | |- getenv _ _ _ = _ => idtac
  | |- _ => eauto
  end;
  symmetry; update_wfsf_bl.
Ltac collapse_bl :=
  erewrite collapse_interp_cycle_ok;
  match goal with
  | WFSF: wf_sf _ _ ?sf |- Collapse.wf_sf _ _ ?sf => apply WFSF
  | |- getenv _ _ _ = _ => idtac
  | |- _ => eauto
  end;
  symmetry;
  erewrite collapse_interp_cycle_ok;
  match goal with
  | WFSF: wf_sf _ _ ?sf |- Collapse.wf_sf _ _ ?sf => apply WFSF
  | |- getenv _ _ _ = _ => idtac
  | |- _ => eauto
  end;
  symmetry;
  update_wfsf_bl.

(* Ltac exploit_var_bl idx newv := *)
(*   lazymatch goal with *)
(*   | WTRENV : Wt.wt_renv ?R ?REnv ?ctx, *)
(*     WFSF: wf_sf ?R ?ext_Sigma ?sf, *)
(*     wt_sigma : ( *)
(*       forall (ufn : ?ext_fn_t) (vc : val), *)
(*       wt_val (arg1Sig (?ext_Sigma ufn)) vc *)
(*       -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)) *)
(*     |- _ => *)
(*     let vs := fresh "VS" in *)
(*     assert (vs: var_simpl R ext_Sigma ctx ext_sigma (vars sf) idx newv); *)
(*     [| rewrite ( *)
(*          replace_var_interp_cycle_ok (wt_sigma:=wt_sigma) _ _ _ _ WTRENV WFSF vs *)
(*        ); *)
(*        update_wfsf_bl ] *)
(*   end. *)

(* Ltac exploit_subact_bl := *)
(*   match goal with *)
(*   | WTRENV : Wt.wt_renv ?R ?REnv ?ctx, *)
(*     WFSF: wf_sf ?R ?ext_Sigma ?sf, *)
(*     SO: subact_ok *)
(*         ?R ?ext_Sigma ?ctx ?ext_sigma (vars ?sf) ?positions ?needle ?rep, *)
(*     wt_sigma : ( *)
(*       forall (ufn : ?ext_fn_t) (vc : val), *)
(*       wt_val (arg1Sig (?ext_Sigma ufn)) vc *)
(*       -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)) *)
(*     |- _ => *)
(*       rewrite ( *)
(*         replace_subact_interp_cycle_ok' *)
(*           (wt_sigma:=wt_sigma) _ _ _ _ WTRENV _ WFSF _ _ _ SO *)
(*       ); update_wfsf *)
(*   end. *)

Ltac finish_bl :=
  simplify_bl; eapply getenv_interp;
  lazymatch goal with
  | |- list_assoc _ _ = _ => vm_compute list_assoc; reflexivity
  | |- Maps.PTree.get _ _ = _ => vm_compute Maps.PTree.get; reflexivity
  | |- _ => eauto
  end.

Ltac isolate_sf_bl :=
  let namea := fresh "sfa" in
  let nameb := fresh "sfb" in
  lazymatch goal with
  | WFSFA: wf_sf _ _ ?sfa, WFSFB: wf_sf _ _ ?sfb
    |- getenv _ (interp_cycle _ _ ?xa) _ = getenv _ (interp_cycle _ _ ?xb) _
    =>
    set (namea := xa); fold namea in WFSFA; subst sfa; vm_compute in namea;
    rename namea into sfa;
    set (nameb := xb); fold nameb in WFSFB; subst sfb; vm_compute in nameb;
    rename nameb into sfb
  | WFSFA: wf_sf _ _ ?sfa, WFSFB: wf_sf _ _ ?sfb
    |- getenv _ (interp_cycle _ _ ?xa) _ = getenv _ (interp_cycle _ _ ?xb) _
    =>
    set (namea := xa); fold namea in WFSFA;
    set (nameb := xb); fold nameb in WFSFB
  end.

Ltac isolate_sf_named_bl namea nameb :=
  lazymatch goal with
  | |- getenv _ (interp_cycle _ _ ?xa) _ = getenv _ (interp_cycle _ _ ?xb) _
    =>
      set (namea := xa); set (nameb := xb)
  end.

Ltac full_pass_bl := simplify_bl; prune_bl; collapse_bl.
Ltac crusher_bl strength :=
  exploit_hypotheses_bl; isolate_sf_bl;
  lazymatch strength with
  | 0 => idtac | 1 => do 1 full_pass_bl | 2 => do 2 full_pass_bl
  | 3 => do 3 full_pass_bl | 4 => do 4 full_pass_bl | 5 => do 5 full_pass_bl
  | 6 => do 6 full_pass_bl | 7 => do 7 full_pass_bl | 8 => do 8 full_pass_bl
  | 9 => do 9 full_pass_bl | 10 => do 10 full_pass_bl | 11 => do 11 full_pass_bl
  | 12 => do 12 full_pass_bl | 13 => do 13 full_pass_bl | 14 => do 14 full_pass_bl
  | 15 => do 15 full_pass_bl | 16 => do 16 full_pass_bl | 17 => do 17 full_pass_bl
  | 18 => do 18 full_pass_bl | 19 => do 19 full_pass_bl | 20 => do 20 full_pass_bl
  | _ => fail "max strength = 20"
  end;
  finish_bl.

Ltac simplify_careful_bl :=
  isolate_sf_bl; simplify_careful_t; symmetry; simplify_careful_t; symmetry;
  update_wfsf_bl.

Ltac full_pass_c_bl :=
  simplify_careful_bl; collapse_bl; prune_bl; isolate_sf_bl.
Ltac crusher_c_bl strength :=
  exploit_hypotheses_bl;
  lazymatch strength with
  | 0 => idtac | 1 => do 1 full_pass_c_bl | 2 => do 2 full_pass_c_bl
  | 3 => do 3 full_pass_c_bl | 4 => do 4 full_pass_c_bl | 5 => do 5 full_pass_c_bl
  | 6 => do 6 full_pass_c_bl | 7 => do 7 full_pass_c_bl | 8 => do 8 full_pass_c_bl
  | 9 => do 9 full_pass_c_bl | 10 => do 10 full_pass_c_bl | 11 => do 11 full_pass_c_bl
  | 12 => do 12 full_pass_c_bl | 13 => do 13 full_pass_c_bl | 14 => do 14 full_pass_c_bl
  | 15 => do 15 full_pass_c_bl | 16 => do 16 full_pass_c_bl | 17 => do 17 full_pass_c_bl
  | 18 => do 18 full_pass_c_bl | 19 => do 19 full_pass_c_bl | 20 => do 20 full_pass_c_bl
  | _ => fail "max strength = 20"
  end;
  finish_bl.

(* Ltac search_subterm_bl needle haystack pos orig_haystack Ppos := *)
(*   lazymatch haystack with *)
(*   | needle => eval vm_compute in (ssprop_one pos needle orig_haystack Ppos) *)
(*   | SBinop _ ?a ?b => *)
(*     let p1 := *)
(*       search_subterm needle a (Direction.branch1 :: pos) orig_haystack *)
(*       (subact_at_pos_binop1 _ _ _ _ _ Ppos) *)
(*     in *)
(*     let p2 := *)
(*       search_subterm needle b (Direction.branch2 :: pos) orig_haystack *)
(*       (subact_at_pos_binop2 _ _ _ _ _ Ppos) *)
(*     in *)
(*     eval vm_compute in *)
(*       (existT _ _ (sprop_binop needle pos _ _ _ (projT2 p1) (projT2 p2))) *)
(*   | SConst _ => eval vm_compute in (ssprop_nil needle orig_haystack pos) *)
(*   | SUnop _ ?a => *)
(*     let p := *)
(*       search_subterm *)
(*         needle a (Direction.branch1 :: pos) orig_haystack *)
(*         (subact_at_pos_unop1 _ _ _ _ Ppos) *)
(*     in *)
(*     eval vm_compute in (existT _ _ (sprop_unop needle pos _ _ (projT2 p))) *)
(*   | SVar _ => eval vm_compute in (ssprop_nil needle orig_haystack pos) *)
(*   | SIf ?a ?b ?c => *)
(*     let p1 := *)
(*       search_subterm needle a (Direction.branch1 :: pos) orig_haystack *)
(*         (subact_at_pos_if1 _ _ _ _ _ Ppos) *)
(*     in *)
(*     let p2 := *)
(*       search_subterm needle b (Direction.branch2 :: pos) orig_haystack *)
(*         (subact_at_pos_if2 _ _ _ _ _ Ppos) *)
(*     in *)
(*     let p3 := *)
(*       search_subterm needle c (Direction.branch3 :: pos) orig_haystack *)
(*         (subact_at_pos_if3 _ _ _ _ _ Ppos) *)
(*     in *)
(*     eval vm_compute in *)
(*       (existT _ _ *)
(*         (sprop_if needle pos _ _ _ _ (projT2 p1) (projT2 p2) (projT2 p3))) *)
(*   | SReg _ => eval vm_compute in (ssprop_nil needle orig_haystack pos) *)
(*   | SExternalCall _ ?a => *)
(*     let p := *)
(*       search_subterm needle a (Direction.branch1 :: pos) orig_haystack *)
(*       (subact_at_pos_extcall1 _ _ _ _ Ppos) *)
(*     in *)
(*     eval vm_compute in (existT _ _ (sprop_unop needle pos _ _ (projT2 p))) *)
(*   end. *)

(* Ltac ssearch_bl needle haystack := *)
(*   let hs := eval vm_compute in haystack in *)
(*   let res := *)
(*     search_subterm *)
(*       needle hs ([]: list Direction.direction) hs (subact_at_pos_rev_refl hs) in *)
(*   res. *)

(* Ltac ssearch_in_elems_bl needle l := *)
(*   lazymatch l with *)
(*   | [] => eval vm_compute in (ssearch_in_elemsT_nil needle) *)
(*   | (?kk, (?tt, ?x))::?r => *)
(*     let ps := ssearch needle x in *)
(*     let pss := ssearch_in_elems needle r in *)
(*     eval vm_compute in (ssearch_in_elemsT_cons needle r kk tt _ _ pss ps) *)
(*   end. *)

(* Ltac ssearch_in_vars_bl needle t H := *)
(*   let vars := eval vm_compute in (Maps.PTree.elements t) in *)
(*   let res := ssearch_in_elems needle vars in *)
(*   let res := eval vm_compute in res in *)
(*   let x := eval vm_compute in (projT1 res) in *)
(*   let P := eval vm_compute in (projT2 res) in *)
(*   let positions := fresh "positions" in *)
(*   set (positions := x); *)
(*   assert (H : *)
(*     Forall2 ( *)
(*       fun '(k, (ty, a)) '(k1, ps) => *)
(*         k = k1 /\ *)
(*         (fun '(_, a) ps => *)
(*           ReplaceSubact.search_subterm_propP needle a [] ps) (ty, a) ps *)
(*     ) (Maps.PTree.elements t) positions) by exact P. *)

(* Ltac get_subact_ok_bl needle vars rep t := *)
(*   match goal with *)
(*   | WTRENV : Wt.wt_renv ?R ?REnv ?ctx, *)
(*     WFSF: wf_sf ?R ?ext_Sigma ?sf, *)
(*     wt_sigma : (forall (ufn : ?ext_fn_t) (vc : val), *)
(*     wt_val (arg1Sig (?ext_Sigma ufn)) vc *)
(*     -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)) *)
(*     |- _ => *)
(*       let H := fresh in *)
(*       ssearch_in_vars needle vars H; *)
(*       generalize ( *)
(*         ReplaceSubact.subact_ok_ltac *)
(*           (REnv:=REnv) R ext_Sigma ctx ext_sigma _ _ _ H rep t *)
(*       ); clear H *)
(*   end. *)

(* Ltac ssearch_in_var_bl needle t k rep ty := *)
(*   match goal with *)
(*   | WTRENV : Wt.wt_renv ?R ?REnv ?ctx, *)
(*     WFSF: wf_sf ?R ?ext_Sigma ?sf, *)
(*     wt_sigma : ( *)
(*       forall (ufn : ?ext_fn_t) (vc : val), *)
(*       wt_val (arg1Sig (?ext_Sigma ufn)) vc *)
(*       -> wt_val (retSig (?ext_Sigma ufn)) (?ext_sigma ufn vc)) *)
(*     |- _ => *)
(*       let res := eval vm_compute in (Maps.PTree.get k t) in *)
(*       match res with *)
(*       | Some (?itt, ?ix) => *)
(*         let res := ssearch needle ix in *)
(*         let x := eval vm_compute in (projT1 res) in *)
(*         let P := eval vm_compute in (projT2 res) in *)
(*         let positions := fresh "positions" in *)
(*         set (positions := x); *)
(*         set (HP := P); *)
(*         generalize ( *)
(*           fun pf => *)
(*             ReplaceSubact.subact_ok_ltac_1var *)
(*               (REnv:=REnv) R ext_Sigma ctx ext_sigma t _ k itt _ positions pf HP *)
(*               rep ty *)
(*         ); clear HP *)
(*       end *)
(*   end. *)
