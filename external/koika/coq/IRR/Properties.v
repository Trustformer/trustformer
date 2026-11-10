Require Import Koika.IRR.Interpretation.
Require Import Koika.KoikaForm.Desugaring.DesugaredSyntax.
Require Import Koika.KoikaForm.Syntax.
Require Import Koika.KoikaForm.Types.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.Utils.EqDec.
Require Import Koika.Utils.Environments.
Require Import Koika.Utils.Maps.
Require Import Koika.Utils.Tactics.
Require Import Koika.IRR.IRR.

Section Properties.
  Context {pos_t reg_t ext_fn_t rule_name_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {ext_fn_t_eq_dec: EqDec ext_fn_t}.
  Context {REnv: Env reg_t}.

  Context (R: reg_t -> type).
  Context (Sigma: ext_fn_t -> ExternalSignature).

  Definition uact := @daction pos_t string string reg_t ext_fn_t.
  Definition schedule := scheduler pos_t rule_name_t.
  Definition ext_funs_defs :=
    forall f: ext_fn_t, val -> val.
  Definition UREnv := REnv.(env_t) (fun _ => val).

  Context (r: UREnv).
  Context (sigma: ext_funs_defs).

  Lemma eval_remove_var:
    forall vvs fuel a n, ~ reachable_var vvs a n
    -> eval_sact r sigma vvs a fuel
    = eval_sact r sigma (PTree.remove n vvs) a fuel.
  Proof.
    induction fuel; simpl; intros; eauto.
    destruct a; simpl; intros; eauto.
    - rewrite PTree.gro. unfold opt_bind; repeat destr. apply IHfuel.
      intro REACH.
      apply H. econstructor; eauto.
      intro; subst. apply H. econstructor.
    - rewrite <- ! IHfuel. eauto.
      intro REACH; apply H. apply reachable_var_if_false; auto.
      intro REACH; apply H. apply reachable_var_if_true; auto.
      intro REACH; apply H. apply reachable_var_if_cond; auto.
    - rewrite <- ! IHfuel. eauto.
      intro REACH; apply H. apply reachable_var_unop; auto.
    - rewrite <- ! IHfuel. eauto.
      intro REACH; apply H. apply reachable_var_binop2; auto.
      intro REACH; apply H. apply reachable_var_binop1; auto.
    - rewrite <- ! IHfuel. eauto.
      intro REACH; apply H. apply reachable_var_externalCall; auto.
  Qed.

  Lemma reachable_remove:
    forall a vvs a0 a1 (RR : reachable_var (PTree.remove a0 vvs) a a1),
    Interpretation.reachable_var
      (reg_t := reg_t) (ext_fn_t := ext_fn_t) vvs a a1.
  Proof.
    induction 1; simpl; intros; eauto.
    - constructor.
    - rewrite PTree.grspec in H. destr_in H. congruence. econstructor; eauto.
    - eapply reachable_var_if_cond; eauto.
    - eapply reachable_var_if_true; eauto.
    - eapply reachable_var_if_false; eauto.
    - eapply reachable_var_binop1; eauto.
    - eapply reachable_var_binop2; eauto.
    - eapply reachable_var_unop; eauto.
    - eapply reachable_var_externalCall; eauto.
  Qed.

  Lemma eval_remove_vars:
    forall fuel a l vvs, Forall (fun n => ~ reachable_var vvs a n) l
    -> eval_sact r sigma vvs a fuel
    = eval_sact r sigma (fold_left (fun t n => PTree.remove n t) l vvs) a fuel.
  Proof.
    induction l; simpl; intros; eauto. inv H.
    rewrite <- IHl. eapply eval_remove_var. eauto.
    eapply Forall_impl; eauto. simpl.
    intros a1 NR RR; apply NR; clear NR.
    eapply reachable_remove; eauto.
  Qed.

  Record wf_sf (sf: IRR (rule_name_t := rule_name_t)) := {
    wf_sf_wt: wt_vvs (Sigma:=Sigma) R (vars sf);
    wf_sf_vvs: vvs_smaller_variables (vars sf);
    wf_sf_final: forall reg k,
      BitsToLists.list_assoc (final_values sf) reg = Some k
      -> wt_sact (Sigma:=Sigma) R (vars sf) (SVar k) (R reg)
  }.
End Properties.
