(*! End-to-end correctness theorem !*)
Require Import Koika.Properties.CompilerCorrectness.CircuitCorrectness.
Require Import Koika.Properties.CompilerCorrectness.LoweringCorrectness.
Require Import Koika.Utils.Common.
Require Import Koika.KoikaForm.Types.
Require Import Koika.Utils.Environments.
Require Import Koika.KoikaForm.Logs.
Require Import Koika.LoweredForm.Lowering.
Require Import Koika.CircuitForm.Generation.
Require Import Koika.CircuitForm.Optimization.
Require Import Koika.Compiler.

Section Thm.
  Context {pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t: Type}.
  Context {eq_dec_var_t: EqDec var_t}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.
  Context {FiniteType_reg_t: FiniteType reg_t}.
  Context {Show_var_t : Show var_t}.
  Context {Show_rule_name_t : Show rule_name_t}.

  Context (r: ContextEnv.(env_t) R).
  Context (sigma: forall f, Sig_denote (Sigma f)).

  Notation CR := (lower_R R).
  Notation CSigma := (lower_Sigma Sigma).

  Notation cr := (lower_r r).
  Notation csigma := (lower_sigma sigma).

  Context (lco: (@local_circuit_optimizer
                   rule_name_t reg_t ext_fn_t
                   CR CSigma
                   (rwdata (rule_name_t := rule_name_t) CR CSigma)
                   (lower_sigma sigma))).

  Section Standalone.
    Context (s: Syntax.scheduler pos_t rule_name_t).
    Context (rules: rule_name_t -> TypedSyntax.rule pos_t var_t fn_name_t R Sigma).
    Context (external: rule_name_t -> bool).

    Theorem compiler_correct:
      let spec_results := TypedSemantics.interp_cycle sigma rules s r in
      let circuits := compile_scheduler lco rules external s in
      forall reg,
        interp_circuit cr csigma (ContextEnv.(getenv) circuits reg) =
        bits_of_value (ContextEnv.(getenv) spec_results reg).
    Proof.
      cbv zeta; intros.
      setoid_rewrite compile_scheduler'_correct.
      - rewrite cycle_lowering_correct.
        unfold lower_r, lower_log; rewrite getenv_map; reflexivity.
      - apply circuit_env_equiv_CReadRegister.
    Qed.
  End Standalone.
End Thm.
