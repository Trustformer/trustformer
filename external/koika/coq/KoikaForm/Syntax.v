(*! Frontend | Untyped syntax !*)
Require Export Koika.Utils.Common.
Require Export Koika.Primitives.
Require Export Koika.KoikaForm.Types.
Require Export Koika.KoikaForm.ErrorReporting.
Require Import Koika.KoikaForm.SimpleVal.

Section Syntax.
  Context {pos_t var_t rule_name_t fn_name_t: Type}.
  Context {var_t_eq_dec: EqDec var_t}.

  Class Lift {from to: Type} := lift: from -> to.
  Class Inj {from to: Type} (f: from -> to) :=
    inj: forall i j, i <> j -> f i <> f j.
  Hint Mode Lift - ! : typeclass_instances.

  Inductive uaction {reg_t ext_fn_t} :=
  | UError (err: error pos_t var_t fn_name_t)
  | UFail (tau: type)
  | UVar (var: var_t)
  | UConst {tau: type} (cst: type_denote tau)
  | UAssign (v: var_t) (ex: uaction)
  | USeq (a1 a2: uaction)
  | UBind (v: var_t) (ex: uaction) (body: uaction)
  | UIf (cond: uaction) (tbranch: uaction) (fbranch: uaction)
  | URead (port: Port) (idx: reg_t)
  | UWrite (port: Port) (idx: reg_t) (value: uaction)
  | UUnop (ufn1: PrimUntyped.ufn1) (arg1: uaction)
  | UBinop (ufn2: PrimUntyped.ufn2) (arg1: uaction) (arg2: uaction)
  | UExternalCall (ufn: ext_fn_t) (arg: uaction)
  | UInternalCall (ufn: InternalFunction var_t fn_name_t uaction)
    (args: list uaction)
  | UAPos (p: pos_t) (e: uaction)
  | USugar (s: usugar)
  with usugar {reg_t ext_fn_t} :=
  | UErrorInAst
  | USkip
  | UConstBits {sz} (bs: bits sz)
  | UConstString (s: string)
  | UConstEnum (sig: enum_sig) (cst: string)
  | UProgn (aa: list uaction)
  | ULet (bindings: list (var_t * uaction)) (body: uaction)
  | UWhen (cond: uaction) (body: uaction)
  | USwitch (var: uaction) (default: uaction)
    (branches: list (uaction * uaction))
  | UStructInit (sig: struct_sig) (fields: list (string * uaction))
  | UArrayInit (tau: type) (elements: list uaction)
  | UCallModule {module_reg_t module_ext_fn_t: Type}
    `{finite_reg: FiniteType module_reg_t} (fR: module_reg_t -> reg_t)
    (fSigma: @Lift module_ext_fn_t ext_fn_t)
    (fn: InternalFunction var_t fn_name_t (
      @uaction module_reg_t module_ext_fn_t
    )) (args: list uaction).

  Section uaction_ind'.
    Context {reg_t ext_fn_t: Type}.
    Variable P: uaction (reg_t := reg_t) (ext_fn_t := ext_fn_t) -> Prop.

    Hypothesis UError_case: forall err, P (UError err).
    Hypothesis UFail_case: forall tau, P (UFail tau).
    Hypothesis UVar_case: forall var, P (UVar var).
    Hypothesis UConst_case: forall tau cst, P (UConst (tau := tau) cst).
    Hypothesis UAssign_case: forall v ex, P ex -> P (UAssign v ex).
    Hypothesis USeq_case: forall a1 a2, P a1 -> P a2 -> P (USeq a1 a2).
    Hypothesis UBind_case:
      forall v ex body, P ex -> P body -> P (UBind v ex body).
    Hypothesis UIf_case:
      forall cond tbranch fbranch,
      P cond -> P tbranch -> P fbranch -> P (UIf cond tbranch fbranch).
    Hypothesis URead_case: forall port idx, P (URead port idx).
    Hypothesis UWrite_case:
      forall port idx value, P value -> P (UWrite port idx value).
    Hypothesis UUnop_case: forall ufn1 arg1, P arg1 -> P (UUnop ufn1 arg1).
    Hypothesis UBinop_case:
      forall ufn2 arg1 arg2, P arg1 -> P arg2 -> P (UBinop ufn2 arg1 arg2).
    Hypothesis UExternalCall_case:
      forall ufn arg, P arg -> P (UExternalCall ufn arg).
    Hypothesis UInternalCall_case:
      forall ufn args,
      P (int_body ufn) -> Forall P args -> P (UInternalCall ufn args).
    Hypothesis UAPos_case: forall p e, P e -> P (UAPos p e).
    (* We don't care about the mutually inductive part. *)
    Hypothesis USugar_case: forall s, P (USugar s).

    Fixpoint uaction_ind' ua: P ua :=
      match ua with
      | UError err => UError_case err
      | UFail tau => UFail_case tau
      | UVar var => UVar_case var
      | @UConst _ _ tau cst => UConst_case tau cst
      | UAssign v ex => UAssign_case v ex (uaction_ind' ex)
      | USeq a1 a2 => USeq_case a1 a2 (uaction_ind' a1) (uaction_ind' a2)
      | UBind v ex body =>
        UBind_case v ex body (uaction_ind' ex) (uaction_ind' body)
      | UIf cond tbranch fbranch =>
        UIf_case cond tbranch fbranch (uaction_ind' cond) (uaction_ind' tbranch)
          (uaction_ind' fbranch)
      | URead port idx => URead_case port idx
      | UWrite port idx value => UWrite_case port idx value (uaction_ind' value)
      | UUnop ufn1 arg1 => UUnop_case ufn1 arg1 (uaction_ind' arg1)
      | UBinop ufn2 arg1 arg2 =>
        UBinop_case ufn2 arg1 arg2 (uaction_ind' arg1) (uaction_ind' arg2)
      | UExternalCall ufn arg => UExternalCall_case ufn arg (uaction_ind' arg)
      | UInternalCall ufn args =>
        UInternalCall_case ufn args (uaction_ind' (int_body ufn)) ((
          fix uaction_list_ind' args: Forall P args :=
            match args with
            | [] => Forall_nil P
            | h::t => Forall_cons (h) (uaction_ind' h) (uaction_list_ind' t)
            end
        ) args)
      | UAPos p e => UAPos_case p e (uaction_ind' e)
      | USugar s => USugar_case s
      end.
  End uaction_ind'.

  Inductive scheduler :=
  | Done
  | Cons (r: rule_name_t) (s: scheduler)
  | Try (r: rule_name_t) (s1 s2: scheduler)
  | SPos (p: pos_t) (s: scheduler).
End Syntax.

Arguments Lift: clear implicits.
Arguments usugar: clear implicits.
Arguments uaction: clear implicits.
Arguments scheduler: clear implicits.
