Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.KoikaForm.Syntax.

Section DesugaredSyntax.
  Context {pos_t var_t rule_name_t fn_name_t: Type}.
  Context {var_t_eq_dec: EqDec var_t}.

  Inductive daction {reg_t ext_fn_t} :=
  | DError (err: error pos_t var_t fn_name_t)
  | DFail (tau: type)
  | DVar (var: var_t)
  | DConst (tau:type) (v: val)
  | DAssign (v: var_t) (ex: daction)
  | DSeq (a1 a2: daction)
  | DBind (v: var_t) (ex: daction) (body: daction)
  | DIf (cond: daction) (tbranch: daction) (fbranch: daction)
  | DRead (port: Port) (idx: reg_t)
  | DWrite (port: Port) (idx: reg_t) (value: daction)
  | DUnop (ufn1: PrimUntyped.ufn1) (arg1: daction)
  | DBinop (ufn2: PrimUntyped.ufn2) (arg1: daction) (arg2: daction)
  | DExternalCall (ufn: ext_fn_t) (arg: daction)
  | DInternalCall
    (ufn: InternalFunction var_t fn_name_t daction) (args: list daction)
  | DAPos (p: pos_t) (e: daction).

  Definition map_error {A B: Type} (f: A -> option B) :=
    fix map_error (l: list A) {struct l}: option (list B) :=
      match l with
      | [] => Some []
      | a::r =>
        let/opt fr := map_error r in
        let/opt fa := f a in
        Some (fa::fr)
      end.

  Fixpoint uaction_to_daction
    {reg_t ext_fn_t} (ua: @uaction pos_t var_t fn_name_t reg_t ext_fn_t)
    {struct ua}
  : option (@daction reg_t ext_fn_t) :=
    match ua with
    | UError err => Some (DError err)
    | UFail t => Some (DFail t)
    | UVar v => Some (DVar v)
    | @UConst _ _ _ _ _ t cst => Some (DConst t (val_of_value cst))
    | UAssign v e =>
      let/opt de := uaction_to_daction e in
      Some (DAssign v de)
    | USeq s1 s2 =>
      let/opt ds1 := uaction_to_daction s1 in
      let/opt ds2 := uaction_to_daction s2 in
      Some (DSeq ds1 ds2)
    | UBind v e body =>
      let/opt de := uaction_to_daction e in
      let/opt dbody := uaction_to_daction body in
      Some (DBind v de dbody)
    | UIf c t f =>
      let/opt dc := uaction_to_daction c in
      let/opt dt := uaction_to_daction t in
      let/opt df := uaction_to_daction f in
      Some (DIf dc dt df)
    | URead prt idx => Some (DRead prt idx)
    | UWrite prt idx v =>
      let/opt dv := uaction_to_daction v in
      Some (DWrite prt idx dv)
    | UUnop fn a =>
      let/opt da := uaction_to_daction a in
      Some (DUnop fn da)
    | UBinop fn a1 a2 =>
      let/opt da1 := uaction_to_daction a1 in
      let/opt da2 := uaction_to_daction a2 in
      Some (DBinop fn da1 da2)
    | UExternalCall ufn a =>
      let/opt da := uaction_to_daction a in
      Some (DExternalCall ufn da)
    | UInternalCall ufn args =>
      let/opt dargs := map_error uaction_to_daction args in
      let/opt dbody := uaction_to_daction (int_body ufn) in
      Some (DInternalCall {|
        int_name := int_name ufn; int_argspec := int_argspec ufn;
        int_retSig := int_retSig ufn; int_body := dbody
      |} dargs)
    | UAPos p e =>
      let/opt de := uaction_to_daction e in
      Some (DAPos p de)
    | USugar _ => None
    end.

  Section daction_ind'.
    Context {reg_t ext_fn_t: Type}.
    Variable P: daction (reg_t := reg_t) (ext_fn_t := ext_fn_t) -> Prop.

    Hypothesis DError_case: forall err, P (DError err).
    Hypothesis DFail_case: forall tau, P (DFail tau).
    Hypothesis DVar_case: forall var, P (DVar var).
    Hypothesis DConst_case: forall t v, P (DConst t v).
    Hypothesis DAssign_case: forall v ex, P ex -> P (DAssign v ex).
    Hypothesis DSeq_case: forall a1 a2, P a1 -> P a2 -> P (DSeq a1 a2).
    Hypothesis DBind_case:
      forall v ex body, P ex -> P body -> P (DBind v ex body).
    Hypothesis DIf_case:
      forall cond tbranch fbranch,
      P cond -> P tbranch -> P fbranch -> P (DIf cond tbranch fbranch).
    Hypothesis DRead_case: forall port idx, P (DRead port idx).
    Hypothesis DWrite_case:
      forall port idx value, P value -> P (DWrite port idx value).
    Hypothesis DUnop_case: forall ufn1 arg1, P arg1 -> P (DUnop ufn1 arg1).
    Hypothesis DBinop_case:
      forall ufn2 arg1 arg2, P arg1 -> P arg2 -> P (DBinop ufn2 arg1 arg2).
    Hypothesis DExternalCall_case:
      forall ufn arg, P arg -> P (DExternalCall ufn arg).
    Hypothesis DInternalCall_case:
      forall ufn args,
      P (int_body ufn) -> Forall P args -> P (DInternalCall ufn args).
    Hypothesis DAPos_case: forall p e, P e -> P (DAPos p e).

    Fixpoint daction_ind' ua: P ua :=
      match ua with
      | DError err => DError_case err
      | DFail tau => DFail_case tau
      | DVar var => DVar_case var
      | DConst t cst => DConst_case t cst
      | DAssign v ex => DAssign_case v ex (daction_ind' ex)
      | DSeq a1 a2 => DSeq_case a1 a2 (daction_ind' a1) (daction_ind' a2)
      | DBind v ex body =>
        DBind_case v ex body (daction_ind' ex) (daction_ind' body)
      | DIf cond tbranch fbranch =>
        DIf_case cond tbranch fbranch (daction_ind' cond) (daction_ind' tbranch)
          (daction_ind' fbranch)
      | DRead port idx => DRead_case port idx
      | DWrite port idx value => DWrite_case port idx value (daction_ind' value)
      | DUnop ufn1 arg1 => DUnop_case ufn1 arg1 (daction_ind' arg1)
      | DBinop ufn2 arg1 arg2 =>
        DBinop_case ufn2 arg1 arg2 (daction_ind' arg1) (daction_ind' arg2)
      | DExternalCall ufn arg => DExternalCall_case ufn arg (daction_ind' arg)
      | DInternalCall ufn args =>
        DInternalCall_case ufn args (daction_ind' (int_body ufn)) ((
          fix daction_list_ind' args: Forall P args :=
            match args with
            | [] => Forall_nil P
            | h::t => Forall_cons (h) (daction_ind' h) (daction_list_ind' t)
            end
        ) args)
      | DAPos p e => DAPos_case p e (daction_ind' e)
      end.
  End daction_ind'.
End DesugaredSyntax.
