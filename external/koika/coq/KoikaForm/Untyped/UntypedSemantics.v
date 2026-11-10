(*! Language | Untyped semantics of typed Kôika programs !*)
Require Export Koika.Utils.Common.
Require Export Koika.Utils.Environments.
Require Export Koika.KoikaForm.Syntax.
Require Export Koika.KoikaForm.Untyped.UntypedLogs.
Require Import Koika.BitsToLists.
Require Import Koika.KoikaForm.Desugaring.DesugaredSyntax.
Require Import Koika.KoikaForm.Desugaring.Desugaring.
Require Import Koika.KoikaForm.SyntaxMacros.
Require TypeInference.
Require TypedSemantics.
Import PrimTyped.
Import PrimUntyped.
Require Import SimpleVal.

Fixpoint size_uaction
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t) {struct ua}
: nat :=
  match ua  with
  | UError err => 0
  | UFail tau => 0
  | UVar var => 0
  | UConst cst => 0
  | UAssign v ex => 1 + size_uaction ex
  | USeq a1 a2 => 1 + size_uaction a1 + size_uaction a2
  | UBind v ex body => 1 + size_uaction ex + size_uaction body
  | UIf cond tbranch fbranch =>
    1 + size_uaction cond + size_uaction tbranch + size_uaction fbranch
  | URead port idx => 0
  | UWrite port idx value => 1 + size_uaction value
  | UUnop ufn1 arg1 => 1 + size_uaction arg1
  | UBinop ufn2 arg1 arg2 => 1 + size_uaction arg1 + size_uaction arg2
  | UExternalCall ufn arg => 1 + size_uaction arg
  | UInternalCall ufn args =>
    1 + size_uaction (int_body ufn) + list_sum (map size_uaction args)
  | UAPos p e => 1 + size_uaction e
  | USugar s => 1 + size_sugar s
  end
with size_sugar
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (s: usugar pos_t var_t fn_name_t reg_t ext_fn_t) {struct s}
: nat :=
   match s with
   | UErrorInAst => 0
   | USkip => 0
   | UConstBits _ => 0
   | UConstString _ => 0
   | UConstEnum _ _ => 0
   | UProgn l => 1 + list_sum (map size_uaction l)
   | ULet bindings body =>
     1 + size_uaction body
     + list_sum (map (fun '(_, a) => size_uaction a) bindings)
   | UWhen cond body => size_uaction cond + size_uaction body
   | USwitch cond default branches =>
     1 + size_uaction cond + size_uaction default
     + list_sum
       (map (fun '(a,b) => S (size_uaction a + size_uaction b)) branches)
   | UStructInit sig l => 1 + list_sum (map (fun '(_, a) => size_uaction a) l)
   | UArrayInit tay l => 1 + list_sum (map size_uaction l)
   | UCallModule fR fSigma fn args =>
     1 + size_uaction (int_body fn) + list_sum (map size_uaction args)
   end.

Definition usigma1' (fn: PrimUntyped.ubits1) (bs: list bool)
: (list bool) :=
  match fn with
  | UNot => (List.map negb bs)
  | USExt w =>
    let msb := List.last bs false in
    (bs ++ List.repeat msb (w - List.length bs))
  | UZExtL w => (bs ++ List.repeat false (w - List.length bs))
  | UZExtR w => (List.repeat false (w - List.length bs) ++ bs)
  | URepeat times => (List.concat (List.repeat bs times))
  | USlice ofs w =>
    (* Remove unrequired bits *)
    let '(_, bs) := take_drop' ofs bs in
    let '(bs, _) := take_drop' w bs in
    (* Append zeros for the padding. Note that the way padding is used here
       makes situations in which the last requested bit it out-of-bounds
       legal. *)
    (bs ++ List.repeat false (w - List.length bs))
  end.

Definition usigma1 fn v : option val :=
  match v with
  | Bits bs => let res := usigma1' fn bs in Some (Bits res)
  | _ => None
  end.

Definition sigma1 (fn: PrimUntyped.ufn1) : val -> option val :=
  match fn with
  | PrimUntyped.UDisplay fn =>
    match fn with
    | PrimUntyped.UDisplayUtf8 => fun _ => Some (Bits [])
    | PrimUntyped.UDisplayValue _ => fun _ => Some (Bits [])
    end
  | PrimUntyped.UConv fn =>
    match fn with
    | PrimUntyped.UPack => fun v =>
      let bs := ubits_of_value v in Some (Bits bs)
    | PrimUntyped.UUnpack tau =>
      fun bs =>
        match bs with
        | Bits bs => let/opt v := uvalue_of_bits (tau:=tau) bs in Some v
        | _ => None
        end
    | PrimUntyped.UIgnore => fun _ => Some (Bits [])
    | PrimUntyped.UId s => fun bs => Some bs
    end
  | PrimUntyped.UBits1 fn => usigma1 fn
  | PrimUntyped.UStruct1 (PrimUntyped.UGetField f) => fun v => get_field v f
  | PrimUntyped.UStruct1 (UGetFieldBits sig f) =>
    fun v =>
      let/opt2 ofs, sz := find_field_offset_right (struct_fields sig) f in
      usigma1 (USlice ofs sz) v
  | PrimUntyped.UArray1 (PrimUntyped.UGetElement idx) =>
    fun v =>
      match v with
      | Array sig l => List.nth_error l idx
      | _ => None
      end
  | PrimUntyped.UArray1 (PrimUntyped.UGetElementBits sig idx) =>
    fun v =>
      usigma1
        (USlice (element_sz sig * (array_len sig - S idx)) (element_sz sig)) v
  end.

Lemma take_drop_impl_take_drop':
  forall {A} (l: list A) n (l1 l2: list A),
  take_drop n l = Some (l1, l2) -> take_drop' n l = (l1, l2).
Proof.
  induction l; intros.
  - destruct n; inv H; auto.
  - destruct n; inv H; auto.
    destruct (take_drop n l) eqn:?; inv H1. destruct p. inv H0.
    apply take_drop'_cons. auto.
Qed.

Lemma usigma1_correct:
  forall ufn fn,
  PrimTypeInference.tc1 ufn (arg1Sig (PrimSignatures.Sigma1 fn)) = Success fn
  -> forall (arg: arg1Sig (PrimSignatures.Sigma1 fn)) ret,
  PrimSpecs.sigma1 fn arg = ret
  -> sigma1 ufn (val_of_value arg) = Some (val_of_value ret).
Proof.
  destruct ufn; simpl; intros.
  - destruct fn.
    + destr_in H; try congruence. inv H. simpl in *. inv Heqr. subst.
      reflexivity.
    + subst. inv H.
      revert arg. rewrite <- H1. simpl.
      intro arg. reflexivity.
  - destruct fn.
    + inv H. revert arg. rewrite <- H2. simpl.
      intros. f_equal. f_equal.
      erewrite ubits_of_value_ok; eauto.
    + inv H.
      generalize (wt_val_of_value _ arg). simpl. inversion 1; subst.
      rewrite uvalue_of_bits_val_of_value. simpl. auto.
    + inv H. revert arg. rewrite <- H2. simpl.
      intros. f_equal.
    + inv H. revert arg. rewrite <- H2. simpl. auto.
  - subst. destr_in H. inv H. simpl in *. inv Heqr.
    revert arg. rewrite <- H0. simpl. destruct fn; simpl in *; intros.
    + f_equal.
      f_equal. rewrite <- vect_to_list_map. f_equal.
    + f_equal. f_equal.
      unfold Bits.extend_end. simpl.
      rewrite vect_to_list_eq_rect.
      rewrite vect_to_list_app. f_equal.
      rewrite vect_to_list_length.
      rewrite repeat_bits_const. f_equal. f_equal.
      rewrite msb_spec; auto.
    + f_equal. f_equal.
      * unfold Bits.extend_end. simpl.
        unfold eq_rect.
        refine (
          match vect_extend_end_cast s width with
          | eq_refl => _
          end
        ).
        rewrite vect_to_list_app. f_equal.
        rewrite vect_to_list_length.
        rewrite repeat_bits_const. f_equal.
    + f_equal. f_equal.
      * unfold Bits.extend_beginning. simpl.
        unfold eq_rect.
        refine (
          match vect_extend_beginning_cast s width with
          | eq_refl => _
          end
        ).
        rewrite vect_to_list_app. f_equal.
        rewrite vect_to_list_length.
        rewrite repeat_bits_const. f_equal.
    + f_equal. f_equal.
      * induction times; simpl; auto.
        rewrite vect_to_list_app. f_equal. eauto.
    + destruct (take_drop' offset (vect_to_list arg)) as (l1 & l2) eqn:Heq1.
      destruct (take_drop' width l2) as (l3 & l4) eqn:Heq2.
      inversion Heq1. inversion Heq2. rewrite H2. rewrite H3.
      f_equal. f_equal.
      unfold Bits.slice.
      rewrite vect_extend_end_firstn.
      unfold Bits.extend_end.
      rewrite vect_to_list_eq_rect.
      rewrite vect_to_list_app.
      rewrite vect_firstn_to_list.
      rewrite vect_skipn_to_list.
      unfold take_drop' in Heq1. inv Heq1. inv Heq2.
      simpl.
      rewrite <- repeat_bits_const.
      f_equal. f_equal. f_equal. rewrite firstn_length. rewrite skipn_length. rewrite vect_to_list_length.
      reflexivity.
    + inv H.
  - destr_in H.
    + repeat destr_in H; inv H.
      simpl in Heqr. clear Heqr. simpl in arg.
      simpl PrimSpecs.sigma1.
      simpl.
      unfold PrimTypeInference.find_field in Heqr0. unfold opt_result in Heqr0.
      destr_in Heqr0; inv Heqr0.
      revert s0 Heqo arg. destruct s. simpl. clear.
      induction struct_fields; intros; eauto. easy.
      destruct a. destruct arg.

      simpl. simpl in Heqo.
      destr_in Heqo. inv Heqo. simpl in *. rewrite Heqs2. auto.
      destr. subst. congruence.
      destr_in Heqo; inv Heqo.
      erewrite IHstruct_fields; eauto. reflexivity.
    + destr_in H; inv H.
      simpl PrimSpecs.sigma1. simpl.
      erewrite find_field_offset_right_spec; eauto. simpl.
      f_equal.
      unfold Bits.slice. rewrite vect_extend_end_firstn.
      unfold Bits.extend_end.
      rewrite vect_to_list_eq_rect.
      rewrite vect_to_list_app.
      rewrite vect_firstn_to_list.
      rewrite vect_skipn_to_list.
      rewrite <- repeat_bits_const.
      simpl. f_equal. f_equal. f_equal. rewrite firstn_length. rewrite skipn_length.
      rewrite vect_to_list_length. reflexivity.
  - destr_in H.
    + repeat destr_in H; inv H. simpl in *.
      rewrite <- vect_nth_map. rewrite <- vect_to_list_map.
      rewrite <- vect_to_list_nth. f_equal.
      unfold PrimTypeInference.check_index in Heqr0.
      unfold opt_result in Heqr0. destr_in Heqr0; inv Heqr0.
      symmetry; apply index_to_nat_of_nat. auto.
    + destr_in H; inv H. simpl in *.
      f_equal. f_equal.
      unfold PrimTypeInference.check_index in Heqr.
      unfold opt_result in Heqr. destr_in Heqr; inv Heqr.
      apply index_to_nat_of_nat in Heqo. subst.
      rewrite firstn_length, skipn_length.
      rewrite vect_to_list_length. unfold array_sz. simpl.
      unfold Bits.slice. rewrite vect_extend_end_firstn.
      unfold Bits.extend_end.
      rewrite vect_to_list_eq_rect.
      rewrite vect_to_list_app.
      rewrite vect_firstn_to_list.
      rewrite vect_skipn_to_list.
      rewrite <- repeat_bits_const.
      simpl.
      unfold element_offset_right. f_equal. f_equal. f_equal. rewrite Bits.rmul_correct.
      rewrite Nat.mul_comm. auto. f_equal. f_equal. f_equal. f_equal.
      rewrite Bits.rmul_correct. rewrite Nat.mul_comm. lia.
Qed.

Definition ubits2_sigma (ub: ubits2) (v1 v2: list bool) : list bool :=
  match ub with
  | UAnd => bitwise andb v1 v2
  | UOr => bitwise orb v1 v2
  | UXor => bitwise xorb v1 v2
  | ULsl =>
    let amount := Bits.to_nat (vect_of_list v2) in
    Nat.iter amount (
      fun v =>
        if eq_dec (List.length v1) O then [] else false :: removelast v
    ) v1
  | ULsr =>
    let amount := Bits.to_nat (vect_of_list v2) in
    Nat.iter amount (
      fun v => if eq_dec (List.length v1) O then [] else tl v ++ [false]
    ) v1
  | UAsr =>
    let amount := Bits.to_nat (vect_of_list v2) in
    Nat.iter amount (
      fun v => if eq_dec (List.length v1) O then [] else tl v ++ [last v false]
    ) v1
  | UConcat => v2 ++ v1
  | USel => [List.nth (Bits.to_nat (vect_of_list v2)) v1 false]
  | USliceSubst ofs w =>
    let '(h, _) := take_drop' ofs v1 in
    let '(_, t) := take_drop' (ofs + w) v1 in
    fst (take_drop' (List.length v1) (h ++ v2 ++ t))
  | UIndexedSlice w => (* A slice of v1 from the value of v2 on *)
    let ofs := Bits.to_nat (vect_of_list v2) in (* Value of v2 *)
    let bs := skipn ofs v1 in (* Skip the first bits of v1 *)
    let bs := firstn w bs in (* Keep the first w bits of the result *)
    (* Append 0s to preserve the length *)
    (bs ++ List.repeat false (w - Nat.min w (List.length v1 - ofs)))
  | UPlus =>
    vect_to_list (
      Bits.of_N (List.length v1) (
        Bits.to_N (vect_of_list v1) + Bits.to_N (vect_of_list v2)))
  | UMinus =>
    vect_to_list (Bits.of_N (List.length v1) (Bits.to_N (
      Bits.of_N (List.length v1) (
        Bits.to_N (vect_of_list v1) + Bits.to_N (Bits.neg (vect_of_list v2))))
      + Bits.to_N (sz:=List.length v1) Bits.one))
  | UMul =>
    vect_to_list (Bits.of_N (List.length v1 + List.length v2) (
      Bits.to_N (vect_of_list v1) * Bits.to_N (vect_of_list v2)))
  | UCompare signed c =>
    let sz1 := List.length v1 in
    let sz2 := List.length v2 in
    match eq_dec sz2 sz1 with
    | left pf =>
      let v1 := vect_of_list v1 in
      let v2 := rew [Bits.bits] pf in vect_of_list v2 in [((
        if signed then
          match c with
          | cLt => Bits.signed_lt
          | cGt => Bits.signed_gt
          | cLe => Bits.signed_le
          | cGe => Bits.signed_ge
          end
        else
          match c with
          | cLt => Bits.unsigned_lt
          | cGt => Bits.unsigned_gt
          | cLe => Bits.unsigned_le
          | cGe => Bits.unsigned_ge
          end
      ) v1 v2)]
    | _ => []
    end
  end.

Lemma ubits2_correct:
  forall
    ub b sz1 sz2
    (UB:
      match ub with
      | USel => Sel sz1
      | USliceSubst offset width => SliceSubst sz1 offset width
      | UIndexedSlice width => IndexedSlice sz1 width
      | UAnd => And sz1
      | UOr => Or sz1
      | UXor => Xor sz1
      | ULsl => Lsl sz1 sz2
      | ULsr => Lsr sz1 sz2
      | UAsr => Asr sz1 sz2
      | UConcat => Concat sz1 sz2
      | UPlus => Plus sz1
      | UMinus => Minus sz1
      | UMul => Mul sz1 sz2
      | UCompare signed c => Compare signed c sz1
      end = b)
    (arg1: arg1Sig (PrimSignatures.Sigma2 (PrimTyped.Bits2 b)))
    (arg2: arg2Sig (PrimSignatures.Sigma2 (PrimTyped.Bits2 b))) ret,
  CircuitPrimSpecs.sigma2 b arg1 arg2 = ret ->
  match val_of_value arg1, val_of_value arg2 with
  | Bits arg1, Bits arg2 => (ubits2_sigma ub arg1 arg2) = (vect_to_list ret)
  | _, _ => False
  end.
Proof.
  simpl. intros. subst.
  destruct ub; simpl in *.
  apply and_correct'.
  apply or_correct'.
  apply xor_correct'.
  - unfold BitFuns.lsl. unfold Bits.lsl.
    rewrite vect_of_list_to_list. unfold Bits.to_nat; rewrite Bits.to_N_rew.
    apply iter_list_vect.
    intros. rewrite vect_to_list_length. destr. subst. reflexivity.
    rewrite lsl1; auto.
  - unfold BitFuns.lsr, Bits.lsr.
    rewrite vect_of_list_to_list. unfold Bits.to_nat; rewrite Bits.to_N_rew.
    apply iter_list_vect.
    intros. rewrite vect_to_list_length. destr. subst. reflexivity.
    rewrite lsr1; auto.
  - unfold BitFuns.asr, Bits.asr.
    rewrite vect_of_list_to_list. unfold Bits.to_nat; rewrite Bits.to_N_rew.
    apply iter_list_vect.
    intros. rewrite vect_to_list_length. destr. subst. reflexivity.
    rewrite asr1; auto.
  - rewrite vect_to_list_app; auto.
  - rewrite sel.
    rewrite vect_of_list_to_list. unfold Bits.to_nat; rewrite Bits.to_N_rew.
    auto.
  - rewrite vect_to_list_length.
    rewrite slice_subst. reflexivity.
  - rewrite slice.
    rewrite vect_of_list_to_list. unfold Bits.to_nat; rewrite Bits.to_N_rew. simpl.
    rewrite vect_to_list_length. reflexivity.
  - unfold Bits.plus.
    rewrite ! vect_of_list_to_list.
    rewrite ! Bits.to_N_rew.
    eapply vect_to_list_eq.
    erewrite (
      f_equal_dep _ (fun x => Bits.of_N x (Bits.to_N arg1 + Bits.to_N arg2))).
    Unshelve. 2: apply vect_to_list_length. auto.
  - unfold Bits.minus.
    rewrite ! vect_of_list_to_list.
    rewrite ! Bits.to_N_rew.
    eapply vect_to_list_eq.
    erewrite (f_equal_dep _ (fun x => Bits.of_N x _)).
    Unshelve. 2: apply vect_to_list_length.
    unfold Bits.plus. f_equal. f_equal.
    replace (Bits.neg (rew [Bits.bits] len_to_list sz1 arg2 in arg2))
      with (rew [Bits.bits] len_to_list sz1 arg2 in (Bits.neg arg2)).
    rewrite Bits.to_N_rew.
    erewrite <- (f_equal_dep _ (fun x => (Bits.of_N x _))).
    Unshelve. 5: apply len_to_list.
    rewrite Bits.to_N_rew. auto.
    unfold Bits.neg.
    rewrite bits_map_rew. reflexivity.
    erewrite <- Bits.to_N_rew.
    Unshelve. 3: apply vect_to_list_length.
    f_equal.
    apply f_equal_dep.
  - unfold Bits.mul.
    rewrite ! vect_of_list_to_list.
    rewrite ! Bits.to_N_rew.
    eapply vect_to_list_eq.
    erewrite
      (f_equal_dep _ (fun x => Bits.of_N x (Bits.to_N arg1 * Bits.to_N arg2))).
    Unshelve. 2: rewrite ! vect_to_list_length; auto. auto.
  - destr.
    + rewrite ! vect_of_list_to_list.
      rewrite rew_compose.
      transitivity (
        vect_to_list (BitFuns.bitfun_of_predicate (
          if signed then
            match c with
            | cLt => Bits.signed_lt
            | cGt => Bits.signed_gt
            | cLe => Bits.signed_le
            | cGe => Bits.signed_ge
            end
          else
            match c with
            | cLt => Bits.unsigned_lt
            | cGt => Bits.unsigned_gt
            | cLe => Bits.unsigned_le
            | cGe => Bits.unsigned_ge
          end) arg1 arg2
        )
      ).
      2: repeat destr; reflexivity.
      rewrite cmp. f_equal.
      repeat destr; apply lift_comparison_rew.
    + clear -n. exfalso. rewrite ! vect_to_list_length in n. congruence.
Qed.

Definition sigma2 (fn: ufn2) (v1 v2: val) : option val :=
  match fn with
  | UEq false => Some (Bits [if val_beq v1 v2 then true else false])
  | UEq true  => Some (Bits [if val_beq v1 v2 then false else true])
  | UBits2 fn =>
    match v1, v2 with
    | Bits v1, Bits v2 => let res := ubits2_sigma fn v1 v2 in Some (Bits res)
    | _, _ => None
    end
  | UStruct2 (USubstField fname) =>
    match v1 with
    | Struct sig v1 =>
      let/opt res := subst_field_name (struct_fields sig) fname v2 v1 in
      Some (Struct sig res)
    | _ => None
    end
  | UStruct2 (USubstFieldBits sig fname) =>
    match v1, v2 with
    | Bits v1, Bits v2 =>
      let/opt2 ofs, w := find_field_offset_right (struct_fields sig) fname in
      let res := ubits2_sigma (USliceSubst ofs w) v1 v2 in Some (Bits res)
    | _, _ => None
    end
  | UArray2 (USubstElement n) =>
    match v1 with
    | Array s v1 =>
      let/opt2 l1, l2 := take_drop n v1 in
      match l2 with
      | [] => None
      | a::l2 => Some (Array s (l1 ++ v2 :: l2))
      end
    | _ => None
    end
  | UArray2 (USubstElementBits sig n) =>
    match v1, v2 with
    | Bits v1, Bits v2 =>
      let res :=
        ubits2_sigma
          (USliceSubst
            ((array_len sig - S n) * element_sz sig) (element_sz sig))
          v1 v2
      in Some (Bits res)
    | _, _ => None
    end
  end.

Lemma val_beq_false:
  forall v1 v2, val_beq v1 v2 = false <-> v1 <> v2.
Proof.
  split; intros.
  - intro EQ. subst. generalize (val_beq_correct v2 v2). intros (_ & A). rewrite A in H. congruence. auto.
  - generalize (val_beq_correct v1 v2). intros. destruct H0.
    destruct (val_beq v1 v2) eqn:?; auto.
    elim H; auto.
Qed.

Lemma sigma2_correct:
  forall ufn fn ty1 ty2,
  PrimTypeInference.tc2 ufn ty1 ty2 = Success fn ->
  forall
    (arg1: arg1Sig (PrimSignatures.Sigma2 fn))
    (arg2: arg2Sig (PrimSignatures.Sigma2 fn)),
  sigma2 ufn (val_of_value arg1) (val_of_value arg2)
  = Some (val_of_value (PrimSpecs.sigma2 fn arg1 arg2)).
Proof.
  destruct ufn; simpl; intros.
  - inv H. simpl in *. destr; f_equal; f_equal.
    unfold BitFuns._neq. unfold beq_dec. destruct (eq_dec).
    subst. destr. reflexivity.
    apply val_beq_false in Heqb; congruence.
    destr. 2: reflexivity.
    exfalso. apply n. apply bits_of_value_inj. apply vect_to_list_inj.
    erewrite ! (ubits_of_value_ok _ _ eq_refl).
    apply val_beq_correct in Heqb0. rewrite Heqb0. reflexivity.
    unfold BitFuns._eq. unfold beq_dec. destruct (eq_dec).
    subst. destr. reflexivity.
    apply val_beq_false in Heqb; congruence.
    destr. 2: reflexivity.
    exfalso. apply n. apply bits_of_value_inj. apply vect_to_list_inj.
    apply val_beq_correct in Heqb0.
    erewrite ! (ubits_of_value_ok _ _ eq_refl). rewrite Heqb0. reflexivity.
  - destr_in H. 2: congruence.
    destr_in Heqr; try congruence.
    destr_in H; try congruence.
    destr_in Heqr0; try congruence.
    inv Heqr0. inv Heqr. inv H.
    generalize (ubits2_correct fn _ s s0 eq_refl arg1 arg2 _ eq_refl).
    destr; try easy.
    destr; try easy. intro A; rewrite A. simpl.  auto.
  - destr_in H.
    + destr_in H; try congruence.
      destr_in Heqr; try congruence.
      destr_in H; try congruence.
      inv Heqr. inv H. simpl in arg1, arg2.
      edestruct subst_field_name_ok as (s' & VOV & s'' & SFN & EQ). eauto.
      rewrite VOV. rewrite SFN. simpl.
      rewrite ! val_of_struct_value_rew.
      f_equal. rewrite EQ. simpl.
      rewrite val_of_struct_value_rew.
      reflexivity.
    + subst. destr_in H; try congruence. inv H. simpl in *.
      rewrite slice_subst.
      erewrite find_field_offset_right_spec; eauto. simpl.
      rewrite vect_to_list_length. reflexivity.
  - destr.
    + destr_in H; try congruence.
      destr_in H; inv H. destr_in Heqr; inv Heqr. simpl in *.
      assert (pos < array_len s).
      {
        destruct (lt_dec pos (array_len s)). auto.
        unfold PrimTypeInference.check_index in Heqr0.
        unfold opt_result in Heqr0.
        destr_in Heqr0; inv Heqr0.
        rewrite index_of_nat_ge_none in Heqo. congruence. lia.
      }
      edestruct @take_drop_succeeds as (l1 & l2 & EQ).
      2: rewrite EQ.
      rewrite map_length. rewrite vect_to_list_length. lia. simpl.
      edestruct (@take_drop_map) as (l1' & l2' & EQ4 & EQ5 & EQ6). eauto.
      edestruct (@take_drop_spec) as (EQ1 & EQ2 & EQ3). apply EQ4.
      rewrite vect_to_list_length in EQ3.
      destr. erewrite <- map_length in EQ3. rewrite <- EQ6 in EQ3. simpl in EQ3.
      lia.
      destruct l2'; simpl in *; try congruence. inv EQ6.
      erewrite vect_replace_to_list; eauto.
      rewrite map_app. reflexivity.
      unfold PrimTypeInference.check_index in Heqr0. unfold opt_result in Heqr0.
      destr_in Heqr0; inv Heqr0.
      symmetry; eapply index_to_nat_of_nat; eauto.
    + destr_in H; try congruence. inv H. simpl in *.
      rewrite slice_subst.
      unfold PrimTypeInference.check_index in Heqr. unfold opt_result in Heqr.
      destr_in Heqr; inv Heqr.
      unfold element_offset_right.
      erewrite index_to_nat_of_nat; eauto.
      rewrite Bits.rmul_correct.
      rewrite vect_to_list_length. reflexivity.
Qed.

Section Interp.
  Context {pos_t var_t fn_name_t: Type}.
  Context {var_t_eq_dec: EqDec var_t}.

  Definition Log {reg_t: Type} REnv := (@_ULog val reg_t REnv).
  Definition uaction reg_t ext_fn_t :=
    (uaction pos_t var_t fn_name_t reg_t ext_fn_t).

  Notation "'let/opt4' v1 ',' v2 ',' v3 ',' v4 ':=' expr 'in' body" :=
    (opt_bind expr (fun '(v1, v2, v3, v4) => body)) (at level 200).

  Variable dummy_pos: pos_t.

  Definition fLog {reg_t reg_t'} (fR: reg_t' -> reg_t) REnv REnv' (l: Log REnv)
  : Log REnv' := REnv'.(create) (fun r => REnv.(getenv) l (fR r)).

  Definition fRinv {reg_t reg_t'} (fR: reg_t' -> reg_t) REnv REnv' (r: reg_t)
  : option reg_t' :=
    let l := filter (
      fun r' =>
        if Nat.eq_dec
          (@finite_index _ (finite_keys REnv) (fR r'))
          (@finite_index _ (finite_keys REnv) r)
        then true
        else false
    ) (@finite_elements _ (finite_keys REnv')) in List.hd_error l.

  Lemma fRinv_in {reg_t reg_t'} (fR: reg_t' -> reg_t) REnv REnv':
    forall r',
    In r' (filter (fun r1 =>
      if Nat.eq_dec
        (@finite_index _ (finite_keys REnv) (fR r1))
        (@finite_index _ (finite_keys REnv) (fR r'))
      then true else false
    ) (@finite_elements _ (finite_keys REnv'))).
  Proof.
    intros.
    rewrite filter_In.
    assert (forall r, In r (@finite_elements _ (finite_keys REnv'))).
    { intros. generalize (@finite_member _ (finite_keys REnv') r).
      apply member_In.
    }
    split; auto.
    destr.
  Qed.

  Lemma fRinv_not_in {reg_t reg_t'} (fR: reg_t' -> reg_t) REnv REnv':
    forall r' r,
    fR r' <> r
    -> ~ In r' (filter (fun r' =>
      if Nat.eq_dec
        (@finite_index _ (finite_keys REnv) (fR r'))
        (@finite_index _ (finite_keys REnv) r)
      then true else false
    ) (@finite_elements _ (finite_keys REnv'))).
  Proof.
    intros. rewrite filter_In. intros (A & B).
    destr_in B. 2: congruence. apply H.
    eapply finite_index_injective. apply e.
  Qed.

  Lemma length_nodup_le_1:
    forall {A} (l: list A), NoDup l
    -> (forall x1 x2, In x1 l -> In x2 l -> x1 = x2)
    -> List.length l <= 1.
  Proof.
    induction 1; simpl; intros; eauto.
    destruct l; simpl in *; auto.
    exfalso; apply H; left.
    apply H1; auto.
  Qed.

  Lemma filter_nodup {A:Type}:
    forall f (l: list A), NoDup l -> NoDup (filter f l).
  Proof.
    induction 1; simpl; intros; eauto.
    constructor.
    destruct (f x); auto. constructor; auto.
    rewrite filter_In. intuition.
  Qed.

  Lemma fRinv_singleton
    {reg_t reg_t'} (fR: reg_t' -> reg_t) REnv REnv'
    (inj: forall i j, i <> j -> fR i <> fR j)
  :
    forall r, List.length (filter (fun r' =>
      if Nat.eq_dec
        (@finite_index _ (finite_keys REnv) (fR r'))
        (@finite_index _ (finite_keys REnv) r)
      then true else false) (@finite_elements _ (finite_keys REnv'))) <= 1.
  Proof.
    intros.
    apply length_nodup_le_1.
    apply filter_nodup. apply finite_nodup.
    intros.
    destruct (Nat.eq_dec
      (@finite_index _ (finite_keys REnv) r)
      (@finite_index _ (finite_keys REnv) (fR x1))
    ).
    eapply finite_index_injective in e. subst.
    destruct (Nat.eq_dec
      (@finite_index _ (finite_keys REnv) (fR x1))
      (@finite_index _ (finite_keys REnv) (fR x2))
    ).
    eapply finite_index_injective in e.
    destruct (@eq_dec _ (@EqDec_FiniteType _ (finite_keys REnv')) x1 x2). auto.
    eapply inj in e. easy. auto.
    eapply fRinv_not_in in H0. easy.
    intro A; rewrite A in n. congruence.
    eapply fRinv_not_in in H. easy.
    intro A; rewrite A in n. congruence.
  Qed.

  Lemma hd_len1:
    forall {A} (l: list A) x,
    List.length l <= 1 -> In x l -> hd_error l = Some x.
  Proof.
    destruct l; simpl in *; intros. easy.
    destruct l; simpl in *. 2: lia.
    intuition congruence.
  Qed.

  Lemma fRinv_correct
    {reg_t reg_t'} (fR: reg_t' -> reg_t) REnv REnv'
    (inj: forall i j, i <> j -> fR i <> fR j)
  : forall r', fRinv fR REnv REnv' (fR r') = Some r'.
  Proof.
    unfold fRinv. intros.
    apply hd_len1. apply fRinv_singleton. auto. apply fRinv_in.
  Qed.

  Lemma hd_error_in:
    forall {A} (l: list A) x, hd_error l = Some x -> In x l.
  Proof.
    destruct l; simpl in *; intros. easy.
    inv H; auto.
  Qed.

  Lemma fRinv_correct_inv {reg_t reg_t'} (fR: reg_t' -> reg_t) REnv REnv':
    forall r r', fRinv fR REnv REnv' r = Some r' -> r = fR r'.
  Proof.
    unfold fRinv.
    intros.
    apply hd_error_in in H.
    rewrite filter_In in H. destruct H.
    destr_in H0; try congruence. clear Heqs.
    apply finite_index_injective in e. congruence.
  Qed.

  Lemma hd_none:
    forall {A} (l: list A), (forall x, ~ In x l) -> hd_error l = None.
  Proof.
    destruct l; simpl; intros; eauto.
    destruct (H a). auto.
  Qed.

  Lemma fRinv_correct' {reg_t reg_t'} (fR: reg_t' -> reg_t) REnv REnv':
    forall r, (forall r', fR r' <> r) -> fRinv fR REnv REnv' r = None.
  Proof.
    unfold fRinv. intros. apply hd_none. intros.
    apply fRinv_not_in. apply H.
  Qed.

  Definition fLog'
    {reg_t reg_t'} (fR: reg_t' -> reg_t) REnv REnv' (l: Log REnv')
    (ol: Log REnv)
  : Log REnv :=
    REnv.(create) (
      fun r =>
        match fRinv fR REnv REnv' r with
        | None => REnv.(getenv) ol r
        | Some r' => REnv'.(getenv) l r'
        end
    ).

  Fixpoint interp_action
    {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
    (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
    (sched_log: Log REnv) (action_log: Log REnv)
    (a: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t) {struct a}
  : option (Log REnv * val * list (var_t * val)) :=
    match a with
    | UError e => None
    | UFail _ => None
    | UVar var =>
      let/opt v := list_assoc Gamma var in Some (action_log, v, Gamma)
    | @UConst _ _ _ _ _ tau cst => Some (action_log, val_of_value cst, Gamma)
    | UAssign k a =>
      let/opt3 action_log, v, Gamma :=
        interp_action r sigma Gamma sched_log action_log a in
      Some (action_log, Bits [], list_assoc_set Gamma k v)
    | USeq a1 a2 =>
      let/opt3 action_log, v, Gamma :=
        interp_action r sigma Gamma sched_log action_log a1 in
      interp_action r sigma Gamma sched_log action_log a2
    | UBind k a1 a2 =>
      let/opt3 action_log, v, Gamma :=
        interp_action r sigma Gamma sched_log action_log a1 in
      let/opt3 action_log, v, Gamma :=
        interp_action r sigma ((k, v):: Gamma) sched_log action_log a2
      in Some (action_log, v, tl Gamma)
    | UIf cond athen aelse =>
      let/opt3 action_log, v, Gamma :=
        interp_action r sigma Gamma sched_log action_log cond in
      match v with
      | Bits [b] =>
        if b then interp_action r sigma Gamma sched_log action_log athen
        else interp_action r sigma Gamma sched_log action_log aelse
      | _ => None
      end
    | URead prt idx =>
      if may_read sched_log prt idx then
        Some (
          log_cons idx (LE Logs.LogRead prt (Bits [])) action_log,
          match prt with
          | P0 => REnv.(getenv) r idx
          | P1 =>
            match latest_write0 (V:=val) (log_app action_log sched_log) idx with
            | Some v => v
            | None => REnv.(getenv) r idx
            end
          end, Gamma
        )
      else None
    | UWrite prt idx v =>
      let/opt3 action_log, val, Gamma :=
        interp_action r sigma Gamma sched_log action_log v in
      if may_write sched_log action_log prt idx then
        Some (
          log_cons idx (LE Logs.LogWrite prt val) action_log, Bits [], Gamma
        )
      else None
    | UUnop fn arg =>
      let/opt3 action_log, arg1, Gamma :=
        interp_action r sigma Gamma sched_log action_log arg in
      let/opt v := sigma1 fn arg1 in Some (action_log, v, Gamma)
    | UBinop fn arg1 arg2 =>
      let/opt3 action_log, arg1, Gamma :=
        interp_action r sigma Gamma sched_log action_log arg1 in
      let/opt3 action_log, arg2, Gamma :=
        interp_action r sigma Gamma sched_log action_log arg2 in
      let/opt v := sigma2 fn arg1 arg2 in Some (action_log, v, Gamma)
    | UExternalCall fn arg1 =>
      let/opt3 action_log, arg1, Gamma :=
        interp_action r sigma Gamma sched_log action_log arg1 in
      Some (action_log, sigma fn arg1, Gamma)
    | UInternalCall f args =>
      let body := int_body f in
      let/opt3 action_log, results, Gamma :=
        fold_left (fun acc a =>
          let/opt3 action_log, l, Gamma := acc in
          let/opt3 action_log, v, Gamma :=
            interp_action r sigma Gamma sched_log action_log a
          in Some (action_log, v::l, Gamma)
        ) args (Some (action_log, [], Gamma)) in
      let/opt3 action_log, v, _ :=
        interp_action r sigma (map
          (fun '(name, _, v) => (name, v))
          (combine (rev (int_argspec f)) results)
        ) sched_log action_log body in
      Some (action_log, v, Gamma)
    | UAPos p a => interp_action r sigma Gamma sched_log action_log a
    | USugar UErrorInAst => None
    | USugar USkip => Some (action_log, Bits [], Gamma)
    | USugar (UConstBits v) =>
      let l := vect_to_list v in
      Some (action_log, Bits l, Gamma)
    | USugar (UConstString s) =>
      Some (
        action_log,
        Array {| array_type := bits_t 8; array_len := String.length s |}
        (List.map
          (fun x => Bits (vect_to_list x))
          (vect_to_list (SyntaxMacros.array_of_bytes s))
        ), Gamma)
    | USugar (UConstEnum sig name) =>
      match vect_index name sig.(enum_members) with
      | Some idx =>
        Some (
          action_log,
          val_of_value (tau:= enum_t sig) (vect_nth sig.(enum_bitpatterns) idx),
          Gamma
        )
      | None => None
      end
    | USugar (UProgn aa) =>
      List.fold_left (fun acc a =>
        let/opt3 action_log, v, Gamma := acc in
        interp_action r sigma Gamma sched_log action_log a
      ) aa (Some (action_log, Bits [], Gamma))
    | USugar (ULet bindings body) =>
      let/opt2 action_log, Gamma' :=
        List.fold_left (fun acc '(var, a) =>
          let/opt2 action_log, Gamma' := acc in
          let/opt3 action_log, v, Gamma' :=
            interp_action r sigma Gamma' sched_log action_log a in
          (Some (action_log, (var,v)::Gamma'))
        ) bindings (Some (action_log, Gamma)) in
      let/opt3 action_log, v, Gamma :=
         interp_action r sigma Gamma' sched_log action_log body in
      Some (action_log, v, Nat.iter (List.length bindings) (@tl _) Gamma)
    | USugar (UWhen cond body) =>
      let/opt3 action_log, v, Gamma :=
        interp_action r sigma Gamma sched_log action_log cond in
      match v with
      | Bits [b] =>
        if b then interp_action r sigma Gamma sched_log action_log body
        else None
      | _ => None
      end
    | USugar (USwitch var default branches) =>
      let/opt3 action_log, found, Gamma :=
         List.fold_left (
          fun acc '(cond, body) =>
            let/opt3 action_log, found, Gamma := acc in
            match found with
            | Some _ => acc
            | _ =>
              let/opt3 action_log, v0, Gamma :=
                interp_action r sigma Gamma sched_log action_log var in
              let/opt3 action_log, v, Gamma :=
                interp_action r sigma Gamma sched_log action_log cond in
              if val_beq v v0 then
                let/opt3 action_log, v, Gamma :=
                  interp_action r sigma Gamma sched_log action_log body in
                Some (action_log, Some v, Gamma)
              else Some (action_log, None, Gamma)
            end
         ) branches (Some (action_log, None, Gamma)) in
      match found with
      | Some v => Some (action_log, v, Gamma)
      | None => interp_action r sigma Gamma sched_log action_log default
      end
    | USugar (UStructInit sig fields) =>
      let zeroes := repeat false (struct_fields_sz (struct_fields sig)) in
      let/opt vs := uvalue_of_struct_bits (struct_fields sig) zeroes in
      let/opt3 action_log, v, Gamma :=
        List.fold_left (fun acc '(name, a) =>
           let/opt3 action_log, vs, Gamma := acc in
           let/opt3 action_log, v, Gamma :=
              interp_action r sigma Gamma sched_log action_log a
           in
           let/opt vs := subst_field_name (struct_fields sig) name v vs in
           (Some (action_log, vs, Gamma))
        ) fields (Some (action_log, vs, Gamma)) in
        Some (action_log, Struct sig v, Gamma)
    | USugar (UArrayInit tau elements) =>
      let zeroes :=
        repeat (repeat false (type_sz tau)) (List.length elements) in
      let/opt vs := uvalue_of_list_bits (tau:=tau) zeroes in
      let sig := {| array_type := tau; array_len := List.length elements |} in
      let/opt4 pos, action_log, vs, Gamma :=
        List.fold_left (fun acc a =>
          let/opt4 pos, action_log, vs, Gamma := acc in
          let/opt3 action_log, v, Gamma :=
            interp_action r sigma Gamma sched_log action_log a in
          let/opt2 l1, l2 := take_drop pos vs in
          match l2 with
          | [] => None
          | a::l2 => Some (S pos, action_log, l1 ++ v :: l2, Gamma)
          end
        ) elements (Some (0, action_log, vs, Gamma)) in
      Some (action_log, Array sig vs, Gamma)
    | USugar (UCallModule fR fSigma fn args) =>
      let/opt3 action_log, results, Gamma0 :=
        fold_left (
          fun (acc : option (_ULog * list val * list (var_t * val))) a =>
            let/opt3 action_log, l, Gamma := acc in (
              let/opt3 action_log, v, Gamma :=
                interp_action r sigma Gamma sched_log action_log a
              in Some (action_log, v :: l, Gamma)
            )
        ) args (Some (action_log, [], Gamma))
      in
        let REnv' := @ContextEnv _ _ in
        let/opt3 action_log1, v, _ :=
          interp_action
            (create REnv' (fun idx => getenv REnv r (fR idx)))
            (fun f => sigma (fSigma f))
            (map
              (fun '(name, _, v) => (name, v))
              (combine (rev (int_argspec fn)) results)
            )
            (fLog fR REnv REnv' sched_log) (fLog fR REnv REnv' action_log)
            (int_body fn)
        in
        Some (fLog' fR REnv REnv' action_log1 action_log, v, Gamma0)
    end.

  Fixpoint interp_daction
    {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
    (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
    (sched_log: Log REnv) (action_log: Log REnv)
    (a: @DesugaredSyntax.daction pos_t var_t fn_name_t reg_t ext_fn_t)
    {struct a}
  : option (Log REnv * val * list (var_t * val)) :=
    match a with
    | DError e => None
    | DFail _ => None
    | DVar var =>
      let/opt v := list_assoc Gamma var in Some (action_log, v, Gamma)
    | DConst tau cst => Some (action_log, cst, Gamma)
    | DAssign k a =>
      let/opt3 action_log, v, Gamma :=
        interp_daction r sigma Gamma sched_log action_log a in
      Some (action_log, Bits [], list_assoc_set Gamma k v)
    | DSeq a1 a2 =>
      let/opt3 action_log, v, Gamma :=
        interp_daction r sigma Gamma sched_log action_log a1 in
      interp_daction r sigma Gamma sched_log action_log a2
    | DBind k a1 a2 =>
      let/opt3 action_log, v, Gamma :=
        interp_daction r sigma Gamma sched_log action_log a1 in
      let/opt3 action_log, v, Gamma :=
        interp_daction r sigma ((k, v):: Gamma) sched_log action_log a2
      in Some (action_log, v, tl Gamma)
    | DIf cond athen aelse =>
      let/opt3 action_log, v, Gamma :=
        interp_daction r sigma Gamma sched_log action_log cond in
      match v with
      | Bits [b] =>
        if b then interp_daction r sigma Gamma sched_log action_log athen
        else interp_daction r sigma Gamma sched_log action_log aelse
      | _ => None
      end
    | DRead prt idx =>
      if may_read sched_log prt idx then
        Some (
          log_cons idx (LE Logs.LogRead prt (Bits [])) action_log,
          match prt with
          | P0 => REnv.(getenv) r idx
          | P1 =>
            match latest_write0 (V:=val) (log_app action_log sched_log) idx with
            | Some v => v
            | None => REnv.(getenv) r idx
            end
          end, Gamma
        )
      else None
    | DWrite prt idx v =>
      let/opt3 action_log, val, Gamma :=
        interp_daction r sigma Gamma sched_log action_log v in
      if may_write sched_log action_log prt idx then
        Some (
          log_cons idx (LE Logs.LogWrite prt val) action_log, Bits [], Gamma
        )
      else None
    | DUnop fn arg =>
      let/opt3 action_log, arg1, Gamma :=
        interp_daction r sigma Gamma sched_log action_log arg in
      let/opt v := sigma1 fn arg1 in Some (action_log, v, Gamma)
    | DBinop fn arg1 arg2 =>
      let/opt3 action_log, arg1, Gamma :=
        interp_daction r sigma Gamma sched_log action_log arg1 in
      let/opt3 action_log, arg2, Gamma :=
        interp_daction r sigma Gamma sched_log action_log arg2 in
      let/opt v := sigma2 fn arg1 arg2 in Some (action_log, v, Gamma)
    | DExternalCall fn arg1 =>
      let/opt3 action_log, arg1, Gamma :=
        interp_daction r sigma Gamma sched_log action_log arg1 in
      Some (action_log, sigma fn arg1, Gamma)
    | DInternalCall f args =>
      let body := int_body f in
      let/opt3 action_log, results, Gamma :=
        fold_left (fun acc a =>
          let/opt3 action_log, l, Gamma := acc in
          let/opt3 action_log, v, Gamma :=
            interp_daction r sigma Gamma sched_log action_log a
          in Some (action_log, v::l, Gamma)
        ) args (Some (action_log, [], Gamma)) in
      let/opt3 action_log, v, _ :=
        interp_daction r sigma (map
          (fun '(name, _, v) => (name, v))
          (combine (rev (int_argspec f)) results)
        ) sched_log action_log body in
      Some (action_log, v, Gamma)
    | DAPos p a => interp_daction r sigma Gamma sched_log action_log a
    end.

  Lemma uaction_to_daction_list:
    forall reg_t ext_fn_t F args (l: list daction)
      (Heqo: Forall2 (fun a d => F a = Some d) args l)
      (H0: Forall
         (fun u: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t =>
            forall (REnv : Env reg_t) (r : env_t REnv (fun _ : reg_t => val))
              (sigma : ext_fn_t -> val -> val) (Gamma : list (var_t * val))
              (sched_log action_log : Log REnv) (d : daction),
            F u = Some d
            -> interp_action r sigma Gamma sched_log action_log u
            = interp_daction r sigma Gamma sched_log action_log d)
         args)
      (REnv: Env reg_t) (r: env_t REnv (fun _ : reg_t => val))
      (sigma: ext_fn_t -> val -> val) sched_log acc,
    fold_left
      (fun
        (acc : option (Log REnv * list val * list (var_t * val)))
        (a0 : Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t)
      =>
       match acc with
       | Some (action_log0, l0, Gamma0) =>
         match interp_action r sigma Gamma0 sched_log action_log0 a0 with
         | Some (action_log1, v, Gamma1) => Some (action_log1, v :: l0, Gamma1)
         | None => None
         end
       | None => None
       end) args acc =
    fold_left
      (fun (acc : option (Log REnv * list val * list (var_t * val)))
         (a0 : @DesugaredSyntax.daction pos_t var_t fn_name_t reg_t ext_fn_t) =>
       match acc with
       | Some (action_log0, l0, Gamma0) =>
           match interp_daction r sigma Gamma0 sched_log action_log0 a0 with
           | Some (action_log1, v, Gamma1) =>
             Some (action_log1, v :: l0, Gamma1)
           | None => None
           end
       | None => None
       end) l acc.
  Proof.
    induction 1; simpl; intros; eauto.
    destr. destr. destr.
    inv H0. erewrite H3; eauto.
    clear.
    assert (
      forall {A B: Type} (f: option A -> B -> option A)
        (Fnone: forall x, f None x = None) l,
      fold_left f l None = None
    ).
    { clear. induction l; simpl; intros; eauto. rewrite Fnone; auto. }
    rewrite H; auto.
    rewrite H; auto.
  Qed.

  Lemma map_error_forall2:
    forall {A B: Type} (f: A -> option B) (l1: list A) (l2: list B),
    map_error f l1 = Some l2
    -> Forall2 (fun a b => f a = Some b) l1 l2.
  Proof.
    induction l1; simpl; intros; eauto. inv H; auto.
    unfold opt_bind in H; repeat destr_in H; inv H.
    constructor; auto.
  Qed.

  Lemma fold_left_none:
    forall
      {A B} (f: option B -> A -> option B) (Fnone: forall a, f None a = None)
      (l: list A),
    fold_left f l None = None.
  Proof. induction l; simpl; intros; eauto. rewrite Fnone. auto. Qed.

  Lemma uaction_to_daction_interp:
    forall
      {reg_t ext_fn_t: Type}
      (a: @Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t)
      {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (Gamma: list (var_t * val))
      (sched_log: Log REnv) (action_log: Log REnv) d
      (U2D: uaction_to_daction a = Some d),
    interp_action r sigma Gamma sched_log action_log a
    = interp_daction r sigma Gamma sched_log action_log d.
  Proof.
    intros reg_t ext_fn_t a.
    pattern a.
    eapply uaction_ind'; simpl; intros; inv U2D; eauto.
    - unfold opt_bind in *; destr_in H1; inv H1.
      simpl. erewrite H; eauto. unfold opt_bind; auto.
    - unfold opt_bind in *; repeat destr_in H2; inv H2.
      simpl; unfold opt_bind. erewrite H; eauto. repeat destr.
      eapply H0; eauto.
    - unfold opt_bind in *; repeat destr_in H2; inv H2.
      simpl; unfold opt_bind.
      erewrite H; eauto. destr. destr. destr.
      erewrite H0; eauto.
    - unfold opt_bind in *; repeat destr_in H3; inv H3.
      simpl; unfold opt_bind.
      erewrite H; eauto. repeat destr; eauto.
    - unfold opt_bind in *; repeat destr_in H1; inv H1.
      simpl; unfold opt_bind.
      erewrite H; eauto.
    - unfold opt_bind in *; repeat destr_in H1; inv H1.
      simpl; unfold opt_bind.
      erewrite H; eauto.
    - unfold opt_bind in *; repeat destr_in H2; inv H2.
      simpl; unfold opt_bind.
      erewrite H; eauto. destr. destr. destr.
      erewrite H0; eauto.
    - unfold opt_bind in *; repeat destr_in H1; inv H1.
      simpl; unfold opt_bind.
      erewrite H; eauto.
    - unfold opt_bind in *; repeat destr_in H2; inv H2.
      simpl; unfold opt_bind.
      erewrite uaction_to_daction_list with(l:=l); eauto.
      destr. destr. destr.
      erewrite H; eauto.
      eapply map_error_forall2. auto.
    - unfold opt_bind in *; repeat destr_in H1; inv H1.
      simpl; unfold opt_bind.
      erewrite H; eauto.
  Qed.

  Fixpoint uprogn2 {reg_t ext_fn_t} (aa: list (uaction reg_t ext_fn_t)) dft :=
    match aa with
    | [] => dft
    | [a] => a
    | a::a0 => USeq a (uprogn2 a0 dft)
    end.

  Lemma repeat_take_drop:
    forall {A} n m (a: A), n <= m
    -> take_drop n (repeat a m) = Some (repeat a n, repeat a (m - n)).
  Proof.
    induction n; simpl; intros; eauto. rewrite Nat.sub_0_r. auto.
    destruct m. lia. simpl.
    rewrite IHn  by lia.
    simpl. reflexivity.
  Qed.

  Lemma Forall_rev:
    forall {A: Type} (P: A -> Prop) l, Forall P l -> Forall P (rev l).
  Proof.
    intros; rewrite Forall_forall in *; intros.
    apply in_rev in H0. eauto.
  Qed.

  Lemma bits_splitn_succeeds:
    forall n sz l, List.length l = n * sz
    -> exists l', bits_splitn n sz l = Some l'
    /\ Forall (fun l => List.length l = sz) l' /\ List.length l' = n.
  Proof.
    induction n; simpl; intros; eauto.
    edestruct (@take_drop_succeeds) as (la & lb & EQ). 2: rewrite EQ. lia.
    simpl.
    edestruct (take_drop_spec _ _ _ _ EQ) as (EQ1 & EQ2 & EQ3). subst.
    edestruct IHn as (l' & EQ4 & EQ5 & EQ6). 2: rewrite EQ4. lia.
    simpl. eexists; split; eauto.
    split; simpl; auto.
  Qed.

  Lemma uvalue_of_bits_succeeds:
    forall t l, List.length l = type_sz t
    -> exists x, uvalue_of_bits (tau:=t) l = Some x.
  Proof.
    intros t.
    pattern t.
    match goal with
    |- ?P t => set (PP:=P)
    end.
    remember (size_type t).
    revert t Heqn.
    pattern n.
    eapply Nat.strong_right_induction with (z:=0).
    2: lia.
    intros n0 _ Plt t Heqn.
    assert (Plt': forall t, size_type t < n0 -> PP t).
    { intros. eapply Plt. 3: reflexivity. lia. auto. }
    clear Plt. rename Plt' into Plt.
    subst.
    destruct t; simpl; intros; eauto.
    - unfold PP. simpl. eauto.
    - unfold PP; simpl. intros. rewrite take_drop_succeeds_eq. simpl. eauto.
      auto.
    - red; intros; simpl in *.
      assert (Plt': forall t, In t (map snd (struct_fields sig)) -> PP t).
      { intros; eapply Plt.
        revert H0. generalize (struct_fields sig).
        intro l0.
        revert l0 t.
        induction l0; simpl; intros; eauto. easy. destruct a. simpl in *.
        destruct H0; subst; eauto. lia.
        apply IHl0 in H0. lia.
      } clear Plt.
      revert Plt' l H.
      generalize (struct_fields sig).
      induction l; simpl; intros; eauto.
      destruct a; simpl in *.
      replace (List.length l0 - type_sz t) with (struct_fields_sz l).
      2:{ rewrite H. unfold struct_fields_sz. simpl. lia. }
      edestruct @take_drop_succeeds as (la & lb & EQ). 2: rewrite EQ. rewrite H.
      unfold struct_fields_sz; simpl; lia.
      simpl.
      edestruct (take_drop_spec _ _ _ _ EQ) as (EQ1 & EQ2 & EQ3).
      subst.
      edestruct IHl as (x & EQ4). intros; eauto.
      2: unfold opt_bind in EQ4; destr_in EQ4; try congruence; rewrite Heqo.
      auto. inv EQ4. simpl.
      edestruct (Plt' t) as (x & EQ5). auto.
      2: rewrite EQ5.
      rewrite EQ3. rewrite H. unfold struct_fields_sz. simpl. lia.
      simpl. eauto.
    - red; simpl; intros.
      edestruct bits_splitn_succeeds as (l' & EQ & F & L). 2: rewrite EQ.
      rewrite Bits.rmul_correct in H. lia. simpl.
      cut (
        exists x, (
          fix uvalue_of_list_bits (l0 : list (list bool))
          : option (list val) :=
            match l0 with
            | [] => Some []
            | hd :: tl =>
              let/opt hd0 := uvalue_of_bits (tau:=array_type sig) hd
              in (let/opt tl0 := uvalue_of_list_bits tl in Some (hd0 :: tl0))
            end
        ) (rev l') = Some x
      ).
      { intros (x & EQ'); rewrite EQ'. simpl; eauto. }
      apply Forall_rev in F.
      rewrite <- rev_length in L.
      destruct sig. simpl in *.
      clear H EQ.
      revert L F Plt.
      generalize (rev l').
      clear. induction array_len; simpl; intros; eauto.
      + destruct l; simpl in *; try lia. eauto.
      + inv F; simpl in *. lia. inv L.
        edestruct (Plt (array_type)). lia. eauto.
        rewrite H1. simpl.
        edestruct IHarray_len; eauto. rewrite H2.
        simpl; eauto.
  Qed.

  Lemma uinit_action
    {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
    (sigma: forall f: ext_fn_t, val -> val)
  :
    forall Gamma sched_log action_log sig,
    exists vs,
    uvalue_of_struct_bits
      (struct_fields sig) (repeat false (struct_fields_sz (struct_fields sig)))
    = Some vs
    /\ interp_action r sigma Gamma sched_log action_log (uinit (struct_t sig))
      = Some (action_log, Struct sig vs, Gamma).
  Proof.
    unfold uinit. intros. simpl.
    destruct sig. simpl.
    induction struct_fields; simpl; intros; eauto.
    destruct a.
    unfold opt_bind.
    rewrite repeat_take_drop.
    2: rewrite repeat_length; lia.
    rewrite vect_to_list_length.
    replace (List.length (repeat _ _) - type_sz t)
      with (struct_fields_sz struct_fields).
    2:{ unfold struct_fields_sz. simpl. rewrite ! repeat_length. lia. }
    replace (_ - _) with (type_sz t).
    2:{ unfold struct_fields_sz. simpl. lia. }
    destruct IHstruct_fields as ( vs & EQ4 & EQ5).
    rewrite EQ4.
    unfold opt_bind in EQ5.
    repeat destr_in EQ5; try congruence.
    destr_in Heqo; try congruence.
    destr_in Heqo0; try congruence.
    inv Heqo0. inv Heqo. inv EQ5.
    rewrite <- repeat_bits_const.
    rewrite repeat_take_drop by lia.
    replace (_ - _) with (struct_fields_sz struct_fields).
    2:{ unfold struct_fields_sz. simpl. lia. }
    rewrite <- repeat_bits_const in Heqo1. rewrite Heqo1.
    clear Heqo1.
    replace (_ - _) with (type_sz t).
    2:{ unfold struct_fields_sz. simpl. lia. }
    edestruct @uvalue_of_bits_succeeds as (x & EQ). 2: rewrite EQ.
    rewrite repeat_length. auto.
    eexists; split; eauto.
  Qed.

  Lemma uprogn_eq {reg_t ext_fn_t: Type}:
    forall aa,
    uprogn aa
    = uprogn2
      (reg_t:=reg_t) (ext_fn_t:=ext_fn_t) aa (UConst (tau:=bits_t 0) Ob).
  Proof. induction aa; simpl; intros; eauto. rewrite IHaa. reflexivity. Qed.

  Lemma Forall2_length:
    forall {A B: Type} (P : A -> B -> Prop) la lb,
    Forall2 P la lb -> List.length la = List.length lb.
  Proof. induction 1; simpl; intros; eauto. Qed.

  Lemma same_lists:
    forall {A: Type} (l1 l2: list A) y,
    Forall (fun x => Some x = y) l1
    -> Forall (fun x => Some x = y) l2
    -> List.length l1 = List.length l2 -> l1 = l2.
  Proof.
    induction l1; simpl; intros; eauto.
    - destruct l2; simpl in *; try lia. auto.
    - destruct l2; simpl in *; try lia. auto.
      inv H1. inv H. inv H0. inv H2. f_equal. eauto.
  Qed.

  Lemma uvalue_of_struct_bits_length:
    forall sig l lv,
    uvalue_of_struct_bits sig l = Some lv -> List.length lv = List.length sig.
  Proof.
    induction sig; simpl; intros; eauto. inv H. reflexivity.
    unfold opt_bind in H.
    repeat destr_in H; inv H; simpl. f_equal. eauto.
  Qed.

  Lemma repeat_plus:
    forall n m {A: Type} (a: A), repeat a (n + m) = repeat a n ++ repeat a m.
  Proof. induction n; simpl; intros; eauto. rewrite IHn. auto. Qed.

  Lemma bits_splitn_repeat:
    forall n sz a l,
    bits_splitn n sz (repeat a (n * sz)) = Some l
    -> Forall (fun v => v = repeat a sz) l.
  Proof.
    induction n; simpl; intros; eauto. inv H. constructor.
    unfold opt_bind in H. repeat destr_in H; inv H.
    rewrite repeat_plus in Heqo.
    rewrite take_drop_head in Heqo. inv Heqo. constructor. auto. eauto.
    rewrite repeat_length. auto.
  Qed.

  Lemma Forall2_app:
    forall {A B: Type} (P : A -> B -> Prop) la1 lb1,
    Forall2 P (la1) (lb1)
    -> forall la2 lb2,
    Forall2 P (la2) (lb2) -> Forall2 P (la1 ++ la2) (lb1 ++ lb2).
  Proof. induction 1; simpl; intros; eauto. Qed.

  Lemma Forall2_rev:
    forall {A B: Type} (P : A -> B -> Prop) la lb,
    Forall2 P la lb -> Forall2 P (rev la) (rev lb).
  Proof. induction 1; simpl; intros; eauto. apply Forall2_app; auto. Qed.

  Lemma uinit_action_array
    {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
    (sigma: forall f: ext_fn_t, val -> val)
  :
    forall Gamma sched_log action_log sig,
    exists vs vl,
    bits_splitn
      (array_len sig) (type_sz (array_type sig))
      (repeat false (array_sz sig)) = Some vs
    /\ Forall (fun v => List.length v = type_sz (array_type sig)) vs
    /\ Forall (fun v => v = repeat false (type_sz (array_type sig))) vs
    /\ List.length vs = array_len sig
    /\ Forall2
      (fun b v => uvalue_of_bits (tau:=array_type sig) b = Some v) vs vl
    /\ interp_action r sigma Gamma sched_log action_log (uinit (array_t sig))
    = Some (action_log, Array sig (rev vl), Gamma).
  Proof.
    unfold uinit. intros. simpl.
    destruct sig. simpl.
    unfold array_sz. simpl.
    edestruct bits_splitn_succeeds as (l' & EQ & F & L).
    2: rewrite EQ.
    rewrite repeat_length. rewrite Bits.rmul_correct; lia.
    exists l'.
    assert (
      exists vl,
      Forall2 (fun b v => uvalue_of_bits (tau:= array_type) b = Some v) l' vl
    ).
    { clear - F. revert F.
      induction 1; simpl; intros; eauto.
      destruct IHF. edestruct uvalue_of_bits_succeeds. eauto.
      exists (x1::x0). constructor; auto.
    }
    destruct H.
    exists x. repeat split; eauto.
    eapply bits_splitn_repeat. eauto.
    rewrite <- EQ. f_equal. rewrite Bits.rmul_correct. reflexivity.
    rewrite <- repeat_bits_const. rewrite EQ. simpl.
    apply Forall2_rev in H.
    clear F L EQ. revert H.
    rewrite <- (rev_involutive x) at 2.
    generalize (rev l') (rev x).
    induction 1; simpl; intros; eauto.
    unfold opt_bind in *.
    destr_in IHForall2; try congruence. inv IHForall2.
    destr_in Heqo;  inv Heqo.
    destr_in Heqo0;  inv Heqo0.
    rewrite H.
    rewrite rev_app_distr. simpl. reflexivity.
  Qed.

  Lemma uvalue_of_list_bits_rew:
    forall {tau} l, (
      fix uvalue_of_list_bits (l : list (list bool)) : option (list val) :=
        match l with
        | [] => Some []
        | hd :: tl =>
          match uvalue_of_bits (tau:=tau) hd with
          | Some x =>
            match uvalue_of_list_bits tl with
            | Some x0 => Some (x :: x0)
            | None => None
            end
          | None => None
          end
        end
    ) l = uvalue_of_list_bits (tau:=tau) l.
  Proof.
    induction l; simpl; intros; eauto. rewrite IHl. destr; simpl; auto.
  Qed.

  Lemma uvalue_of_list_bits_inv:
    forall tau n l l0,
    uvalue_of_list_bits (tau:=tau) (repeat l n) = Some l0
    -> Forall (fun v => Some v = uvalue_of_bits (tau:=tau) l) l0
    /\ List.length l0 = n.
  Proof.
    induction n; simpl; intros; eauto. inv H. split; constructor.
    unfold opt_bind in H; repeat destr_in H; inv H.
    split. constructor; eauto.
    eapply Forall_impl. 2: eapply IHn; eauto. simpl. rewrite Heqo. auto.
    simpl. f_equal. eapply IHn; eauto.
  Qed.

  Definition interp_rule
    {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
    (sigma: forall f: ext_fn_t, val -> val)
    (sched_log: Log REnv) (rl: uaction reg_t ext_fn_t)
  : option (Log REnv) :=
    match interp_action r sigma nil sched_log log_empty rl with
    | Some (l, _, _) => Some l
    | None => None
    end.

  Definition interp_drule
    {reg_t ext_fn_t: Type} {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
    (sigma: forall f: ext_fn_t, val -> val)
    (sched_log: Log REnv) (rl: daction)
  : option (Log REnv) :=
    match interp_daction r sigma nil sched_log log_empty rl with
    | Some (l, _, _) => Some l
    | None => None
    end.

  Context {rule_name_t: Type}.

  Section Scheduler.
    Context {reg_t ext_fn_t: Type}.
    Context (rules: rule_name_t -> uaction reg_t ext_fn_t).

    Fixpoint interp_scheduler'
      {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (sched_log: Log REnv)
      (s: scheduler pos_t rule_name_t) {struct s}
    :=
      let interp_try rl s1 s2 :=
        match interp_rule r sigma sched_log (rules rl) with
        | Some l => interp_scheduler' r sigma (log_app l sched_log) s1
        | None => interp_scheduler' r sigma sched_log s2
        end
      in
      match s with
      | Done => sched_log
      | Cons r s => interp_try r s s
      | Try r s1 s2 => interp_try r s1 s2
      | SPos _ s => interp_scheduler' r sigma sched_log s
      end.

    Definition interp_scheduler
      {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (s: scheduler pos_t rule_name_t)
    := interp_scheduler' r sigma log_empty s.

    Definition interp_cycle
      {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (s: scheduler pos_t rule_name_t)
    := commit_update r (interp_scheduler r sigma s).
  End Scheduler.
  Section DScheduler.
    Context {reg_t ext_fn_t: Type}.
    Context (rules:
      rule_name_t -> @daction pos_t var_t fn_name_t reg_t ext_fn_t).

    Fixpoint interp_dscheduler'
      {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (sched_log: Log REnv)
      (s: scheduler pos_t rule_name_t) {struct s}
    :=
      let interp_try rl s1 s2 :=
        match interp_drule r sigma sched_log (rules rl) with
        | Some l => interp_dscheduler' r sigma (log_app l sched_log) s1
        | None => interp_dscheduler' r sigma sched_log s2
        end
      in
      match s with
      | Done => sched_log
      | Cons r s => interp_try r s s
      | Try r s1 s2 => interp_try r s1 s2
      | SPos _ s => interp_dscheduler' r sigma sched_log s
      end.

    Definition interp_dscheduler
      {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (s: scheduler pos_t rule_name_t)
    := interp_dscheduler' r sigma log_empty s.

    Definition interp_dcycle
      {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (s: scheduler pos_t rule_name_t)
    := commit_update r (interp_dscheduler r sigma s).
  End DScheduler.

  Lemma urule_to_drule_interp:
    forall
      {reg_t ext_fn_t: Type}
      (a: @Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t)
      {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val)
      (sched_log: Log REnv)
      d
      (U2D: uaction_to_daction a = Some d),
      interp_rule r sigma sched_log a =
        interp_drule r sigma sched_log d.
  Proof.
    unfold interp_rule, interp_drule.
    intros.
    erewrite uaction_to_daction_interp; eauto.
  Qed.

  Lemma uscheduler'_to_dscheduler'_interp:
    forall
      {reg_t ext_fn_t: Type}
      (rules:
        rule_name_t -> @Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t)
      (drules: rule_name_t -> @daction pos_t var_t fn_name_t reg_t ext_fn_t)
      (U2A: forall rl, uaction_to_daction (rules rl) = Some (drules rl))
      {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val)
      s (sched_log: Log REnv),
      interp_scheduler' rules r sigma sched_log s =
        interp_dscheduler' drules r sigma sched_log s.
  Proof.
    induction s; simpl; intros; eauto.
    erewrite urule_to_drule_interp; eauto.
    destr; eauto.
    erewrite urule_to_drule_interp; eauto.
    destr; eauto.
  Qed.


  Lemma uscheduler_to_dscheduler_interp:
    forall
      {reg_t ext_fn_t: Type}
      (rules:
        rule_name_t -> @Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t)
      (drules: rule_name_t -> @daction pos_t var_t fn_name_t reg_t ext_fn_t)
      (U2A: forall rl, uaction_to_daction (rules rl) = Some (drules rl))
      {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val)
      s,
      interp_scheduler rules r sigma s =
        interp_dscheduler drules r sigma s.
  Proof.
    unfold interp_scheduler, interp_dscheduler. intros.
    eapply uscheduler'_to_dscheduler'_interp; eauto.
  Qed.

  Lemma ucycle_to_dcycle_interp:
    forall
      {reg_t ext_fn_t: Type}
      (rules:
        rule_name_t -> @Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t)
      (drules: rule_name_t -> @daction pos_t var_t fn_name_t reg_t ext_fn_t)
      (U2A: forall rl, uaction_to_daction (rules rl) = Some (drules rl))
      {REnv: Env reg_t} (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val)
      s,
      interp_cycle rules r sigma s =
        interp_dcycle drules r sigma s.
  Proof.
    unfold interp_cycle, interp_dcycle. intros.
    erewrite uscheduler_to_dscheduler_interp; eauto.
  Qed.

End Interp.

Section Desugar.
  Context {var_t pos_t fn_name_t: Type}.
  Context {var_t_eq_dec: EqDec var_t}.

  Inductive match_states reg_t reg_t' REnv REnv' (fR: reg_t' -> reg_t)
  : option (Log REnv' * val * list (var_t * val))
    -> option (Log REnv * val * list (var_t * val)) -> Prop
  :=
  | match_states_none: match_states reg_t reg_t' REnv REnv' fR None None
  | match_states_some:
    forall l1 l2 v g, l1 = fLog fR REnv REnv' l2 ->
    match_states reg_t reg_t' REnv REnv' fR (Some (l1, v, g)) (Some (l2, v, g)).

  Definition fState'
    {reg_t reg_t' B C} (fR: reg_t' -> reg_t) REnv REnv'
    (l: option (Log REnv' * B * C)) (ol: Log REnv)
  : option (Log REnv * B * C) :=
    let/opt3 al, v, g := l in Some (fLog' fR REnv REnv' al ol, v, g).

  Definition desugar_ok
    reg_t' ext_fn_t'
    (u:
      uaction (pos_t:=pos_t) (var_t:=var_t) (fn_name_t:=fn_name_t) reg_t'
      ext_fn_t'
    )
  :=
    forall
      reg_t ext_fn_t REnv (r: REnv.(env_t) (fun _ => val))
      (sigma: forall f: ext_fn_t, val -> val) (fR: reg_t' -> reg_t)
      (inj: forall i j, i <> j -> fR i <> fR j) (fSigma: ext_fn_t' -> ext_fn_t)
      REnv',
    let r' := REnv'.(create) (fun idx => REnv.(getenv) r (fR idx)) in
    let sigma' := fun f => sigma (fSigma f) in
    forall
      (Gamma : list (var_t * val)) (action_log sched_log : Log REnv)
      (p : pos_t),
    fState' fR REnv REnv' (
      interp_action r' sigma' Gamma
      (fLog fR REnv REnv' sched_log) (fLog fR REnv REnv' action_log) u
    )
    action_log = interp_action
      r sigma Gamma sched_log action_log (desugar_action' p fR fSigma u).

  Lemma existsb_flog:
    forall reg_t reg_t' (fR: reg_t' -> reg_t) REnv REnv' l i fn,
    log_existsb (fLog fR REnv REnv' l) i fn = log_existsb l (fR i) fn.
  Proof.
    unfold log_existsb; intros. unfold fLog. rewrite getenv_create. auto.
  Qed.

  Lemma may_read_flog:
    forall reg_t reg_t' (fR: reg_t' -> reg_t) REnv REnv' l p i,
    may_read (fLog fR REnv REnv' l) p i = may_read l p (fR i).
  Proof.
    unfold may_read. intros.
    rewrite ! existsb_flog. reflexivity.
  Qed.

  Lemma log_cons_flog:
    forall
      reg_t reg_t' (fR: reg_t' -> reg_t) (ed: EqDec reg_t') REnv REnv' l i le
      (inj: forall i j, i <> j -> fR i <> fR j),
    log_cons i le (fLog fR REnv REnv' l) =
      fLog fR REnv REnv' (log_cons (fR i) le l).
  Proof.
    unfold fLog. unfold log_cons. intros.
    rewrite <- (create_getenv_id REnv' (putenv REnv' _ _ _)).
    apply create_funext. intros.
    destruct (eq_dec i k).
    - subst. rewrite get_put_eq.
      rewrite get_put_eq.
      rewrite getenv_create. auto.
    - rewrite get_put_neq. 2: auto.
      rewrite getenv_create.
      rewrite get_put_neq. auto. apply inj; auto.
  Qed.

  Lemma log_cons_flog':
    forall
      reg_t reg_t' (fR: reg_t' -> reg_t) (ed: EqDec reg_t') REnv REnv' l l0 i le
      (inj: forall i j, i <> j -> fR i <> fR j),
    fLog' fR REnv REnv' (log_cons i le l) l0 =
      (log_cons (fR i) le (fLog' fR REnv REnv' l l0)).
  Proof.
    unfold fLog'. unfold log_cons. intros.
    etransitivity. 2: apply create_getenv_id.
    apply create_funext. intros.
    destr.
    - apply fRinv_correct_inv in Heqo. subst.
      destruct (eq_dec i r).
      + subst. rewrite get_put_eq.
        rewrite get_put_eq.
        rewrite getenv_create. rewrite fRinv_correct; auto.
      + rewrite get_put_neq. 2: auto.
        rewrite getenv_create.
        rewrite get_put_neq. 2: apply inj; auto.
        rewrite getenv_create. rewrite fRinv_correct; auto.
    - rewrite get_put_neq.
      rewrite getenv_create. rewrite Heqo. auto.
      intro; subst. rewrite fRinv_correct in Heqo; auto. congruence.
  Qed.

  Lemma log_app_flog:
    forall reg_t reg_t' (fR: reg_t' -> reg_t) REnv REnv' l1 l2,
    fLog fR REnv REnv' (log_app l1 l2) =
      log_app (fLog fR REnv REnv' l1) (fLog fR REnv REnv' l2).
  Proof.
    unfold fLog. unfold log_app. intros.
    rewrite <- (create_getenv_id REnv' (map2 REnv' _ _ _)).
    apply create_funext. intros.
    rewrite ! getenv_map2.
    rewrite ! getenv_create. auto.
  Qed.

  Lemma may_write_flog:
    forall reg_t reg_t' (fR: reg_t' -> reg_t) REnv REnv' l1 l2 p i,
    may_write (fLog fR REnv REnv' l1) (fLog fR REnv REnv' l2) p i =
      may_write l1 l2 p (fR i).
  Proof.
    unfold may_write. intros.
    rewrite <- log_app_flog.
    rewrite ! existsb_flog. reflexivity.
  Qed.

  Lemma find_flog:
    forall
      {T} reg_t reg_t' (fR: reg_t' -> reg_t) REnv REnv' l i (fn: _ -> option T),
    log_find (fLog fR REnv REnv' l) i fn = log_find l (fR i) fn.
  Proof. unfold log_find; intros. unfold fLog. rewrite getenv_create. auto. Qed.

  Lemma latest_write0_flog:
    forall reg_t reg_t' (fR: reg_t' -> reg_t) REnv REnv' l i,
    latest_write0 (fLog fR REnv REnv' l) i = latest_write0 l (fR i).
  Proof.
    unfold latest_write0.
    intros; rewrite find_flog; auto.
  Qed.

  Notation "'let/opt4' v1 ',' v2 ',' v3 ',' v4 ':=' expr 'in' body" :=
    (opt_bind expr (fun '(v1, v2, v3, v4) => body)) (at level 200).

  Lemma fLog_fLog' {reg_t reg_t'} {REnv: Env reg_t} {REnv': Env reg_t'}:
    forall fR (inj: forall i j, i <> j -> fR i <> fR j) l0 l,
    fLog fR REnv REnv' (fLog' fR REnv REnv' l0 l) = l0.
  Proof.
    unfold fLog , fLog'. intros.
    transitivity (create REnv' (getenv REnv' l0)). 2: apply create_getenv_id.
    apply create_funext. intros.
    rewrite getenv_create.
    rewrite fRinv_correct. auto. auto.
  Qed.

  Lemma fLog'_fLog {reg_t reg_t'} {REnv: Env reg_t} {REnv': Env reg_t'}:
    forall fR l0,
    fLog' fR REnv REnv' (fLog fR REnv REnv' l0) l0 = l0.
  Proof.
    unfold fLog , fLog'. intros.
    transitivity (create REnv (getenv REnv l0)). 2: apply create_getenv_id.
    apply create_funext. intros.
    destr.
    rewrite getenv_create.
    apply fRinv_correct_inv in Heqo. subst; auto.
  Qed.

  Lemma fLog'_fLog2 {reg_t reg_t'} {REnv: Env reg_t} {REnv': Env reg_t'}:
    forall
      fR l0 l1 (EXT: forall r, getenv REnv l0 (fR r) = getenv REnv l1 (fR r)),
    fLog' fR REnv REnv' (fLog fR REnv REnv' l0) l1 = l1.
  Proof.
    unfold fLog , fLog'. intros.
    etransitivity. 2: apply create_getenv_id.
    apply create_funext. intros. destr. rewrite getenv_create.
    apply fRinv_correct_inv in Heqo. subst; auto.
  Qed.

  Lemma fLog'_fLog3 {reg_t reg_t'} {REnv: Env reg_t} {REnv': Env reg_t'}:
    forall fR (inj: forall i j, i <> j -> fR i <> fR j) l0 l1
      (EXT:
        forall k, (forall r, k <> fR r)
        -> getenv REnv l0 k = getenv REnv l1 k
      ),
    fLog' fR REnv REnv' (fLog fR REnv REnv' l0) l1 = l0.
  Proof.
    unfold fLog , fLog'. intros.
    etransitivity. 2: apply create_getenv_id.
    apply create_funext. intros.
    destr.
    rewrite getenv_create.
    apply fRinv_correct_inv in Heqo. subst; auto.
    symmetry; apply EXT. intros r EQ; subst.
    rewrite fRinv_correct in Heqo. easy. auto.
  Qed.

  Lemma fLog'_fLog' {reg_t reg_t'} {REnv: Env reg_t} {REnv': Env reg_t'}:
    forall fR l0 l1 l2,
    fLog' fR REnv REnv' l1 (fLog' fR REnv REnv' l2 l0) =
      fLog' fR REnv REnv' l1 l0.
  Proof.
    unfold fLog'. intros. apply create_funext. intros. destr.
    rewrite getenv_create. rewrite Heqo. auto.
  Qed.


  Context {reg_t' ext_fn_t': Type}.

  Fixpoint check_ucall_module_inj
    {reg_t ext_fn_t} (a: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t)
    {struct a}
  : Prop :=
    match a with
    | USugar (UCallModule fR fSigma fn args) =>
      Inj fR /\ Forall (fun x => x) (map (check_ucall_module_inj) args)
      /\ check_ucall_module_inj (int_body fn)
    | UError e => True
    | UFail _ => True
    | UVar var => True
    | @UConst _ _ _ _ _ tau cst => True
    | UAssign k a => check_ucall_module_inj a
    | USeq a1 a2 => check_ucall_module_inj a1 /\ check_ucall_module_inj a2
    | UBind k a1 a2 => check_ucall_module_inj a1 /\ check_ucall_module_inj a2
    | UIf cond athen aelse =>
      check_ucall_module_inj cond /\ check_ucall_module_inj athen
      /\ check_ucall_module_inj aelse
    | URead prt idx => True
    | UWrite prt idx v => check_ucall_module_inj v
    | UUnop fn arg => check_ucall_module_inj arg
    | UBinop fn arg1 arg2 =>
      check_ucall_module_inj arg1 /\ check_ucall_module_inj arg2
    | UExternalCall fn arg1 => check_ucall_module_inj arg1
    | UInternalCall f args =>
      Forall (fun x => x) (map (@check_ucall_module_inj reg_t ext_fn_t) args)
      /\ check_ucall_module_inj (int_body f)
    | UAPos p a => check_ucall_module_inj a
    | USugar UErrorInAst => True
    | USugar USkip => True
    | USugar (UConstBits v) => True
    | USugar (UConstString s) => True
    | USugar (UConstEnum sig name) => True
    | USugar (UProgn aa) => Forall (fun x => x) (map check_ucall_module_inj aa)
    | USugar (ULet bindings body) =>
      Forall
        (fun x => x) (map (fun '(_, a) => check_ucall_module_inj a) bindings)
      /\ check_ucall_module_inj body
    | USugar (UWhen cond body) =>
      check_ucall_module_inj cond /\ check_ucall_module_inj body
    | USugar (USwitch var default branches) =>
      check_ucall_module_inj var
      /\ Forall
        (fun x => x)
        (map
          (fun '(cond, body) => check_ucall_module_inj cond
            /\ check_ucall_module_inj body
          )
          branches
        )
      /\ check_ucall_module_inj default
    | USugar (UStructInit sig fields) =>
      Forall (fun x => x) (map (fun '(_, a) => check_ucall_module_inj a) fields)
    | USugar (UArrayInit tau elements) =>
      Forall (fun x => x) (map (check_ucall_module_inj) elements)
    end.

  Definition val_eq_dec (v1 v2: val ) : {v1 = v2} + {v1 <> v2}.
  Proof.
    intros. destruct (val_beq v1 v2) eqn:?.
    left; apply val_beq_correct; auto.
    right; apply val_beq_false; auto.
  Defined.

  Lemma val_beq_eq_dec:
    forall {C:Type} (A B: C) v1 v2,
    (if val_beq v1 v2 then A else B) = (if val_eq_dec v1 v2 then A else B).
  Proof.
    intros.
    destruct (val_beq v1 v2) eqn:?.
    destr. apply val_beq_correct in Heqb; congruence.
    destr. apply val_beq_false in Heqb. congruence.
  Qed.

  Lemma interp_action_desugar_ok:
    forall
      (a: Syntax.uaction pos_t var_t fn_name_t reg_t' ext_fn_t')
      (CUMI: check_ucall_module_inj a),
    desugar_ok _ _ a.
  Proof.
    red. intros ua. pattern reg_t', ext_fn_t' , ua.
    match goal with
    | |- ?P _ _ ua => set (PP:=P)
    end.
    remember (size_uaction ua).
    revert reg_t' ext_fn_t' ua Heqn.
    pattern n.
    eapply Nat.strong_right_induction with (z:=0). 2: lia.
    intros n0 _ Plt reg_t' ext_fn_t' ua Heqn. subst.
    assert (Plt':
      forall
        reg_t ext_fn_t (a: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t),
        size_uaction a < size_uaction ua -> PP reg_t ext_fn_t a
    ).
    { intros. eapply Plt. 3: reflexivity. lia. auto. } clear Plt.
    rename Plt' into IHua. clear n. unfold PP.
    unfold desugar_action in *.
    Opaque ContextEnv.
    destruct ua; intros; simpl;
    fold (desugar_action'
      (pos_t:=pos_t) (var_t:=var_t) (fn_name_t:=fn_name_t) (reg_t:=reg_t)
      (ext_fn_t:=ext_fn_t) (reg_t':=reg_t') (ext_fn_t':=ext_fn_t')
    ); eauto.
    - unfold desugar_action'.
      unfold interp_action.
      unfold opt_bind. destr; auto.
      simpl.
      rewrite fLog'_fLog. auto.
    - rewrite fLog'_fLog. auto.
    - cbn. rewrite <- (IHua) with (REnv':=REnv').
      unfold opt_bind.
      destr. destruct p0.  destruct p0. simpl. auto. simpl. auto.
      simpl. lia. auto. auto.
    - cbn. rewrite <- (IHua) with (REnv':=REnv').
      unfold opt_bind.
      destr. destruct p0.  destruct p0. simpl.
      rewrite <- (IHua) with (REnv':=REnv').
      rewrite fLog_fLog'; auto.
      unfold fState'. unfold opt_bind. destr.
      destruct p0. destruct p0.
      rewrite fLog'_fLog'. auto. simpl. lia. simpl in *. tauto. auto.
      reflexivity. simpl. lia.
      simpl in *; tauto. auto.
    - rewrite <- (IHua) with (REnv':=REnv').
      unfold opt_bind.
      destr; auto. destruct p0. destruct p0. simpl.
      rewrite <- (IHua) with (REnv':=REnv').
      rewrite fLog_fLog'.
      destr; auto. destruct p0. destruct p0. simpl.
      rewrite fLog'_fLog'. auto.
      auto. simpl; lia. simpl in *; tauto.
      auto. simpl; lia. simpl in *; tauto. auto.
    - rewrite <- (IHua) with (REnv':=REnv').
      unfold opt_bind.
      destr; auto. destruct p0. destruct p0. simpl.
      destr; auto. destr; auto. destr; auto. destr; auto.
      rewrite <- (IHua) with (REnv':=REnv')
        by (auto; simpl in *; try tauto; lia).
      rewrite fLog_fLog'; auto.
      unfold fState'. repeat destr.
      unfold opt_bind; repeat destr; auto. rewrite fLog'_fLog'; auto.
      rewrite <- (IHua) with (REnv':=REnv')
        by (auto; simpl in *; try tauto; lia).
      rewrite fLog_fLog'; auto.
      unfold fState'. repeat destr.
      unfold opt_bind; repeat destr; auto. rewrite fLog'_fLog'; auto.
      simpl; lia.
      simpl in *. tauto.
      auto.
    - rewrite may_read_flog. destr; auto.
      simpl.
      rewrite log_cons_flog; auto. f_equal. f_equal.
      f_equal.
      unfold fLog', fLog.
      etransitivity. 2: apply create_getenv_id.
      apply create_funext. intros. destr.
      rewrite getenv_create. apply fRinv_correct_inv in Heqo; subst; auto.
      unfold log_cons. rewrite get_put_neq. auto. intro; subst.
      erewrite fRinv_correct in Heqo. easy. auto.
      destr; auto. rewrite getenv_create. auto.
      rewrite <- log_app_flog.
      rewrite latest_write0_flog. rewrite getenv_create. auto.
      apply (@EqDec_FiniteType _ (finite_keys REnv')).
    - rewrite <- (IHua) with (REnv':=REnv') by (auto; simpl; lia).
      destruct (interp_action) as [((al & vv) & g)|] eqn:?; simpl; auto.
      rewrite <- may_write_flog with (REnv':=REnv').
      rewrite fLog_fLog'; auto.
      destr; auto. simpl. rewrite log_cons_flog'; auto.
      apply (@EqDec_FiniteType _ (finite_keys REnv')).
    - rewrite <- (IHua) with (REnv':=REnv') by (auto; simpl; lia).
      destruct (interp_action) as [((al & vv) & g)|] eqn:?; simpl; auto.
      unfold opt_bind.
      destr; auto.
    - rewrite <- (IHua) with (REnv':=REnv')
        by (auto; simpl in *; try tauto; lia).
      destruct (interp_action) as [((al & vv) & g)|] eqn:?; simpl; auto.
      rewrite <- (IHua) with (REnv':=REnv')
        by (auto; simpl in *; try tauto; lia).
      rewrite fLog_fLog'; auto.
      destruct (interp_action _ _ _ _ _ ua2) as [((al' & vv') & g')|]
      eqn:?; simpl; auto. unfold opt_bind. destr; auto.
      rewrite fLog'_fLog'; auto.
    - rewrite <- (IHua) with (REnv':=REnv')
        by (auto; simpl in *; try tauto; lia).
      destruct (interp_action) as [((al & vv) & g)|] eqn:?; simpl; auto.
    - cbn.
      assert (
        forall acc, fold_left (
          fun
            (acc : option (Log _ * list val * list (var_t * val)))
            (a : uaction  reg_t ext_fn_t)
          =>
           let/opt3 action_log0, l, Gamma0 := acc in (
             let/opt3 action_log1, v, Gamma1 :=
               interp_action r sigma Gamma0 sched_log action_log0 a
             in Some (action_log1, v :: l, Gamma1)
           )
        ) (map (fun a  => desugar_action' p fR fSigma a) args) acc
        =
          let/opt3 al, lv, g :=
            fold_left (fun
              (acc : option (Log _ * list val * list (var_t * val)))
              (a : uaction reg_t' ext_fn_t')
            =>
             let/opt3 action_log0, l, Gamma0 := acc in (
              let/opt3 action_log1, v, Gamma1 :=
                interp_action
                  (create REnv' (fun idx : reg_t' => getenv REnv r (fR idx)))
                  (fun f : ext_fn_t' => sigma (fSigma f)) Gamma0
                  (fLog fR REnv REnv' sched_log) action_log0 a
              in
              Some (action_log1, v :: l, Gamma1))
            ) args
            (let/opt3 al, l, g := acc in Some (fLog fR REnv REnv' al, l, g))
            in let/opt3 l0, _, _ := acc
          in Some (fLog' fR REnv REnv' al l0, lv, g)
      ).
      {
        assert (forall arg, In arg args -> PP _ _ arg).
        { intros; eapply IHua. simpl.
          clear IHua.
          cut (size_uaction arg <= list_sum (map size_uaction args)). cbn. lia.
          revert arg H. induction args; simpl; intros; eauto. easy.
          destruct H. subst. lia.
          apply IHargs in H. lia.
          simpl in *. intuition. inv H0; auto.
        }
        revert H. clear - CUMI inj.
        induction args; simpl; intros; eauto.
        destruct acc; simpl; auto. destruct p0, p0; simpl.
        rewrite fLog'_fLog; auto.
        rewrite IHargs; auto.
        destruct acc; simpl; auto. destruct p0 as ((l & lv) & Gamma').
        rewrite <- H with (REnv':=REnv'); auto. simpl.
        destruct (interp_action _ _ _ _ _ a) as [((? & ?) & ?)|] eqn:?;
          simpl; auto.
        rewrite fLog_fLog'; auto.
        unfold opt_bind. destr; auto.
        destruct p0, p0.
        rewrite fLog'_fLog'; auto.
        rewrite fold_left_none. simpl. auto. simpl. auto.
        simpl in CUMI; destruct CUMI. inv H0; auto.
        simpl in CUMI; destruct CUMI. inv H0; auto.
        simpl; intuition.
      }
      rewrite H. clear H. simpl.
      unfold opt_bind at 1. unfold Log. destr; setoid_rewrite Heqo; simpl; auto.
      destruct p0, p0. simpl.
      rewrite <- IHua with (REnv':=REnv'); auto. 2: cbn; lia.
      rewrite fLog_fLog'; auto.
      unfold opt_bind.
      destr; simpl; auto.
      destruct p0. destruct p0. simpl. rewrite fLog'_fLog'. auto.
      simpl in CUMI. tauto.
    - cbn. apply IHua. cbn; lia. auto. auto.
    - change (desugar_action' p fR fSigma (USugar s))
        with (desugar p fR fSigma s).
      destruct s; simpl; intros; auto.
      + rewrite fLog'_fLog. reflexivity.
      + rewrite fLog'_fLog. reflexivity.
      + rewrite fLog'_fLog. reflexivity.
      + cbn. destr; auto. simpl.
        rewrite fLog'_fLog. auto.
      + assert (forall a, In a aa -> PP _ _ a).
        { induction aa; simpl; intros; eauto. easy.
          destruct H; subst; eauto.
          apply IHua. cbn. lia.
          eapply IHaa; eauto.
          intros; eapply IHua.
          cbn in *. clear - H0. unfold list_sum, list_sum' in H0. lia.
          clear - CUMI. simpl in *. inv CUMI; auto.
        }
        clear IHua.
        change (desugar p fR fSigma (UProgn aa))
          with (uprogn (map (desugar_action' p fR fSigma) aa)).
        assert (
          forall
            (Gamma : list (var_t * val)) (action_log sched_log : Log _)
            (p : pos_t) v0,
          aa <> []
          -> fState'
            fR REnv REnv'
            (fold_left (
              fun (acc : option (Log _ * val * list (var_t * val))) a =>
                let/opt3 action_log0, _, Gamma0 := acc in
                interp_action
                  (create REnv' (fun idx : reg_t' => getenv REnv r (fR idx)))
                  (fun f : ext_fn_t' => sigma (fSigma f)) Gamma0
                  (fLog fR REnv REnv' sched_log) action_log0 a
            ) aa (Some (fLog fR REnv REnv' action_log, v0, Gamma)))
            action_log
          = interp_action
            r sigma Gamma sched_log action_log
            (uprogn (map (desugar_action' p fR fSigma) aa))
        ).
        {
          revert aa H CUMI. simpl.
          induction aa; simpl; intros; eauto.
          - easy.
          - destruct aa; simpl in *. apply H. auto. inv CUMI; auto.
            auto.
            rewrite <-  H with (REnv':=REnv'); auto.
            destruct (interp_action _ _ _ _ _ a) eqn:?; simpl; auto.
            destruct p1. destruct p1. simpl.
            erewrite <- IHaa.
            rewrite fLog_fLog'; auto.
            unfold fState'. unfold opt_bind. destr; auto.
            destruct p1, p1; simpl; auto.
            rewrite fLog'_fLog'. auto. intros; eauto.
            inv CUMI. auto.
            exact v0. congruence.
            rewrite fold_left_none. reflexivity. simpl. auto.
            inv CUMI; auto.
        } intros.
        destruct aa. simpl. rewrite fLog'_fLog; auto.
        apply H0. congruence.
      + cbn.
        fold (desugar_action'
          (pos_t:=pos_t) (var_t:=var_t) (fn_name_t:=fn_name_t) (reg_t:=reg_t)
          (ext_fn_t:=ext_fn_t) (reg_t':=reg_t') (ext_fn_t':=ext_fn_t')
         ); eauto.
        revert action_log Gamma p.
        induction bindings; simpl; intros; eauto.
        * rewrite <- IHua with (REnv':=REnv').
          unfold opt_bind; destr. destr. destr.
          simpl. lia. simpl in CUMI. tauto. auto.
        * destr.
          cbn.
          simpl in CUMI.
          rewrite <- IHua with (REnv':=REnv'); try (auto; simpl in *; lia).
          2: destruct CUMI as [CUMI0 _]; inv CUMI0; auto.
          destruct (interp_action _ _ _ _ _ u) eqn:?; simpl; auto.
          2:{ rewrite fold_left_none. simpl; auto. intros; destr; simpl; auto. }
          { destruct p0. destruct p0.
            simpl.
            rewrite <- IHbindings; auto.
            rewrite fLog_fLog'; auto.
            destruct (fold_left _ _ _) eqn:?; simpl; auto.
            destruct p0.
            destruct (interp_action _ _ _ _ _ body) eqn:?; simpl; auto.
            destruct p0, p0. simpl.
            rewrite fLog'_fLog'; auto. simpl; intros. eapply IHua; eauto.
            simpl. lia.
            clear - CUMI. simpl. intuition. inv H; auto.
          }
      + fold (desugar_action'
          (pos_t:=pos_t) (var_t:=var_t) (fn_name_t:=fn_name_t) (reg_t:=reg_t)
          (ext_fn_t:=ext_fn_t) (reg_t':=reg_t')
          (ext_fn_t':=ext_fn_t')
        ); eauto.
        rewrite <- (IHua) with (REnv':=REnv')
          by (auto; simpl in *; try tauto; lia).
        destruct (interp_action _ _ _ _ _ cond)
          as [((? & ?) & ?)|] eqn:?; simpl; auto.
        rewrite <- (IHua) with (REnv':=REnv')
          by (auto; simpl in *; try tauto; lia).
        unfold fState'; repeat destr; simpl; auto.
        rewrite fLog_fLog'; auto.
        unfold opt_bind; destr; auto.
        repeat destr.
        rewrite fLog'_fLog'; auto.
      + cbn.
        fold (desugar_action'
          (pos_t:=pos_t) (var_t:=var_t) (fn_name_t:=fn_name_t) (reg_t:=reg_t)
          (ext_fn_t:=ext_fn_t) (reg_t':=reg_t') (ext_fn_t':=ext_fn_t')
        ); eauto.
        revert action_log Gamma p.
        induction branches; simpl; intros; eauto.
        rewrite <- IHua with (REnv':=REnv')
          by (auto; simpl in *; try tauto; lia).
        auto. destruct a. cbn.
        rewrite <- IHua with (REnv':=REnv')
          by (auto; simpl in *; try tauto; lia).
        destruct (interp_action _ _ _ _ _ var) eqn:?.
        2:{ clear. simpl. rewrite fold_left_none; simpl; auto. intros; destr. }
        destruct p0. destruct p0. simpl.
        simpl in CUMI. destruct CUMI as (CUMI0 & CUMI1 & CUMI2). inv CUMI1.
        rewrite <- IHua with (REnv':=REnv')
          by (auto; simpl in *; try tauto; lia).
        rewrite fLog_fLog'; auto.
        destruct (interp_action _ _ _ _ _ u) eqn:?; simpl; auto.
        2:{ clear. rewrite fold_left_none; simpl; auto. intros; destr. }
        destruct p0. destruct p0. simpl.
        rewrite <- IHua with (REnv':=REnv')
          by (auto; simpl in *; try tauto; lia).
        rewrite fLog_fLog'; auto.
        rewrite fLog'_fLog'; auto.
        rewrite <- IHbranches; auto.
        2: intros; eapply IHua; simpl in *; lia.
        rewrite fLog_fLog'; auto.
        rewrite ! val_beq_eq_dec.
        destruct val_eq_dec.
        * subst. destruct val_eq_dec; try congruence.
          destruct (interp_action _ _ _ _ _ u0) eqn:?; simpl.
          destruct p0. destruct p0.
          replace (fold_left _ _ _) with (Some (l4, Some v0, l3)).
          2: {
            clear. induction branches; simpl; intros; eauto. destruct a; auto.
          }
          simpl. rewrite fLog'_fLog'; auto.
          rewrite fold_left_none; simpl; auto. intros; destr.
        * destruct val_eq_dec; try congruence.
          destruct (fold_left _ _ _) eqn:?; simpl; auto.
          repeat destr.
          simpl. rewrite fLog'_fLog'; auto.
          unfold fState'. unfold opt_bind.
          repeat destr.
          rewrite fLog'_fLog'; auto.
        * clear - CUMI0 H1 H2 CUMI2.
          simpl. intuition.
      + cbn.
        fold (desugar_action'
          (pos_t:=pos_t) (var_t:=var_t) (fn_name_t:=fn_name_t) (reg_t:=reg_t)
          (ext_fn_t:=ext_fn_t) (reg_t':=reg_t') (ext_fn_t':=ext_fn_t')
        ); eauto.
        simpl.
        unfold ustruct_init.
        edestruct @uinit_action as (vs & UOSB & IA).
        rewrite UOSB. simpl.
        assert (structinit_ok:
          forall
            fields sched_log Gamma action_log u sig vs0 p
            (IH: forall u, In u (map snd fields) -> desugar_ok _ _ u)
            action_log' Gamma'
            (IA: (interp_action r sigma Gamma sched_log action_log u) =
              Some (
                fLog' fR REnv REnv' action_log' action_log, Struct sig vs0,
                Gamma'
              )
            )
            (LEN: List.length vs0 = List.length (struct_fields sig)),
          fState' fR REnv REnv' (let/opt3 action_log0, v, Gamma0
          := fold_left (
            fun
              (acc : option (_ULog * list val * list (var_t * val)))
              '(name, a)
            =>
              let/opt3 action_log0, vs0, Gamma0 := acc in
              let/opt3 action_log1, v, Gamma1 :=
                interp_action
                  (create REnv' (fun idx : reg_t' => getenv REnv r (fR idx)))
                  (fun f : ext_fn_t' => sigma (fSigma f)) Gamma0
                  (fLog fR REnv REnv' sched_log) action_log0 a
              in
              let/opt vs1 := subst_field_name (struct_fields sig) name v vs0 in
              Some (action_log1, vs1, Gamma1)
          ) fields (Some (action_log', vs0, Gamma')) in
          Some (action_log0, Struct sig v, Gamma0)) (action_log)
          = (interp_action
            r sigma Gamma sched_log action_log (
              fold_left (fun acc '(f, a) =>
                UBinop (PrimUntyped.UStruct2 (PrimUntyped.USubstField f)) acc a
              )
              (map (fun '(f, a) => (f, desugar_action' p fR fSigma a)) fields)
            u)
          )
        ).
        {
          clear CUMI UOSB IA IHua fields sig sched_log Gamma action_log p vs.
          induction fields; simpl; intros; eauto.
          destruct a; simpl in *.
          destruct (interp_action _ _ Gamma' _ _ u0) eqn:?.
          - destruct p0. destruct p0. simpl.
            destruct (subst_field_name (struct_fields sig) s v vs0) eqn:?.
            + simpl.
              erewrite <- IHfields. eauto.
              intros; eauto.
              simpl.
              rewrite IA. simpl.
              rewrite <- IH with (REnv':=REnv') by (auto; simpl; lia).
              rewrite fLog_fLog'; auto.
              rewrite Heqo. simpl. rewrite Heqo0. simpl.
              rewrite fLog'_fLog'; auto.
              Lemma subst_field_name_length:
                forall fields s v vs0 vs1,
                  subst_field_name fields s v vs0 = Some vs1 ->
                  List.length vs1 = List.length vs0.
              Proof.
                induction fields; simpl; intros; eauto.
                destr_in H; inv H.
                unfold opt_bind in H.
                repeat destr_in H; inv H. reflexivity.
                simpl. f_equal; eapply IHfields; eauto.
              Qed.
              erewrite subst_field_name_length; eauto.
            + Lemma subst_field_name_none:
                forall fields s v vs0,
                  List.length fields = List.length vs0 ->
                  subst_field_name fields s v vs0 = None ->
                  ~ In s (map fst fields).
              Proof.
                induction fields; simpl; intros; eauto.
                destruct a. destr_in H0; simpl in *; inv H.
                destr_in H0. inv H0.
                unfold opt_bind in H0. destr_in H0; inv H0.
                eapply IHfields in Heqo; eauto. intuition.
              Qed.
              Lemma subst_field_name_not_in_none:
                forall fields s v vs0,
                  ~ In s (map fst fields) ->
                  subst_field_name fields s v vs0 = None.
              Proof.
                induction fields; simpl; intros; eauto.
                destr.
                destruct a. simpl in *.
                destr. destr. intuition congruence.
                rewrite IHfields. simpl; auto. intuition.
              Qed.
              simpl.
              apply subst_field_name_none in Heqo0.
              Lemma interp_action_fold:
                forall
                  reg_t ext_fn_t REnv r sigma l
                  (u: Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t)
                  Gamma sched_log action_log,
                interp_action (REnv:=REnv) r sigma Gamma sched_log action_log u
                = None
                -> interp_action
                  (REnv:=REnv) r sigma Gamma sched_log action_log
                  (fold_left (fun acc '(f, a) =>
                    UBinop
                      (PrimUntyped.UStruct2 (PrimUntyped.USubstField f)) acc a
                  ) l u) = None.
              Proof.
                induction l; simpl; intros; eauto. destr.
                apply IHl. simpl. rewrite H. simpl. auto.
              Qed.
              rewrite interp_action_fold.
              rewrite fold_left_none; simpl; auto. intros; destr. auto.
              simpl. rewrite IA. simpl.
              rewrite <- IH with (REnv':=REnv') by (auto; simpl; lia).
              rewrite fLog_fLog'. rewrite Heqo. simpl.
              rewrite subst_field_name_not_in_none. reflexivity. auto.
              eauto. auto.
          - simpl.
            rewrite interp_action_fold.
            rewrite fold_left_none. simpl. auto.
            intros; destr. simpl. auto.
            simpl. rewrite IA. simpl.
            erewrite <- IH. rewrite fLog_fLog'; auto.
            rewrite Heqo. simpl. auto. auto. auto.
        }
        apply structinit_ok.
        red; intros; eapply IHua. simpl.
        { clear - H. revert u H.
          induction fields; simpl; intros; eauto. easy.
          destruct a; simpl in *.
          destruct H; subst; auto. lia.
          apply IHfields in H. lia.
        }
        simpl in CUMI.
        { clear - H CUMI. revert u H CUMI.
          induction fields; simpl; intros; eauto. easy.
          destruct a; simpl in *. inv CUMI.
          destruct H; subst; auto.
        }
        auto.
        rewrite IA.
        rewrite fLog'_fLog; auto.
        eapply uvalue_of_struct_bits_length; eauto.
      + cbn.
        fold (
          desugar_action'
            (pos_t:=pos_t) (var_t:=var_t) (fn_name_t:=fn_name_t) (reg_t:=reg_t)
            (ext_fn_t:=ext_fn_t) (reg_t':=reg_t') (ext_fn_t':=ext_fn_t')
        ); eauto. simpl.
        edestruct (
          uvalue_of_bits_succeeds
            (array_t
              {| array_type := tau; array_len := Datatypes.length elements |}
            )
            (List.concat
              (rev (repeat (repeat false (type_sz tau)) (List.length elements)))
            )
        ) as (x & EQ).
        erewrite length_concat_same. simpl. rewrite rev_length.
        rewrite Bits.rmul_correct.
        rewrite repeat_length. reflexivity.
        rewrite Forall_forall; intros x IN.
        apply in_rev in IN.
        apply repeat_spec in IN. subst. rewrite repeat_length. auto.
        simpl in EQ.
        unfold opt_bind in EQ. repeat destr_in EQ; try congruence.
        rewrite uvalue_of_list_bits_rew in Heqo0. inv EQ.
        rewrite bits_splitn_concat in Heqo. inv Heqo.
        rewrite rev_involutive in Heqo0.
        rewrite Heqo0. simpl.
        2:{
          rewrite Forall_forall; intros x IN.
          apply in_rev in IN.
          apply repeat_spec in IN. subst. rewrite repeat_length. auto.
        }
        2:{ rewrite rev_length. rewrite repeat_length. reflexivity. }
        assert (arrayinit_ok:
          forall tau n elements pos action_log sched_log Gamma p
            u l0 action_log' Gamma',
            let sig := {| array_type:= tau; array_len := n |} in
            forall
              (INIT:
                (interp_action r sigma Gamma sched_log action_log u)
                = Some (
                  fLog' fR REnv REnv' action_log' action_log, Array sig l0,
                  Gamma'
                )
              )
              (LEN: List.length l0 = n)
              (POS: pos + List.length elements = n)
              (IH: forall u0, In u0 elements -> desugar_ok _ _ u0),
            fState'
              fR REnv REnv'
              (
                let/opt4 _, action_log0, vs, Gamma0 :=
                fold_left (
                  fun
                    (acc : option (nat * _ULog * list val * list (var_t * val)))
                    a
                  =>
                    let/opt4 pos, action_log0, vs, Gamma0 := acc in (
                      let/opt3 action_log1, v, Gamma1
                      := interp_action
                        (create REnv'
                          (fun idx : reg_t' => getenv REnv r (fR idx))
                        )
                        (fun f : ext_fn_t' => sigma (fSigma f)) Gamma0
                        (fLog fR REnv REnv' sched_log) action_log0 a
                      in (
                        let/opt pat1 := take_drop pos vs
                          in match pat1 with
                          | (l1, []) => None
                          | (l1, _ :: l3) =>
                            Some (S pos, action_log1, l1 ++ v :: l3, Gamma1)
                          end
                      )
                    )
                )
                elements (Some (pos, action_log', l0, Gamma'))
                in Some (
                  action_log0, Array {| array_type := tau; array_len := n |} vs,
                  Gamma0
                )
              )
              action_log
            = (
              interp_action
                r sigma Gamma sched_log action_log (
                  snd (fold_left (fun '(pos, acc) a => (
                    S pos,
                    UBinop (PrimUntyped.UArray2 (PrimUntyped.USubstElement pos))
                      acc (desugar_action' p fR fSigma a)
                  )) elements (pos, u))
                )
            )
        ).
        { clear - inj.
          induction elements; simpl; intros; eauto.
          destruct (interp_action _ _ _ _ action_log' a)
            as [((al' & v0) & G')|] eqn:?.
          - simpl.
            edestruct (@take_drop_succeeds) as (la & lb & EQ).
            2: rewrite EQ. lia. simpl.
            destruct (take_drop_spec _ _ _ _ EQ) as (EQ1 & EQ2 & EQ3). subst.
            rewrite <- POS in EQ3.
            destruct lb; simpl in *; try lia.
            generalize IH as IH'. intro.
            specialize (IH _ (or_introl eq_refl)). red in IH.
            specialize (
              IH _ _ _ r sigma _ inj fSigma REnv' Gamma'
              (fLog' fR REnv REnv' action_log' action_log) sched_log p
            ).
            rewrite fLog_fLog' in IH; auto.
            rewrite Heqo in IH. simpl in IH.
            erewrite <- IHelements.
            2:{
              simpl. rewrite INIT. simpl. rewrite <- IH.
              simpl. rewrite fLog'_fLog'.
              rewrite take_drop_head. simpl. eauto. auto.
            } reflexivity.
            repeat rewrite app_length; simpl; auto.
            repeat rewrite app_length; simpl; auto. lia.
            intros; eapply IH'; eauto.
          - transitivity (@None (Log REnv * val * list (var_t * val))).
            clear. simpl.
            rewrite fold_left_none; simpl; auto.
            cut (
              interp_action r sigma Gamma sched_log action_log (
                UBinop
                  (PrimUntyped.UArray2 (PrimUntyped.USubstElement pos)) u
                  (desugar_action' p fR fSigma a)
              ) = None
            ).
            clear.
            generalize (S pos).
            generalize (
              UBinop
                (PrimUntyped.UArray2 (PrimUntyped.USubstElement pos)) u
                (desugar_action' p fR fSigma a)
            ).
            induction elements; simpl; intros; eauto.
            apply IHelements. intros; eauto.
            simpl. rewrite H. simpl. auto. simpl.
            rewrite INIT. simpl. rewrite <- IH; auto. rewrite fLog_fLog'; auto.
            rewrite Heqo. simpl. auto.
        }
        apply arrayinit_ok.
        clear arrayinit_ok.
        edestruct @uinit_action_array with (
          sig :=
            {| array_type := tau; array_len := Datatypes.length elements |}
        ) as (vs & vl & BS & F & FF & L &F2 & IA).
        rewrite IA.
        clear IA.
        cut (l0 = rev vl). intros ->; auto.
        rewrite fLog'_fLog; auto.
        { clear BS.
          apply uvalue_of_list_bits_inv in Heqo0.
          destruct Heqo0.
          assert (Forall (fun v =>
            Some v = uvalue_of_bits (tau:=tau) (repeat false (type_sz tau))
          ) vl).
          { clear - F2 FF. simpl in FF.
            revert F2 FF.
            induction 1; simpl; intros; eauto. inv FF.
            constructor; eauto.
          }
          simpl in *.
          eapply Forall2_length in F2.
          eapply same_lists. eauto.
          rewrite Forall_forall. intros x IN. apply in_rev in IN.
          revert x IN. rewrite <-Forall_forall; auto.
          rewrite rev_length; lia.
        }
        apply uvalue_of_list_bits_inv in Heqo0. intuition. reflexivity.
        red; intros; eapply IHua. simpl.
        revert H. clear.
        induction elements; simpl; intros; eauto. easy. destruct H; subst. lia.
        apply IHelements in H. lia.
        clear - CUMI H.
        revert H CUMI. clear.
        induction elements; simpl; intros; eauto. easy. inv CUMI.
        destruct H; subst; auto. auto.
      + fold (desugar_action'
          (pos_t:=pos_t) (var_t:=var_t) (fn_name_t:=fn_name_t) (reg_t:=reg_t)
          (ext_fn_t:=ext_fn_t) (reg_t':=module_reg_t)
          (ext_fn_t':=module_ext_fn_t)
        ); eauto.
        fold (desugar_action'
          (pos_t:=pos_t) (var_t:=var_t) (fn_name_t:=fn_name_t) (reg_t:=reg_t)
          (ext_fn_t:=ext_fn_t) (reg_t':=reg_t') (ext_fn_t':=ext_fn_t')
        ); eauto.
        assert (
          forall acc,
          fold_left
            (fun
                (acc : option (Log _ * list val * list (var_t * val)))
                (a : uaction  reg_t ext_fn_t)
              =>
                let/opt3 action_log0, l, Gamma0 := acc in (
                  let/opt3 action_log1, v, Gamma1 :=
                    interp_action r sigma Gamma0 sched_log action_log0 a
                  in Some (action_log1, v :: l, Gamma1)
                )
            )
            (map (fun a  => desugar_action' p fR fSigma a) args) acc
          =
           let/opt3 al, l, g := acc in
           fState'
             fR REnv REnv'
             (fold_left (
                fun
                  (acc : option (Log _ * list val * list (var_t * val)))
                  (a : uaction reg_t' ext_fn_t')
                =>
                  let/opt3 action_log0, l, Gamma0 := acc in (
                    let/opt3 action_log1, v, Gamma1 :=
                      interp_action
                        (create
                          REnv' (fun idx : reg_t' => getenv REnv r (fR idx))
                        )
                        (fun f : ext_fn_t' => sigma (fSigma f))
                        Gamma0 (fLog fR REnv REnv' sched_log) action_log0 a
                    in Some (action_log1, v :: l, Gamma1)
                  )
                )
                args (Some (fLog fR REnv REnv' al, l, g))
             )
             al
        ).
        { assert (forall arg, In arg args -> PP _ _ arg).
          {
            intros; eapply IHua. simpl.
            clear IHua.
            cut (size_uaction arg <= list_sum (map size_uaction args)). cbn.
            lia.
            revert arg H. induction args; simpl; intros; eauto. easy.
            destruct H. subst. lia.
            apply IHargs in H. lia. clear - CUMI.
            simpl in *. intuition. inv H1; auto.
          }
          revert H. clear -CUMI inj.
          induction args; simpl; intros; eauto.
          destruct acc; simpl; auto. destruct p0, p0; simpl.
          rewrite fLog'_fLog; auto.
          erewrite IHargs; auto.
          destruct acc; simpl; auto. destruct p0 as ((l & lv) & Gamma').
          rewrite <- H with (REnv':=REnv'); auto. simpl.
          destruct (interp_action _ _ _ _ _ a)
            as [((? & ?) & ?)|] eqn:?; simpl; auto.
          - rewrite fLog_fLog'; auto.
            unfold fState', opt_bind. destr; auto.
            destruct p0, p0.
            rewrite fLog'_fLog'. auto.
          - rewrite fold_left_none. reflexivity. simpl. auto.
          - clear -CUMI.
            simpl in *; intuition. inv H1; auto.
          - clear -CUMI.
            simpl in *; intuition. inv H1; auto.
        }
        assert (Inj fR0). { clear - CUMI. simpl in CUMI. intuition. }
        erewrite H. simpl.
        destruct (fold_left _ _ _) eqn:?; simpl; auto.
        destruct p0, p0. simpl.
        erewrite <- IHua with (REnv' := @ContextEnv _ _). 2: simpl; lia.
        simpl.
        replace (
          create ContextEnv (fun idx : module_reg_t =>
            getenv REnv'
            (create REnv' (fun idx0 : reg_t' => getenv REnv r (fR idx0)))
            (fR0 idx))
        ) with (
          create
            ContextEnv (fun idx : module_reg_t => getenv REnv r (fR (fR0 idx)))
        ).
        2:{ apply create_funext. intros; rewrite getenv_create. auto. }
        Lemma fLog_fLog
          {reg_t1 reg_t2 reg_t3: Type} {REnv: Env reg_t1} {REnv': Env reg_t2}
          {REnv'': Env reg_t3} (fR': reg_t3 -> reg_t2) (fR: reg_t2 -> reg_t1)
        :
          forall (l: Log REnv),
          fLog fR' REnv' REnv'' (fLog fR REnv REnv' l) =
          fLog (fun r => fR (fR' r)) REnv REnv'' l.
        Proof.
          unfold fLog. simpl; intros.
          apply create_funext. intros.
          rewrite getenv_create. auto.
        Qed.
        rewrite ! fLog_fLog.
        replace (
          fLog
            (fun r0 : module_reg_t => fR (fR0 r0)) REnv ContextEnv
            (fLog' fR REnv REnv' _u _)
        ) with (fLog fR0 REnv' ContextEnv _u).
        2:{
          rewrite <- (@fLog_fLog) with (REnv':=REnv').
          rewrite fLog_fLog'; auto.
        }
        { unfold opt_bind. destr; auto.
          destruct p0, p0. simpl. f_equal. f_equal. f_equal.
          unfold fLog'. apply create_funext. simpl; intros.
          destr.
          - apply fRinv_correct_inv in Heqo0. subst.
            rewrite getenv_create.
            destr.
            + apply fRinv_correct_inv in Heqo0. subst.
              change (fR (fR0 m)) with ((fun r => fR (fR0 r)) m).
              rewrite fRinv_correct; auto.
            + rewrite fRinv_correct'. rewrite getenv_create.
              rewrite fRinv_correct; auto.
              intros; apply inj. intro; subst.
              rewrite fRinv_correct in Heqo0; auto. easy.
          - rewrite fRinv_correct'. rewrite getenv_create.
            rewrite Heqo0. auto.
            intros r' EQ.
            subst.
            rewrite fRinv_correct in Heqo0. easy. auto.
        }
        clear - CUMI. simpl in CUMI. intuition.
        intros; eapply inj; eauto.
  Qed.
End Desugar.

Section Eq.
  Context {pos_t var_t fn_name_t reg_t ext_fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {var_t_eq_dec: EqDec var_t}.

  Context {TR: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.
  Context {REnv: Env reg_t}.
  Context (r: env_t REnv (fun x : reg_t => val)).
  Context (sigma: forall f: ext_fn_t, val -> val).
  Context (tr: env_t REnv (fun x : reg_t => TR x)).
  Context (tsigma: forall f, Sig_denote (Sigma f)).

  Hypothesis tsigma_correct:
    forall f v, sigma f (val_of_value v) = val_of_value (tsigma f v).

  Definition env_t_R
    {K: Type} {V1 V2: K -> Type} (R: forall k, V1 k -> V2 k -> Prop) (e: Env K)
    (e1: env_t e (fun x => V1 x)) (e2: env_t e (fun x => V2 x))
  : Prop :=
    forall k, R k (getenv e e1 k) (getenv e e2 k).

  Definition logentry_eq {V:type} (ule: LogEntry val) (le: Logs.LogEntry V)
  : Prop :=
    (kind ule) = (Logs.kind le) /\ port ule = Logs.port le
    /\
    match Logs.kind le as l return (
      match l return Type with
      | Logs.LogRead  => unit
      | Logs.LogWrite => type_denote V
      end -> Prop
    ) with
    | Logs.LogRead  => fun _ => UntypedLogs.val ule = Bits []
    | Logs.LogWrite => fun v => UntypedLogs.val ule = val_of_value v
    end (Logs.val le).

  Definition rlog_eq {V:type} (url: RLog val) (rl: Logs.RLog V) :=
    Forall2 (fun ule le => logentry_eq ule le) url rl.

  Notation Log := (@_ULog val reg_t REnv).
  Notation uaction := (uaction pos_t var_t fn_name_t reg_t ext_fn_t).

  Definition log_eq
    REnv (ul: env_t REnv (fun _ => RLog val)) (l: Logs.Log TR REnv)
  : Prop :=
    env_t_R
      (V1:= fun k => Logs.RLog (TR k)) (V2:= fun k => RLog val)
      (fun k v1 v2 => rlog_eq v2 v1) REnv l ul.

  Inductive gamma_eq :
    forall (sig: tsig var_t), list (var_t * val)
    -> TypedSemantics.tcontext sig -> Prop
  :=
  | gamma_eq_nil:
    gamma_eq [] [] (CtxEmpty)
  | gamma_eq_cons:
    forall sig k t v ug g,
    gamma_eq sig ug g
    -> gamma_eq ((k,t)::sig) ((k,val_of_value v)::ug) (@CtxCons _ _ _ (k,t) v g)
  .

  Lemma gamma_eq'
    {sig} (UGamma: list (var_t * val)) (Gamma: TypedSemantics.tcontext sig)
  :
    gamma_eq sig UGamma Gamma
    -> forall k t (m: member _ sig),
    assoc k sig = Some (existT _ t m)
    -> Some (val_of_value (cassoc m Gamma)) =  (list_assoc UGamma k).
  Proof.
    induction 1; simpl; intros; eauto. congruence. simpl in *.
    repeat destr_in H0; simpl in *; subst.
    unfold eq_rect_r in H0; simpl in H0.
    inv H0.
    apply Eqdep_dec.inj_pair2_eq_dec in H3. subst. 2: apply eq_dec.
    simpl. auto.
    inv H0.
    apply Eqdep_dec.inj_pair2_eq_dec in H3. subst. 2: apply eq_dec.
    simpl. eauto.
    inv H0.
  Qed.

  Lemma cast_action'_eq:
    forall
      (p: pos_t) (sig: tsig var_t) (tau1 tau2: type)
      (a: TypedSyntax.action pos_t var_t fn_name_t TR Sigma sig tau1)
      (e: error_message var_t fn_name_t) a',
    TypeInference.cast_action' TR Sigma p tau2 a e = Success a' ->
    exists p : tau1 = tau2, a' = eq_rect _ _ a _ p.
  Proof.
    unfold TypeInference.cast_action'. intros.
    destr_in H. subst.
    unfold eq_rect_r in H. simpl in H. inv H.
    exists eq_refl; reflexivity. inv H.
  Qed.

  Lemma cast_action_eq:
    forall
      (p: pos_t) (sig: tsig var_t) (tau1 tau2: type)
      (a: TypedSyntax.action pos_t var_t fn_name_t TR Sigma sig tau1) a',
    TypeInference.cast_action TR Sigma p tau2 a = Success a'
    -> exists p : tau1 = tau2, a' = eq_rect _ _ a _ p.
  Proof.
    intros. unfold TypeInference.cast_action in H.
    eapply cast_action'_eq; eauto.
  Qed.

  Lemma list_assoc_gss:
    forall {K V: Type} (eq: EqDec K) (l: list (K * V)) k v,
    list_assoc (list_assoc_set l k v) k = Some v.
  Proof.
    induction l; simpl; intros; eauto. destr.
    repeat destr; eauto.
    simpl. rewrite Heqs. auto.
    simpl. rewrite Heqs. eauto.
  Qed.

  Lemma list_assoc_gso:
    forall {K V: Type} (eq: EqDec K) (l: list (K * V)) k k' v (d: k <> k'),
    list_assoc (list_assoc_set l k v) k' = list_assoc l k'.
  Proof.
    induction l; simpl; intros; eauto.
    destr.
    repeat destr; simpl; eauto.
    - rewrite Heqs0. auto.
    - rewrite Heqs0. auto.
    - rewrite Heqs0. eauto.
  Qed.

  Lemma gamma_eq_replace:
    forall
      sig g1 g2 (Geq: gamma_eq sig g1 g2) k t v (m: member (k, t) sig)
      (ASSOC:
        assoc k sig = Some (existT (fun k2 : type => member (k, k2) sig) t m)
      ),
    gamma_eq sig (list_assoc_set g1 k (val_of_value v)) (creplace m v g2).
  Proof.
    induction 1; simpl; intros; eauto. congruence.
    repeat destr_in ASSOC; simpl in *; try congruence.
    - subst. unfold eq_rect_r in ASSOC; simpl in ASSOC.
      inv ASSOC.
      apply Eqdep_dec.inj_pair2_eq_dec in H1. subst. 2: apply eq_dec.
      simpl. constructor. auto.
    - inv ASSOC.
      apply Eqdep_dec.inj_pair2_eq_dec in H1. subst. 2: apply eq_dec. simpl.
      constructor. eauto.
  Qed.

  Lemma log_eq_existsb:
    forall usched_log sched_log,
    log_eq REnv usched_log sched_log
    -> forall idx f uf, (
      forall ule idx le,
      ule = le -> uf ule idx = f le idx
    )
    -> Logs.log_existsb sched_log idx f = log_existsb usched_log idx uf.
  Proof.
    unfold Logs.log_existsb, log_existsb. intros.
    unfold log_eq in H. red in H.
    red in H.
    generalize (H idx).
    generalize (@getenv _ REnv (fun x => Logs.RLog (TR x)) sched_log idx).
    generalize (getenv REnv usched_log idx).
    clear - H0.
    induction 1; simpl; intros. auto.
    red in H. intuition.
    destruct x, y; simpl in *. subst.
    erewrite H0; eauto. f_equal. eauto.
  Qed.

  Lemma may_read_eq:
    forall usched_log sched_log,
    log_eq REnv usched_log sched_log
    -> forall port idx,
    Logs.may_read sched_log port idx = may_read usched_log port idx.
  Proof.
    unfold Logs.may_read, may_read.
    intros.
    rewrite ! log_eq_existsb
      with (f:=Logs.is_write0) (uf:=is_write0) (usched_log:=usched_log); auto.
    rewrite ! log_eq_existsb
      with (f:=Logs.is_write1) (uf:=is_write1) (usched_log:=usched_log); auto.
    destruct ule, le; simpl; auto; try easy.
    destruct ule, le; simpl; auto; try easy.
  Qed.

  Lemma log_eq_app:
    forall ul1 ul2 l1 l2,
    log_eq REnv ul1 l1 -> log_eq REnv ul2 l2
    -> log_eq REnv (log_app ul1 ul2) (Logs.log_app l1 l2).
  Proof.
    unfold log_app, Logs.log_app.
    unfold log_eq. unfold env_t_R.
    simpl. intros.
    rewrite ! getenv_map2.
    apply Forall2_app; eauto.
    apply H. apply H0.
  Qed.

  Lemma may_write_eq:
    forall usched_log sched_log,
    log_eq REnv usched_log sched_log
    -> forall urule_log rule_log,
    log_eq REnv urule_log rule_log
    -> forall port idx,
    Logs.may_write sched_log rule_log port idx
    = may_write usched_log urule_log port idx.
  Proof.
    unfold Logs.may_write, may_write.
    intros.
    generalize (log_eq_app _ _ _ _ H0 H).
    intros.
    rewrite ! log_eq_existsb
      with
        (f:=Logs.is_write0) (uf:=is_write0)
        (usched_log:=log_app urule_log usched_log);
    auto.
    rewrite ! log_eq_existsb
      with
        (f:=Logs.is_write1) (uf:=is_write1)
        (usched_log:=log_app urule_log usched_log);
    auto.
    rewrite ! log_eq_existsb
      with
        (f:=Logs.is_read1) (uf:=is_read1)
        (usched_log:=log_app urule_log usched_log);
    auto.
    destruct ule, le; simpl; auto; try easy.
    destruct ule, le; simpl; auto; try easy.
    destruct ule, le; simpl; auto; try easy.
  Qed.

  Lemma log_find_eq:
    forall ulog log,
    log_eq REnv ulog log
    -> forall idx, forall f uf, (
      forall ule (le: Logs.LogEntry (TR idx)),
      logentry_eq ule le -> uf ule = option_map (val_of_value) (f le)
    )
    -> option_map (val_of_value (tau:=TR idx)) (Logs.log_find log idx f)
    = (log_find ulog idx uf).
  Proof.
    unfold Logs.log_find, log_find.
    intros.
    red in H. red in H. red in H.
    generalize (H idx).
    generalize (@getenv _ REnv (fun x => Logs.RLog (TR x)) log idx).
    generalize (getenv REnv ulog idx).
    clear - H0.
    induction 1; simpl; intros. auto.
    erewrite H0; eauto. destr; simpl; eauto.
  Qed.

  Lemma latest_write0_eq:
    forall ulog log,
    log_eq REnv ulog log
    -> forall idx,
    option_map (val_of_value (tau:=TR idx)) (Logs.latest_write0 log idx)
    = (latest_write0 ulog idx).
  Proof.
    unfold Logs.latest_write0, latest_write0.
    intros.
    eapply log_find_eq. auto.
    intros. red in H0. intuition.
    destruct ule, le; simpl in *. subst.
    destr_in val0.
    - subst. reflexivity.
    - subst. destr; auto.
  Qed.

  Lemma log_eq_cons:
    forall idx ulog (log: Logs._Log) ule le,
    log_eq REnv ulog log -> logentry_eq ule le
    -> log_eq REnv (log_cons idx ule ulog) (Logs.log_cons idx le log).
  Proof.
    unfold log_eq. unfold env_t_R.
    unfold rlog_eq.
    intros. unfold log_cons, Logs.log_cons.
    destruct (eq_dec idx k).
    - subst. rewrite ! get_put_eq. constructor; eauto.
    - rewrite ! get_put_neq; eauto.
  Qed.

  Fixpoint assert_argtypes'
    {sig} (args_desc: tsig var_t)
    (args:
      list (
        pos_t
        * {
          tau : type & TypedSyntax.action pos_t var_t fn_name_t TR Sigma sig tau
        }
      )
    )
  : result (context (K := (var_t * type)) (fun k_tau =>
      TypedSyntax.action pos_t var_t fn_name_t TR Sigma sig (snd k_tau)
    ) args_desc) unit
  :=
    match args_desc, args with
    | [], [] => Success CtxEmpty
    | [], _ => Failure tt
    | _, [] => Failure tt
    | (name1, tau1) :: fn_sig, (pos1, arg1) :: args =>
      match TypeInference.cast_action TR Sigma pos1 tau1 (projT2 arg1) with
      | Success arg1 =>
        let/res ctx := assert_argtypes' fn_sig args in
        Success (CtxCons (name1, tau1) arg1 ctx)
      | _ => Failure tt
      end
    end.

  Lemma assert_argtypes'_eq :
    forall {T:Type} (sig: tsig var_t) args_desc args s ufn fname n p,
    TypeInference.assert_argtypes'
      (T:=T) TR Sigma ufn n fname p args_desc args = Success s
    <-> assert_argtypes' (sig:=sig) args_desc args = Success s.
  Proof.
    induction args_desc; simpl; intros; eauto.
    - destr; split; intuition congruence.
    - destruct a. split. intros.
      + destr_in H; [inv H|]. destr_in H.
        destr_in H; [|inv H].
        destr_in H; [|inv H]. inv H.
        erewrite (proj1 (IHargs_desc _ _ _ _ _ _)). eauto. eauto.
      + intros. destr_in H; [inv H|]. destr_in H.
        destr_in H; [|inv H].
        destr_in H; [|inv H]. inv H.
        erewrite (proj2 (IHargs_desc _ _ _ _ _ _)). eauto. eauto.
  Qed.

  Lemma result_list_map_length {A B F: Type} (f: A -> result B F):
    forall la lb,
    result_list_map f la = Success lb -> List.length lb = List.length la.
  Proof.
    induction la; simpl; intros; eauto. inv H; reflexivity.
    destr_in H; [|inv H].
    destr_in H; [|inv H]. inv H.
    simpl.
    erewrite IHla; eauto.
  Qed.

  Lemma result_list_map_app1 {A B F: Type} (f: A -> result B F):
    forall la1 la2 lb1 lb2,
    result_list_map f la1 = Success lb1
    -> result_list_map f la2 = Success lb2
    -> result_list_map f (la1 ++ la2) = Success (lb1 ++ lb2).
  Proof.
    induction la1; simpl; intros; eauto. inv H. simpl; auto.
    destr_in H; [|inv H]. destr_in H; [|inv H]. inv H.
    erewrite IHla1; eauto. simpl; auto.
  Qed.

  Lemma result_list_map_app2 {A B F: Type} (f: A -> result B F):
    forall la1 la2 lb,
    result_list_map f (la1 ++ la2) = Success lb
    -> exists lb1 lb2,
      result_list_map f la1 = Success lb1 /\ result_list_map f la2 = Success lb2
      /\ lb = lb1 ++ lb2.
  Proof.
    induction la1; simpl; intros; eauto.
    destr_in H; [|inv H].
    destr_in H; [|inv H]. inv H.
    edestruct IHla1 as (lb1 & lb2 & EQ1 & EQ2 & EQl). eauto. subst.
    rewrite EQ1, EQ2.
    eexists; eexists; repeat split; eauto.
  Qed.

  Lemma result_list_map_rev {A B F: Type} (f: A -> result B F):
    forall la lb,
    result_list_map f la = Success lb
    -> result_list_map f (rev la) = Success (rev lb).
  Proof.
    induction la; simpl; intros; eauto. inv H; reflexivity.
    destr_in H; [|inv H].
    destr_in H; [|inv H]. inv H.
    simpl. erewrite result_list_map_app1; eauto. simpl. rewrite Heqr0. auto.
  Qed.

  Lemma combine_nil_inv:
    forall {A B: Type} (la: list A) (lb: list B),
    List.length la = List.length lb -> combine la lb = [] -> la = [] /\ lb = [].
  Proof.
    induction la; simpl; intros.
    - destruct lb; simpl in *; auto. lia.
    - destruct lb. simpl in H. lia. inv H0.
  Qed.

  Lemma rev_nil_inv: forall {A:Type} (l: list A), rev l = [] -> l = [].
  Proof.
    destruct l; simpl in *. auto.
    intros.
    apply (f_equal (@List.length _)) in H.
    rewrite app_length in H; simpl in H; lia.
  Qed.

  Lemma combine_app:
    forall {A B : Type} (la1 la2 : list A) (lb1 lb2: list B),
    List.length la1 = List.length lb1 -> List.length la2 = List.length lb2 ->
    combine (la1 ++ la2) (lb1 ++ lb2) = combine la1 lb1 ++ combine la2 lb2.
  Proof.
    induction la1; simpl; intros; eauto.
    - destruct lb1; simpl in *; try lia. auto.
    - destruct lb1; simpl in *; try lia.
      rewrite IHla1 by lia. auto.
  Qed.

  Lemma combine_rev:
    forall {A B : Type} (la : list A) (lb: list B),
    List.length la = List.length lb ->
    rev (combine la lb) = combine (rev la) (rev lb).
  Proof.
    induction la; simpl; intros; eauto.
    destr. simpl in *; lia. simpl in *.
    rewrite IHla by lia.
    rewrite combine_app. simpl. auto.
    rewrite ! rev_length; lia.
    simpl; lia.
  Qed.

  Lemma combine_map:
    forall
      {A B C: Type} (f: A * B * C -> A * C) (g: A * B -> A)
      (FG: forall x y z, f (x,y,z) = (g (x,y), z)) (l1: list (A * B))
      (l2: list C),
    map f (combine l1 l2) = combine (map g l1) l2.
  Proof.
    induction l1; simpl; intros; eauto.
    destr. reflexivity. simpl. f_equal; eauto. destruct a; eauto.
  Qed.

  Hypothesis r_eq: forall i, getenv REnv r i = val_of_value (getenv REnv tr i).

  Lemma interp_action_correct:
    forall
      ua p sig tau a
      (TA:
        TypeInference.type_action TR Sigma p sig ua = Success (existT _ tau a)
      )
      (Gamma: TypedSemantics.tcontext sig) (UGamma: list (var_t * val))
      (GammaEq: gamma_eq sig UGamma Gamma) sched_log action_log action_log'
      usched_log uaction_log (SL: log_eq REnv usched_log sched_log)
      (AL: log_eq REnv uaction_log action_log) v Gamma',
    TypedSemantics.interp_action tr tsigma Gamma sched_log action_log a
    = Some (action_log', v, Gamma')
    -> exists uaction_log' UGamma',
    interp_action
      (pos_t:=pos_t) (fn_name_t := fn_name_t) r sigma UGamma usched_log
      uaction_log ua
    = Some (uaction_log', val_of_value v, UGamma')
      /\ log_eq REnv uaction_log' action_log' /\ gamma_eq sig UGamma' Gamma'.
  Proof.
    intros ua. pattern ua.
    match goal with
    | |- ?P ua => set (PP:=P)
    end.
    remember (size_uaction ua).
    revert ua Heqn.
    pattern n.
    eapply Nat.strong_right_induction with (z:=0). 2: lia.
    intros n0 _ Plt ua Heqn. subst.
    assert (Plt': forall a, size_uaction a < size_uaction ua -> PP a).
    { intros. eapply Plt. 3: reflexivity. lia. auto. } clear Plt.
    rename Plt' into IHua. clear n. unfold PP.
    destruct ua; simpl; intros.
    - inv TA.
    - inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. subst.
      simpl in H. inv H.
      apply eq_dec.
    - destr_in TA; inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst.
      simpl in H. inv H.
      unfold opt_result in Heqr0; destr_in Heqr0; inv Heqr0. destruct s.
      simpl.
      setoid_rewrite <- gamma_eq'. simpl.
      exists uaction_log, UGamma; split; eauto. eauto. eauto.
    - inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst.
      simpl in H. inv H.
      exists uaction_log, UGamma; split; eauto.
    - destr_in TA; [|inv TA].
      destr_in TA; [|inv TA].
      destr_in TA; [|inv TA]. inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec.
      subst. simpl in H.
      unfold opt_bind in H.
      destr_in H; [|inv H].
      destr_in H. destr_in H. inv H.
      unfold opt_result in Heqr0; destr_in Heqr0; inv Heqr0.
      destruct s. simpl in *.
      destruct s0. simpl in *.
      apply cast_action_eq in Heqr2.
      destruct Heqr2 as (pf & EQ). subst.
      simpl in Heqo.
      edestruct (IHua ua) as (ual' & g' & IA' & ALeq & Geq). lia. eauto.
      4: apply Heqo. eauto. eauto. eauto.
      rewrite IA'. simpl.
      eexists; eexists; repeat split; eauto.
      apply gamma_eq_replace; eauto.
    - destr_in TA; [|inv TA].
      destr_in TA; [|inv TA].
      destr_in TA; [|inv TA]. inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec.
      subst. simpl in H.
      unfold opt_bind in H.
      destr_in H; [|inv H].
      destr_in H. destr_in H.
      destruct s. simpl in *.
      apply cast_action_eq in Heqr1.
      destruct Heqr1 as (pf & EQ). subst.
      simpl in Heqo.
      edestruct (IHua ua1) as (ual' & g' & IA' & ALeq & Geq). lia. eauto.
      4: apply Heqo. eauto. eauto. eauto.
      rewrite IA'. simpl.
      destruct s1. simpl in *.
      edestruct (IHua ua2) as (ual2' & g2' & IA2' & ALeq2 & Geq2). lia. eauto.
      4: apply H. eauto. eauto. eauto.
      rewrite IA2'.
      eexists; eexists; repeat split; eauto.
    - destr_in TA; [|inv TA]. destr_in TA; [|inv TA].  inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec.
      subst. simpl in H.
      unfold opt_bind in H.
      destr_in H; [|inv H].
      destr_in H. destr_in H. destr_in H; [|inv H].
      destruct p2. destruct p2. inv H.
      destruct s, s0. simpl in *.
      edestruct (IHua ua1) as (ual' & g' & IA' & ALeq & Geq). lia. eauto.
      4: apply Heqo. eauto. eauto. eauto.
      rewrite IA'. simpl.
      edestruct (IHua ua2) as (ual2' & g2' & IA2' & ALeq2 & Geq2). lia. eauto.
      4: apply Heqo0. 2-3: eauto.
      constructor; eauto.
      setoid_rewrite IA2'. simpl.
      eexists; eexists; repeat split; eauto. inv Geq2.
      apply Eqdep_dec.inj_pair2_eq_dec in H4. 2: apply eq_dec.
      subst. simpl. auto.
    - destr_in TA; [|inv TA]. destr_in TA; [|inv TA]. destr_in TA; [|inv TA].
      destr_in TA; [|inv TA]. destr_in TA; [|inv TA]. inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec.
      subst. simpl in H.
      unfold opt_bind in H.
      destr_in H; [|inv H].
      destruct p0. destruct p0.
      destruct s. simpl in *.
      apply cast_action_eq in Heqr1.
      destruct Heqr1 as (pf & EQ). subst.
      simpl in Heqo.
      edestruct (IHua ua1) as (ual' & g' & IA' & ALeq & Geq). lia. eauto.
      4: apply Heqo. eauto. eauto. eauto.
      rewrite IA'. simpl.
      destruct s1, s2. simpl in *.
      apply cast_action_eq in Heqr4.
      destruct Heqr4 as (pf & EQ). subst.
      simpl in H.
      destr.
      + edestruct (IHua ua2) as (ual2' & g2' & IA2' & ALeq2 & Geq2). lia. eauto.
        4: apply H. eauto. eauto. eauto.
        rewrite IA2'. simpl.
        eexists; eexists; repeat split; eauto.
      + edestruct (IHua ua3) as (ual2' & g2' & IA2' & ALeq2 & Geq2). lia. eauto.
        4: apply H. eauto. eauto. eauto.
        rewrite IA2'. simpl.
        eexists; eexists; repeat split; eauto.
    - inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec.
      subst. simpl in H.
      erewrite may_read_eq in H; eauto.
      destr_in H; [|inv H]. inv H.
      eexists; eexists; repeat split; eauto.
      f_equal. f_equal. f_equal.
      rewrite ! r_eq. destr.
      erewrite <- latest_write0_eq; eauto.
      2: apply log_eq_app; eauto.
      destruct (Logs.latest_write0) eqn:?; simpl; auto.
      apply log_eq_cons; auto.
      red. simpl. auto.
    - destr_in TA; [|inv TA]. destr_in TA; [|inv TA]. inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec.
      subst. simpl in H.
      unfold opt_bind in H.
      destr_in H; [|inv H].
      destruct p0. destruct p0.
      destruct s. simpl in *.
      apply cast_action_eq in Heqr1.
      destruct Heqr1 as (pf & EQ). subst.
      simpl in Heqo.
      edestruct (IHua ua) as (ual' & g' & IA' & ALeq & Geq). lia. eauto.
      4: apply Heqo. eauto. eauto. eauto.
      rewrite IA'. simpl.
      erewrite may_write_eq in H; eauto.
      destr_in H; [|inv H]. inv H.
      eexists; eexists; repeat split; eauto.
      apply log_eq_cons; auto.
      red. simpl. auto.
    - destr_in TA; [|inv TA].
      destr_in TA; [|inv TA].
      destr_in TA; [|inv TA].
      inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec.
      subst. simpl in H.
      unfold opt_bind in H.
      destr_in H; [|inv H].
      destruct p0. destruct p0. inv H.
      destruct s. simpl in *.
      apply cast_action_eq in Heqr2.
      destruct Heqr2 as (pf & EQ). subst.
      simpl in Heqo.
      edestruct (IHua ua) as (ual' & g' & IA' & ALeq & Geq). lia. eauto.
      4: apply Heqo. eauto. eauto. eauto.
      rewrite IA'. simpl.
      unfold TypeInference.lift_fn1_tc_result in Heqr1.
      unfold result_map_failure in Heqr1. destr_in Heqr1; inv Heqr1.
      erewrite usigma1_correct; eauto. simpl.
      eexists; eexists; repeat split; eauto.
    - destr_in TA; [|inv TA]. destr_in TA; [|inv TA]. destr_in TA; [|inv TA].
      destr_in TA; [|inv TA]. destr_in TA; [|inv TA]. inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec.
      subst. simpl in H.
      unfold opt_bind in H.
      destr_in H; [|inv H].
      destruct p0. destruct p0.
      destr_in H; [|inv H].
      destruct p0. destruct p0.
      inv H.
      destruct s, s0. simpl in *.
      apply cast_action_eq in Heqr3.
      destruct Heqr3 as (pf & EQ). subst.
      simpl in Heqo.
      apply cast_action_eq in Heqr4.
      destruct Heqr4 as (pf & EQ). subst.
      simpl in Heqo0.
      edestruct (IHua ua1) as (ual' & g' & IA' & ALeq & Geq). lia. eauto.
      4: apply Heqo. eauto. eauto. eauto.
      rewrite IA'. simpl.
      edestruct (IHua ua2) as (ual2' & g2' & IA2' & ALeq2 & Geq2). lia. eauto.
      4: apply Heqo0. eauto. eauto. eauto.
      rewrite IA2'. simpl.
      unfold TypeInference.lift_fn2_tc_result in Heqr2.
      unfold result_map_failure in Heqr2. destr_in Heqr2; inv Heqr2.
      erewrite sigma2_correct; eauto. simpl.
      eexists; eexists; repeat split; eauto.
    - destr_in TA; [|inv TA].
      destr_in TA; [|inv TA].
      inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec.
      subst. simpl in H.
      unfold opt_bind in H.
      destr_in H; [|inv H].
      destruct p0. destruct p0. inv H.
      destruct s. simpl in *.
      apply cast_action_eq in Heqr1.
      destruct Heqr1 as (pf & EQ). subst.
      simpl in Heqo.
      edestruct (IHua ua) as (ual' & g' & IA' & ALeq & Geq). lia. eauto.
      4: apply Heqo. eauto. eauto. eauto.
      rewrite IA'. simpl.
      eexists; eexists; repeat split; eauto.
      rewrite tsigma_correct. eauto.
    - destr_in TA; [|inv TA]. destr_in TA; [|inv TA]. destr_in TA; [|inv TA].
      destr_in TA; [|inv TA]. inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec.
      subst. simpl in H.
      unfold opt_bind in H.
      destr_in H; [|inv H].
      destruct p0. destruct p0.
      destr_in H; [|inv H].
      destruct p0. destruct p0.
      inv H.
      destruct s1. simpl in *.
      apply cast_action_eq in Heqr3.
      destruct Heqr3 as (pf & EQ). subst.
      simpl in Heqo0.
      unfold TypeInference.assert_argtypes in Heqr1.
      rewrite assert_argtypes'_eq in Heqr1.
      assert (List.length args = List.length (rev s)).
      { apply result_list_map_length in Heqr0. rewrite <- Heqr0.
        rewrite rev_length; auto.
      }
      assert (
        forall (p : pos_t) (sig : tsig var_t) s,
        result_list_map (TypeInference.type_action TR Sigma p sig) args
        = Success s
        -> forall
          (Gamma : TypedSemantics.tcontext sig) (UGamma : list (var_t * val)),
        gamma_eq sig UGamma Gamma
        -> forall
          (sched_log action_log action_log' : Logs.Log TR REnv)
          (usched_log uaction_log : env_t REnv (fun _ : reg_t => RLog val)),
        log_eq REnv usched_log sched_log -> log_eq REnv uaction_log action_log
        -> forall
          (s0 : context
            (fun k_tau : var_t * type =>
              TypedSyntax.action pos_t var_t fn_name_t TR Sigma sig (snd k_tau)
            )
            (rev (int_argspec ufn))
          ),
          assert_argtypes'
            (rev (int_argspec ufn))
            (rev (combine (map (TypeInference.actpos p) args) s))
          = Success s0
          -> List.length args = List.length (rev s)
          -> forall v (Gamma' : TypedSemantics.tcontext sig),
            TypedSemantics.interp_args'
              (@TypedSemantics.interp_action
                pos_t var_t fn_name_t reg_t ext_fn_t TR Sigma REnv tr tsigma
              )
              Gamma sched_log action_log s0
          = Some (action_log', v, Gamma')
          -> exists (uaction_log' : Log) res (UGamma' : list (var_t * val)),
          fold_right
            (
              fun a0 (acc : option (Log * list val * list (var_t * val))) =>
                let/opt3 action_log0, l0, Gamma0 := acc in (
                  let/opt3 action_log1, v0, Gamma1 :=
                    interp_action r sigma Gamma0 usched_log action_log0 a0
                  in
                  Some (action_log1, v0 :: l0, Gamma1)
                )
            )
            (Some (uaction_log, [], UGamma)) (rev args)
          = Some (uaction_log', res, UGamma')
            /\ gamma_eq _ (combine (map fst (rev (int_argspec ufn))) (res)) v
            /\ log_eq REnv uaction_log' action_log'
            /\ gamma_eq sig UGamma' Gamma'
      ).
      { clear - IHua.
        rewrite <- (rev_involutive args).
        assert (IHua': forall arg, In arg (rev args) -> PP arg).
        { intros. eapply IHua. apply In_rev in H. revert arg H.
          induction args; simpl; intros; eauto. easy.
          destruct H. subst. lia.
          eapply IHargs in H. lia. intros. eapply IHua. simpl. lia.
        }
        clear IHua. revert IHua'.
        generalize (rev args) as args'.
        intros args' IHua' p sig s RLM.
        apply result_list_map_rev in RLM.
        rewrite combine_rev.
        rewrite map_rev. rewrite rev_involutive.
        revert RLM. rewrite rev_involutive.
        generalize (rev s) as s'. clear s.
        rewrite rev_length.
        revert args' IHua' p sig.
        generalize (rev (int_argspec ufn)). clear args.
        Lemma interp_args_correct:
          let PP := fun u  =>
            forall
              (p : pos_t) (sig : tsig var_t) (tau : type)
              (a : TypedSyntax.action pos_t var_t fn_name_t TR Sigma sig tau),
            TypeInference.type_action TR Sigma p sig u
            = Success
              (existT (fun tau0 : type =>
                TypedSyntax.action pos_t var_t fn_name_t TR Sigma sig tau0) tau
                a
              )
            -> forall
              (Gamma : TypedSemantics.tcontext sig)
              (UGamma : list (var_t * val)),
            gamma_eq sig UGamma Gamma
            -> forall
              (sched_log action_log action_log' : Logs.Log TR REnv)
              (usched_log uaction_log : env_t REnv (fun _ : reg_t => RLog val)),
            log_eq REnv usched_log sched_log
            -> log_eq REnv uaction_log action_log
            -> forall (v : tau) (Gamma' : TypedSemantics.tcontext sig),
            TypedSemantics.interp_action tr tsigma Gamma sched_log action_log a
            = Some (action_log', v, Gamma')
            -> exists (uaction_log' : Log) (UGamma' : list (var_t * val)),
            interp_action r sigma UGamma usched_log uaction_log u
            =
            Some (uaction_log', val_of_value v, UGamma')
            /\ log_eq REnv uaction_log' action_log'
            /\ gamma_eq sig UGamma' Gamma'
            in forall (l : list (var_t * type)) args',
            (forall arg , In arg args' -> PP arg)
            -> forall
              (p : pos_t) (sig : tsig var_t)
              (s' : list
                {tau :
                  type & TypedSyntax.action pos_t var_t fn_name_t TR Sigma sig
                  tau
                }
              ),
            result_list_map (TypeInference.type_action TR Sigma p sig) args'
            = Success s'
            -> forall
              (Gamma : TypedSemantics.tcontext sig)
              (UGamma : list (var_t * val)),
            gamma_eq sig UGamma Gamma
            -> forall
              (sched_log action_log action_log' : Logs.Log TR REnv)
              (usched_log uaction_log : env_t REnv (fun _ : reg_t => RLog val)),
            log_eq REnv usched_log sched_log
            -> log_eq REnv uaction_log action_log
            -> forall
              s0 : context
              (fun k_tau : var_t * type =>
                TypedSyntax.action
                  pos_t var_t fn_name_t TR Sigma sig (snd k_tau)
              )
              l,
            assert_argtypes' l (combine (map (TypeInference.actpos p) args') s')
            = Success s0
            -> Datatypes.length args' = Datatypes.length s'
            -> forall
              (v : TypedSemantics.tcontext l)
              (Gamma' : TypedSemantics.tcontext sig),
            TypedSemantics.interp_args'
              (@TypedSemantics.interp_action
                pos_t var_t fn_name_t reg_t ext_fn_t TR Sigma REnv tr tsigma
              )
              Gamma sched_log action_log s0
            = Some (action_log', v, Gamma')
            -> exists
              (uaction_log' : Log) (res : list val)
              (UGamma' : list (var_t * val)),
            fold_right
              (fun a0 (acc : option (Log * list val * list (var_t * val))) =>
                let/opt3 action_log0, l0, Gamma0 := acc in (
                  let/opt3 action_log1, v0, Gamma1 :=
                    interp_action r sigma Gamma0 usched_log action_log0 a0
                  in
                  Some (action_log1, v0 :: l0, Gamma1)
                )
              )
            (Some (uaction_log, [], UGamma)) args'
            = Some (uaction_log', res, UGamma')
            /\ gamma_eq l (combine (map fst l) res) v
            /\ log_eq REnv uaction_log' action_log'
            /\ gamma_eq sig UGamma' Gamma'.
        Proof.
          induction l; simpl; intros.
          - destr_in H4; [|now inv H4]. inv H4.
            apply combine_nil_inv in Heql; eauto. destruct Heql. subst.
            destruct args'; simpl in *; try congruence. inv H6.
            eexists; eexists; eexists; repeat split; eauto.
            constructor.
            rewrite <- H5. rewrite map_length. auto.
          - destr_in H4.
            destr_in H4; [inv H4|].
            destr_in H4.
            destr_in H4; [|inv H4].
            destr_in H4; [|inv H4]. inv H4.
            destruct args'.
            + simpl in Heql0. congruence.
            + simpl in Heql0.
              destr_in Heql0. congruence. inv Heql0. simpl in *.
              unfold opt_bind in H6.
              destr_in H6; [|inv H6]. destruct p0. destruct p0.
              destr_in H6; [|inv H6]. destruct p0. destruct p0.
              inv H6. simpl in *.
              destr_in H0; [|inv H0].
              destr_in H0; [|inv H0]. inv H0. simpl in *.
              edestruct IHl as (ual' & res & ug' & EQ & Geq' & ALeq & Geq2').
              intros; eapply H. right; apply H0.
              apply Heqr3. 4: eauto.
              5: apply Heqo. eauto. eauto. eauto. lia.
              rewrite EQ. simpl.
              destruct s; simpl in *.
              apply cast_action_eq in Heqr0.
              destruct Heqr0 as (pf & EQr0). subst.
              simpl in Heqo0.
              edestruct (H u) as (ual2' & ug2' & EQ2 & ALeq2 & Geq4').
              auto. eauto.
              4: eauto. eauto. eauto. eauto.
              rewrite EQ2. simpl.
              eexists; eexists; eexists; repeat split; eauto.
              constructor. auto.
        Qed.
        apply interp_args_correct.
        - rewrite map_length.
          apply result_list_map_length in RLM.
          rewrite ! rev_length in *. auto.
      }
      edestruct H0 as (uaction_log' & res & UGamma' & FR & Geq1 & ALeq & Geq2).
      eauto. 4: eauto. 5: eauto. eauto. eauto. eauto. auto.
      rewrite fold_left_rev_right in FR.
      setoid_rewrite FR. simpl.
      clear H0 FR.
      edestruct (IHua (int_body ufn)) as (ual' & g' & IA' & ALeq2 & Geq).
      lia. eauto. eauto. 3: eauto. eauto. eauto.
      erewrite combine_map.
      rewrite IA'. simpl.
      eexists; eexists; repeat split; eauto.
      simpl; reflexivity.
    - destr_in TA; [|inv TA].
      inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec.
      subst. simpl in H.
      destruct s. simpl in *.
      edestruct (IHua ua) as (ual' & g' & IA' & ALeq & Geq). lia. eauto.
      4: apply H. eauto. eauto. eauto.
      rewrite IA'.
      eexists; eexists; repeat split; eauto.
    - inv TA.
  Qed.

  Lemma interp_action_none:
    forall ua p sig tau a
      (TA:
        TypeInference.type_action TR Sigma p sig ua = Success (existT _ tau a)
      ) (Gamma: TypedSemantics.tcontext sig) (UGamma: list (var_t * val))
      (GammaEq: gamma_eq sig UGamma Gamma) sched_log action_log usched_log
      uaction_log (SL: log_eq REnv usched_log sched_log)
      (AL: log_eq REnv uaction_log action_log),
    TypedSemantics.interp_action tr tsigma Gamma sched_log action_log a = None
    -> interp_action
      (pos_t:=pos_t) (fn_name_t := fn_name_t) r sigma UGamma usched_log
      uaction_log ua
    = None.
  Proof.
    intros ua. pattern ua.
    match goal with
    | |- ?P ua => set (PP:=P)
    end.
    remember (size_uaction ua).
    revert ua Heqn.
    pattern n.
    eapply Nat.strong_right_induction with (z:=0). 2: lia.
    intros n0 _ Plt ua Heqn. subst.
    assert (Plt': forall a, size_uaction a < size_uaction ua -> PP a).
    { intros. eapply Plt. 3: reflexivity. lia. auto. } clear Plt.
    rename Plt' into IHua. clear n. unfold PP.
    destruct ua; simpl; intros; auto.
    - destr_in TA; inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst.
      simpl in H. inv H.
    - inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst.
      simpl in H. inv H.
    - destr_in TA; [|inv TA].
      destr_in TA; [|inv TA].
      destr_in TA; [|inv TA]. inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec.
      subst. simpl in H.
      unfold opt_bind in H.
      repeat destr_in H; [inv H|].
      unfold opt_result in Heqr0; destr_in Heqr0; inv Heqr0.
      destruct s. simpl in *.
      destruct s0. simpl in *.
      apply cast_action_eq in Heqr2.
      destruct Heqr2 as (pf & EQ). subst.
      simpl in Heqo.
      erewrite IHua; eauto.
    - destr_in TA; [|inv TA].
      destr_in TA; [|inv TA].
      destr_in TA; [|inv TA]. inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec.
      subst. simpl in H.
      destruct s; simpl in *.
      apply cast_action_eq in Heqr1.
      destruct Heqr1 as (pf & EQ). subst.
      simpl in H.
      unfold opt_bind in H.
      repeat destr_in H.
      edestruct interp_action_correct as (ual' & g' & IA' & ALeq & Geq). eauto.
      4: eauto. eauto. eauto. eauto. rewrite IA'. simpl.
      destruct s1. simpl in *.
      erewrite IHua; eauto. lia.
      erewrite IHua; eauto. simpl; lia.
    - destr_in TA; [|inv TA].
      destr_in TA; [|inv TA].
      inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec.
      subst. simpl in H.
      destruct s, s0. simpl in *.
      unfold opt_bind in H.
      repeat destr_in H; try (now inv H).
      edestruct (interp_action_correct ua1) as (ual' & g' & IA' & ALeq & Geq).
      eauto. 4: apply Heqo. eauto. eauto. eauto.
      rewrite IA'. simpl.
      erewrite IHua; eauto. lia.
      constructor; eauto.
      erewrite IHua; eauto. lia.
    - destr_in TA; [|inv TA]. destr_in TA; [|inv TA]. destr_in TA; [|inv TA].
      destr_in TA; [|inv TA]. destr_in TA; [|inv TA]. inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst.
      simpl in H. destruct s. simpl in *.
      apply cast_action_eq in Heqr1.
      destruct Heqr1 as (pf & EQ). subst.
      simpl in H.
      destruct s1, s2. simpl in *.
      apply cast_action_eq in Heqr4.
      destruct Heqr4 as (pf & EQ). subst.
      simpl in H.
      unfold opt_bind in H.
      destr_in H. destruct p0. destruct p0.
      edestruct (interp_action_correct ua1) as (ual' & g' & IA' & ALeq & Geq).
      eauto. 4: apply Heqo. eauto. eauto. eauto.
      rewrite IA'. simpl.
      destr_in H.
      erewrite IHua; eauto. lia.
      erewrite IHua; eauto. lia.
      erewrite IHua; eauto. lia.
    - inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec.
      subst. simpl in H.
      erewrite may_read_eq in H; eauto.
      destr_in H; [inv H|]. auto.
    - destr_in TA; [|inv TA].
      destr_in TA; [|inv TA].
      inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec.
      subst. simpl in H.
      destruct s. simpl in *.
      apply cast_action_eq in Heqr1.
      destruct Heqr1 as (pf & EQ). subst.
      simpl in H.
      unfold opt_bind in H.
      destr_in H.
      + destruct p0. destruct p0.
        edestruct (interp_action_correct ua) as (ual' & g' & IA' & ALeq & Geq).
        eauto.
        4: apply Heqo. eauto. eauto. eauto.
        rewrite IA'. simpl.
        erewrite may_write_eq in H; eauto.
        destr_in H; inv H. auto.
      + erewrite IHua; eauto.
    - destr_in TA; [|inv TA]. destr_in TA; [|inv TA]. destr_in TA; [|inv TA].
      inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst.
      simpl in H.
      destruct s. simpl in *.
      apply cast_action_eq in Heqr2.
      destruct Heqr2 as (pf & EQ). subst.
      simpl in H.
      unfold opt_bind in H.
      repeat destr_in H; inv H.
      erewrite IHua; eauto.
    - destr_in TA; [|inv TA]. destr_in TA; [|inv TA]. destr_in TA; [|inv TA].
      destr_in TA; [|inv TA]. destr_in TA; [|inv TA]. inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst.
      simpl in H.
      destruct s, s0. simpl in *.
      apply cast_action_eq in Heqr3.
      destruct Heqr3 as (pf & EQ). subst.
      apply cast_action_eq in Heqr4.
      destruct Heqr4 as (pf & EQ). subst.
      simpl in H. unfold opt_bind in H. repeat destr_in H; inv H.
      edestruct (interp_action_correct ua1) as (ual' & g' & IA' & ALeq & Geq).
      eauto. 4: apply Heqo. eauto. eauto. eauto.
      rewrite IA'. simpl. erewrite IHua; eauto. lia. erewrite IHua; eauto. lia.
    - destr_in TA; [|inv TA]. destr_in TA; [|inv TA]. inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst.
      simpl in H.
      destruct s. simpl in *.
      apply cast_action_eq in Heqr1.
      destruct Heqr1 as (pf & EQ). subst.
      simpl in H.
      unfold opt_bind in H.
      repeat destr_in H; [inv H|].
      erewrite IHua; eauto.
    - destr_in TA; [|inv TA]. destr_in TA; [|inv TA]. destr_in TA; [|inv TA].
      destr_in TA; [|inv TA]. inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst.
      simpl in H.
      destruct s1. simpl in *.
      apply cast_action_eq in Heqr3.
      destruct Heqr3 as (pf & EQ). subst.
      simpl in H.
      unfold TypeInference.assert_argtypes in Heqr1.
      rewrite assert_argtypes'_eq in Heqr1.
      assert (List.length args = List.length (rev s)).
      { apply result_list_map_length in Heqr0. rewrite <- Heqr0.
        rewrite rev_length; auto.
      }
      assert (
        forall (p : pos_t) (sig : tsig var_t) s,
        result_list_map (TypeInference.type_action TR Sigma p sig) args
        = Success s
        -> forall
          (Gamma : TypedSemantics.tcontext sig) (UGamma : list (var_t * val)),
        gamma_eq sig UGamma Gamma
        -> forall
          (sched_log action_log action_log' : Logs.Log TR REnv)
          (usched_log uaction_log : env_t REnv (fun _ : reg_t => RLog val)),
        log_eq REnv usched_log sched_log -> log_eq REnv uaction_log action_log
        -> forall
          (s0 :
            context (fun k_tau : var_t * type =>
              TypedSyntax.action pos_t var_t fn_name_t TR Sigma sig (snd k_tau)
            ) (rev (int_argspec ufn))
          ),
        assert_argtypes'
          (rev (int_argspec ufn))
          (rev (combine (map (TypeInference.actpos p) args) s)) = Success s0
        -> List.length args = List.length (rev s)
        -> TypedSemantics.interp_args'
          (@TypedSemantics.interp_action
              pos_t var_t fn_name_t reg_t ext_fn_t TR Sigma REnv tr tsigma
          )
          Gamma sched_log action_log s0
        = None ->
        fold_right
          (
            fun a0 (acc : option (Log * list val * list (var_t * val))) =>
              let/opt3 action_log0, l0, Gamma0 := acc in
              (
                let/opt3 action_log1, v0, Gamma1 :=
                  interp_action r sigma Gamma0 usched_log action_log0 a0 in
                Some (action_log1, v0 :: l0, Gamma1)
              )
          )
          (Some (uaction_log, [], UGamma)) (rev args)
        = None
      ).
      { generalize interp_action_correct as IAC. intro IAC.
        clear - IHua IAC.
        rewrite <- (rev_involutive args).
        assert (IHua': forall arg, In arg (rev args) -> PP arg).
        { intros. eapply IHua. apply In_rev in H. revert arg H.
          induction args; simpl; intros; eauto. easy.
          destruct H. subst. lia.
          eapply IHargs in H. lia. intros. eapply IHua. simpl. lia.
        } clear IHua. revert IHua'.
        generalize (rev args) as args'.
        intros args' IHua' p sig s RLM.
        apply result_list_map_rev in RLM.
        rewrite combine_rev.
        rewrite map_rev. rewrite rev_involutive.
        revert RLM. rewrite rev_involutive.
        generalize (rev s) as s'. clear s.
        rewrite rev_length.
        revert args' IHua' p sig.
        generalize (rev (int_argspec ufn)). clear args.
        induction l; simpl; intros.
        - destr_in H2; [|now inv H2]. inv H2.
          apply combine_nil_inv in Heql; eauto. destruct Heql. subst.
          destruct args'; simpl in *; try congruence. inv H4.
        - destr_in H2.
          destr_in H2; [inv H2|].
          destr_in H2.
          destr_in H2; [|inv H2].
          destr_in H2; [|inv H2]. inv H2.
          destruct args'.
          + simpl in Heql0. congruence.
          + simpl in Heql0.
            destr_in Heql0. congruence. inv Heql0. simpl in *.
            unfold opt_bind in H4.
            destr_in RLM; [|inv RLM].
            destr_in RLM; [|inv RLM]. inv RLM. simpl in *.
            destr_in H4. destruct p0. destruct p0.
            * edestruct interp_args_correct
                as (ual' & res & ug' & FR & Geq & Leq & Geq2).
              intros arg IN. intros; eapply IAC.  12: eauto. all:eauto.
              rewrite FR. simpl.
              repeat destr_in H4. inv H4.
              destruct s. simpl in *. erewrite IHua'; simpl; eauto.
              apply cast_action_eq in Heqr0. destruct Heqr0 as (pf & EQ). subst.
              simpl in *. eauto.
            * erewrite IHl; simpl; eauto.
        - rewrite map_length.
          apply result_list_map_length in RLM.
          rewrite ! rev_length in *. auto.
      }
      move H at bottom.
      unfold opt_bind in H.
      repeat destr_in H; try inv H.
      * rewrite combine_rev in Heqr1.
        rewrite <- map_rev in Heqr1.
        edestruct interp_args_correct
          as (ual' & res & ug' & FR & Geq & Leq & Geq2).
        intros arg IN. intros; eapply interp_action_correct. 10:eauto.
        6: apply result_list_map_rev; eauto. 5: eauto. 9: eauto. all: eauto.
        rewrite rev_length; auto.
        rewrite <- fold_left_rev_right. setoid_rewrite FR. simpl.
        erewrite IHua; simpl; eauto. lia.
        erewrite combine_map. eauto. reflexivity.
        rewrite map_length. rewrite H0.
        rewrite rev_length; auto.
      * rewrite <- fold_left_rev_right.
        erewrite H1. reflexivity. 6: eauto. eauto. eauto. all: eauto.
    - destr_in TA; [|inv TA].
      inv TA.
      apply Eqdep_dec.inj_pair2_eq_dec in H2. 2: apply eq_dec. subst.
      simpl in H. destruct s. simpl in *.
      eapply IHua; eauto.
    - inv TA.
  Qed.

  Lemma log_eq_empty: log_eq REnv log_empty Logs.log_empty.
  Proof.
    repeat red.
    unfold log_empty, Logs.log_empty.
    intros; repeat rewrite getenv_create. constructor.
  Qed.

  Lemma interp_rule_correct:
    forall
      ua p rl (TA: TypeInference.tc_rule TR Sigma p ua = Success rl) sched_log
      usched_log (SL: log_eq REnv usched_log sched_log) action_log,
    TypedSemantics.interp_rule tr tsigma sched_log rl = Some (action_log)
    -> exists uaction_log,
    interp_rule
      (pos_t:=pos_t) (fn_name_t := fn_name_t) r sigma usched_log ua
    = Some (uaction_log)
    /\ log_eq REnv uaction_log action_log.
  Proof.
    intros.
    unfold TypeInference.tc_rule in TA.
    unfold TypeInference.tc_action in TA.
    destr_in TA; [|inv TA].
    destruct s; simpl in *.
    apply cast_action_eq in TA. destruct TA as (pp & EQ).
    subst. simpl in *.
    unfold TypedSemantics.interp_rule in H.
    destr_in H; [|inv H].
    destruct p0. destruct p0. inv H.
    unfold interp_rule.
    edestruct interp_action_correct as (ual' & ug' & IA & LE & GE).
    eauto. constructor. 3: eauto. apply SL.
    apply log_eq_empty.
    rewrite IA.
    eexists; split; eauto.
  Qed.

  Lemma interp_rule_none:
    forall
      ua p rl (TA: TypeInference.tc_rule TR Sigma p ua = Success rl)
      sched_log usched_log (SL: log_eq REnv usched_log sched_log),
    TypedSemantics.interp_rule tr tsigma sched_log rl = None
    -> interp_rule (pos_t:=pos_t) (fn_name_t := fn_name_t) r sigma usched_log ua
    = None.
  Proof.
    intros.
    unfold TypeInference.tc_rule in TA.
    unfold TypeInference.tc_action in TA.
    destr_in TA; [|inv TA].
    destruct s; simpl in *.
    apply cast_action_eq in TA. destruct TA as (pp & EQ).
    subst. simpl in *.
    unfold TypedSemantics.interp_rule in H.
    repeat destr_in H; [inv H|].
    unfold interp_rule.
    erewrite interp_action_none; eauto. constructor.
    apply log_eq_empty.
  Qed.

  Context {rule_name_t: Type}.
  Lemma interp_scheduler'_correct:
    forall
      (urules:
        rule_name_t -> Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t
      )
      (rules: rule_name_t -> TypedSyntax.rule pos_t var_t fn_name_t TR Sigma)
      (TC:
        forall rnt, exists p,
        TypeInference.tc_rule TR Sigma p (urules rnt) = Success (rules rnt)
      ),
    forall s l1 ul1 l2,
    log_eq REnv ul1 l1
    -> TypedSemantics.interp_scheduler' tr tsigma rules l1 s = l2
    -> exists ul2,
    interp_scheduler' urules r sigma ul1 s = ul2 /\ log_eq REnv ul2 l2.
  Proof.
    induction s; simpl; intros; eauto.
    - subst. eexists; split; eauto.
    - destr_in H0.
      + destruct (TC r0) as (p & TCR).
        edestruct interp_rule_correct as (l' & EQ1 & EQ2). eauto. 2: eauto.
        eauto. rewrite EQ1.
        eapply IHs; eauto.
        apply log_eq_app; auto.
      + destruct (TC r0) as (p & TCR).
        erewrite interp_rule_none; eauto.
    - destr_in H0.
      + destruct (TC r0) as (p & TCR).
        edestruct interp_rule_correct as (l' & EQ1 & EQ2). eauto. 2: eauto.
        eauto. rewrite EQ1.
        eapply IHs1; eauto.
        apply log_eq_app; auto.
      + destruct (TC r0) as (p & TCR).
        erewrite interp_rule_none; eauto.
  Qed.

  Lemma interp_scheduler_correct:
    forall
      (urules:
        rule_name_t -> Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t
      )
      (rules: rule_name_t -> TypedSyntax.rule pos_t var_t fn_name_t TR Sigma)
      (TC:
        forall rnt, exists p,
        TypeInference.tc_rule TR Sigma p (urules rnt) = Success (rules rnt)
       ),
    forall s l2,
    TypedSemantics.interp_scheduler tr tsigma rules s = l2
    -> exists ul2,
    interp_scheduler urules r sigma s = ul2 /\ log_eq REnv ul2 l2.
  Proof.
    intros. unfold interp_scheduler, TypedSemantics.interp_scheduler.
    eapply interp_scheduler'_correct; eauto. apply log_eq_empty.
  Qed.
End Eq.

Section Final.
  Context {reg_t: Type}.
  Context {REnv : Env reg_t}.
  Variable (TR: reg_t -> type).
  Variable (r: env_t REnv (fun x : reg_t => val)).
  Variable (tr: env_t REnv (fun x : reg_t => TR x)).
  Hypothesis (rtr: env_t_R (fun i uv v => uv = val_of_value v) REnv r tr).

  Context {pos_t var_t ext_fn_t fn_name_t rule_name_t : Type}.
  Context {var_t_eq_dec: EqDec var_t}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context (Sigma: ext_fn_t -> Sig 1).
  Variable (sigma: forall f: ext_fn_t, val -> val).
  Variable (tsigma: forall f, Sig_denote (Sigma f)).

  Hypothesis tsigma_correct:
    forall f v, sigma f (val_of_value v) = val_of_value (tsigma f v).

  Lemma latest_write_eq:
    forall ulog log,
    log_eq (TR:=TR) REnv ulog log
    -> forall idx,
    option_map val_of_value (Logs.latest_write log idx) =
    latest_write ulog idx.
  Proof.
    unfold Logs.latest_write, latest_write.
    intros.
    apply log_find_eq. auto.
    intros.
    red in H0. intuition.
    destruct ule, le; simpl in *. subst.
    destr_in val0. reflexivity. simpl. congruence.
  Qed.

  Lemma log_eq_commit_update:
    forall ul l,
    log_eq REnv ul l
    -> env_t_R
      (fun (i : reg_t) (uv : val) (v : TR i) => uv = val_of_value v) REnv
      (create REnv (fun k : reg_t =>
        match latest_write ul k with
        | Some v => v
        | None => getenv REnv r k
        end)
      )
      (create REnv (fun k : reg_t =>
        match Logs.latest_write l k with
        | Some v => v
        | None => getenv REnv tr k
        end)
      ).
  Proof.
    intros.
    red. intros.
    rewrite !getenv_create.
    erewrite <- latest_write_eq. 2: eauto.
    destruct (Logs.latest_write) eqn:?; simpl. auto.
    apply rtr.
  Qed.

  Lemma interp_cycle_correct:
    forall
      (urules:
        rule_name_t -> Syntax.uaction pos_t var_t fn_name_t reg_t ext_fn_t
      )
      (rules: rule_name_t -> TypedSyntax.rule pos_t var_t fn_name_t TR Sigma)
      (TC:
        forall rnt, exists p,
        TypeInference.tc_rule TR Sigma p (urules rnt) = Success (rules rnt)
      ),
    forall s,
    env_t_R
      (fun i uv v => uv = val_of_value (tau:=TR i) v) REnv
      (interp_cycle urules r sigma s)
      (TypedSemantics.interp_cycle tsigma rules s tr).
  Proof.
    unfold interp_cycle, TypedSemantics.interp_cycle. intros.
    unfold commit_update, Logs.commit_update.
    apply log_eq_commit_update.
    edestruct @interp_scheduler_correct as (l2 & EQ & LEQ); eauto.
    subst.  eauto.
  Qed.
End Final.
