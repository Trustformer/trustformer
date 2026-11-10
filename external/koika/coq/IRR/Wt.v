Require Import Coq.Program.Equality.
Require Import Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.BitsToLists.
Require Import Koika.KoikaForm.Desugaring.Desugaring.
Require Import Koika.KoikaForm.Desugaring.DesugaredSyntax.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.KoikaForm.TypeInference.

Section WT.
  Variables pos_t fn_name_t: Type.
  Variable var_t: Type.
  Context {eq_dec_var_t: EqDec var_t}.

  Lemma cast_action'_eq:
    forall
      (p: pos_t) (sig: tsig var_t) (tau1 tau2: type)
      {reg_t ext_fn_t: Type} (R: reg_t -> type)
      (Sigma: ext_fn_t -> ExternalSignature)
      (a: TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau1)
      (e: error_message var_t fn_name_t) a',
    TypeInference.cast_action' R Sigma p tau2 a e = Success a'
    -> exists p : tau1 = tau2, a' = eq_rect _ _ a _ p.
  Proof.
    unfold TypeInference.cast_action'. intros.
    destr_in H. subst.
    unfold eq_rect_r in H. simpl in H. inv H.
    exists eq_refl; reflexivity. inv H.
  Qed.

  Lemma cast_action_eq:
    forall
      {reg_t ext_fn_t: Type} (R: reg_t -> type)
      (Sigma: ext_fn_t -> ExternalSignature)
      (p: pos_t) (sig: tsig var_t) (tau1 tau2: type)
      (a: TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau1) a',
    TypeInference.cast_action R Sigma p tau2 a = Success a'
    -> exists p : tau1 = tau2, a' = eq_rect _ _ a _ p.
  Proof.
    intros. unfold TypeInference.cast_action in H.
    eapply cast_action'_eq; eauto.
  Qed.

  Lemma cast_action'_ok:
    forall {reg_t ext_fn_t: Type}
           (R: reg_t -> type)
           (Sigma: ext_fn_t -> ExternalSignature)
           (sig : tsig var_t) (t1 : type) (a : TypedSyntax.action pos_t var_t fn_name_t R Sigma sig t1)
           (pos : pos_t) (t2 : type) (p: t1 = t2),
      cast_action' R Sigma pos t2 a (BasicError (TypeMismatch t1 t2)) =
      Success (rew [TypedSyntax.action pos_t var_t fn_name_t R Sigma sig] p in a).
  Proof.
    unfold cast_action'.
    intros. subst.
    destruct eq_dec; try congruence. simpl.
    unfold eq_rect_r.
    rewrite eq_dec_rew_type_family. auto.
  Qed.

  Lemma cast_action_ok:
    forall {reg_t ext_fn_t: Type}
           (R: reg_t -> type)
           (Sigma: ext_fn_t -> ExternalSignature)
           sig t1 (a: TypedSyntax.action pos_t var_t fn_name_t R Sigma sig t1) pos t2 (p: t1 = t2),
      cast_action R Sigma pos (sig:=sig) t2 a = Success (rew  [TypedSyntax.action pos_t var_t fn_name_t R Sigma sig] p in a).
  Proof.
    unfold cast_action. intros.
    apply cast_action'_ok.
  Qed.

  Lemma argtypes_app':
    forall {reg_t ext_fn_t: Type}
           (R: reg_t -> type)
           (Sigma: ext_fn_t -> ExternalSignature)
           {T} sig p (src: T) nexpected fn_name l1 l2 l3 l4 s1 s2,
      assert_argtypes' R Sigma src nexpected fn_name p l1 l3 = Success s1
      -> assert_argtypes' R Sigma src nexpected fn_name p l2 l4 = Success s2
      -> assert_argtypes'
        (sig:=sig)
        (fn_name_t := fn_name_t)
        (pos_t := pos_t)
        (var_t := var_t)
        R Sigma src nexpected fn_name p
        (l1 ++ l2)
        (l3 ++ l4) =
      Success (capp s1 s2).
  Proof.
    induction l1; simpl; intros; eauto.
    - destruct l3; simpl in *; try lia. eauto. inv H.
    - repeat destr_in H; inv H.
      simpl. rewrite Heqr. erewrite IHl1. eauto. eauto. auto.
  Qed.

  Lemma Forall2_length:
    forall {A B} (P: A -> B -> Prop) l1 l2,
    Forall2 P l1 l2 -> List.length l1 = List.length l2.
  Proof. induction 1; simpl; intros; eauto. Qed.

  Lemma uprogn_wt_type:
    forall {reg_t ext_fn_t} (R: reg_t -> type) (Sigma: ext_fn_t -> ExternalSignature)aa sig,
      Forall (fun ua =>
                forall p,
                exists a : {tau : type & TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau},
                  type_action R Sigma p sig ua = Success a /\ projT1 a = unit_t
             ) aa
             -> forall p,
      exists a : {tau : type & TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau},
        type_action R Sigma p sig (SyntaxMacros.uprogn aa) =
        Success a /\ projT1 a = unit_t.
  Proof.
    induction 1; simpl; intros; eauto.
    destruct l; simpl in *; eauto.
    edestruct H as (a0 & TA0 & EQt0). rewrite TA0.
    erewrite cast_action_ok.
    edestruct IHForall as (a1 & TA1 & EQt1). rewrite TA1.
    eexists; split; eauto. Unshelve. auto.
  Qed.

  Lemma ustruct_subst_wt:
    forall {reg_t ext_fn_t} (R: reg_t -> type)
           (Sigma: ext_fn_t -> ExternalSignature)
           sg p sig fields,
      Forall (fun '(f,v) =>
                exists idx,
                  PrimTypeInference.find_field sg f = Success idx /\
                  exists a,
                    type_action R Sigma p sig v = Success a /\ projT1 a = snd(List_nth (struct_fields sg) idx)) fields
                    -> forall i ai,
        type_action R Sigma p sig i = Success ai
        -> projT1 ai = struct_t sg
        -> exists a,
          type_action
            (pos_t := pos_t)
            (var_t := var_t)
            (fn_name_t := fn_name_t)
            R Sigma p sig
            (fold_left (fun acc '(f, a0) =>
                          UBinop (PrimUntyped.UStruct2 (PrimUntyped.USubstField f)) acc a0
                       ) fields i) = Success a /\ projT1 a = struct_t sg.
  Proof.
    induction 1; simpl; intros; eauto.
    destruct x.
    decompose [ex and] H; clear H. subst.
    eapply IHForall. simpl. rewrite H1, H5.
    unfold lift_fn2_tc_result.
    setoid_rewrite H2.
    rewrite H4. simpl.
    erewrite cast_action_ok; eauto.
    erewrite cast_action_ok; eauto. simpl. auto.
    Unshelve. auto. unfold field_type; auto.
  Qed.

  Lemma uarray_subst_wt:
    forall {reg_t ext_fn_t} (R: reg_t -> type)
       (Sigma: ext_fn_t -> ExternalSignature) p sig sg elements,
      Forall (fun v =>
                exists a,
                  type_action R Sigma p sig v = Success a /\ projT1 a = array_type sg) elements
                  -> forall pi i ai,
        pi + List.length elements = array_len sg
        -> type_action R Sigma p sig i = Success ai
        -> projT1 ai = array_t sg
        -> exists a,
          type_action
            (pos_t := pos_t)
            (var_t := var_t)
            (fn_name_t := fn_name_t)
            R Sigma p sig
            (snd (fold_left (fun '(pos, acc) a0 =>
                               (S pos,
                                UBinop (PrimUntyped.UArray2 (PrimUntyped.USubstElement pos)) acc a0)
                            ) elements (pi, i))) = Success a /\ projT1 a = array_t sg.
  Proof.
    induction 1; simpl; intros; eauto.
    decompose [ex and] H; clear H.
    edestruct (@index_of_nat_bounded (array_len sg) pi) as (idx & IDXEQ). lia.
    eapply IHForall. lia. simpl. rewrite H2, H5.
    unfold lift_fn2_tc_result.
    setoid_rewrite H3.
    unfold PrimTypeInference.check_index.
    rewrite IDXEQ. simpl.
    erewrite cast_action_ok; eauto.
    erewrite cast_action_ok; eauto. simpl. auto.
    Unshelve. auto. auto.
  Qed.

  Definition wt_renv {reg_t:Type} (R: reg_t -> type) (REnv: Env reg_t) ctx :=
    forall x, wt_val (R x) (getenv REnv ctx x).

  Definition wt_log
    {reg_t:Type} (R: reg_t -> type) (REnv: Env reg_t)
    (l: UntypedSemantics.Log REnv)
  :=
    forall idx le, In le (getenv REnv l idx)
    -> kind le = Logs.LogWrite
    -> wt_val (R idx) (UntypedLogs.val le).

  Inductive wt_env : tsig var_t -> list (var_t * val) -> Prop :=
  | wt_env_nil: wt_env [] []
  | wt_env_cons:
    forall sig ctx t x v, wt_env sig ctx
    -> wt_val t x
    -> wt_env ((v,t)::sig) ((v,x)::ctx).

  Ltac trim H :=
    match type of H with
    | ?a -> ?b =>
      let x := fresh "H" in
      assert(x: a);[|specialize(H x); clear x]
    end.

  Lemma wt_var_determ:
    forall sig v t1 t2,
    wt_var var_t sig v t1
    -> wt_var var_t sig v t2
    -> t1 = t2.
  Proof.
    intros sig v t1 t2 H H0. inv H; inv H0. congruence.
  Qed.

  Ltac iinv A :=
    inv A;
    repeat
      match goal with
       | H: existT _ _ _ = existT _ _ _ |- _ =>
         apply Eqdep.EqdepTheory.inj_pair2 in H; try subst
       end.

  Lemma wt_env_list_assoc:
    forall sig ctx, wt_env sig ctx
    -> forall var v t, list_assoc ctx var = Some v
    -> wt_var var_t sig var t
    -> wt_val t v.
  Proof.
    intros sig ctx WTE var v t LA WTV.
    inv WTV.
    revert var v LA tm H.
    induction WTE; simpl; intros; eauto. congruence.
    destr_in H0; subst.
    - inv LA.
      unfold eq_rect_r in H0. rewrite eq_dec_rew_type_family in H0. inv H0.
      simpl. auto.
    - repeat destr_in H0; inv H0. simpl.
      eapply IHWTE in LA. 2: eauto. simpl in LA. auto.
  Qed.

  Lemma wt_env_set:
    forall sig k t0 Gamma v0, wt_var var_t sig k t0
    -> wt_env sig Gamma
    -> wt_val t0 v0
    -> wt_env sig (list_assoc_set Gamma k v0).
  Proof.
    intros sig k t0 Gamma v0 WTV WTE WTv.
    inv WTV. revert v0 tm WTv H.
    induction WTE; simpl; intros; eauto. easy.
    repeat destr_in H0; inv H0.
    + unfold eq_rect_r in H2. rewrite eq_dec_rew_type_family in H2. inv H2.
      simpl in *. constructor; auto.
    + simpl in *. constructor; eauto. eapply IHWTE; eauto. simpl; auto.
  Qed.

  Lemma list_find_op_spec:
    forall {A B} (f: A -> option B) l v,
    list_find_opt f l = Some v
    -> exists x, In x l /\ f x = Some v.
  Proof.
    induction l; simpl; intros; eauto. easy.
    destr_in H. inv H. exists a; split; eauto.
    edestruct IHl as (xx & IN & SOME); eauto.
  Qed.
  Lemma log_find_wt:
    forall {T reg_t} R (REnv: Env reg_t) l idx f v,
    log_find (T:=T) l idx f = Some v
    -> forall (FF: forall x y, f x = Some y -> kind x = Logs.LogWrite),
       wt_log R REnv l
    -> exists x, f x = Some v /\ wt_val (R idx) (UntypedLogs.val x).
  Proof.
    intros.
    red in H0.
    unfold log_find in H.
    edestruct @list_find_op_spec as (x & F & IN). eauto.
    generalize IN; intro IN'.
    apply FF in IN.
    apply H0 in F; auto.
    eauto.
  Qed.

  Lemma wt_log_app:
    forall {reg_t} (R: reg_t -> type) REnv l1 l2,
    wt_log R REnv l1
    -> wt_log R REnv l2
    -> wt_log R REnv (log_app l1 l2).
  Proof.
    unfold wt_log. intros.
    revert H1.
    unfold log_app.
    rewrite getenv_map2. rewrite in_app_iff. intros [?|?]; eauto.
  Qed.

  Instance eq_dec_env {A: Type} `{Env A} : EqDec A.
  Proof.
    destruct Env0. apply EqDec_FiniteType.
  Defined.

  Lemma wt_log_cons:
    forall {reg_t} (R: reg_t -> type) REnv l1 le idx, wt_log R REnv l1
    -> (kind le = Logs.LogWrite -> wt_val (R idx) (UntypedLogs.val le))
    -> wt_log R REnv (log_cons idx le l1).
  Proof.
    unfold wt_log. intros.
    revert H1.
    unfold log_cons.
    destruct (@eq_dec _ (@eq_dec_env _ REnv) idx idx0); subst.
    rewrite get_put_eq. simpl; intros; eauto. destruct H1; subst; simpl in *. eauto. eauto.
    rewrite get_put_neq. eauto. auto.
  Qed.

  Fixpoint typsz (t: type) : nat :=
    match t with
    | bits_t sz => 1
    | enum_t sg => 1
    | struct_t sg => 1 + list_sum (map (fun '(_,t) => typsz t) (struct_fields sg))
    | array_t sg => 1 + typsz (array_type sg)
    end.

  Lemma type_ind' :
    forall
      (P: type -> Prop) (Pb: forall sz, P (bits_t sz))
      (Pe: forall sg, P (enum_t sg))
      (Ps:
        forall sg (IH: forall v t, In (v, t) (struct_fields sg) -> P t),
        P (struct_t sg))
      (Pa: forall sg (IH: P (array_type sg)), P (array_t sg)) t,
    P t.
  Proof.
    intros P Pb Pe Ps Pa t.
    eapply (strong_ind_type (fun n => forall t, typsz t = n -> P t)).
    3: reflexivity. 2: reflexivity.
    intros. subst.
    assert (IH: forall t, typsz t < typsz t0 -> P t).
    { intros; eapply H; eauto. }
    clear H. destruct t0; auto.
    - apply Ps.
      intros. eapply IH.
      clear - H.
      simpl.
      revert H. generalize (struct_fields sig).
      induction l; simpl; intros; eauto. easy.
      destruct a.
      destruct H; subst; simpl in *; eauto. inv H. lia.
      apply IHl in H. lia.
  Qed.

  Lemma uvalue_of_struct_bits_rew :
    forall fields l,
    (fix uvalue_of_struct_bits
       (fields : list (string * type)) (bs : list bool) {struct fields}
     : option (list val) :=
       match fields with
       | [] => Some []
       | (_, tau) :: fields0 =>
         match take_drop (Datatypes.length bs - type_sz tau) bs with
         | Some (b0, b1) =>
           match uvalue_of_struct_bits fields0 b0 with
           | Some x0 =>
             match uvalue_of_bits (tau:=tau) b1 with
             | Some x1 => Some (x1 :: x0)
             | None => None
             end
           | None => None
           end
         | None => None
         end
       end) fields l = uvalue_of_struct_bits fields l.
  Proof. reflexivity. Qed.

  Lemma bits_splitn_inv:
    forall n sz l1 l2,
    bits_splitn n sz l1 = Some l2
    -> Forall (fun x => List.length x = sz) l2 /\ List.length l2 = n.
  Proof.
    induction n; simpl; intros; eauto. inv H; split; constructor.
    unfold opt_bind in H. repeat destr_in H; inv H.
    edestruct IHn; eauto. subst. simpl.
    split; auto.
    constructor; eauto. eapply take_drop_spec in Heqo. tauto.
  Qed.
  Lemma uvalue_of_list_bits_inv:
    forall (tau : type) (l : list (list bool)) (l0 : list val)
      (F: Forall (fun x => List.length x = type_sz tau) l)
      (IH:
        forall (v1 : list bool) (v : val), Datatypes.length v1 = type_sz tau
          -> uvalue_of_bits (tau:=tau) v1 = Some v -> wt_val tau v),
    uvalue_of_list_bits (tau:=tau) l = Some l0
    -> Forall (fun y => wt_val tau y) l0 /\ List.length l0 = List.length l.
  Proof.
    induction l; simpl; intros; eauto.
    - inv H; split; constructor.
    - unfold opt_bind in H. repeat destr_in H; inv H.
      split.
      constructor; eauto.
      eapply IH; eauto. inv F; eauto.
      inv F. eapply IHl; eauto.
      simpl; auto.
      edestruct IHl; eauto. inv F; auto.
  Qed.

  Lemma uvalue_of_list_bits_app:
    forall tau l1 l2 l1' l2', uvalue_of_list_bits (tau:=tau) l1 = Some l1'
    -> uvalue_of_list_bits (tau:=tau) l2 = Some l2'
    -> uvalue_of_list_bits (tau:=tau) (l1 ++ l2) = Some (l1' ++ l2').
  Proof.
    induction l1; simpl; intros; eauto. inv H; auto.
    unfold opt_bind in H. repeat destr_in H; inv H.
    simpl. erewrite IHl1; eauto. simpl. auto.
  Qed.

  Lemma uvalue_of_list_bits_rev:
    forall tau l l', uvalue_of_list_bits (tau:=tau) l = Some l'
    -> uvalue_of_list_bits (tau:=tau) (rev l) = Some (rev l').
  Proof.
    induction l; simpl; intros; eauto. inv H; auto.
    unfold opt_bind in H. repeat destr_in H; inv H.
    simpl. eapply uvalue_of_list_bits_app. eauto. simpl. rewrite Heqo. reflexivity.
  Qed.

  Lemma uvalue_of_struct_bits_wt:
    forall fields l v
      (IH: forall (v : string) (t : type), In (v, t) fields
           -> forall (v1 : list bool) (v0 : val),
              Datatypes.length v1 = type_sz t
           -> uvalue_of_bits (tau:=t) v1 = Some v0
           -> wt_val t v0)
      (LEN: List.length l = struct_fields_sz fields),
    uvalue_of_struct_bits fields l = Some v
    -> Forall2 wt_val (map snd fields) v.
  Proof.
    induction fields; simpl; intros; eauto. inv H. constructor.
    unfold opt_bind in H. repeat destr_in H; inv H.
    simpl.
    constructor; eauto.
    eapply IH; eauto.
    eapply take_drop_spec in Heqo. intuition. rewrite H2.
    rewrite LEN. unfold struct_fields_sz. simpl. lia.
    eapply IHfields; eauto.
    eapply take_drop_spec in Heqo. intuition. rewrite H1.
    rewrite LEN. unfold struct_fields_sz; simpl. lia.
  Qed.

  Lemma uvalue_of_bits_wt:
    forall tau v1 v, List.length v1 = type_sz tau
    -> uvalue_of_bits (tau:=tau) v1 = Some v
    -> wt_val tau v.
  Proof.
    intros tau. pattern tau.
    eapply type_ind'; simpl; intros; eauto.
    - inv H0. constructor. auto.
    - unfold opt_bind in H0; repeat destr_in H0; inv H0.
      constructor; auto.
      eapply take_drop_spec in Heqo; eauto. tauto.
    - unfold opt_bind in H0; repeat destr_in H0; inv H0.
      rewrite uvalue_of_struct_bits_rew in Heqo.
      constructor.
      eapply uvalue_of_struct_bits_wt; eauto.
    - unfold opt_bind in H0; repeat destr_in H0; inv H0.
      rewrite UntypedSemantics.uvalue_of_list_bits_rew in Heqo0.
      apply bits_splitn_inv in Heqo. destruct Heqo.
      apply uvalue_of_list_bits_rev in Heqo0.
      rewrite rev_involutive in Heqo0.
      eapply uvalue_of_list_bits_inv in Heqo0; eauto.
      destruct Heqo0.
      constructor.
      rewrite <- (rev_involutive).
      eapply UntypedSemantics.Forall_rev. auto.
      rewrite <- H1, <- H3, rev_length. auto.
  Qed.

  Lemma wt_val_bits:
    forall n l, n = List.length l -> wt_val (bits_t n) (Bits l).
  Proof. intros; subst; constructor; auto. Qed.

  Lemma wt_unop_sigma1:
    forall u ta tr v0 v, wt_unop u ta tr
    -> wt_val ta v0
    -> UntypedSemantics.sigma1 u v0 = Some v
    -> wt_val tr v.
  Proof.
    intros u ta tr v0 v WTU WTv SIG.
    inv WTU; simpl in *.
    - inv SIG; constructor; reflexivity.
    - inv SIG; constructor; reflexivity.
    - inv SIG. constructor.
      apply ubits_of_value_len'. auto.
    - unfold opt_bind in SIG. repeat destr_in SIG; inv SIG.
      inv WTv.
      eapply uvalue_of_bits_wt; eauto.
    - inv SIG; constructor; auto.
    - inv SIG. auto.
    - inv WTv. simpl in *. inv SIG.
      constructor. apply map_length.
    - inv WTv. simpl in *. inv SIG.
      apply wt_val_bits; auto.
      rewrite app_length. rewrite repeat_length. lia.
    - inv WTv. simpl in *. inv SIG.
      apply wt_val_bits; auto.
      rewrite app_length. rewrite repeat_length. lia.
    - inv WTv. simpl in *. inv SIG.
      apply wt_val_bits; auto.
      rewrite app_length. rewrite repeat_length. lia.
    - inv WTv. simpl in *. inv SIG.
      apply wt_val_bits; auto.
      erewrite length_concat_same. rewrite repeat_length. eauto.
      rewrite Forall_forall; intros x IN.
      apply repeat_spec in IN. subst. auto.
    - inv WTv. simpl in *.
      unfold opt_bind in SIG; repeat destr_in SIG; inv SIG.
      constructor.
      rewrite app_length.
      rewrite repeat_length. rewrite firstn_length, skipn_length. lia.
    - inv WTv. simpl in *.
      unfold PrimTypeInference.find_field in H. unfold opt_result in H.
      destr_in H; inv H.
      revert H1 SIG Heqo. unfold field_type.
      revert idx. clear. generalize (struct_fields sg).
      intro l; revert lv.
      induction l. simpl. easy.
      intros. Opaque eq_dec. simpl in *.
      repeat destr_in Heqo; inv Heqo.
      + repeat destr_in SIG; inv SIG. inv H1. simpl; auto.
        simpl in n. congruence.
      + repeat destr_in SIG; inv SIG. simpl in n; congruence.
        eapply IHl; eauto.
        inv H1. simpl; auto.
    - inv WTv. simpl in *.
      unfold PrimTypeInference.find_field in H. unfold opt_result in H.
      destr_in H; inv H.
      revert H1 SIG Heqo. unfold field_sz, field_type.
      intros. unfold opt_bind in SIG.
      repeat destr_in SIG; inv SIG.
      apply wt_val_bits; auto.
      simpl. rewrite firstn_length, skipn_length.
      rewrite app_length, repeat_length.
      simpl. rewrite firstn_length, skipn_length. 
      unfold struct_sz. simpl. transitivity n0. 2: lia.
      revert idx Heqo Heqo0. generalize (struct_fields sg). clear.
      induction l; simpl; intros; eauto. easy.
      repeat destr_in Heqo; inv Heqo.
      + repeat destr_in Heqo0; inv Heqo0; simpl in *. reflexivity.
        congruence.
      + repeat destr_in Heqo0; inv Heqo0; simpl in *. congruence. eauto.
    - inv WTv.
      rewrite Forall_forall in H1. apply H1.
      eapply nth_error_In; eauto.
    - inv WTv. simpl in *.
      unfold opt_bind in SIG.
      repeat destr_in SIG; inv SIG.
      destruct (
        take_drop' (element_sz sg * (array_len sg - S idx)) bs
      ) eqn:Heqp.
      destruct (take_drop' (element_sz sg) l0) eqn:Heqp0.
      inversion Heqp. inversion Heqp0.
      rewrite H3, H4.
      eapply wt_val_bits; eauto.
      simpl.
      inv Heqp.
      repeat rewrite ?firstn_length, ?skipn_length, ?app_length, ?repeat_length. lia.
  Qed.

  Lemma bitwise_length:
    forall f a b, List.length a = List.length b
    -> List.length (bitwise f a b) = List.length a.
  Proof.
    induction a; simpl; intros; eauto.
    - destruct b; simpl in *; try congruence.
    - destruct b; simpl in *; try congruence.
      erewrite IHa; eauto.
  Qed.

  Lemma wt_binop_sigma1:
    forall u ta tb tr v0 v1 v,
    wt_binop u ta tb tr
    -> wt_val ta v0
    -> wt_val tb v1
    -> UntypedSemantics.sigma2 u v0 v1 = Some v
    -> wt_val tr v.
  Proof.
    intros u ta tb tr v0 b1 v WTB WTv1 WTv2 SIG.
    inv WTB; simpl in *.
    - destruct neg; inv SIG; constructor; auto.
    - repeat destr_in SIG; inv SIG. apply wt_val_bits; auto.
      inv WTv1. inv WTv2.
      erewrite bitwise_length; eauto.
    - repeat destr_in SIG; inv SIG. apply wt_val_bits; auto.
      inv WTv1. inv WTv2.
      erewrite bitwise_length; eauto.
    - repeat destr_in SIG; inv SIG. apply wt_val_bits; auto.
      inv WTv1. inv WTv2.
      erewrite bitwise_length; eauto.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits; auto.
      Lemma iter_length:
        forall {A} n (f: list A -> list A) (l: list A) len,
        List.length l = len
        -> (forall l, List.length l = len -> List.length (f l) = len)
        -> List.length (Nat.iter n f l) = List.length l.
      Proof.
        induction n; simpl; intros; eauto.
        rewrite H0; eauto. erewrite IHn; eauto.
      Qed.
      erewrite iter_length. auto. eauto. intros.
      rewrite <- H.
      Transparent eq_dec. destruct l. simpl; auto.
      Opaque removelast. simpl. f_equal.
      Lemma removelast_length:
        forall {A} (l: list A), List.length (removelast l) = List.length l - 1.
      Proof.
        Transparent removelast.
        induction l; simpl; intros; eauto.
        destruct l. reflexivity. Opaque removelast.
        simpl. rewrite IHl. simpl. lia.
      Qed.
      rewrite removelast_length. simpl. lia.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits; auto.
      erewrite iter_length. auto. eauto. intros.
      rewrite <- H.
      destruct l. simpl; auto.
      simpl. rewrite app_length; simpl. lia.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits; auto.
      erewrite iter_length. auto. eauto. intros.
      rewrite <- H.
      destruct l; simpl; auto.
      rewrite app_length; simpl. lia.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits; auto.
      rewrite app_length; simpl. lia.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits; auto.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits; auto.
      repeat rewrite ?firstn_length, ?skipn_length, ?app_length, ?repeat_length. lia.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits; auto.
      repeat rewrite ?firstn_length, ?skipn_length, ?app_length, ?repeat_length. lia.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits; auto.
      rewrite vect_to_list_length. auto.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits; auto.
      rewrite vect_to_list_length. auto.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits; auto.
      rewrite vect_to_list_length. auto.
    - inv WTv1. inv WTv2. destruct eq_dec; try congruence. inv SIG. apply wt_val_bits; auto.
    - inv WTv1.
      unfold opt_bind in SIG. repeat destr_in SIG; inv SIG. constructor. auto.
      unfold PrimTypeInference.find_field in H.
      unfold opt_result in H. destr_in H; inv H.
      revert Heqo Heqo0 H1.
      destruct sg. simpl in *.
      revert idx WTv2. unfold field_type. simpl.
      Opaque eq_dec.
      revert lv l.
      induction struct_fields; simpl; intros; eauto.
      inv Heqo0.
      repeat destr_in Heqo; inv Heqo. simpl in *.
      rewrite Heqs0 in Heqo0. inv Heqo0. inv H1; constructor; eauto.
      simpl in *.
      rewrite Heqs0 in Heqo0. inv Heqo0.
      unfold opt_bind in H0. destr_in H0; inv H0.
      destr_in H2; inv H2. inv H1; constructor; eauto.
    - inv WTv1. inv WTv2.
      unfold opt_bind in SIG. repeat destr_in SIG; inv SIG.
      destruct (take_drop' n bs) eqn:Heqp1.
      destruct (take_drop' (n + n0) bs) eqn:Heqp2.
      apply wt_val_bits; auto.
      unfold PrimTypeInference.find_field in H.
      unfold opt_result in H. destr_in H; inv H.
      rewrite <- H1.
      unfold fst.
      repeat rewrite ?firstn_length, ?skipn_length, ?app_length, ?repeat_length. 
      cut (n0 = List.length bs0). lia.
      rewrite H2. clear - Heqo Heqo0.
      revert idx Heqo Heqo0.
      unfold field_sz, field_type. generalize (struct_fields sg).
      induction l; simpl; intros; eauto. easy.
      repeat destr_in Heqo; inv Heqo; simpl in *;
        rewrite Heqs0 in Heqo0; inv Heqo0. reflexivity.
      destr_in H1; inv H1; eauto.
    - inv WTv1.
      unfold opt_bind in SIG. repeat destr_in SIG; inv SIG.
      generalize (take_drop_spec _ _ _ _ Heqo); intuition. subst. constructor.
      2: rewrite <- H2, ! app_length; simpl; auto.
      Lemma Forall_app:
        forall {A} (P: A -> Prop) l1 l2,
        Forall P (l1 ++ l2) <-> (Forall P l1 /\ Forall P l2).
      Proof.
        induction l1; simpl; intros; eauto.
        split. split; auto. intuition.
        intuition. inv H; constructor; auto. rewrite IHl1 in H3; intuition.
        inv H. rewrite IHl1 in H3; intuition.
        inv H0. constructor. auto. rewrite IHl1; tauto.
      Qed.
      rewrite Forall_app in H1 |- *. destruct H1; split; auto.
      inv H1; constructor; auto.
    - inv WTv1. inv WTv2. inv SIG. apply wt_val_bits. auto.
      repeat rewrite ?firstn_length, ?skipn_length, ?app_length, ?repeat_length. lia.
  Qed.

  Lemma Forall2_impl:
    forall {A B} (P1 P2: A -> B -> Prop) l1 l2, Forall2 P1 l1 l2
    -> (forall x y, In x l1 -> In y l2 -> P1 x y -> P2 x y)
    -> Forall2 P2 l1 l2.
  Proof.
    induction 1; simpl; intros; eauto.
    constructor; eauto.
  Qed.

  Lemma wt_env_app:
    forall sig1 ctx1, wt_env sig1 ctx1
    -> forall sig2 ctx2, wt_env sig2 ctx2
    -> wt_env (sig1 ++ sig2) (ctx1 ++ ctx2).
  Proof.
    induction 1; simpl; intros; eauto.
    constructor; auto.
  Qed.

  Lemma wt_env_rev:
    forall sig ctx, wt_env sig ctx
    -> wt_env (rev sig) (rev ctx).
  Proof.
    induction 1; simpl; intros; eauto. constructor.
    apply wt_env_app. auto. repeat constructor. auto.
  Qed.

  Lemma forall2_wt_wt_env:
    forall lv lt, Forall2 (fun v t => wt_val t v) lv (map snd lt)
    -> wt_env
         (rev lt)
         (map (fun '(name, _, v0) => (name, v0)) (combine (rev lt) (rev lv))).
  Proof.
    intros. rewrite <- UntypedSemantics.combine_rev.
    2: erewrite (Forall2_length _ _ _ H), map_length; eauto.
    rewrite map_rev.
    apply wt_env_rev.
    revert lt H.
    induction lv; simpl; intros; eauto.
    - inv H. destruct lt; simpl in *; try congruence. constructor.
    - inv H. destruct lt; simpl in *; try congruence.
      destr. simpl in *. inv H2. constructor; eauto.
  Qed.

  Lemma wt_env_tl sig ctx: wt_env sig ctx -> wt_env (tl sig) (tl ctx).
  Proof. induction 1; simpl; auto. constructor. Qed.

  Lemma wt_env_iter_tl n: forall sig ctx,
    wt_env sig ctx
    -> wt_env
         (Nat.iter
           n (@tl (var_t * type)) sig)
           (Nat.iter n (@tl (var_t * val)) ctx).
  Proof.
    induction n; simpl; intros; eauto.
    apply wt_env_tl. eauto.
  Qed.

  Lemma tl_app:
    forall {A: Type} (l1 l2: list A),
    Nat.iter (List.length l1) (@tl A) (l1 ++ l2) = l2.
  Proof.
    induction l1; simpl; intros; eauto.
    simpl. rewrite <- iter_assoc_spec. simpl. rewrite IHl1. auto.
  Qed.

  Lemma sig_of_bindings_eq:
    forall {A: Type} (bindings: list (var_t * A)) (bind_taus: list type) sig,
    sig_of_bindings var_t bindings bind_taus sig
    -> sig = map (fun '(name, _, t) => (name, t)) (combine bindings bind_taus).
  Proof.
    induction 1; simpl; intros; eauto.
    f_equal. eauto.
  Qed.

  Lemma forall2_map_l:
    forall {A B C: Type} (f: A -> B) (P: B -> C -> Prop) l1 (l2: list C),
    Forall2 (fun x y => P (f x) y) l1 l2
    -> Forall2 P (map f l1) l2.
  Proof. induction 1; simpl; intros; eauto. Qed.

  Lemma fold_subst_field_name_some:
    forall sg vals si sf,
    fold_left (
      fun vs '(name, v) =>
        let/opt vs0 := vs in
        subst_field_name (struct_fields sg) name v vs0)
      vals si
    = Some sf
    -> exists ssi, si = Some ssi.
  Proof.
    induction vals; simpl; intros; eauto.
    repeat destr_in H. destruct si; simpl in *. eauto.
    apply IHvals in H. destruct H; congruence.
  Qed.

  Lemma subst_field_name_wt:
    forall sg name v,
      (exists idx : index (Datatypes.length (struct_fields sg)),
          PrimTypeInference.find_field sg name = Success idx /\
          wt_val (snd (List_nth (struct_fields sg) idx)) v)
          -> forall si sf,
        Forall2 (wt_val) (map snd (struct_fields sg)) si
        -> subst_field_name (struct_fields sg) name v si = Some sf
        -> Forall2 (wt_val) (map snd (struct_fields sg)) sf.
  Proof.
    unfold PrimTypeInference.find_field.
    intro sg.
    generalize (struct_fields sg).

    assert (
        forall (l : list (string * type)) (name : string) (v : val),
          (exists idx : index (Datatypes.length l),
              List_assoc name l = Some idx /\
              wt_val (snd (List_nth l idx)) v)
              -> forall si sf : list val,
            Forall2 wt_val (map snd l) si
            -> subst_field_name l name v si = Some sf -> Forall2 wt_val (map snd l) sf
      ).
    {
      clear.
      induction l; simpl; intros; eauto.
      destr_in H1; congruence.
      destruct a; simpl in *.
      destruct H as (idx & EQ & WTv).
      repeat destr_in H1; inv H1.
      - inv EQ. simpl in *. inv H0; constructor; auto.
      - destr_in EQ; inv EQ. unfold opt_bind in H2; destr_in H2; inv H2.
        inv H0; constructor; auto.
        eapply IHl; eauto.
    }
    intros; eapply H; eauto.
    decompose [ex and] H0. unfold opt_result in H4. destr_in H4; inv H4.
    eexists; split; eauto.
  Qed.

  Lemma fold_subst_field_name_wt:
    forall sg vals,
      Forall (fun '(name,v) =>
                exists idx : index (Datatypes.length (struct_fields sg)),
                  PrimTypeInference.find_field sg name = Success idx /\
                  wt_val (snd (List_nth (struct_fields sg) idx)) v
             ) vals
             -> forall si sf,
        Forall2 (wt_val) (map snd (struct_fields sg)) si
        -> fold_left (fun vs '(name, v) =>
                     let/opt vs0 := vs in
                     subst_field_name (struct_fields sg) name v vs0
                  ) vals (Some si) = Some sf
                  -> Forall2 (wt_val) (map snd (struct_fields sg)) sf.
  Proof.
    induction 1; simpl; intros; eauto.
    inv H0; auto.
    destruct x.
    edestruct fold_subst_field_name_some; eauto. rewrite H3 in H2.
    eapply IHForall. 2: eauto.
    eapply subst_field_name_wt; eauto.
  Qed.

  Lemma forall2_3:
    forall {A B C D: Type}
           (P: (A * B) -> C -> Prop)
           (Q: D -> C -> Prop)
           (R: A * D -> Prop)
           l1 l2 l3,
      Forall2 P l1 l2
      -> Forall2 Q l3 l2
      -> (forall x y z,
          P x y
          -> Q z y
          -> R (fst x, z)
      )
      -> Forall R (combine (map fst l1) l3).
  Proof.
    induction l1; simpl; intros; eauto. inv H. inv H0. constructor; eauto.
  Qed.

  Lemma fold_subst_none:
    forall (vals: list val),
      fold_left
        (fun acc v =>
           let/opt2 pos, vs := acc in
           let/opt pat0 := take_drop pos vs in
           match pat0 with
             (l1, []) => None
           | (l1, _ :: l3) => Some (S pos, l1 ++ v :: l3)
           end
        ) vals None = None.
  Proof.
    induction vals; simpl; intros; eauto.
  Qed.

  Lemma fold_subst_array_wt:
    forall t vals,
      Forall (fun v => wt_val t v) vals
      -> forall ai af,
        Forall (fun v => wt_val t v) (snd ai)
        -> fold_left
          (fun acc v =>
             let/opt2 pos, vs := acc in
             let/opt pat0 := take_drop pos vs in
             match pat0 with
               (l1, []) => None
             | (l1, _ :: l3) => Some (S pos, l1 ++ v :: l3)
             end
          ) vals (Some ai) = Some af
          -> Forall (fun v => wt_val t v) (snd af) /\ List.length (snd af) = List.length (snd ai).
  Proof.
    induction 1; simpl; intros; eauto. inv H0; auto.
    destruct ai. unfold opt_bind in H2. repeat destr_in H2; inv H2.
    - rewrite fold_subst_none in H4; congruence.
    - eapply IHForall in H4.
      destruct H4. simpl in *.
      apply take_drop_spec in Heqo. destruct Heqo as [Heqo _]. subst.
      split; auto.
      rewrite H3; rewrite ! app_length. simpl; auto.
      apply take_drop_spec in Heqo. destruct Heqo as [Heqo _]. subst.
      clear - H H1. simpl in *.
      rewrite Forall_app in *. intuition. inv H2. constructor; auto.
    - rewrite fold_subst_none in H4; congruence.
  Qed.

  Lemma Forall2_Forall:
    forall {A B: Type} (P: A -> B -> Prop) l1 l2,
      Forall2 P l1 l2
      -> Forall (fun x => exists y, In y l2 /\ P x y) l1.
  Proof.
    induction 1; simpl; intros; eauto.
    constructor; eauto.
    eapply Forall_impl; eauto. simpl. intros. decompose [ex and] H1; eauto.
  Qed.

  Fixpoint size_daction
    {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
    (da: @daction pos_t var_t fn_name_t reg_t ext_fn_t) {struct da}
  : nat :=
    match da with
    | DError err => 0
    | DFail tau => 0
    | DVar var => 0
    | DConst _ cst => 0
    | DAssign v ex => 1 + size_daction ex
    | DSeq a1 a2 => 1 + size_daction a1 + size_daction a2
    | DBind v ex body => 1 + size_daction ex + size_daction body
    | DIf cond tbranch fbranch =>
      1 + size_daction cond + size_daction tbranch + size_daction fbranch
    | DRead port idx => 0
    | DWrite port idx value => 1 + size_daction value
    | DUnop ufn1 arg1 => 1 + size_daction arg1
    | DBinop ufn2 arg1 arg2 => 1 + size_daction arg1 + size_daction arg2
    | DExternalCall ufn arg => 1 + size_daction arg
    | DInternalCall ufn args =>
      1 + size_daction (int_body ufn) + list_sum (map size_daction args)
    | DAPos p e => 1 + size_daction e
    end.

  Lemma interp_dlist_wt:
    forall
      {reg_t ext_fn_t} (R: reg_t -> type)
      (REnv: Env reg_t),
    forall (i: list (var_t * val)
    -> UntypedSemantics.Log REnv
    -> UntypedSemantics.Log REnv
    -> @daction pos_t var_t fn_name_t reg_t ext_fn_t
    -> option (UntypedSemantics.Log REnv * val * list (var_t * val)) ) args argtypes
           sig
           (ARGS: Forall2 (fun a t =>
                             forall ctx ctx' action_log sched_log action_log' v,
                               wt_env sig ctx
                               -> wt_log R REnv action_log
                               -> wt_log R REnv sched_log
                               -> i ctx action_log sched_log a =  Some (action_log', v, ctx')
                               -> wt_env sig ctx' /\ wt_val t v /\ wt_log R REnv action_log'
                          ) args argtypes),
    forall ctx action_log sched_log,
      wt_env sig ctx
      -> wt_log R REnv action_log
      -> wt_log R REnv sched_log
      -> forall l0 at0,
        Forall2 (fun v t => wt_val t v) (rev l0) at0
        -> forall action_log' ctx' lv,
          fold_left (fun acc a =>
                       match acc with
                       | Some (action_log0, l, Gamma) =>
                           match i Gamma sched_log action_log0 a with
                           | Some (action_log, v, Gamma0) =>
                               Some (action_log, v::l, Gamma0)
                           | None => None
                           end
                       | None => None
                       end
                    ) args (Some (action_log, l0, ctx)) = Some (action_log', lv, ctx')
                    -> wt_env sig ctx' /\
            Forall2 (fun v t => wt_val t v) (rev lv) (at0 ++ argtypes) /\
            wt_log R REnv action_log'.
  Proof.
    induction args; simpl; intros; eauto.
    - inv ARGS. inv H3. simpl; repeat split; eauto. rewrite app_nil_r; auto.
    - inv ARGS. repeat destr_in H3.
      edestruct H6 as (WTE & WTV & WTL). 4: now eauto. auto. auto. auto.
      eapply IHargs in H3. 2: eauto. destruct H3; split; eauto.
      revert H4. instantiate (1:=at0++[y]). rewrite <- app_assoc. simpl. auto. auto. auto.
      auto.
      simpl.
      apply Forall2_app. eauto.
      econstructor; eauto.
      rewrite UntypedSemantics.fold_left_none in H3. congruence. auto.
  Qed.

  Lemma wt_daction_preserves_wt_env:
    forall
      {reg_t ext_fn_t} (R: reg_t -> type) (Sigma: ext_fn_t -> ExternalSignature)
      (REnv: Env reg_t) (r: env_t REnv (fun _ => val))
      (sigma: ext_fn_t -> val -> val)
      (sigma_wt:
        forall fn v, wt_val (arg1Sig (Sigma fn)) v
        -> wt_val (retSig (Sigma fn)) (sigma fn v))
      a ctx ctx' t sig action_log sched_log action_log' v,
    wt_renv R REnv r
    -> wt_env sig ctx
    -> wt_daction pos_t fn_name_t var_t (R:=R) (Sigma:=Sigma) sig a t
    -> wt_log R REnv action_log
    -> wt_log R REnv sched_log
    -> UntypedSemantics.interp_daction r sigma ctx action_log sched_log a
       = Some (action_log', v, ctx')
    -> wt_env sig ctx' /\ wt_val t v /\ wt_log R REnv action_log'.
  Proof.
    intros reg_t ext_fn_t R Sigma REnv r sigma sigma_wt ua.
    remember (size_daction ua).
    revert ua Heqn.
    pattern n.
    eapply Nat.strong_right_induction with (z:=0). 2: lia.
    intros n0 _ Plt ua Heqn. subst.
    assert (Plt':
             forall
               (ua': @daction pos_t var_t fn_name_t reg_t ext_fn_t),
               size_daction ua' < size_daction ua
               -> forall (ctx ctx' : list (var_t * val)) (t : type) (sig : tsig var_t)
                      (action_log sched_log action_log' : UntypedSemantics.Log REnv) (v : val),
                 wt_renv R REnv r
                 -> wt_env sig ctx
                 -> wt_log R REnv action_log
                 -> wt_log R REnv sched_log
                 -> wt_daction pos_t fn_name_t var_t (R:=R) (Sigma:=Sigma) sig ua' t
                 -> UntypedSemantics.interp_daction r sigma ctx action_log sched_log ua' = Some (action_log', v, ctx') -> wt_env sig ctx' /\ wt_val t v /\ wt_log R REnv action_log').
    { intros. eapply Plt. 9: eauto. 3: reflexivity. lia. eauto. auto. eauto. all: eauto. } clear Plt.
    rename Plt' into IHua. clear n.
    intros ctx ctx' t sig action_log sched_log action_log' v WTR WTE WTA WTLa WTLs INT.
    inv WTA; simpl in INT; unfold opt_bind in INT; repeat destr_in INT; inv INT.
    - repeat split; auto.
      eapply wt_env_list_assoc; eauto.
    - repeat split; auto.
    - eapply IHua in Heqo; eauto.
      destruct Heqo as (? & ? & ?).
      repeat split; eauto.
      + eapply wt_env_set; eauto.
      + constructor; reflexivity.
    - eapply IHua in Heqo; eauto.
      destruct Heqo as (?&?&?).
      eapply IHua in H2; eauto. simpl; lia. simpl; lia.
    - eapply IHua in Heqo; eauto.
      destruct Heqo as (?&?&?).
      eapply IHua in Heqo0; eauto.
      destruct Heqo0 as (?&?&?).
      intuition. inv H4. simpl; auto. simpl; lia.
      constructor; auto. simpl; lia.
    - eapply IHua in Heqo; eauto.
      destruct Heqo as (?&?&?).
      eapply IHua in H3; eauto.
      simpl; lia. simpl; lia.
    - eapply IHua in Heqo; eauto.
      destruct Heqo as (?&?&?).
      eapply IHua in H3; eauto.
      simpl; lia. simpl; lia.
    - repeat split; auto.
      eapply wt_log_cons. auto. simpl. inversion 1.
    - repeat split; auto.
      + unfold latest_write0 in Heqo.
        edestruct @log_find_wt. apply Heqo.  intros. destruct x; simpl in H.
        repeat destr_in H; inv H. reflexivity.
        eapply wt_log_app; eauto. destruct H.
        unfold log_latest_write0_fn in H. repeat destr_in H; inv H. simpl in *; auto.
      + eapply wt_log_cons; eauto. simpl. congruence.
    - repeat split; auto.
      eapply wt_log_cons; eauto. simpl. congruence.
    - eapply IHua in Heqo; eauto.
      destruct Heqo as (?&?&?).
      repeat split; auto. repeat constructor.
      eapply wt_log_cons; eauto.
    - eapply IHua in Heqo; eauto.
      destruct Heqo as (?&?&?).
      repeat split; auto.
      eapply wt_unop_sigma1; eauto.
    - eapply IHua in Heqo; eauto.
      destruct Heqo as (?&?&?).
      eapply IHua in Heqo0; eauto.
      destruct Heqo0 as (?&?&?).
      repeat split; auto.
      eapply wt_binop_sigma1; eauto.
      simpl; lia. simpl; lia.
    - eapply IHua in Heqo; eauto. destruct Heqo as (?&?&?).
      repeat split; eauto.
    - edestruct @interp_dlist_wt as (WTE' & WTLV & WTLA'). 6: now eauto.
      + eapply Forall2_impl. eauto.
        intros; eauto.
        eapply IHua. 7: now eauto.
        simpl.
        clear - H1. revert H1; induction args; simpl; intros; eauto. easy.
        destruct H1; subst; simpl in *; eauto. lia.
        apply IHargs in H. lia.
        all: eauto.
      + auto.
      + auto.
      + auto.
      + simpl. constructor.
      + eapply IHua in Heqo0; eauto.
        intuition; eauto.
        simpl; lia.
        eapply forall2_wt_wt_env in WTLV.
        rewrite rev_involutive in WTLV. auto.
    - eapply IHua in H1; eauto.
  Qed.
End WT.
