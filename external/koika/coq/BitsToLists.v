Require Export Koika.Utils.Common.
Require Export Koika.Utils.Environments.
Require Export Koika.KoikaForm.Syntax.
Require Export Koika.KoikaForm.Untyped.UntypedLogs.
Require Import Koika.KoikaForm.Desugaring.DesugaredSyntax.
Require Import Koika.KoikaForm.SimpleVal.
Require Export Koika.Utils.Tactics.
Require Import Coq.Program.Equality.

Lemma ubits_of_value_len:
  forall {tau} (v: type_denote tau) bs,
  ubits_of_value (val_of_value v) = bs -> List.length bs = type_sz tau.
Proof.
  fix IHt 1. destruct tau; simpl; intros; subst.
  apply vect_to_list_length.
  apply vect_to_list_length.
  - revert sig v. destruct sig. simpl.
    induction struct_fields; simpl; intros.
    + subst. reflexivity.
    + destruct a. destruct v. simpl.
      rewrite List.concat_app. simpl.
      rewrite app_length. simpl.
      rewrite IHstruct_fields.
      unfold struct_fields_sz. simpl. f_equal.
      rewrite app_nil_r.
      eapply IHt; eauto.
  - revert sig v. destruct sig. simpl. intros.
    induction array_len; simpl. auto.
    destruct v. simpl.
    rewrite concat_app. rewrite app_length. simpl.
    unfold vect_to_list in IHarray_len. rewrite IHarray_len.
    clear IHarray_len. f_equal. rewrite app_nil_r. eapply IHt. eauto.
Qed.

Lemma ubits_of_value_ok:
  forall {tau} (v: type_denote tau) bs,
  ubits_of_value (val_of_value v) = bs -> vect_to_list (bits_of_value v) = bs.
Proof.
  fix IHt 1. destruct tau; simpl; intros; subst; auto.
  - revert sig v. destruct sig. simpl.
    induction struct_fields; simpl; intros.
    + subst. reflexivity.
    + destruct a. destruct v. simpl.
      rewrite List.concat_app. simpl.
      rewrite <- IHstruct_fields. rewrite app_nil_r.
      simpl in *.
      rewrite <- (IHt _ t0 _ eq_refl).
      rewrite <- vect_to_list_app.
      reflexivity.
  - revert sig v. destruct sig. simpl. intros.
    induction array_len; simpl. auto.
    destruct v. simpl.
    rewrite vect_to_list_app. rewrite IHarray_len. clear IHarray_len.
    rewrite concat_app. f_equal. simpl.
    rewrite app_nil_r. eapply IHt. eauto.
Qed.

Definition bits_split (n: nat) {sz} (v: bits sz)
: option (bits n * bits (sz - n)).
Proof.
  destruct (lt_dec n sz). 2: exact None.
  replace sz with (n + (sz - n)) in v. 2: lia.
  destruct (Bits.split v) eqn:?.
  exact (Some (v0, v1)).
Defined.

Fixpoint take_drop {A: Type} (n: nat) (l: list A) : option (list A * list A) :=
  match n with
  | O   => Some ([], l)
  | S n =>
    match l with
    | []   => None
    | a::l => let/opt2 l1, l2 := take_drop n l in Some (a::l1, l2)
    end
  end.

(* take_drop is a weird name for a function that splits a list *)
Definition take_drop' {A: Type} n (l: list A) :=
  (List.firstn n l, List.skipn n l).

Fixpoint bits_splitn (nb sz_elt: nat) (bs: list bool)
: option (list (list bool)) :=
    match nb with
    | O => Some []
    | S nb =>
      let/opt2 hd, rest := take_drop sz_elt bs in
      let/opt tl := bits_splitn nb sz_elt rest in
      Some (hd :: tl)
    end.

Lemma take_drop_succeeds:
  forall {A:Type} (n: nat) (l: list A) (LT: n <= Datatypes.length l),
  exists la lb, take_drop n l = Some (la, lb).
Proof.
  induction n; simpl; intros; eauto.
  destruct l; simpl in LT. lia.
  destruct (IHn l) as (la & lb & EQ). lia.
  rewrite EQ. simpl.
  eauto.
Qed.

Lemma take_drop_spec:
  forall {A:Type} (n: nat) (l la lb: list A),
  take_drop n l = Some (la, lb)
  -> l = la ++ lb /\ List.length la = n /\ List.length lb = List.length l - n.
Proof.
  induction n; simpl; intros; eauto.
  inversion H; clear H; subst. repeat split; try reflexivity. lia.
  destruct l. congruence.
  destruct (take_drop n l) eqn:EQ; simpl in H; try congruence.
  destruct p. inversion H; clear H; subst.
  apply IHn in EQ. destruct EQ as (EQ1 & EQ2 & EQ3). subst. simpl.
  repeat split; lia.
Qed.

Lemma take_drop'_cons:
  forall {A} (l l1 l2: list A) a n,
  take_drop' n l = (l1, l2) -> take_drop' (S n) (a::l) = (a::l1, l2).
Proof.
  unfold take_drop'. simpl. intros. destruct (take_drop n l) eqn:?.
  - destruct p. inversion H; subst. simpl. auto.
  - simpl. inversion H; subst. auto.
Qed.

Lemma take_drop'_spec:
  forall {A:Type} (n: nat) (l la lb: list A),
  take_drop' n l = (la, lb)
  -> l = la ++ lb /\ List.length la <= n
  /\ List.length lb = List.length l - List.length la.
Proof.
  induction n; simpl; intros; eauto.
  inversion H; clear H; subst. repeat split; try reflexivity. simpl; lia.
  destruct l; simpl in *. unfold take_drop' in H. simpl in *.
  inversion H; clear H.
  simpl. repeat split; lia.
  destruct (take_drop' n l) as (l1 & l2) eqn:?.
  erewrite take_drop'_cons in H; eauto. inversion H; subst. simpl.
  apply IHn in Heqp. destruct Heqp as (EQ1 & EQ2 & EQ3). subst.
  repeat split; auto. lia.
Qed.

Lemma app_eq_inv:
  forall {A:Type} (a b c d: list A),
  a ++ b = c ++ d -> List.length a = List.length c -> a = c /\ b = d.
Proof.
  induction a; simpl; intros; eauto.
  - destruct c; simpl in H0; try congruence.
    simpl in *. auto.
  - destruct c; simpl in H0; try congruence.
    simpl in *. inversion H; clear H; subst.
    apply IHa in H3. destruct H3; subst; auto. lia.
Qed.

Inductive wt_val: type -> val -> Prop :=
| wt_bits: forall n bs, List.length bs = n -> wt_val (bits_t n) (Bits bs)
| wt_enum: forall sig bs,
  List.length bs = enum_bitsize sig -> wt_val (enum_t sig) (Enum sig bs)
| wt_struct: forall sig lv,
  Forall2 (fun nt v => wt_val nt v) (map snd (struct_fields sig)) lv
  -> wt_val (struct_t sig) (Struct sig lv)
| wt_array: forall sig lv,
  Forall (fun v => wt_val (array_type sig) v) lv
  -> List.length lv = array_len sig
  -> wt_val (array_t sig) (Array sig lv).

Fixpoint size_type (t: type) :=
  match t with
  | bits_t n => 1
  | enum_t sig => 1
  | struct_t sig =>
    1 + list_sum (List.map (fun '(_, t) => size_type t) (struct_fields sig))
  | array_t sig => 1 + size_type (array_type sig)
  end.

Lemma wt_val_ind':
  forall
    (P : type -> val -> Prop)
    (Hbits: forall (n : nat) (bs : list bool),
      Datatypes.length bs = n -> P (bits_t n) (Bits bs))
    (Henum: forall (sig : enum_sig) (bs : list bool),
      Datatypes.length bs = enum_bitsize sig -> P (enum_t sig) (Enum sig bs))
    (Hstruct: forall (sig : struct_sig) (lv : list val),
      Forall2 (fun (nt : type) (v : val) => wt_val nt v)
        (map snd (struct_fields sig)) lv
        -> Forall2 (fun (nt : type) (v : val) => wt_val nt v -> P nt v)
        (map snd (struct_fields sig)) lv
        -> P (struct_t sig) (Struct sig lv))
    (Harray:
      forall (sig : array_sig) (lv : list val),
      Forall (fun v : val => wt_val (array_type sig) v) lv
      -> Forall (fun v : val => wt_val (array_type sig) v
      -> P (array_type sig) v) lv
      -> Datatypes.length lv = array_len sig
      -> P (array_t sig) (Array sig lv)) (t: type) (v: val),
    wt_val t v
    -> P t v.
Proof.
  intros P Hbits Henum Hstruct Harray t v.
  remember (size_type t).
  revert t v Heqn.
  pattern n.
  eapply Nat.strong_right_induction with (z:=0).
  2: lia.
  intros n0 _ Plt t t0 a Heqn.
  assert (Plt': forall t v, size_type t < n0 -> wt_val t v -> P t v).
  { intros. eapply Plt. 3: reflexivity. lia. auto. auto. }
  clear Plt. rename Plt' into Plt.
  subst.
  inversion Heqn; subst; eauto.
  - eapply Hstruct. eauto.
    revert H.
    simpl in Plt.
    assert (
      Forall (fun '(n,t) => forall v, wt_val t v -> P t v) (struct_fields sig)
    ).
    {
      revert Plt; clear. destruct sig. simpl.
      induction struct_fields; simpl; intros. constructor.
      constructor; eauto. destruct a; simpl; intros.
      eapply Plt. lia. auto.
      apply IHstruct_fields.
      intros; eapply Plt; eauto. lia.
    }
    clear Heqn. revert H lv. clear Plt.
    destruct sig. simpl. clear.
    induction 1; simpl; intros; eauto. inv H. constructor.
    inv H1.
    constructor; auto. destruct x; simpl in *; eauto.
  - eapply Harray; eauto.
    rewrite Forall_forall. intros x IN WT.
    eapply Plt; eauto.
Qed.

Fixpoint size_val (v: val) :=
  match v with
  | Bits _ => 1
  | Enum _ _ => 1
  | Struct sig lv => 1 + list_sum (map size_val lv)
  | Array sig lv => 1 + list_sum (map size_val lv)
  end.

Lemma take_drop_succeeds_eq:
  forall {A:Type} (n: nat) (l: list A) (LT: n = Datatypes.length l),
  take_drop n l = Some (l, []).
Proof.
  induction n; simpl; intros; eauto.
  destruct l; simpl in LT. reflexivity. lia.
  destruct l; simpl in LT; try lia.
  rewrite IHn; simpl; auto.
Qed.

Lemma take_drop_head:
  forall {A} n (l1 l2: list A), n = List.length l1
  -> take_drop n (l1 ++ l2) = Some (l1, l2).
Proof.
  intros. subst. revert l2.
  induction l1; simpl; intros; subst; eauto.
  rewrite IHl1. simpl. reflexivity.
Qed.

Lemma length_concat_same:
  forall {A} (l: list (list A)) sz, Forall (fun x => List.length x = sz) l
  -> Datatypes.length (List.concat l) = List.length l * sz.
Proof.
  induction 1; simpl; intros; eauto.
  rewrite app_length; rewrite IHForall. lia.
Qed.

Lemma ubits_of_value_len':
  forall tau v, wt_val tau v
  -> List.length (ubits_of_value v) = type_sz tau.
Proof.
  intros tau v WT.
  pattern tau, v.
  eapply wt_val_ind'; simpl; intros; eauto.
  - revert sig lv H0 H. destruct sig. simpl.
    induction struct_fields; simpl; intros.
    + inv H0. reflexivity.
    + inv H0. inv H. simpl.
      rewrite concat_app, app_length. simpl.
      rewrite app_nil_r. rewrite H3; auto.
      erewrite IHstruct_fields. reflexivity. eauto. auto.
  - rewrite Bits.rmul_correct. erewrite length_concat_same.
    rewrite rev_length. rewrite map_length. rewrite H1. reflexivity.
    rewrite Forall_forall in *.
    intros x IN. subst.
    apply In_rev in IN.
    rewrite in_map_iff in IN. destruct IN as (x0 & EQ & IN); subst.
    eapply H0. auto. eauto.
Qed.

Lemma bits_splitn_concat:
  forall sz l n,
  Forall (fun l => List.length l = sz) l
  -> List.length l = n -> bits_splitn n sz (List.concat l) = Some l.
Proof.
  intros. subst.
  induction H; simpl; intros; auto.
  rewrite take_drop_head; auto. simpl.
  rewrite IHForall. simpl. reflexivity.
Qed.

Fixpoint uvalue_of_bits {tau: type} (bs: list bool) {struct tau}: option val :=
  let uvalue_of_struct_bits := (
    fix uvalue_of_struct_bits {fields: list (string * type)} (bs: list bool)
      : option (list val)
    :=
     match fields with
     | [] => Some []
     | (nm, tau) :: fields =>
       let/opt2 b0, b1 := take_drop (List.length bs - type_sz tau) bs in
       let/opt tl := uvalue_of_struct_bits (fields:=fields) b0 in
       let/opt hd := uvalue_of_bits (tau:=tau) b1 in
       Some ( hd :: tl)
     end
  ) in
  let uvalue_of_list_bits tau :=
    fix uvalue_of_list_bits (l : list (list bool)) : option (list val) :=
      match l with
      | [] => Some []
      | hd::tl =>
        let/opt hd := uvalue_of_bits (tau:=tau) hd in
        let/opt tl := uvalue_of_list_bits tl in
        Some (hd::tl)
      end
  in
  match tau with
  | bits_t _ => Some (Bits bs)
  | enum_t sig =>
    let/opt2 b0, _ := take_drop (enum_bitsize sig) bs in
    Some (Enum sig b0)
  | struct_t sig =>
    let/opt lv := uvalue_of_struct_bits (fields:=struct_fields sig) bs in
    Some (Struct sig lv)
  | array_t sig =>
    let/opt lbs := bits_splitn (array_len sig) (type_sz (array_type sig)) bs in
    let/opt lv := uvalue_of_list_bits (array_type sig) (rev lbs) in
    Some (Array sig lv)
  end.

Lemma uvalue_of_bits_val:
  forall tau v, wt_val tau v
  -> uvalue_of_bits (tau:=tau) (ubits_of_value v) = Some v.
Proof.
  intros tau v WT.
  pattern tau, v.
  eapply wt_val_ind'; simpl; intros; eauto.
  - rewrite take_drop_succeeds_eq; simpl; auto.
  - revert sig lv H H0. destruct sig. simpl.
    induction struct_fields; simpl; intros.
    + inv H. reflexivity.
    + inv H. inv H0. destruct a. simpl in *.
      rewrite concat_app, app_length. simpl.
      rewrite app_nil_r.
      erewrite ubits_of_value_len'. 2: eauto.
      rewrite take_drop_head. 2: lia. simpl.
      generalize (IHstruct_fields l' H5 H7). intro A.
      match type of A with
      | context[ let/opt _ := ?a in _ ] => destruct a eqn:?
      end; simpl in *; try congruence.
      rewrite H4. simpl. inv A; auto. auto.
  - assert (Forall (
      fun v =>
        wt_val (array_type sig) v
        /\ uvalue_of_bits (tau:= array_type sig) (ubits_of_value v) = Some v
      )
    lv).
    { rewrite Forall_forall in *; simpl; intros. split; eauto. }
    clear H H0.
    rewrite bits_splitn_concat.
    simpl.
    rewrite rev_involutive.
    cut ((
      fix uvalue_of_list_bits (l : list (list bool)) : option (list val) :=
        match l with
        | [] => Some []
        | hd :: tl =>
          let/opt hd0 := uvalue_of_bits (tau:=array_type sig) hd in
          let/opt tl0 := uvalue_of_list_bits tl in Some (hd0 :: tl0)
        end
    ) (map ubits_of_value lv) = Some lv).
    intro A; rewrite A. simpl. reflexivity.
    revert H1 H2. generalize lv (array_len sig). clear.
    intros l n EQ. subst. revert l.
    induction l; simpl; intros; eauto.
    inv H2. destruct H1. rewrite H0. simpl.
    rewrite IHl. simpl. auto. auto.
    rewrite Forall_forall in *. intros x IN.
    apply In_rev in IN.
    rewrite in_map_iff in IN. destruct IN as (xx & EQ & IN). subst.
    erewrite ubits_of_value_len'. eauto.
    apply H2. auto. rewrite rev_length, map_length; auto.
Qed.

Lemma wt_val_of_value: forall (tau: type) (v: tau), wt_val tau (val_of_value v).
Proof.
  fix IHt 1. destruct tau; simpl; intros.
  - constructor. rewrite vect_to_list_length. auto.
  - constructor. rewrite vect_to_list_length. auto.
  - eapply wt_struct.
    revert v. generalize (struct_fields sig).
    induction l; simpl; intros; eauto.
    destruct a. destruct v. simpl. constructor. apply IHt.
    eauto.
  - eapply wt_array.
    rewrite Forall_forall. intros x IN.
    rewrite in_map_iff in IN.
    destruct IN as (xx & EQ & IN). subst.
    apply IHt.
    rewrite map_length.
    rewrite vect_to_list_length. auto.
Qed.

Lemma uvalue_of_bits_val':
  forall tau v,
  uvalue_of_bits (tau:=tau) (ubits_of_value (val_of_value (tau:=tau) v))
  = Some (val_of_value (tau:=tau) v).
Proof.
  intros.
  apply uvalue_of_bits_val.
  apply wt_val_of_value.
Qed.

Fixpoint get_field_struct (s: list (string * type)) (lv: list val) f
: option val :=
  match s, lv with
  | (n, _)::s, a::lv => if eq_dec n f then Some a else get_field_struct s lv f
  | _, _ => None
  end.

Fixpoint find_field_offset_right (s: list (string * type)) f
: option (nat * nat) :=
  match s with
  | (n, t)::s =>
    if eq_dec f n then Some (struct_fields_sz s, type_sz t)
    else find_field_offset_right s f
  | [] => None
  end.

Definition get_field (s: val) f : option val :=
  match s with
  | Struct sig lv => get_field_struct (struct_fields sig) lv f
  | _ => None
  end.

Lemma uvalue_of_bits_val_of_value:
  forall (tau: type) (v: vect bool (type_sz tau)),
  uvalue_of_bits (tau:=tau) (vect_to_list v)
  = Some (val_of_value (value_of_bits v)).
Proof.
  intros; rewrite <- uvalue_of_bits_val'. f_equal.
  erewrite <- ubits_of_value_ok. 2: eauto.
  rewrite bits_of_value_of_bits. auto.
Qed.

Lemma repeat_bits_const: forall x n, repeat x n = vect_to_list (Bits.const n x).
Proof.
  induction n; simpl; auto.
  rewrite IHn. reflexivity.
Qed.

Lemma last_nth:
  forall {A} d (l: list A), last l d = nth (List.length l - 1) l d.
Proof.
  induction l; simpl; intros; eauto.
  destr. simpl. auto.
  rewrite IHl. simpl. rewrite Nat.sub_0_r. reflexivity.
Qed.

Lemma bits_nth_list:
  forall s (v: vect bool s) idx,
  Bits.nth v idx = nth (index_to_nat idx) (vect_to_list v) false.
Proof.
  induction s; intros. simpl in idx; easy.
  unfold Bits.nth. destr. simpl. auto. fold @vect_nth.
  rewrite IHs. destruct v.  simpl. reflexivity.
Qed.

Lemma msb_spec: forall s (v: bits s), Bits.msb v = last (vect_to_list v) false.
Proof.
  unfold Bits.msb. intros.
  destr. destruct v. reflexivity.
  rewrite vect_last_nth.
  rewrite last_nth. rewrite vect_to_list_length.
  simpl Nat.sub.
  rewrite Nat.sub_0_r.
  rewrite bits_nth_list. f_equal.
  apply index_to_nat_of_nat.
  apply index_of_nat_largest.
Qed.

Lemma vect_extend_end_firstn:
  forall x s' (v: bits (Nat.min x s')) d,
  vect_to_list (vect_extend_end_firstn v d) =
  vect_to_list (vect_extend_end v x d).
Proof.
  unfold vect_extend_end_firstn.
  intros. rewrite vect_to_list_eq_rect. auto.
Qed.

Lemma vect_to_list_cons:
  forall {A: Type} e s (v: vect A s),
  vect_to_list (e::v)%vect = e:: vect_to_list v.
Proof. reflexivity. Qed.

Lemma vect_firstn_to_list:
  forall s (v: bits s) n,
  vect_to_list (vect_firstn n v) = fst (take_drop' n (vect_to_list v)).
Proof.
  induction s; simpl; intros. simpl in *. destruct v. destr; reflexivity.
  destr. reflexivity.
  erewrite <- vect_to_list_eq_rect.
  Unshelve.
  3: replace (Nat.min (S n0) (S s)) with (S (Nat.min n0 s)); reflexivity.
  simpl.
  rewrite vect_to_list_cons.
  rewrite IHs.
  destruct v. simpl.
  cbn. reflexivity.
Qed.

Lemma vect_skipn_to_list:
  forall s (v: bits s) n,
  vect_to_list (vect_skipn n v) = snd (take_drop' n (vect_to_list v)).
Proof.
  induction s; simpl; intros. simpl in *. destruct v. destr; reflexivity.
  destr. reflexivity.
  rewrite IHs.
  unfold take_drop'.
  destruct v. simpl.
  cbn. unfold vect_to_list.
  reflexivity.
Qed.

Lemma take_drop'_spec2:
  forall {A:Type} (n: nat) (l la lb: list A), take_drop' n l = (la, lb)
  -> l = la ++ lb /\ List.length la = Nat.min n (List.length l).
Proof.
  induction n; simpl; intros; eauto.
  inversion H; clear H; subst. repeat split; try reflexivity.
  destruct l; simpl in *. unfold take_drop' in H. simpl in *.
  inversion H; clear H.
  simpl. repeat split; lia.
  destruct (take_drop' n l) as (l1 & l2) eqn:?.
  erewrite take_drop'_cons in H; eauto. inv H. simpl.
  apply IHn in Heqp. destruct Heqp as (EQ1 & EQ2). subst.
  repeat split; auto.
Qed.

Lemma struct_fields_sz_skipn:
  forall n f, struct_fields_sz (skipn n f) <= struct_fields_sz f.
Proof.
  induction n; simpl; intros; eauto. destr. auto.
  etransitivity. apply IHn. unfold struct_fields_sz. simpl. lia.
Qed.

Lemma field_offset_right_le:
  forall sig s, field_offset_right sig s <= struct_sz sig.
Proof.
  unfold field_offset_right, struct_sz.
  simpl type_sz.
  intros; apply struct_fields_sz_skipn.
Qed.

Lemma find_field_offset_right_spec:
  forall f sig (i: index (List.length (struct_fields sig))),
  PrimTypeInference.find_field sig f = Success i
  -> find_field_offset_right (struct_fields sig) f
  = Some (field_offset_right sig i, field_sz sig i).
Proof.
  intros f sig i FF.
  unfold PrimTypeInference.find_field in FF. unfold opt_result in FF.
  destr_in FF; inv FF.
  revert i Heqo. simpl. destruct sig. simpl. clear.
  induction struct_fields; intros; eauto. easy.
  simpl. destruct a. simpl in *.
  destr_in Heqo.
  * inv Heqo. f_equal.
  * destr_in Heqo; inv Heqo.
    erewrite IHstruct_fields; eauto.
    f_equal.
Qed.

Definition enum_sig_eq_dec (s1 s2: enum_sig) : {s1 = s2} + {s1 <> s2}.
Proof.
  destruct s1, s2; simpl.
  destruct (eq_dec enum_name enum_name0).
  2: right; intro A; inv A; congruence.
  destruct (eq_dec enum_size enum_size0).
  2: right; intro A; inv A; congruence.
  destruct (eq_dec enum_bitsize enum_bitsize0).
  2: right; intro A; inv A; congruence.
  subst.
  destruct (eq_dec enum_members enum_members0).
  destruct (eq_dec enum_bitpatterns enum_bitpatterns0).
  left; subst; reflexivity. right; intro A; inv A.
  apply Eqdep_dec.inj_pair2_eq_dec in H1. 2: apply eq_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H1. 2: apply eq_dec.
  congruence.
  right; intro A; inv A.
  apply Eqdep_dec.inj_pair2_eq_dec in H0. 2: apply eq_dec. congruence.
Defined.

Definition struct_sig_eq_dec (s1 s2: struct_sig) : {s1 = s2} + {s1 <> s2}.
Proof.
  destruct s1, s2; simpl.
  destruct (eq_dec struct_name struct_name0).
  2: right; intro A; inv A; congruence.
  destruct (eq_dec struct_fields struct_fields0).
  2: right; intro A; inv A; congruence.
  left; subst; reflexivity.
Defined.

Lemma strong_ind_type:
  forall (P: nat -> Type) (IH: forall n, (forall m, m < n -> P m) -> P n),
  forall n, forall m, m <= n -> P m.
Proof.
  induction n. intros. apply IH. lia.
  intros.
  destruct (le_dec m n); eauto.
  assert (m = S n) by lia. clear H n0. subst.
  apply IH. intros. apply IHn; auto. lia.
Defined.

Lemma val_ind':
  forall
    (P : val -> Type) (Hbits: forall (bs : list bool), P (Bits bs))
    (Henum: forall (sig : enum_sig) (bs : list bool), P (Enum sig bs))
    (Hstruct: forall (sig : struct_sig) (lv : list val),
      (forall x, In x lv -> P x) -> P (Struct sig lv))
    (Harray:
      forall (sig : array_sig) (lv : list val),
      (forall x, In x lv -> P x)-> P (Array sig lv))
    (v: val),
  P v.
Proof.
  intros P Hbits Henum Hstruct Harray v.
  remember (size_val v).
  revert v Heqn.
  pattern n.
  eapply strong_ind_type. 2: reflexivity.
  intros n0 Plt v Heqn.
  assert (Plt': forall v, size_val v < n0 -> P v).
  { intros. eapply Plt. 2: reflexivity. lia. }
  clear Plt. rename Plt' into Plt.
  subst.
  destruct v; eauto.
  - eapply Hstruct.
    intros.
    eapply Plt. simpl.
    clear Plt. revert x v H.
    induction v; simpl; intros; eauto. easy.
    destruct H; subst; eauto. lia.
    eapply Nat.lt_le_trans. apply IHv; auto. lia.
  - eapply Harray.
    intros.
    eapply Plt. simpl.
    clear Plt. revert x v H.
    induction v; simpl; intros; eauto. easy.
    destruct H; subst; eauto. lia.
    eapply Nat.lt_le_trans. apply IHv; auto. lia.
Defined.

Definition list_eq_dec'
  {A: Type} (l1 l2: list A) (Aeq: forall x y, In x l1 -> {x = y} + {x <> y})
: {l1 = l2} + {l1 <> l2}.
Proof.
  revert l1 Aeq l2; induction l1; simpl; intros.
  - destruct l2. left; reflexivity. right; intro B; inv B.
  - destruct l2. right; congruence.
    destruct (Aeq a a0). simpl; auto. subst.
    2: right; intro B; inv B; congruence.
    edestruct (fun pf => IHl1 pf l2). intros; eauto.
    subst. left; reflexivity.
    right; intro B; inv B; congruence.
Defined.

Definition
  list_eqb {A: Type} (Aeq: forall x y:A, bool) :=
  fix list_eqb (l1 l2: list A)
    : bool :=
  match l1, l2 with
  | [], [] => true
  | [], _ | _, [] => false
  | a1::l1, a2::l2 => Aeq a1 a2 && list_eqb l1 l2
  end.

Fixpoint val_beq (v1 v2: val) {struct v1}: bool :=
  match v1, v2 with
  | Bits l1, Bits l2 =>
      list_eqb Bool.eqb l1 l2
  | Enum sg1 l1, Enum sg2 l2 =>
      if enum_sig_eq_dec sg1 sg2
      then list_eqb Bool.eqb l1 l2
      else false
  | Struct sg1 l1, Struct sg2 l2 =>
      if eq_dec sg1 sg2
      then list_eqb  val_beq l1 l2
      else false
  | Array sg1 l1, Array sg2 l2 =>
      if eq_dec sg1 sg2
      then list_eqb  val_beq l1 l2
      else false
  | _, _ => false
  end.

Lemma list_eqb_correct:
  forall
    {A:Type} (eqb: A -> A -> bool)
    (eqb_correct: forall a b, eqb a b = true <-> a = b) (l1 l2: list A),
  list_eqb eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1; destruct l2; simpl; intros; eauto.
  - tauto.
  - intuition congruence.
  - intuition congruence.
  - rewrite andb_true_iff. rewrite eqb_correct. rewrite IHl1.
    split. intuition. subst; auto.
    inversion 1; intuition congruence.
Qed.

Lemma list_eqb_correct2:
  forall
    {A:Type} (l1 l2: list A) (eqb: A -> A -> bool)
    (eqb_correct: forall a b, In a l1 -> eqb a b = true <-> a = b),
  list_eqb eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1; destruct l2; simpl; intros; eauto.
  - tauto.
  - intuition congruence.
  - intuition congruence.
  - rewrite andb_true_iff. rewrite eqb_correct. rewrite IHl1.
    split. intuition. subst; auto.
    inversion 1; intuition congruence.
    intros; eauto. auto.
Qed.

Lemma val_beq_correct: forall v1 v2, val_beq v1 v2 = true <-> v1 = v2.
Proof.
  intro v1; pattern v1. eapply val_ind'.
  + intros bs v2.
    split.
    intro VBEQ; destruct v2; simpl in VBEQ; try congruence.
    apply list_eqb_correct in VBEQ. subst; auto.
    apply eqb_true_iff.
    intros; subst. simpl. rewrite list_eqb_correct. auto.
    apply eqb_true_iff.
  + intros sig bs v2. split.
    intro VBEQ; simpl in VBEQ; destr_in VBEQ; try congruence.
    destr_in VBEQ.
    apply list_eqb_correct in VBEQ. subst; auto.
    apply eqb_true_iff. congruence.
    intros; subst. simpl. destr; try congruence.
    rewrite list_eqb_correct. auto.
    apply eqb_true_iff.
  + intros sig lv IH v2.
    destruct v2; try (simpl; intuition congruence).
    unfold val_beq. fold val_beq.
    destr. rewrite list_eqb_correct2.
    subst. intuition congruence. intros; apply IH; auto.
    intuition congruence.
  + intros sig lv IH v2.
    destruct v2; try (simpl; intuition congruence).
    unfold val_beq. fold val_beq.
    destr. rewrite list_eqb_correct2.
    subst. intuition congruence. intros; apply IH; auto.
    intuition congruence.
Qed.

Definition enum_sig_eqb (s1 s2: enum_sig) :=
  (enum_name s1 =? enum_name s2)
  && (Nat.eqb (enum_size s1) (enum_size s2))
  && (Nat.eqb (enum_bitsize s1) (enum_bitsize s2))
  && list_eqb eqb
     (vect_to_list (enum_members s1)) (vect_to_list (enum_members s2))
  && list_eqb
     (fun l1 l2 => list_eqb  Bool.eqb l1 l2)
     (map vect_to_list (vect_to_list (enum_bitpatterns s1)))
     (map vect_to_list (vect_to_list (enum_bitpatterns s2))).

Lemma map_inj:
  forall
    {A B: Type} (f: A -> B) (finj: forall a b, f a = f b -> a = b) l1 l2
    (EQ: map f l1 = map f l2),
  l1 = l2.
Proof.
  induction l1; simpl; intros; eauto.
  destruct l2; simpl in *; congruence.
  destruct l2; simpl in *; try congruence.
  inv EQ.
  apply finj in H0. apply IHl1 in H1. congruence.
Qed.

Lemma list_eqb_refl:
  forall {A: Type} (eqb: A -> A -> bool) (eqb_refl: forall a, eqb a a = true) l,
  list_eqb eqb l l = true.
Proof.
  induction l; simpl; intros; eauto.
  rewrite eqb_refl, IHl; auto.
Qed.

Lemma val_eq_dec_bits:
  forall {T: Type} (A1 A2: T) b1 b2,
  (if val_beq (Bits b1) (Bits b2) then A1 else A2)
  = (if list_eqb Bool.eqb b1 b2 then A1 else A2).
Proof.
  intros.
  simpl. auto.
Qed.

Fixpoint bitwise (f: bool -> bool -> bool) (l1 l2: list bool) {struct l1}
: list bool :=
  match l1, l2 with
  | [], [] => []
  | [], l2 => map (fun x => f false x) l2
  | l1, [] => map (fun x => f x false) l1
  | a1::l1, a2::l2 => f a1 a2 :: bitwise f l1 l2
  end.

Lemma and_correct:
  forall
    sz
    (arg1: arg1Sig (PrimSignatures.Sigma2 (PrimTyped.Bits2 (PrimTyped.And sz))))
    (arg2: arg2Sig (PrimSignatures.Sigma2 (PrimTyped.Bits2 (PrimTyped.And sz))))
    ret,
  PrimSpecs.sigma2 (PrimTyped.Bits2 (PrimTyped.And sz)) arg1 arg2 = ret
  -> match val_of_value arg1, val_of_value arg2 with
  | Bits arg1, Bits arg2 => Bits (bitwise andb arg1 arg2) = (val_of_value ret)
  | _, _ => False
  end.
Proof.
  simpl. intros. f_equal. subst.
  revert arg1 arg2.
  induction sz; simpl. reflexivity.
  destruct arg1, arg2. simpl.
  unfold Bits.and in *. simpl.
  rewrite vect_to_list_cons. f_equal. rewrite <- IHsz.
  reflexivity.
Qed.

Lemma len_to_list:
  forall sz (v: bits sz), sz = Datatypes.length (vect_to_list v).
Proof. intros; rewrite vect_to_list_length. reflexivity. Defined.

Lemma vect_to_list_of_list:
  forall (v: list bool), vect_to_list (vect_of_list v) = v.
Proof.
  induction v; simpl; intros. reflexivity.
  rewrite vect_to_list_cons. congruence.
Qed.

Lemma vect_of_list_to_list:
  forall sz (v: bits sz),
  vect_of_list (vect_to_list v) = rew [vect bool] (len_to_list sz v) in v.
Proof.
  intros. apply vect_to_list_inj.
  rewrite vect_to_list_of_list.
  rewrite vect_to_list_eq_rect. reflexivity.
Qed.

Lemma vect_to_list_vect_unsnoc:
  forall sz (v: bits (S sz)) b v',
  vect_unsnoc v = (b, v') -> vect_to_list v' = removelast (vect_to_list v).
Proof.
  induction sz; simpl; intros.
  - inv H. destruct v. simpl. reflexivity.
  - destr_in H. inv H.
    rewrite vect_to_list_cons. f_equal.
    erewrite IHsz. 2: eauto. simpl. reflexivity.
Qed.

Lemma lsl1:
  forall sz (v: bits sz), sz <> 0
  -> vect_to_list (Bits.lsl1 v) = false :: removelast (vect_to_list v).
Proof.
  unfold Bits.lsl1. destruct sz. congruence. intros.
  rewrite vect_to_list_cons. f_equal.
  erewrite vect_to_list_vect_unsnoc. 2: apply surjective_pairing.
  reflexivity.
Qed.

Lemma lsl1':
  forall sz (v: bits sz),
  vect_to_list (Bits.lsl1 v)
  = if eq_dec sz O then [] else false :: removelast (vect_to_list v).
Proof.
  intros. destr.
  subst. destruct v; reflexivity.
  apply lsl1; auto.
Qed.

Lemma and_correct':
  forall sz (arg1: bits_t sz) (arg2: bits_t sz),
  bitwise andb (vect_to_list arg1) (vect_to_list arg2)
  = vect_to_list (Bits.and arg1 arg2).
Proof.
  induction sz; simpl. reflexivity.
  destruct arg1, arg2. simpl.
  unfold Bits.and in *. simpl.
  rewrite vect_to_list_cons. f_equal. rewrite <- IHsz.
  reflexivity.
Qed.

Lemma or_correct':
  forall sz (arg1: bits_t sz) (arg2: bits_t sz),
  bitwise orb (vect_to_list arg1) (vect_to_list arg2)
  = vect_to_list (Bits.or arg1 arg2).
Proof.
  induction sz; simpl. reflexivity.
  destruct arg1, arg2. simpl.
  unfold Bits.or in *. simpl.
  rewrite vect_to_list_cons. f_equal. rewrite <- IHsz.
  reflexivity.
Qed.

Lemma xor_correct':
  forall sz (arg1: bits_t sz) (arg2: bits_t sz),
  bitwise xorb (vect_to_list arg1) (vect_to_list arg2)
  = vect_to_list (Bits.xor arg1 arg2).
Proof.
  induction sz; simpl. reflexivity.
  destruct arg1, arg2. simpl.
  unfold Bits.xor in *. simpl.
  rewrite vect_to_list_cons. f_equal. rewrite <- IHsz.
  reflexivity.
Qed.

Lemma iter_assoc_spec:
  forall {A:Type} (f: A -> A) n x, Nat.iter n f (f x) = f (Nat.iter n f x).
Proof.
  induction n; simpl; intros; eauto.
  rewrite IHn. auto.
Qed.

Lemma vect_dotimes_spec:
  forall {A:Type} (f: A -> A) n x, vect_dotimes f n x = Nat.iter n f x.
Proof.
  induction n; simpl; intros. auto.
  rewrite IHn, iter_assoc_spec. auto.
Qed.

Lemma vect_to_list_snoc:
  forall sz (v: bits sz) x,
  vect_to_list (vect_snoc x v) = vect_to_list v ++ [x].
Proof.
  induction sz; simpl; intros; eauto.
  rewrite vect_to_list_cons. f_equal.
  rewrite IHsz. reflexivity.
Qed.

Lemma lsr1:
  forall sz (v: bits sz), sz <> 0
  -> vect_to_list (Bits.lsr1 v) = tl (vect_to_list v) ++ [false].
Proof.
  unfold Bits.lsr1. intros. destr.
  rewrite vect_to_list_snoc.
  rewrite <- (vect_cons_hd_tl v) at 2.
  rewrite vect_to_list_cons. simpl. reflexivity.
Qed.

Lemma asr1:
  forall sz (v: bits sz), sz <> 0
  -> vect_to_list
    (Bits.asr1 v) = tl (vect_to_list v) ++ [last (vect_to_list v) false].
Proof.
  unfold Bits.asr1. intros. destr.
  rewrite vect_to_list_snoc. f_equal.
  rewrite msb_spec. auto.
Qed.

Lemma iter_list_vect:
  forall sz (v: bits sz) (f: list bool -> list bool) (g: bits sz -> bits sz),
  (forall x, f (vect_to_list x) = vect_to_list (g x))
  -> forall n,
  Nat.iter n f (vect_to_list v) = vect_to_list (vect_dotimes g n v).
Proof.
  intros. rewrite vect_dotimes_spec. induction n; simpl; intros; eauto.
  rewrite IHn. apply H.
Qed.

Lemma sel:
  forall sz (bs: bits sz) idx,
  vect_to_list (BitFuns.sel bs idx)
  = [List.nth (Bits.to_nat idx) (vect_to_list bs) false].
Proof.
  unfold BitFuns.sel. intros.
  destr.
  rewrite bits_nth_list. unfold Bits.to_index in Heqo.
  erewrite index_to_nat_of_nat. 2: eauto. reflexivity.
  unfold Bits.to_index in Heqo.
  rewrite nth_overflow. reflexivity.
  rewrite vect_to_list_length.
  apply index_of_nat_none_ge in Heqo. lia.
Qed.

Lemma slice_subst:
  forall sz (bs: bits sz) ofs w v,
  vect_to_list (Bits.slice_subst ofs w bs v) =
    let '(h, _) := take_drop' ofs (vect_to_list bs) in
    let '(_, t) := take_drop' (ofs + w) (vect_to_list bs) in
    fst (take_drop' sz (h ++ (vect_to_list v) ++ t)).
Proof.
  unfold Bits.slice_subst. intros.
  destr. destr.
  rewrite vect_to_list_eq_rect.
  rewrite vect_firstn_to_list. f_equal.
  rewrite ! vect_to_list_app.
  rewrite vect_firstn_to_list. f_equal.
  rewrite Heqp. simpl. f_equal.
  rewrite vect_skipn_to_list. rewrite Heqp0. reflexivity.
Qed.

Lemma slice:
  forall sz (bs: bits sz) ofs w,
  vect_to_list (Bits.slice ofs w bs) =
    let '(_, bs) := take_drop' ofs (vect_to_list bs) in
    let '(bs, _) := take_drop' w bs in
    (bs ++ List.repeat false (w - Nat.min w (sz - ofs))).
Proof.
  intros. unfold Bits.slice. rewrite vect_extend_end_firstn.
  unfold Bits.extend_end.
  rewrite vect_to_list_eq_rect.
  rewrite vect_to_list_app.
  rewrite vect_firstn_to_list.
  rewrite vect_skipn_to_list.
  rewrite <- repeat_bits_const.
  destr. simpl. reflexivity.
Qed.

Lemma vect_to_list_eq:
  forall sz1 sz2 (v1: bits sz1) (v2: bits sz2) (pf: sz1 = sz2),
  rew [fun x => bits x] pf in v1 = v2 -> vect_to_list v1 = vect_to_list v2.
Proof. intros. subst. rewrite vect_to_list_eq_rect. auto. Qed.

Lemma bits_map_rew:
  forall sz1 sz2 (v: bits sz1) f (pf: sz1 = sz2),
  Bits.map f (rew [Bits.bits] pf in v) = rew [Bits.bits] pf in (Bits.map f v).
Proof. intros. subst. simpl. auto. Qed.

Lemma cmp:
  forall sz (v1 v2: bits sz) c,
  vect_to_list (BitFuns.bitfun_of_predicate c v1 v2) = [c v1 v2].
Proof. unfold BitFuns.bitfun_of_predicate. simpl; intros. reflexivity. Qed.

Lemma lift_comparison_rew:
  forall
    {A} sz1 sz1' (pf: sz1 = sz1') (pf2: sz1 = sz1') (v1: bits sz1)
    (v2: bits sz1) (cast: forall sz, bits sz -> A) compare cmp,
  Bits.lift_comparison (cast sz1') compare cmp (rew [Bits.bits] pf in v1)
    (rew [Bits.bits] pf2 in v2)
  = Bits.lift_comparison (cast sz1) compare cmp v1 v2.
Proof.
  intros. subst. simpl.
  rewrite (Eqdep_dec.UIP_refl_nat _ pf2). simpl. reflexivity.
Qed.

Fixpoint subst_field (n: nat) (v: val) (s: list val) : option (list val) :=
  match n, s with
  | _, [] => None
  | O, a::r => Some (v::r)
  | S n, a::r => let/opt s := subst_field n v r in Some (a::s)
  end.

Fixpoint val_of_struct_value'
  (fields : list (string * type)) (x : struct_denote fields) {struct fields}
: list val :=
  match fields as fields0 return (struct_denote fields0 -> list val) with
  | [] => fun _ : unit => []
  | p :: fields0 =>
    let (_, tau) as p0 return (snd p0 * struct_denote fields0 -> list val)
      := p in
    fun '(x0, xs) => val_of_value x0 :: val_of_struct_value' fields0 xs
  end x.

Lemma val_of_struct_value_rew:
  forall fields x, (
    fix val_of_struct_value
      (fields : list (string * type)) (x : struct_denote fields) {struct fields}
    : list val :=
      match fields as fields0 return (struct_denote fields0 -> list val) with
      | [] => fun _ : unit => []
      | p :: fields0 =>
        let (_, tau) as p0 return (snd p0 * struct_denote fields0 -> list val)
          := p in
        fun '(x0, xs) => val_of_value x0 :: val_of_struct_value fields0 xs
      end x
  ) fields x = val_of_struct_value' fields x.
Proof. induction fields; simpl; intros; eauto. Qed.

Lemma subst_field_ok':
  forall flds idx v s,
    subst_field (index_to_nat idx) (val_of_value v)
      (val_of_struct_value' flds s)
    = Some (val_of_struct_value' flds (BitFuns.subst_field flds s idx v)).
Proof.
  induction flds; simpl; intros; eauto. easy.
  repeat destr. simpl in *. auto.
  simpl in *. rewrite IHflds. simpl. auto.
Qed.

Lemma subst_field_ok:
  forall sig idx (s: struct_t sig) v,
  exists s', val_of_value s = Struct sig s'
  /\ exists s'',
    subst_field (index_to_nat idx) (val_of_value v) s' = Some s''
    /\ Struct sig s'' =
      val_of_value (tau:=struct_t sig) (
        BitFuns.subst_field (struct_fields sig) s idx v
      ).
Proof.
  intros.
  simpl in s.
  revert s idx v. simpl. intros.
  rewrite ! val_of_struct_value_rew.
  eexists; split; eauto.
  rewrite subst_field_ok'.
  eexists; split; eauto.
Qed.

Fixpoint subst_field_name
  (flds: list (string * type)) (n: string) (v: val) (s: list val)
: option (list val) :=
  match flds, s with
  | _, [] => None
  | [], _ => None
  | (name, _)::flds, a::r =>
    if eq_dec n name then Some (v::r)
    else let/opt s := subst_field_name flds n v r in Some (a::s)
  end.

Lemma subst_field_name_ok':
  forall flds x idx fname v s,
    PrimTypeInference.find_field
      {| struct_name := x; struct_fields := flds|} fname = Success idx
    -> subst_field_name
      flds fname (val_of_value v) (val_of_struct_value' flds s)
    = Some (val_of_struct_value' flds (BitFuns.subst_field flds s idx v)).
Proof.
  induction flds; simpl; intros; eauto. easy.
  destr_in v.
  - destruct a. destruct s. simpl in *.
    unfold PrimTypeInference.find_field in H. simpl in H.
    destr_in H.
    + subst. simpl in H. inv H. auto.
    + destr_in H; inv H.
  - destruct a, s.
    unfold PrimTypeInference.find_field in H. simpl in H.
    destr_in H.
    + subst. simpl in H. inv H.
    + destr_in H; inv H. simpl in *. erewrite IHflds with (x:=x). simpl. auto.
      unfold PrimTypeInference.find_field. simpl. rewrite Heqo. simpl. auto.
Qed.

Lemma subst_field_name_ok:
  forall sig fname idx (s: struct_t sig) v,
  PrimTypeInference.find_field sig fname = Success idx
  -> exists s', val_of_value s = Struct sig s'
    /\ exists s'',
      subst_field_name (struct_fields sig) fname (val_of_value v) s' = Some s''
    /\ Struct sig s''
      = val_of_value
        (tau:=struct_t sig) (BitFuns.subst_field (struct_fields sig) s idx v).
Proof.
  intros.
  simpl in s.
  revert s idx v H. simpl. intros.
  rewrite ! val_of_struct_value_rew.
  eexists; split; eauto.
  erewrite subst_field_name_ok'.
  eexists; split; eauto.
  instantiate(1:= struct_name sig).
  destruct sig. eauto.
Qed.

Lemma vect_replace_to_list:
  forall {A: Type} sz (v: vect A sz) l1 (a: A) l2 x idx,
  vect_to_list v = l1 ++ a :: l2 -> List.length l1 = index_to_nat idx
  -> vect_to_list (vect_replace v idx x) = l1 ++ x :: l2.
Proof.
  induction sz; simpl; intros; eauto. easy.
  destr.
  - destruct l1; simpl in *; try lia. subst.
    rewrite vect_to_list_cons. f_equal.
    destruct v; simpl in *.
    unfold vect_to_list in H. simpl in H. inv H. reflexivity.
  - rewrite vect_to_list_cons. subst. simpl.
    destruct v; simpl in *.
    unfold vect_to_list in H. simpl in H. fold (@vect_to_list A) in H.
    destruct l1. simpl in *. lia. simpl in H. inv H.
    simpl. f_equal. simpl in H0. inv H0.
    eapply IHsz; eauto.
Qed.

Lemma take_drop_map:
  forall {A B: Type} (f: A -> B) n l l1 l2,
  take_drop n (map f l) = Some (l1, l2)
  -> exists l1' l2',
  take_drop n l = Some (l1', l2') /\ l1 = List.map f l1' /\ l2 = List.map f l2'.
Proof.
  induction n; simpl; intros; eauto.
  - inv H. exists [], l; repeat split; eauto.
  - destr_in H. inv H.
    destruct (take_drop n l0) eqn:?; try congruence. 2: inv H.
    destruct p; simpl in *. inv H.
    destr. simpl in *. congruence. simpl in *. inv Heql0.
    edestruct IHn as (l1' & l2' & EQ1 & EQ2 & EQ3). eauto.
    rewrite EQ1. simpl. (do 2 eexists); repeat split; eauto.
    subst; reflexivity.
Qed.

Fixpoint list_assoc {K V: Type} {eq: EqDec K} (l: list (K * V)) (k: K)
: option V :=
  match l with
  | [] => None
  | (k1,v1)::l => if eq_dec k k1 then Some v1 else list_assoc  l k
  end.

Fixpoint list_assoc_set
  {K V: Type} {eq: EqDec K} (l: list (K * V)) (k: K) (v: V)
: list (K * V) :=
  match l with
  | [] => [(k,v)]
  | (k1,v1)::l =>
    if eq_dec k k1 then (k1,v)::l else (k1,v1) :: list_assoc_set l k v
  end.

Fixpoint uvalue_of_struct_bits (fields: list (string * type)) (bs: list bool)
: option (list val) :=
  match fields with
  | [] => Some []
  | (nm, tau) :: fields =>
    let/opt2 b0, b1 := take_drop (List.length bs - type_sz tau) bs in
    let/opt tl := uvalue_of_struct_bits fields b0 in
    let/opt hd := uvalue_of_bits (tau:=tau) b1 in
    Some ( hd :: tl)
  end.

Fixpoint uvalue_of_list_bits {tau} (bs: list (list bool)) : option (list val) :=
  match bs with
  | [] => Some []
  | l :: bs =>
    let/opt hd0 := uvalue_of_bits (tau:=tau) l in
    let/opt tl0 := uvalue_of_list_bits (tau:=tau) bs in
    Some (hd0 :: tl0)
  end.

  Inductive wt_unop : PrimUntyped.ufn1 -> type -> type -> Prop :=
  | wt_unop_display_utf8 sg:
    array_type sg = bits_t 8
    -> wt_unop
       (PrimUntyped.UDisplay PrimUntyped.UDisplayUtf8) (array_t sg) unit_t
  | wt_unop_display_value opts tau:
    wt_unop (PrimUntyped.UDisplay (PrimUntyped.UDisplayValue opts)) tau unit_t
  | wt_unop_upack tau:
    wt_unop (PrimUntyped.UConv PrimUntyped.UPack) tau (bits_t (type_sz tau))
  | wt_unop_uunpack tau:
    wt_unop (PrimUntyped.UConv (PrimUntyped.UUnpack tau)) (bits_t (type_sz tau))
      tau
  | wt_unop_uignore tau:
    wt_unop (PrimUntyped.UConv PrimUntyped.UIgnore) tau unit_t
  | wt_unop_uid tau s:
    wt_unop (PrimUntyped.UConv (PrimUntyped.UId s)) tau tau
  | wt_unop_unot sz:
    wt_unop (PrimUntyped.UBits1 PrimUntyped.UNot) (bits_t sz) (bits_t sz)
  | wt_unop_usext sz width:
    wt_unop (PrimUntyped.UBits1 (PrimUntyped.USExt width)) (bits_t sz)
      (bits_t (Nat.max sz width))
  | wt_unop_uzextl sz width:
    wt_unop (PrimUntyped.UBits1 (PrimUntyped.UZExtL width)) (bits_t sz)
      (bits_t (Nat.max sz width))
  | wt_unop_uzextr sz width:
    wt_unop (PrimUntyped.UBits1 (PrimUntyped.UZExtR width)) (bits_t sz)
      (bits_t (Nat.max sz width))
  | wt_unop_urepeat sz times:
    wt_unop (PrimUntyped.UBits1 (PrimUntyped.URepeat times)) (bits_t sz)
      (bits_t (times * sz))
  | wt_unop_uslice sz ofs width:
    wt_unop (PrimUntyped.UBits1 (PrimUntyped.USlice ofs width)) (bits_t sz)
      (bits_t width)
  | wt_unop_ugetfield sg name idx:
    PrimTypeInference.find_field sg name = Success idx
    -> wt_unop (PrimUntyped.UStruct1 (PrimUntyped.UGetField name)) (struct_t sg)
       (field_type sg idx)
  | wt_unop_ugetfieldbits sg name idx:
    PrimTypeInference.find_field sg name = Success idx
    -> wt_unop (PrimUntyped.UStruct1 (PrimUntyped.UGetFieldBits sg name))
       (struct_bits_t sg) (field_bits_t sg idx)
  | wt_unop_ugetelement sg idx idx0:
    PrimTypeInference.check_index sg idx = Success idx0
    -> wt_unop (PrimUntyped.UArray1 (PrimUntyped.UGetElement idx)) (array_t sg)
       (array_type sg)
  | wt_unop_ugetelementbits sg idx idx0:
    PrimTypeInference.check_index sg idx = Success idx0
    -> wt_unop (PrimUntyped.UArray1 (PrimUntyped.UGetElementBits sg idx))
       (bits_t (array_sz sg)) (bits_t (element_sz sg)).

  Inductive wt_binop : PrimUntyped.ufn2 -> type -> type -> type -> Prop :=
  | wt_binop_eq neg tau: wt_binop (PrimUntyped.UEq neg) tau tau (bits_t 1)
  | wt_binop_and sz:
    wt_binop (PrimUntyped.UBits2 PrimUntyped.UAnd) (bits_t sz) (bits_t sz)
      (bits_t sz)
  | wt_binop_or sz:
    wt_binop (PrimUntyped.UBits2 PrimUntyped.UOr) (bits_t sz) (bits_t sz)
      (bits_t sz)
  | wt_binop_xor sz:
    wt_binop (PrimUntyped.UBits2 PrimUntyped.UXor) (bits_t sz) (bits_t sz)
      (bits_t sz)
  | wt_binop_lsl sz sh_sz:
    wt_binop (PrimUntyped.UBits2 PrimUntyped.ULsl) (bits_t sz) (bits_t sh_sz)
      (bits_t sz)
  | wt_binop_lsr sz sh_sz:
    wt_binop (PrimUntyped.UBits2 PrimUntyped.ULsr) (bits_t sz) (bits_t sh_sz)
      (bits_t sz)
  | wt_binop_asr sz sh_sz:
    wt_binop (PrimUntyped.UBits2 PrimUntyped.UAsr) (bits_t sz) (bits_t sh_sz)
      (bits_t sz)
  | wt_binop_concat sz1 sz2:
    wt_binop (PrimUntyped.UBits2 PrimUntyped.UConcat) (bits_t sz1) (bits_t sz2)
      (bits_t (sz1 + sz2))
  | wt_binop_sel sz:
    wt_binop (PrimUntyped.UBits2 PrimUntyped.USel) (bits_t sz)
      (bits_t (log2 sz)) (bits_t 1)
  | wt_binop_slice_subst sz ofs w:
    wt_binop (PrimUntyped.UBits2 (PrimUntyped.USliceSubst ofs w)) (bits_t sz)
      (bits_t w) (bits_t sz)
  | wt_binop_indexedslice sz w:
    wt_binop (PrimUntyped.UBits2 (PrimUntyped.UIndexedSlice w)) (bits_t sz)
      (bits_t (log2 sz)) (bits_t w)
  | wt_binop_plus sz:
    wt_binop (PrimUntyped.UBits2 PrimUntyped.UPlus) (bits_t sz) (bits_t sz)
      (bits_t sz)
  | wt_binop_minus sz:
    wt_binop (PrimUntyped.UBits2 PrimUntyped.UMinus) (bits_t sz) (bits_t sz)
      (bits_t sz)
  | wt_binop_mul sz1 sz2:
    wt_binop (PrimUntyped.UBits2 PrimUntyped.UMul) (bits_t sz1) (bits_t sz2)
      (bits_t (sz1 + sz2))
  | wt_binop_compare signed bc sz:
    wt_binop (PrimUntyped.UBits2 (PrimUntyped.UCompare signed bc)) (bits_t sz)
      (bits_t sz) (bits_t 1)
  | wt_binop_substfield name sg idx:
    PrimTypeInference.find_field sg name = Success idx
    -> wt_binop (PrimUntyped.UStruct2 (PrimUntyped.USubstField name))
       (struct_t sg) (field_type sg idx) (struct_t sg)
  | wt_binop_substfieldbits name sg idx:
    PrimTypeInference.find_field sg name = Success idx
    -> wt_binop (PrimUntyped.UStruct2 (PrimUntyped.USubstFieldBits sg name))
       (struct_bits_t sg) (field_bits_t sg idx) (struct_bits_t sg)
  | wt_binop_substelement sg idx idx0:
    PrimTypeInference.check_index sg idx = Success idx0
    -> wt_binop (PrimUntyped.UArray2 (PrimUntyped.USubstElement idx))
       (array_t sg) (array_type sg) (array_t sg)
  | wt_binop_substelementbits sg idx idx0:
    PrimTypeInference.check_index sg idx = Success idx0
    -> wt_binop (PrimUntyped.UArray2 (PrimUntyped.USubstElementBits sg idx))
       (bits_t (array_sz sg)) (bits_t (element_sz sg)) (bits_t (array_sz sg)).

  Definition ret_type_unop (ufn: PrimUntyped.ufn1) (tau: type) :=
    match ufn with
    | PrimUntyped.UConv PrimUntyped.UPack => bits_t (type_sz tau)
    | PrimUntyped.UConv (PrimUntyped.UUnpack tau0) => tau0
    | PrimUntyped.UConv (PrimUntyped.UId _) => tau
    | PrimUntyped.UBits1 PrimUntyped.UNot => tau
    | PrimUntyped.UBits1 (PrimUntyped.USExt width)
    | PrimUntyped.UBits1 (PrimUntyped.UZExtL width)
    | PrimUntyped.UBits1 (PrimUntyped.UZExtR width) =>
      match tau with
      | bits_t sz => bits_t (Nat.max sz width)
      | _ => unit_t
      end
    | PrimUntyped.UBits1 (PrimUntyped.URepeat times) =>
      match tau with
      | bits_t sz => bits_t (times * sz)
      | _ => unit_t
      end
    | PrimUntyped.UBits1 (PrimUntyped.USlice _ width) => bits_t width
    | PrimUntyped.UStruct1 (PrimUntyped.UGetField name) =>
      match tau with
      | struct_t sg =>
        match PrimTypeInference.find_field sg name with
        | Success idx => field_type sg idx
        | Failure _ => unit_t
        end
      | _ => unit_t
      end
    | PrimUntyped.UStruct1 (PrimUntyped.UGetFieldBits sg name) =>
      match PrimTypeInference.find_field sg name with
      | Success idx => field_bits_t sg idx
      | Failure _ => unit_t
      end
    | PrimUntyped.UArray1 (PrimUntyped.UGetElement _) =>
      match tau with
      | array_t sg => array_type sg
      | _ => unit_t
      end
    | PrimUntyped.UArray1 (PrimUntyped.UGetElementBits sg _) =>
      bits_t (element_sz sg)
    | _ => unit_t
    end.

  Definition ret_type_binop (ufn: PrimUntyped.ufn2) (tau1 tau2: type) : type :=
    match ufn with
    | (PrimUntyped.UEq _)
    | (PrimUntyped.UBits2 PrimUntyped.USel)
    | (PrimUntyped.UBits2 (PrimUntyped.UCompare _ _))
    => bits_t 1
    | (PrimUntyped.UBits2 PrimUntyped.UAnd)
    | (PrimUntyped.UBits2 PrimUntyped.UOr)
    | (PrimUntyped.UBits2 PrimUntyped.UXor)
    | (PrimUntyped.UBits2 PrimUntyped.ULsl)
    | (PrimUntyped.UBits2 PrimUntyped.ULsr)
    | (PrimUntyped.UBits2 PrimUntyped.UAsr)
    | (PrimUntyped.UBits2 (PrimUntyped.USliceSubst _ _))
    | (PrimUntyped.UBits2 PrimUntyped.UPlus)
    | (PrimUntyped.UBits2 PrimUntyped.UMinus)
    => tau1
    | (PrimUntyped.UBits2 (PrimUntyped.UIndexedSlice w))
    => bits_t w
    | (PrimUntyped.UBits2 PrimUntyped.UConcat)
    | (PrimUntyped.UBits2 PrimUntyped.UMul)
    =>
      match tau1, tau2 with
      | bits_t s1, bits_t s2 => bits_t (s1 + s2)
      | _, _ => bits_t 0
      end
    | (PrimUntyped.UStruct2 (PrimUntyped.USubstField name)) => tau1
    | (PrimUntyped.UStruct2 (PrimUntyped.USubstFieldBits sg name)) => tau1
    | (PrimUntyped.UArray2 (PrimUntyped.USubstElement idx)) => tau1
    | (PrimUntyped.UArray2 (PrimUntyped.USubstElementBits sg idx)) => tau1
    end.

  Lemma wt_unop_type_unop_ret:
    forall u t1 t2, wt_unop u t1 t2 -> t2 = ret_type_unop u t1.
  Proof.
    induction 1; simpl; intros; eauto.
    rewrite H; auto.
    rewrite H; auto.
  Qed.

  Lemma wt_binop_type_binop_ret:
    forall u t1 t2 t3, wt_binop u t1 t2 t3 -> t3 = ret_type_binop u t1 t2.
  Proof. induction 1; simpl; intros; eauto. Qed.

Section WT.
  Variables pos_t fn_name_t: Type.
  Variable var_t: Type.
  Context {eq_dec_var_t: EqDec var_t}.

  Inductive wt_var : tsig var_t -> var_t -> type -> Prop :=
  | wt_var_intro: forall sig v t tm,
    assoc v sig = Some tm -> projT1 tm = t -> wt_var sig v t.

  Inductive wt_list
    {ext_fn_t: Type} {reg_t: Type}
    (P:
      tsig var_t -> uaction pos_t var_t fn_name_t reg_t ext_fn_t -> type -> Prop
    )
  : tsig var_t -> list (var_t * uaction pos_t var_t fn_name_t reg_t ext_fn_t)
    -> list type -> Prop
  :=
  | wt_list_nil sig: wt_list P sig [] []
  | wt_list_cons sig v a l t lt:
    P sig a t
    -> wt_list P ((v,t)::sig) l lt
    -> wt_list P sig ((v,a)::l) (t::lt).

  Inductive sig_of_bindings {A:Type}
  : list (var_t * A) -> list type -> tsig var_t -> Prop :=
  | sig_of_bindings_nil: sig_of_bindings [] [] []
  | sig_of_bindings_cons: forall bindings bind_taus sig v x t,
    sig_of_bindings bindings bind_taus sig
    -> sig_of_bindings ((x,v)::bindings) (t::bind_taus) ((x,t)::sig).

  Inductive wt_action
    {ext_fn_t: Type} {reg_t: Type} {R: reg_t -> type}
    {Sigma: ext_fn_t -> ExternalSignature}
  : tsig var_t -> uaction pos_t var_t fn_name_t reg_t ext_fn_t -> type -> Prop
  :=
  | wt_action_fail: forall sig t, wt_action sig (UFail t) t
  | wt_action_var: forall sig var t,
    wt_var sig var t
    -> wt_action sig (UVar var) t
  | wt_action_const: forall sig tau cst,
    wt_action sig (@UConst _ _ _ _ _ tau cst) tau
  | wt_action_assign: forall sig k a t,
    wt_action sig a t
    -> wt_var sig k t
    -> wt_action sig (UAssign k a) (bits_t 0)
  | wt_action_seq: forall sig a1 a2 t2,
    wt_action sig a1 unit_t
    -> wt_action sig a2 t2
    -> wt_action sig (USeq a1 a2) t2
  | wt_action_bind: forall sig k a1 a2 t1 t2,
    wt_action sig a1 t1
    -> wt_action ((k,t1)::sig) a2 t2
    -> wt_action sig (UBind k a1 a2) t2
  | wt_action_if: forall sig cond athen aelse t,
    wt_action sig cond (bits_t 1)
    -> wt_action sig athen t
    -> wt_action sig aelse t
    -> wt_action sig (UIf cond athen aelse) t
  | wt_action_read: forall sig prt idx, wt_action sig (URead prt idx) (R idx)
  | wt_action_write: forall sig prt idx v,
    wt_action sig v (R idx)
    -> wt_action sig (UWrite prt idx v) unit_t
  | wt_action_unop: forall sig ufn arg targ tret,
    wt_unop ufn targ tret
    -> wt_action sig arg targ
    -> wt_action sig (UUnop ufn arg) tret
  | wt_action_binop: forall sig ufn arg1 arg2 targ1 targ2 tret,
    wt_binop ufn targ1 targ2 tret
    -> wt_action sig arg1 targ1
    -> wt_action sig arg2 targ2
    -> wt_action sig (UBinop ufn arg1 arg2) tret
  | wt_action_uexternalcall: forall sig fn a,
    wt_action sig a (arg1Sig (Sigma fn))
    -> wt_action sig (UExternalCall fn a) (retSig (Sigma fn))
  | wt_action_internal_call: forall sig fn args,
    Forall2 (wt_action sig) args (map snd (int_argspec fn))
    -> wt_action (List.rev fn.(int_argspec)) (int_body fn) (int_retSig fn)
    -> wt_action sig (UInternalCall fn args) (fn.(int_retSig))
  | wt_action_uapos: forall sig tau pos e,
    wt_action sig e tau
    -> wt_action sig (UAPos pos e) tau
  | wt_action_uskip: forall sig, wt_action sig (USugar USkip) (bits_t 0)
  | wt_action_uconstbits: forall sig {sz} (arg : bits_t sz),
    wt_action sig (USugar (UConstBits arg)) (bits_t sz)
  | wt_action_uconststring: forall sig (s : string),
    wt_action sig (USugar (UConstString s))
      (array_t {| array_type := bits_t 8; array_len := String.length s; |})
  | wt_action_uconstenum: forall sig sg name r,
    vect_index name sg.(enum_members) = Some r
    -> wt_action sig (USugar (UConstEnum sg name)) (enum_t sg)
  | wt_action_uprogn: forall sig aa,
    (forall a, In a aa -> wt_action sig a unit_t)
    -> wt_action sig (USugar (UProgn aa)) (bits_t 0)
  | wt_action_ulet:
    forall sig sig' bindings body (bind_taus: list type) body_tau,
    wt_list wt_action sig bindings bind_taus
    -> sig_of_bindings bindings bind_taus sig'
    -> wt_action (rev sig' ++ sig) body body_tau
    -> wt_action sig (USugar (ULet bindings body)) body_tau
  | wt_action_uwhen: forall sig cond body,
    wt_action sig cond (bits_t 1)
    -> wt_action sig body unit_t
    -> (* XXX See related FIXME comment in Desugaring.v *)
    wt_action sig (USugar (UWhen cond body)) unit_t
  | wt_action_uswitch: forall sig var default branches tau tau',
    wt_action sig var tau
    -> wt_action sig default tau'
    -> Forall (
      fun b => wt_action sig (fst b) tau /\ wt_action sig (snd b) tau'
    ) branches
    -> wt_action sig (USugar (USwitch var default branches)) tau'
  | wt_action_ustructinit: forall sig (sg: struct_sig) fields,
    Forall (
      fun f => exists idx,
        PrimTypeInference.find_field sg (fst f) = Success idx
        /\ wt_action sig (snd f) (snd (List_nth (struct_fields sg) idx))
    ) fields
    -> wt_action sig (USugar (UStructInit sg fields)) (struct_t sg)
  | wt_action_uarrayinit: forall sig tau elements,
    Forall (fun e => wt_action sig e tau) elements
    -> wt_action sig (USugar (UArrayInit tau elements)) (
         array_t {| array_type := tau; array_len := List.length elements |})
  | wt_action_ucallmodule:
    forall
      sig {module_reg_t module_ext_fn_t : Type}
      `{finite_reg: FiniteType module_reg_t} (fR: module_reg_t -> reg_t)
      (fSigma: @Lift module_ext_fn_t ext_fn_t)
      (fn: InternalFunction var_t fn_name_t (
        @uaction pos_t var_t fn_name_t module_reg_t module_ext_fn_t
      ))
      (args: list (uaction pos_t var_t fn_name_t reg_t ext_fn_t)),
    Forall2 (wt_action sig) args (map snd (int_argspec fn))
    -> @wt_action
      module_ext_fn_t module_reg_t (fun x => R (fR x))
      (fun x => Sigma (fSigma x)) (List.rev fn.(int_argspec)) (int_body fn)
      (int_retSig fn)
    -> wt_action sig (USugar (UCallModule fR fSigma fn args)) (fn.(int_retSig)).

  Inductive wt_daction
    {ext_fn_t: Type} {reg_t: Type} {R: reg_t -> type}
    {Sigma: ext_fn_t -> ExternalSignature}
  : tsig var_t -> @daction pos_t var_t fn_name_t reg_t ext_fn_t -> type -> Prop
  :=
  | wt_daction_fail: forall sig t, wt_daction sig (DFail t) t
  | wt_daction_var: forall sig var t,
    wt_var sig var t -> wt_daction sig (DVar var) t
  | wt_daction_const: forall sig v tau,
    wt_val tau v
    -> wt_daction sig (DConst tau v) tau
  | wt_daction_assign: forall sig k a t,
    wt_daction sig a t
    -> wt_var sig k t
    -> wt_daction sig (DAssign k a) (bits_t 0)
  | wt_daction_seq: forall sig a1 a2 t2,
    wt_daction sig a1 unit_t
    -> wt_daction sig a2 t2
    -> wt_daction sig (DSeq a1 a2) t2
  | wt_daction_bind: forall sig k a1 a2 t1 t2,
    wt_daction sig a1 t1
    -> wt_daction ((k,t1)::sig) a2 t2
    -> wt_daction sig (DBind k a1 a2) t2
  | wt_daction_if: forall sig cond athen aelse t,
    wt_daction sig cond (bits_t 1)
    -> wt_daction sig athen t
    -> wt_daction sig aelse t
    -> wt_daction sig (DIf cond athen aelse) t
  | wt_daction_read: forall sig prt idx, wt_daction sig (DRead prt idx) (R idx)
  | wt_daction_write: forall sig prt idx v,
    wt_daction sig v (R idx)
    -> wt_daction sig (DWrite prt idx v) unit_t
  | wt_daction_unop: forall sig ufn arg targ tret,
    wt_unop ufn targ tret
    -> wt_daction sig arg targ
    -> wt_daction sig (DUnop ufn arg) tret
  | wt_daction_binop: forall sig ufn arg1 arg2 targ1 targ2 tret,
    wt_binop ufn targ1 targ2 tret
    -> wt_daction sig arg1 targ1
    -> wt_daction sig arg2 targ2
    -> wt_daction sig (DBinop ufn arg1 arg2) tret
  | wt_daction_uexternalcall: forall sig fn a,
    wt_daction sig a (arg1Sig (Sigma fn))
    -> wt_daction sig (DExternalCall fn a) (retSig (Sigma fn))
  | wt_daction_internal_call: forall sig fn args,
    Forall2 (wt_daction sig) args (map snd (int_argspec fn))
    -> wt_daction (List.rev fn.(int_argspec)) (int_body fn) (int_retSig fn)
    -> wt_daction sig (DInternalCall fn args) (fn.(int_retSig))
  | wt_daction_uapos: forall sig tau pos e,
    wt_daction sig e tau
    -> wt_daction sig (DAPos pos e) tau.
End WT.
