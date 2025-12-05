(*! Properties that are useful to reason about untyped semantics !*)
(* TODO: move this to the kôika repo *)
Require Export Koika.Utils.Common.
Require Import Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.KoikaForm.Untyped.UntypedLogs.

Require Import Coq.Lists.List.
Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Program.Equality.

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Section Logs.
    Context {V: Type}.

    Context {reg_t: Type}.
    Context {REnv: Env reg_t}.
    Definition R : reg_t -> Type := fun _ => V.

    Notation Log := (@_ULog V reg_t REnv).

    Lemma log_find_empty {T} idx (f: @LogEntry (R idx) -> option T):
        log_find (log_empty: Log) idx f = None.
    Proof.
        unfold log_find, log_empty; intros; rewrite getenv_create; reflexivity.
    Qed.

    Lemma log_app_assoc : forall (l1 l2 l3: Log),
        log_app (log_app l1 l2) l3 = log_app l1 (log_app l2 l3).
    Proof.
        unfold log_app, map2; intros.
        apply create_funext. intros.
        rewrite !getenv_create.
        rewrite app_assoc.
        reflexivity.
    Qed.

    Lemma log_app_empty_l : forall (l: Log),
        log_app log_empty l = l.
    Proof.
        intros.
        apply equiv_eq.
        unfold equiv, log_app, map2, log_empty; intros.
        rewrite !getenv_create, app_nil_l.
        reflexivity.
    Qed.

    Lemma log_app_empty_r : forall (l: Log),
        log_app l log_empty = l.
    Proof.
        intros.
        apply equiv_eq.
        unfold equiv, log_app, map2, log_empty; intros.
        rewrite !getenv_create, app_nil_r.
        reflexivity.
    Qed.

    Lemma log_existsb_empty:
        forall p idx,
        log_existsb (log_empty: Log) idx p = false.
    Proof.
        unfold log_existsb, log_empty; intros.
        rewrite getenv_create.
        reflexivity.
    Qed.
End Logs.

Section FiniteType.

    Context {T: Type}.
    Context {fin_t: FiniteType T}.

    Lemma finite_index_bounded (x: T):
        (finite_index x < List.length (finite_elements))%nat.
    Proof.
        generalize (finite_surjective x). intros H.
        apply nth_error_Some. (* hammer. *) sfirstorder.
    Qed.

    Lemma finite_elements_is_finfun_listing:
        FinFun.Listing finite_elements.
    Proof.
        unfold FinFun.Listing.
        split.
        - apply finite_nodup.
        - unfold FinFun.Full.
          intros x.
          generalize (finite_surjective x). intros H.
          apply (nth_error_In finite_elements (finite_index x)). (* hammer. *) sfirstorder.
    Qed.

    Lemma finite_index_finfun_inj: 
        FinFun.Injective finite_index.
    Proof.
        unfold FinFun.Injective. exact finite_index_injective.
    Qed.

    Lemma finite_index_plus_constant_r_inj:
        forall c x y,
        finite_index x + c = finite_index y + c ->
        x = y.
    Proof.
        intros. generalize (finite_index_injective x y). intros.
        apply Nat.add_cancel_r in H. (* hammer. *) sfirstorder.
    Qed.

    Lemma finite_index_plus_constant_l_inj:
        forall c x y,
        c + finite_index x = c + finite_index y ->
        x = y.
    Proof.
        intros. generalize (finite_index_injective x y). intros.
        apply Nat.add_cancel_l in H. (* hammer. *) sfirstorder.
    Qed.

End FiniteType.

Section Schedule.

    Context {pos_t rule_name_t: Type}.
    Context {rule_name_t_eq_dec: EqDec rule_name_t}.
    Definition sched := @scheduler pos_t rule_name_t.

    Fixpoint scheduler_has_rule (scheduler : sched) (r_target : rule_name_t) : Prop :=
        match scheduler with
        | Done => False
        | Cons r s => if eq_dec r r_target then True else scheduler_has_rule s r_target
        | Try r s1 s2 => if eq_dec r r_target then True else (scheduler_has_rule s1 r_target \/ scheduler_has_rule s2 r_target)
        | SPos p s => scheduler_has_rule s r_target
        end.
    
    Lemma scheduler_has_rule_dec:
        forall (s: sched) (r: rule_name_t),
        {scheduler_has_rule s r} + {~ scheduler_has_rule s r}.
    Proof.
        induction s; intros; simpl.
        - right; intros H; inversion H.
        - destruct (eq_dec r r0).
            + left; auto.
            + specialize (IHs r0). auto.
        - destruct (eq_dec r r0).
            + left; auto.
            + specialize (IHs1 r0). specialize (IHs2 r0).
                destruct IHs1; destruct IHs2.
                * left; auto.
                * left; auto.
                * left; auto.
                * right. intros [H1 | H2]; auto.
        - specialize (IHs r). auto.
    Qed.

    Lemma scheduler_has_not_rule_inductive:
        forall (s: sched) (r: rule_name_t),
        ~ scheduler_has_rule s r ->
            match s with
            | Done => True
            | Cons r0 s' => if eq_dec r0 r then False else ~ scheduler_has_rule s' r
            | Try r0 s1 s2 => if eq_dec r0 r then False else (~ scheduler_has_rule s1 r /\ ~ scheduler_has_rule s2 r)
            | SPos p s' => ~ scheduler_has_rule s' r
            end.
    Proof.
        induction s; intros; simpl in *.
        - auto.
        - destruct (eq_dec r r0).
            + exfalso; apply H. (* hammer. *) sfirstorder.
            + (* hammer. *) sfirstorder.
        - destruct (eq_dec r r0).
            + exfalso; apply H. (* hammer. *) sfirstorder.
            + (* hammer. *) sfirstorder.
        - (* hammer. *) sfirstorder.
    Qed.

End Schedule.

Section Environments.

    Lemma getenv_ccreate:
         forall {K : Type} {FT: FiniteType K}
            {V : esig K}
            (fn : forall k : K, V k)
            (k : K),
            ContextEnv.(getenv) (ccreate finite_elements (fun k _ => fn k)) k = fn k.
    Proof.
        intros. unfold getenv. cbn.
        rewrite cassoc_ccreate. reflexivity.
    Qed.

    Lemma get_put_eq:
        forall {K : Type} {FT: FiniteType K} {V : esig K} (ev : env_t ContextEnv V) (k : K) (v : V k),
            ContextEnv.(getenv) (ContextEnv.(putenv) ev k v) k = v.
    Proof.
        intros. rewrite get_put_eq. reflexivity.
    Qed.

    Lemma cassoc_put_eq:
        forall {K : Type} {FT: FiniteType K} {V : esig K} (ev : env_t ContextEnv V) (k : K) (v : V k),
            cassoc (finite_member k) (ContextEnv.(putenv) ev k v) = v.
    Proof.
        intros. generalize (get_put_eq ev k v). intros H.
        unfold getenv in H. cbn in *. rewrite H. reflexivity.
    Qed.

    Lemma get_put_neq:
        forall {K : Type} {FT: FiniteType K} {V : esig K} (ev : env_t ContextEnv V) (k k' : K) (v : V k),
            k <> k' ->
            ContextEnv.(getenv) (ContextEnv.(putenv) ev k v) k' = ContextEnv.(getenv) ev k'.
    Proof.
        intros. rewrite get_put_neq. reflexivity. sfirstorder.
    Qed.

    Lemma cassoc_put_neq:
        forall {K : Type} {FT: FiniteType K} {V : esig K} (ev : env_t ContextEnv V) (k k' : K) (v : V k),
            k <> k' ->
            cassoc (finite_member k') (ContextEnv.(putenv) ev k v) = cassoc (finite_member k') ev.
    Proof.
        intros. generalize (get_put_neq ev k k' v H). intros Hget.
        unfold getenv in Hget. cbn in *. rewrite Hget. reflexivity.
    Qed.

End Environments.

Section BitsToLists.
    
    Lemma bits_to_list_assoc_fallback_cons:
        forall {K V: Type} {eq: EqDec K} (l: list (K * V)) (k: K) x k1 v1,
        BitsToLists.list_assoc l k = Some x -> 
            BitsToLists.list_assoc ((k1, v1) :: l) k <> None.
    Proof.
        intros. unfold not. intros.  unfold BitsToLists.list_assoc in *. 
        destruct (eq_dec k k1).
        - inversion H0.
        - hauto.
    Qed.
    
    Lemma bits_to_list_assoc_fallback_app:
        forall {K V: Type} {eq: EqDec K} (l: list (K * V)) (k: K) x a,
        BitsToLists.list_assoc l k = Some x -> 
            BitsToLists.list_assoc (a ++ l) k <> None.
    Proof.
        intros. unfold not. intros. unfold BitsToLists.list_assoc in *.
        generalize dependent H.
        induction a; intros. 
        { rewrite app_nil_l in H0. (* hammer. *) timeout 10 sfirstorder. }
        rewrite <- app_comm_cons in H0.
        cbn in H0. destruct a as [k1 v1].
        destruct (eq_dec k k1).
        - inversion H0.
        - hauto.
    Qed.

    Lemma bits_to_list_assoc_app:
        forall {K V: Type} {eq: EqDec K} (l: list (K * V)) (k: K) x a,
        BitsToLists.list_assoc l k = Some x -> 
            BitsToLists.list_assoc (l ++ a) k = Some x.
    Proof.
        intros. generalize dependent H.
        induction l; intros; cbn in *; try congruence.
        destruct a0 as [k1 v1]. destruct (eq_dec k k1).
        - subst. exact H.
        - apply IHl. exact H.
    Qed.

    Lemma bits_to_list_assoc_app_not_in:
        forall {K V: Type} {eq: EqDec K} (l: list (K * V)) (k: K) x a,
        ~ In k (map fst a) ->
        BitsToLists.list_assoc l k = Some x -> 
            BitsToLists.list_assoc (a ++ l) k = Some x.
    Proof.
        intros. generalize dependent H0.
        induction a; intros; cbn in *.
        - exact H0.
        - destruct a as [k1 v1]. destruct (eq_dec k k1).
            + subst. contradict H. left. reflexivity.
            + apply IHa; auto.
    Qed.

    Lemma bits_to_list_assoc_app_not_in2:
        forall {K V: Type} {eq: EqDec K} (l: list (K * V)) (k: K) x a,
        ~ In k (map fst a) ->
        BitsToLists.list_assoc (a ++ l) k = Some x -> 
            BitsToLists.list_assoc l k = Some x.
    Proof.
        intros. generalize dependent H0.
        induction a; intros; cbn in *.
        - exact H0.
        - destruct a as [k1 v1]. destruct (eq_dec k k1).
            + subst. contradict H. left. reflexivity.
            + apply IHa; auto.
    Qed.

    Lemma bits_to_list_assoc_app_not_in3:
        forall {K V: Type} {eq: EqDec K} (l: list (K * V)) (k: K) a,
        ~ In k (map fst a) ->
        BitsToLists.list_assoc (a ++ l) k = BitsToLists.list_assoc l k.
    Proof.
        intros.
        induction a; intros; cbn in *.
        - reflexivity.
        - destruct a as [k1 v1]. destruct (eq_dec k k1).
            + subst. contradict H. left. reflexivity.
            + apply IHa; auto.
    Qed.

    Lemma bits_to_list_assoc_app_both_none:
        forall {K V: Type} {eq: EqDec K} (l: list (K * V)) (k: K) a,
        BitsToLists.list_assoc l k = None ->
        BitsToLists.list_assoc a k = None -> 
            BitsToLists.list_assoc (a ++ l) k = None.
    Proof.
        intros. generalize dependent H0.
        induction a; intros; cbn in *.
        - exact H.
        - destruct a as [k1 v1]. destruct (eq_dec k k1).
            + inversion H0.
            + apply IHa; auto.
    Qed.

    Lemma bits_to_list_assoc_app_both_none1:
        forall {K V: Type} {eq: EqDec K} (l: list (K * V)) (k: K) a,
        BitsToLists.list_assoc a k = None -> 
            BitsToLists.list_assoc (a ++ l) k = BitsToLists.list_assoc l k.
    Proof.
        intros. generalize dependent H.
        induction a; intros; cbn in *.
        - reflexivity.
        - destruct a as [k1 v1]. destruct (eq_dec k k1).
            + inversion H.
            + apply IHa; auto.
    Qed.

    Lemma bits_to_list_assoc_app_not_in_middle:
        forall {K V: Type} {eq: EqDec K} (l1 l2: list (K * V)) (k: K) a,
        ~ In k (map fst a) ->
        BitsToLists.list_assoc (l1 ++ a ++ l2) k = BitsToLists.list_assoc (l1 ++ l2) k.
    Proof.
        intros.
        induction a; intros; cbn in *.
        - reflexivity.
        - destruct a as [k1 v1]. destruct (eq_dec k k1).
          + subst. contradict H. left. reflexivity.
          + destruct (BitsToLists.list_assoc l1 k) eqn:Hassoc.
            * rewrite !bits_to_list_assoc_app with (x:=v) (1:=Hassoc). reflexivity.
            * rewrite !bits_to_list_assoc_app_both_none1 with (1:=Hassoc) in *. cbn. destruct (eq_dec k k1); try congruence.
              apply IHa. intro; apply H. right. exact H0.
    Qed.

    Lemma bits_of_list_vect_to_list:
        forall {n} (b: bits n),
            Bits.of_list (vect_to_list b) = rew [vect bool] (BitsToLists.len_to_list n b) in b.
    Proof.
        intros. apply vect_to_list_inj. rewrite BitsToLists.vect_to_list_of_list.
        rewrite vect_to_list_eq_rect. reflexivity.
    Qed. 
    
    Lemma vect_fold_left_of_zeros:
        forall n acc,
            vect_fold_left (fun (acc : list bool) (t : bool) => t :: acc) acc (Bits.zeroes n) = repeat false n ++ acc.
    Proof.
        intros. induction n; intros; simpl. reflexivity.
        rewrite IHn. simpl. reflexivity.
    Qed.

End BitsToLists.

Section ContextLogs.
    Context {V: Type}.

    Context {reg_t: Type}.
    Context {reg_t_finite : FiniteType reg_t}.

    Notation CEnv := (@ContextEnv reg_t reg_t_finite).
    Notation Log := (@_ULog V reg_t CEnv).

    Lemma log_existsb_context_concat:
        forall (logX logY : Log) (elemX : reg_t) (c : env_t ContextEnv (fun _ : reg_t => list (LogEntry V))) isX,
            log_existsb logX elemX isX = log_existsb logY elemX isX ->
            @log_existsb V reg_t CEnv (ccreate finite_elements (fun (k : reg_t) (_ : member k finite_elements) => c.[k] ++ logX.[k])) elemX isX =
            @log_existsb V reg_t CEnv (ccreate finite_elements (fun (k : reg_t) (_ : member k finite_elements) => c.[k] ++ logY.[k])) elemX isX.
    Proof.
        intros. unfold log_existsb in *. rewrite !getenv_ccreate.
        rewrite !existsb_app. rewrite H. reflexivity.
    Qed.

    Lemma cassoc_log_cons_neq:
        forall (log: Log) (idx idx': reg_t) (le: LogEntry V),
            idx <> idx' ->
            cassoc (finite_member idx') (log_cons idx le log) = cassoc (finite_member idx') log.
    Proof.
        intros. unfold log_cons. rewrite cassoc_put_neq. 2: exact H. reflexivity.
    Qed.

    Lemma cassoc_log_cons_eq:
        forall (log: Log) (idx: reg_t) (le: LogEntry V),
            cassoc (finite_member idx) (log_cons idx le log) = le :: cassoc (finite_member idx) log.
    Proof.
        intros. unfold log_cons. rewrite cassoc_put_eq. reflexivity.
    Qed.

    Lemma cassoc_log_app:
        forall (log1 log2: Log) (idx: reg_t),
            cassoc (finite_member idx) (log_app log1 log2) = cassoc (finite_member idx) log1 ++ cassoc (finite_member idx) log2.
    Proof.
        intros. unfold log_app. simpl. rewrite cassoc_ccreate. unfold getenv. cbn. reflexivity.
    Qed.

End ContextLogs.

Section Datatypes.

    Lemma datatypes_length_vect_fold_left_of_bits:
        forall {n} (v : bits n),
            Datatypes.length (vect_fold_left (fun (acc : list bool) (t : bool) => t :: acc) [] v) = n.
    Proof.
        intros. unfold vect_fold_left.
        induction n; intros; simpl. reflexivity.
        rewrite IHn. simpl. lia.
    Qed.

    Lemma datatypes_length_firstn_vect_fold_left_of_bits':
        forall {n} (v : bits n),
            Datatypes.length (firstn n (vect_fold_left (fun (acc : list bool) (t : bool) => t :: acc) [] v)) = n.
    Proof.
        intros. unfold vect_fold_left.
        induction n; intros; simpl. reflexivity.
        rewrite IHn. simpl. lia.
    Qed.

    Lemma datatypes_length_firstn_vect_fold_left_of_bits:
        forall {n} x (v : bits n),
            x < n ->
            Datatypes.length (firstn x (vect_fold_left (fun (acc : list bool) (t : bool) => t :: acc) [] v)) = x.
    Proof.
        unfold vect_fold_left.
        induction n; intros; simpl. lia.
        destruct x; simpl. reflexivity.
        rewrite IHn; lia.
    Qed.

    Lemma repeat_nil:
        forall {A: Type} n (a: A),
        n = 0%nat ->
        repeat a n = [].
    Proof.
        intros. subst. reflexivity.
    Qed.

    Lemma datatypes_length_bitwise:
        forall l1 l2 f,
            Datatypes.length (BitsToLists.bitwise f l1 l2) = Nat.max (Datatypes.length l1) (Datatypes.length l2).
    Proof.
        intros. 
        generalize dependent l2.
        induction l1; intros.
        - cbn. destruct l2; simpl. reflexivity. 
          rewrite map_length. reflexivity.
        - cbn. destruct l2.
          + cbn. rewrite map_length. reflexivity.
          + cbn. rewrite IHl1. reflexivity.
    Qed.

End Datatypes.

Section Lists.

    Lemma in_filter_means_in_filter_cons:
        forall {A: Type} (f: A -> bool) (l: list A) a b,
        In a (filter f l) ->
        In a (filter f (b :: l)).
    Proof.
        intros. destruct (f b) eqn:Hfb; cbn; rewrite Hfb.
        - right. exact H.
        - exact H.
    Qed.

End Lists.

Section Bits.

    Lemma bits_single_is_neg_beq_dec:
        forall x, beq_dec x Ob~0 = negb (Bits.single x).
    Proof.
        intros. unfold Bits.single, beq_dec.
        destruct x. destruct vtl. destruct vhd; cbn; auto.
    Qed. 

End Bits.

Section Helper.

    Lemma tl_skipn:
        forall {T} (l: list T) n,
        tl (List.skipn n l) = List.skipn (S n) l.
    Proof.
        intros.
        generalize dependent l.
        induction n; intros; simpl.
        - reflexivity.
        - destruct l; simpl in *; try reflexivity. apply IHn.
    Qed.

    Lemma pair_inj':
        forall {A B: Type} (p1 p2: A * B),
        fst p1 = fst p2 ->
        snd p1 = snd p2 ->
        p1 = p2.
    Proof.
        intros. destruct p1. destruct p2. simpl in *.
        subst. reflexivity.
    Qed.

    Lemma tf_h_match_skipn_cons:
        forall {T1 T2 T3} (X1 X2: option (T1 * T2 * list T3)) n1 n2,
        n2 = S n1 ->
        X1 = X2 ->
        match
            match X1 with
            | Some (l, v, G) => Some (l, v, List.skipn n1 G)
            | None => None
            end
        with
        | Some (l, v, G) => Some (l, v, tl G)
        | None => None
        end = match X2 with
        | Some (l, v, G) => Some (l, v, List.skipn n2 G)
        | None => None
        end.
    Proof.
        intros. rewrite H, H0. destruct X2 as [[[l v] G]|]; simpl.
        - repeat f_equal. destruct G.
          * rewrite skipn_nil. reflexivity.
          * rewrite tl_skipn. reflexivity.
        - reflexivity.
    Qed.

    Lemma tf_h_match_skipn:
        forall {T1 T2 T3} (X1 X2: option (T1 * T2 * list T3)) n1 n2,
        n2 = n1 ->
        X1 = X2 ->
        match X1 with
        | Some (l, v, G) => Some (l, v, List.skipn n1 G)
        | None => None
        end = match X2 with
        | Some (l, v, G) => Some (l, v, List.skipn n2 G)
        | None => None
        end.
    Proof.
        intros. rewrite H, H0. destruct X2 as [[[l v] G]|]; simpl; reflexivity.
    Qed.

End Helper.


