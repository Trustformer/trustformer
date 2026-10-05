(*! Running the declassification rules FORWARD.  A rule's [di_extract] turns the
    bits it may read into the bits of its target; chaining them from a seed of
    published values recovers every node the analysis calls declassifiable.
    This is what makes a latency function over public data alone possible. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.
Require Import Koika.BitsToLists.

Require Import Trustformer.Theorems.Definitions.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.DFG.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Theorems.SchedulerSimulation.
Require Import Trustformer.Theorems.Internal.SchedulerRoundTrip.
Require Import Trustformer.Theorems.IPR.
Require Import Trustformer.Theorems.Internal.IPRProof.

Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

(* The first [Some] a list yields, which is how an instance is chosen: any rule
   that fires gives the same bits, so the search needs no order. *)
Fixpoint find_map {A B} (f: A -> option B) (l: list A) : option B :=
  match l with
  | [] => None
  | a :: rest => match f a with Some b => Some b | None => find_map f rest end
  end.

Lemma find_map_some {A B} (f: A -> option B) (l: list A) (b: B) :
  find_map f l = Some b -> exists a, List.In a l /\ f a = Some b.
Proof.
  induction l as [| a l IH]; cbn [find_map]; intro H; [ discriminate | ].
  destruct (f a) as [b' |] eqn:Hfa.
  - injection H as <-. exists a. split; [ left; reflexivity | exact Hfa ].
  - destruct (IH H) as [a' [Hin Hf]].
    exists a'. split; [ right; exact Hin | exact Hf ].
Qed.

(* The sources' bits in the order the instance lists them. *)
Fixpoint gather {A} (f: nid_t -> option A) (ns: list nid_t) : option (list A) :=
  match ns with
  | [] => Some []
  | n :: rest =>
      match f n, gather f rest with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
      end
  end.

Lemma gather_some {A} (f: nid_t -> option A) (ns: list nid_t) (vs: list A) :
  gather f ns = Some vs ->
  forall d: A, vs = map (fun n => match f n with Some v => v | None => d end) ns.
Proof.
  revert vs. induction ns as [| n ns IH]; intros vs H d; cbn [gather] in H.
  - injection H as <-. reflexivity.
  - destruct (f n) as [v |] eqn:Hfn; [ | discriminate ].
    destruct (gather f ns) as [vs' |] eqn:Hg; [ | discriminate ].
    injection H as <-. cbn [map]. rewrite Hfn. f_equal.
    exact (IH vs' eq_refl d).
Qed.


(* Widening pads at the top and narrowing drops it, so one list-level resize
   covers [Semantics.convert] in both directions. *)
Definition resize_bits (w: nat) (l: list bool) : list bool :=
  firstn w (l ++ List.repeat false w).

Lemma firstn_repeat_false (k m: nat) :
  firstn k (List.repeat false m) = List.repeat false (Nat.min k m).
Proof.
  revert m. induction k as [| k IH]; intro m; [ reflexivity | ].
  destruct m as [| m]; [ reflexivity | ].
  cbn [List.repeat firstn Nat.min]. rewrite IH. reflexivity.
Qed.

Lemma convert_to_list (szA szB: nat) (x: bits_t szA) :
  vect_to_list (convert (szB := szB) x) = resize_bits szB (vect_to_list x).
Proof.
  unfold convert, resize_bits.
  destruct (eq_dec szA szB) as [e | ne].
  - destruct e. cbn [eq_rect].
    rewrite firstn_app, vect_to_list_length.
    rewrite firstn_all2 by (rewrite vect_to_list_length; lia).
    replace (szA - szA) with 0 by lia. cbn [firstn].
    symmetry. apply app_nil_r.
  - rewrite BitsToLists.slice. cbn [take_drop' fst snd].
    rewrite firstn_app, vect_to_list_length, firstn_repeat_false.
    f_equal. f_equal. pose proof (vect_to_list_length x). lia.
Qed.

Lemma list_assoc_app {V} (l1 l2: list (nat * V)) (k: nat) (v: V) :
  list_assoc (l1 ++ l2) k = Some v ->
  list_assoc l1 k = Some v \/ list_assoc l2 k = Some v.
Proof.
  induction l1 as [| [k1 v1] l1 IH]; cbn [List.app list_assoc]; intro H.
  - right; exact H.
  - destruct (eq_dec k k1) as [-> | Hne]; [ left; exact H | exact (IH H) ].
Qed.

Lemma list_assoc_app_l {V} (l1 l2: list (nat * V)) (k: nat) (v: V) :
  list_assoc l1 k = Some v -> list_assoc (l1 ++ l2) k = Some v.
Proof.
  induction l1 as [| [k1 v1] l1 IH]; cbn [List.app list_assoc]; intro H;
    [ discriminate | ].
  destruct (eq_dec k k1) as [-> | Hne]; [ exact H | exact (IH H) ].
Qed.

Lemma list_assoc_In {V} (l: list (nat * V)) (k: nat) (v: V) :
  list_assoc l k = Some v -> List.In (k, v) l.
Proof.
  induction l as [| [k1 v1] l IH]; cbn [list_assoc]; intro H; [ discriminate | ].
  destruct (eq_dec k k1) as [-> | Hne].
  - injection H as <-. left; reflexivity.
  - right; exact (IH H).
Qed.

(* The inverse of [vect_to_list] at a known width: [convert] casts the vector
   the list builds, and at the right length that cast is the identity. *)
Definition bits_of_list (w: nat) (l: list bool) : bits_t w :=
  convert (vect_of_list l).

Lemma resize_bits_id (w: nat) (l: list bool) :
  length l = w -> resize_bits w l = l.
Proof.
  intro H. unfold resize_bits.
  rewrite firstn_app, H, firstn_all2 by lia.
  replace (w - w) with 0 by lia. cbn [firstn]. apply app_nil_r.
Qed.

Lemma vect_to_list_bits_of_list (w: nat) (l: list bool) :
  length l = w -> vect_to_list (bits_of_list w l) = l.
Proof.
  intro Hl. unfold bits_of_list.
  rewrite convert_to_list, BitsToLists.vect_to_list_of_list.
  apply resize_bits_id. exact Hl.
Qed.

Lemma bits_of_list_to_list {w} (x: bits_t w) :
  bits_of_list w (vect_to_list x) = x.
Proof.
  apply (vect_to_list_inj bool w).
  apply vect_to_list_bits_of_list, vect_to_list_length.
Qed.

Section Extract.
  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation sched := (tfs_schedule ctx cost_limit).
  Local Notation s_var := (tfs_spec_states ctx).
  Local Notation i_var := (tfs_spec_inputs ctx).
  Local Notation o_var := (tfs_spec_outputs ctx).
  Local Notation i_sz := (tfs_spec_inputs_size ctx).
  Local Notation o_sz := (tfs_spec_outputs_size ctx).
  Local Notation sched_st_env  := (ContextEnv.(env_t) (tf_states_type (tfs_states_size sched))).
  Local Notation sched_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation sched_sys_state := (sched_st_env * sched_out_env)%type.
  Local Notation sched_input_t :=
    (forall x : tfs_inputs sched, type_denote (tf_inputs_type (tfs_inputs_size sched) x)).
  Local Notation a_index := (Vect.index (length (buffer_needs ctx cost_limit))).
  Local Notation nsz act n :=
    (sz (nth n (graph (build_dfg ctx act)) {| nid := 0; op := DFG_Empty; sz := 0 |})).
  Local Notation s_sz := (tfs_spec_states_size ctx).
  Local Notation src_st_env  := (ContextEnv.(env_t) (tf_states_type s_sz)).
  Local Notation src_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation src_sys_state := (src_st_env * src_out_env)%type.
  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).
  Local Notation spec_run act sp input :=
    (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx)
       (tfs_spec_action_ops ctx act) sp input).
  Local Notation rvalid act a_idx pi n ss input :=
    (tf_eval_expr (tfs_states_size sched) (tfs_inputs_size sched)
       (tfs_outputs_size sched) (szB := 1)
       (snd (compile_dfg_expr_at ctx (buffer_needs ctx cost_limit) pi
               (length (graph (build_dfg ctx act))) a_idx
               (build_dfg ctx act) n (sample_bufs ctx cost_limit act a_idx)))
       ss input) (only parsing).
  Local Notation decl_instances := (Taint.decl_instances ctx).
  Local Notation resp_val :=
    (forall p : tfs_ips sched, bits_t (ip_resp_sz (tfs_ip sched p))).
  Local Notation bneeds := (buffer_needs ctx cost_limit).
  Local Notation eval1 e ss input :=
    (tf_eval_expr (tfs_states_size sched) (tfs_inputs_size sched)
       (tfs_outputs_size sched) (szB := 1) e ss input) (only parsing).

  (* What the attacker has worked out so far: node ids to bits. *)
  Definition val_table := list (nid_t * list bool).

  Definition tbl_get (t: val_table) (n: nid_t) : option (list bool) :=
    list_assoc t n.

  (* A guard literal holds when the recovered condition bit matches it. *)
  Definition lit_ok (f: nid_t -> list bool) (l: Taint.lit) : bool :=
    match f (fst l) with
    | [b] => Bool.eqb b (snd l)
    | _ => false
    end%list.

  (* ---- ONE OPERATION, on the bits its arguments carry ----
     Each clause is [tf_eval_expr]'s own, read at the nodes' declared widths;
     [node_args_sz] is what makes the casts identities. *)
  Definition pv_op2 (bop: tf_binary_ops) (w sa sb: nat)
      (x: bits_t sa) (y: bits_t sb) : bits_t w :=
    match bop with
    | tf_and => Bits.and (convert x) (convert y)
    | tf_or  => Bits.or  (convert x) (convert y)
    | tf_xor => Bits.xor (convert x) (convert y)
    | tf_add => Bits.plus  (convert x) (convert y)
    | tf_sub => Bits.minus (convert x) (convert y)
    | tf_mul => convert (Bits.mul (convert (szB := w) x) (convert (szB := w) y))
    | tf_cmp szC cop =>
        let u := convert (szB := szC) x in
        let v := convert (szB := szC) y in
        match cop with
        | tf_eq  => if beq_dec u v then convert (Bits.of_nat 1 1) else convert (Bits.of_nat 1 0)
        | tf_neq => if beq_dec u v then convert (Bits.of_nat 1 0) else convert (Bits.of_nat 1 1)
        | tf_lt  => if Bits.unsigned_lt u v then convert (Bits.of_nat 1 1) else convert (Bits.of_nat 1 0)
        | tf_le  => if Bits.unsigned_le u v then convert (Bits.of_nat 1 1) else convert (Bits.of_nat 1 0)
        | tf_gt  => if Bits.unsigned_gt u v then convert (Bits.of_nat 1 1) else convert (Bits.of_nat 1 0)
        | tf_ge  => if Bits.unsigned_ge u v then convert (Bits.of_nat 1 1) else convert (Bits.of_nat 1 0)
        end
    | tf_concat hz lz =>
        convert (Bits.app (convert (szB := hz) x) (convert (szB := lz) y))
    end.

  (* FORWARD: a node's bits from its arguments' bits.  A leaf comes from the
     seed instead, and the round trip's own nodes carry no value a table
     speaks about. *)
  Definition pstep (act: tfs_action sched) (rec: nid_t -> option (list bool))
      (n: nid_t) : option (list bool) :=
    let w := nsz act n in
    match Definitions.node_op ctx cost_limit act n with
    | DFG_Const c => Some (vect_to_list (Bits.of_nat w c))
    | DFG_Unary uop a =>
        match rec a with
        | None => None
        | Some la =>
            match uop with
            | tf_not => Some (vect_to_list (Bits.neg (bits_of_list w la)))
            | tf_resize s =>
                Some (vect_to_list (convert (szB := w) (bits_of_list s la)))
            end
        end
    | DFG_Resize a =>
        match rec a with
        | None => None
        | Some la =>
            Some (vect_to_list (convert (szB := w) (bits_of_list (nsz act a) la)))
        end
    | DFG_Binary bop a b =>
        match rec a, rec b with
        | Some la, Some lb =>
            Some (vect_to_list (pv_op2 bop w (nsz act a) (nsz act b)
                                  (bits_of_list (nsz act a) la)
                                  (bits_of_list (nsz act b) lb)))
        | _, _ => None
        end
    | DFG_Phi c t e =>
        match rec c with
        | Some (bb :: nil) => if bb then rec t else rec e
        | _ => None
        end
    | _ => None
    end.

  (* BACKWARD: the target of a rule whose guard and sources are recovered. *)
  Definition pback (act: tfs_action sched) (rec: nid_t -> option (list bool))
      (n: nid_t) : option (list bool) :=
    find_map
      (fun i =>
         if andb (Nat.eqb (di_target i) n)
                 (forallb (fun l => lit_ok (fun c => match rec c with
                                                     | Some v => v
                                                     | None => []
                                                     end) l)
                    (di_guard i))
         then match gather rec (di_sources i) with
              | Some vs => Some (di_extract i vs)
              | None => None
              end
         else None)
      (decl_instances (build_dfg ctx act)).

  (* ---- soundness ---- *)

  (* Every entry the attacker starts from is a value the run really has, WHERE
     THE NODE HAS SETTLED: before that, a published table says nothing about
     what the buffers behind it hold. *)
  Definition seed_sound (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t) (seed: val_table) : Prop :=
    forall n v, tbl_get seed n = Some v ->
      Definitions.settled_at ctx cost_limit act a_idx ss input n ->
      vect_to_list (nval ctx cost_limit act a_idx ss input (nsz act n) n) = v.

  Definition decl_guards_sized (act: tfs_action sched) : Prop :=
    forall i, List.In i (decl_instances (build_dfg ctx act)) ->
      Definitions.instance_guards_sized ctx cost_limit act i.

  Lemma bits_of_list_nval (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t) (w: nat) (m: nid_t)
      (l: list bool) :
    vect_to_list (nval ctx cost_limit act a_idx ss input w m) = l ->
    bits_of_list w l = nval ctx cost_limit act a_idx ss input w m.
  Proof. intro H. rewrite <- H. apply bits_of_list_to_list. Qed.

  (* ---- soundness ----

     A table is SOUND when every entry is a value the run really has, where the
     node has settled: before that, a published table says nothing about what
     the buffers behind it hold.  [seed_sound] is that property, and the two
     lemmas below are the two ways a round extends a sound table. *)

  Lemma pstep_sound (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t) (tbl: val_table)
      (n: nid_t) (w: list bool) :
    seed_sound act a_idx ss input tbl ->
    1 <= n ->
    n < length (graph (build_dfg ctx act)) ->
    pstep act (tbl_get tbl) n = Some w ->
    Definitions.settled_at ctx cost_limit act a_idx ss input n ->
    vect_to_list (nval ctx cost_limit act a_idx ss input (nsz act n) n) = w.
  Proof.
    intros Htbl Hn1 Hnlen Hps Hst.
    assert (Hnode_in : List.In (nth n (graph (build_dfg ctx act))
                                  {| nid := 0; op := DFG_Empty; sz := 0 |})
                         (graph (build_dfg ctx act)))
      by (apply nth_In; exact Hnlen).
    pose proof (wfg_build_dfg ctx cost_limit act _ Hnode_in) as Hfg.
    unfold node_args_sz in Hfg.
    assert (Hrange : forall x,
              List.In x (get_args ctx (nth n (graph (build_dfg ctx act))
                                         {| nid := 0; op := DFG_Empty; sz := 0 |})) ->
              1 <= x /\ x < n)
      by (intros x Hx; exact (node_args_range ctx cost_limit act n Hn1 Hnlen x Hx)).
    unfold pstep in Hps. unfold Definitions.node_op in Hps.
      destruct (op (nth n (graph (build_dfg ctx act))
                      {| nid := 0; op := DFG_Empty; sz := 0 |}))
        as [c | iv | dv | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa
           | dp darg den | sp stok sen | ja jb | ] eqn:Hop;
        cbn [fst snd] in Hps; try discriminate.
      * (* a literal *)
        injection Hps as <-. unfold nval.
        rewrite (nre_const ctx cost_limit act a_idx n c Hn1 Hnlen Hop).
        reflexivity.
      * (* not, and the resize written as a unary *)
        destruct (tbl_get tbl arg) as [la |] eqn:Ha; [ | discriminate ].
        destruct (Hrange arg ltac:(unfold get_args; rewrite Hop; left; reflexivity))
          as [Ha1 Ha2].
        assert (Hargst : Definitions.settled_at ctx cost_limit act a_idx ss input arg).
        { destruct Hst as [pi [Hpi Hv]]. exists pi. split; [ exact Hpi | ].
          exact (nrv_peel_unary ctx cost_limit act a_idx n uop arg pi ss input
                   ltac:(unfold Definitions.node_op; rewrite Hop; reflexivity)
                   Ha1 Hnlen Hv). }
        pose proof (Htbl arg la Ha Hargst) as Hav.
        destruct uop as [| source_size].
        -- injection Hps as <-.
           destruct (wsz_node_sz ctx cost_limit act arg _ Hfg) as [_ Hasz].
           rewrite Hasz in Hav.
           rewrite (bits_of_list_nval act a_idx ss input _ arg la Hav).
           unfold nval.
           rewrite (nre_unary ctx cost_limit act a_idx n tf_not arg Hn1 Hnlen Hop).
           reflexivity.
        -- injection Hps as <-.
           destruct (wsz_node_sz ctx cost_limit act arg _ Hfg) as [_ Hasz].
           rewrite Hasz in Hav.
           rewrite (bits_of_list_nval act a_idx ss input _ arg la Hav).
           unfold nval.
           rewrite (nre_unary ctx cost_limit act a_idx n (tf_resize source_size)
                      arg Hn1 Hnlen Hop).
           reflexivity.
      * (* a binary operation *)
        destruct (tbl_get tbl a1) as [la |] eqn:Ha; [ | discriminate ].
        destruct (tbl_get tbl a2) as [lb |] eqn:Hb; [ | discriminate ].
        injection Hps as <-.
        destruct (Hrange a1 ltac:(unfold get_args; rewrite Hop; left; reflexivity))
          as [Ha1 Ha2].
        destruct (Hrange a2 ltac:(unfold get_args; rewrite Hop; right; left; reflexivity))
          as [Hb1 Hb2].
        assert (Hargst : Definitions.settled_at ctx cost_limit act a_idx ss input a1
                         /\ Definitions.settled_at ctx cost_limit act a_idx ss input a2).
        { destruct Hst as [pi [Hpi Hv]].
          destruct (nrv_peel_binary ctx cost_limit act a_idx n bop a1 a2 pi ss input
                      ltac:(unfold Definitions.node_op; rewrite Hop; reflexivity)
                      Ha1 Hb1 Hnlen Hv) as [Hv1 Hv2].
          split; [ exists pi; split; [ exact Hpi | exact Hv1 ]
                 | exists pi; split; [ exact Hpi | exact Hv2 ] ]. }
        destruct Hargst as [Hst1 Hst2].
        pose proof (Htbl a1 la Ha Hst1) as Hav.
        pose proof (Htbl a2 lb Hb Hst2) as Hbv.
        rewrite (bits_of_list_nval act a_idx ss input _ a1 la Hav).
        rewrite (bits_of_list_nval act a_idx ss input _ a2 lb Hbv).
        unfold nval.
        rewrite (nre_binary ctx cost_limit act a_idx n bop a1 a2 Hn1 Hnlen Hop).
        unfold pv_op2.
        destruct bop as [| | | | | | szC cop | hz lz];
          [ destruct Hfg as [Hf1 Hf2];
            destruct (wsz_node_sz ctx cost_limit act a1 _ Hf1) as [_ H1sz];
            destruct (wsz_node_sz ctx cost_limit act a2 _ Hf2) as [_ H2sz];
            rewrite H1sz, H2sz; cbn [tf_eval_expr]; rewrite !convert_same;
            reflexivity .. | | ].
        -- (* a comparison: the operands are read at the compared width *)
           destruct Hfg as [Hf1 Hf2].
           destruct (wsz_node_sz ctx cost_limit act a1 _ Hf1) as [_ H1sz].
           destruct (wsz_node_sz ctx cost_limit act a2 _ Hf2) as [_ H2sz].
           rewrite H1sz, H2sz. cbn [tf_eval_expr]. rewrite !convert_same.
           destruct cop; reflexivity.
        -- (* a concatenation: each operand at its own declared width *)
           destruct Hfg as [Hf1 Hf2].
           destruct (wsz_node_sz ctx cost_limit act a1 _ Hf1) as [_ H1sz].
           destruct (wsz_node_sz ctx cost_limit act a2 _ Hf2) as [_ H2sz].
           rewrite H1sz, H2sz. cbn [tf_eval_expr]. rewrite !convert_same.
           reflexivity.
      * (* a resize *)
        destruct (tbl_get tbl arg) as [la |] eqn:Ha; [ | discriminate ].
        injection Hps as <-.
        destruct (Hrange arg ltac:(unfold get_args; rewrite Hop; left; reflexivity))
          as [Ha1 Ha2].
        assert (Hargst : Definitions.settled_at ctx cost_limit act a_idx ss input arg).
        { destruct Hst as [pi [Hpi Hv]]. exists pi. split; [ exact Hpi | ].
          exact (nrv_peel_resize ctx cost_limit act a_idx n arg pi ss input
                   ltac:(unfold Definitions.node_op; rewrite Hop; reflexivity)
                   Ha1 Hnlen Hv). }
        pose proof (Htbl arg la Ha Hargst) as Hav.
        rewrite (bits_of_list_nval act a_idx ss input _ arg la Hav).
        unfold nval.
        rewrite (nre_resize ctx cost_limit act a_idx n arg Hn1 Hnlen Hop).
        reflexivity.
      * (* a phi: the condition names the arm, and that arm's bits are it *)
        destruct (tbl_get tbl cnd) as [lc |] eqn:Hc; [ | discriminate ].
        destruct lc as [| bb lc0]; [ discriminate | ].
        destruct lc0 as [| ? ?]; [ | discriminate ].
        destruct (Hrange cnd ltac:(unfold get_args; rewrite Hop; left; reflexivity))
          as [Hc1 Hc2].
        destruct (Hrange tid ltac:(unfold get_args; rewrite Hop; right; left; reflexivity))
          as [Ht1 Ht2].
        destruct (Hrange eid ltac:(unfold get_args; rewrite Hop; right; right; left; reflexivity))
          as [He1 He2].
        assert (Hopn : Definitions.node_op ctx cost_limit act n = DFG_Phi cnd tid eid)
          by (unfold Definitions.node_op; rewrite Hop; reflexivity).
        destruct (IPRProof.phi_args_settled ctx cost_limit act a_idx ss input
                    n cnd tid eid Hopn
                    Hc1 Ht1 He1 Hnlen Hst) as [Hstc [Hstt Hste]].
        pose proof (Htbl cnd _ Hc Hstc) as Hcv.
        destruct Hfg as [Hfc [Hft Hfe]].
        destruct (wsz_node_sz ctx cost_limit act cnd 1 Hfc) as [_ Hcsz].
        destruct (wsz_node_sz ctx cost_limit act tid _ Hft) as [_ Htsz].
        destruct (wsz_node_sz ctx cost_limit act eid _ Hfe) as [_ Hesz].
        rewrite Hcsz in Hcv.
        assert (Hcb : nval ctx cost_limit act a_idx ss input 1 cnd
                      = Definitions.bit_of bb).
        { apply (vect_to_list_inj bool 1).
          rewrite Hcv, bit_of_to_list. reflexivity. }
        unfold nval.
        rewrite (nre_phi ctx cost_limit act a_idx n cnd tid eid Hn1 Hnlen Hop).
        cbn [tf_eval_expr].
        unfold nval in Hcb. rewrite Hcb.
        destruct bb.
        -- assert (Hnz : eval1 (node_ref_expr ctx cost_limit act a_idx cnd) ss input
                         <> Bits.zero)
             by (unfold nval in Hcb; rewrite Hcb; exact ones1_neq_zero).
           pose proof (Htbl tid w Hps (Hstt Hnz)) as Htv.
           rewrite Htsz in Htv.
           match goal with
           | |- context [@beq_dec ?T ?E ?a ?z] =>
               replace (@beq_dec T E a z) with false
                 by (symmetry; apply beq_dec_false_iff; exact ones1_neq_zero)
           end.
           exact Htv.
        -- assert (Hz : eval1 (node_ref_expr ctx cost_limit act a_idx cnd) ss input
                        = Bits.zero)
             by (unfold nval in Hcb; exact Hcb).
           pose proof (Htbl eid w Hps (Hste Hz)) as Hev.
           rewrite Hesz in Hev.
           rewrite beq_dec_refl.
           exact Hev.
  Qed.

  Lemma pback_sound (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t) (tbl: val_table)
      (n: nid_t) (v: list bool) :
    seed_sound act a_idx ss input tbl ->
    decl_guards_sized act ->
    (forall i, List.In i (decl_instances (build_dfg ctx act)) ->
       instance_extracts ctx cost_limit act a_idx i) ->
    (forall i, List.In i (decl_instances (build_dfg ctx act)) ->
       Definitions.instance_lifts ctx cost_limit act a_idx i) ->
    pback act (tbl_get tbl) n = Some v ->
    Definitions.settled_at ctx cost_limit act a_idx ss input n ->
    vect_to_list (nval ctx cost_limit act a_idx ss input (nsz act n) n) = v.
  Proof.
    intros Htbl Hgsz Hinst Hlift Hex Hst.
      unfold pback in Hex.
      destruct (find_map_some _ _ _ Hex) as [i [Hin Hfi]].
      destruct (andb (Nat.eqb (di_target i) n)
                  (forallb (fun l => lit_ok (fun c => match tbl_get tbl c with
                                                      | Some w => w
                                                      | None => []
                                                      end) l)
                     (di_guard i))) eqn:Hcond; [ | discriminate ].
      apply andb_prop in Hcond. destruct Hcond as [Htgt Hguards].
      apply Nat.eqb_eq in Htgt.
      destruct (gather (tbl_get tbl) (di_sources i)) as [vs |] eqn:Hg;
        [ | discriminate ].
      injection Hfi as <-.
      assert (Hsttgt : Definitions.settled_at ctx cost_limit act a_idx ss input (di_target i))
        by (rewrite Htgt; exact Hst).
      destruct (Hlift i Hin ss input Hsttgt) as [Hgst Hsst].
      (* the guard the instance records really holds in this state *)
      assert (Hpi : Definitions.pi_holds ctx cost_limit act a_idx input
                      (di_guard i) ss).
      { intros c b Hcb.
        rewrite forallb_forall in Hguards.
        pose proof (Hguards (c, b) Hcb) as Hl. unfold lit_ok in Hl.
        cbn [fst snd] in Hl.
        destruct (tbl_get tbl c) as [w |] eqn:Hc; [ | discriminate ].
        destruct w as [| b0 w0]; [ discriminate | ].
        destruct w0 as [| ? ?]; [ | discriminate ].
        apply Bool.eqb_prop in Hl. subst b0.
        pose proof (Hgst c (in_map fst _ _ Hcb)) as Hstc.
        pose proof (Htbl c _ Hc Hstc) as Hcv.
        pose proof (Hgsz i Hin (c, b) Hcb) as Hcsz. cbn [fst] in Hcsz.
        rewrite Hcsz in Hcv.
        apply (vect_to_list_inj bool 1).
        rewrite Hcv, bit_of_to_list. reflexivity. }
      (* and the extraction equation turns the sources' bits into the target's *)
      pose proof (Hinst i Hin ss input Hpi) as Heq.
      rewrite Htgt in Heq. rewrite Heq. f_equal.
      rewrite (gather_some _ _ _ Hg []).
      apply map_ext_in. intros s Hsin.
      destruct (tbl_get tbl s) as [w |] eqn:Hsv.
      * exact (Htbl s _ Hsv (Hsst Hpi s Hsin)).
      * exfalso. clear - Hg Hsin Hsv.
        revert Hg Hsin. generalize (di_sources i) as ns. intro ns.
        revert vs. induction ns as [| m ns IHn]; intros vs Hg Hsin;
          cbn [gather] in Hg; [ destruct Hsin | ].
        destruct (tbl_get tbl m) as [w |] eqn:Hm; [ | discriminate ].
        destruct (gather (tbl_get tbl) ns) as [vs' |] eqn:Hgn;
          [ | discriminate ].
        destruct Hsin as [-> | Hsin]; [ congruence | ].
        exact (IHn vs' eq_refl Hsin).
  Qed.



  (* ---- THE TABLE THE ATTACKER BUILDS ----
     One node, filled if the table can fill it: forward from its arguments, or
     backward through a rule.  An entry once set is never read again, so the
     table only grows and its entries never move -- which is what makes both
     the soundness invariant and the coverage argument below one-liners. *)
  Definition pfill (act: tfs_action sched) (tbl: val_table) (n: nid_t)
    : val_table :=
    match tbl_get tbl n with
    | Some _ => tbl
    | None =>
        match pstep act (tbl_get tbl) n with
        | Some v => (n, v) :: tbl
        | None =>
            match pback act (tbl_get tbl) n with
            | Some v => (n, v) :: tbl
            | None => tbl
            end
        end
    end.

  (* ONE ROUND over every node of the graph, in id order. *)
  Definition pround (act: tfs_action sched) (tbl: val_table) : val_table :=
    fold_left (pfill act)
      (List.seq 1 (length (graph (build_dfg ctx act)) - 1)) tbl.

  Fixpoint ptable (act: tfs_action sched) (seed: val_table) (rounds: nat)
    : val_table :=
    match rounds with
    | 0 => seed
    | S r => pround act (ptable act seed r)
    end.

  (* ---- the table only grows, and its entries never change ---- *)

  Lemma pfill_get (act: tfs_action sched) (tbl: val_table) (m n: nid_t)
      (v: list bool) :
    tbl_get tbl n = Some v -> tbl_get (pfill act tbl m) n = Some v.
  Proof.
    intro H. unfold pfill.
    assert (Hcons : forall w, tbl_get tbl m = None ->
              tbl_get ((m, w) :: tbl) n = Some v).
    { intros w Hm. unfold tbl_get. cbn [list_assoc].
      destruct (eq_dec n m) as [-> | Hne]; [ rewrite Hm in H; discriminate | ].
      exact H. }
    destruct (tbl_get tbl m) as [w |] eqn:Hm; [ exact H | ].
    destruct (pstep act (tbl_get tbl) m) as [w |] eqn:Hps;
      [ exact (Hcons w eq_refl) | ].
    destruct (pback act (tbl_get tbl) m) as [w |] eqn:Hpb;
      [ exact (Hcons w eq_refl) | exact H ].
  Qed.

  Lemma pround_get (act: tfs_action sched) (tbl: val_table) (n: nid_t)
      (v: list bool) :
    tbl_get tbl n = Some v -> tbl_get (pround act tbl) n = Some v.
  Proof.
    unfold pround.
    generalize (List.seq 1 (length (graph (build_dfg ctx act)) - 1)) as l.
    intro l. revert tbl.
    induction l as [| m l IH]; intros tbl H; [ exact H | ].
    cbn [fold_left]. exact (IH _ (pfill_get act tbl m n v H)).
  Qed.

  Lemma ptable_get (act: tfs_action sched) (seed: val_table) (r r': nat)
      (n: nid_t) (v: list bool) :
    r <= r' ->
    tbl_get (ptable act seed r) n = Some v ->
    tbl_get (ptable act seed r') n = Some v.
  Proof.
    intro Hle. induction Hle as [| r' Hle IH]; intro H; [ exact H | ].
    cbn [ptable]. exact (pround_get act _ n v (IH H)).
  Qed.

  (* ---- a round keeps the table sound ---- *)

  Lemma pfill_sound (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t) (tbl: val_table) (m: nid_t) :
    decl_guards_sized act ->
    (forall i, List.In i (decl_instances (build_dfg ctx act)) ->
       instance_extracts ctx cost_limit act a_idx i) ->
    (forall i, List.In i (decl_instances (build_dfg ctx act)) ->
       Definitions.instance_lifts ctx cost_limit act a_idx i) ->
    1 <= m ->
    m < length (graph (build_dfg ctx act)) ->
    seed_sound act a_idx ss input tbl ->
    seed_sound act a_idx ss input (pfill act tbl m).
  Proof.
    intros Hgsz Hinst Hlift Hm1 Hmlen Htbl.
    assert (Hcons : forall w,
              vect_to_list (nval ctx cost_limit act a_idx ss input
                              (nsz act m) m) = w ->
              Definitions.settled_at ctx cost_limit act a_idx ss input m ->
              seed_sound act a_idx ss input ((m, w) :: tbl)).
    { intros w Hw _ n v Hget Hst. unfold tbl_get in Hget. cbn [list_assoc] in Hget.
      destruct (eq_dec n m) as [-> | Hne];
        [ injection Hget as <-; exact Hw | exact (Htbl n v Hget Hst) ]. }
    unfold pfill.
    destruct (tbl_get tbl m) as [w |] eqn:Hm; [ exact Htbl | ].
    destruct (pstep act (tbl_get tbl) m) as [w |] eqn:Hps.
    - intros n v Hget Hst. unfold tbl_get in Hget. cbn [list_assoc] in Hget.
      destruct (eq_dec n m) as [-> | Hne]; [ | exact (Htbl n v Hget Hst) ].
      injection Hget as <-.
      exact (pstep_sound act a_idx ss input tbl m w Htbl Hm1 Hmlen Hps Hst).
    - destruct (pback act (tbl_get tbl) m) as [w |] eqn:Hpb; [ | exact Htbl ].
      intros n v Hget Hst. unfold tbl_get in Hget. cbn [list_assoc] in Hget.
      destruct (eq_dec n m) as [-> | Hne]; [ | exact (Htbl n v Hget Hst) ].
      injection Hget as <-.
      exact (pback_sound act a_idx ss input tbl m w Htbl Hgsz Hinst Hlift Hpb Hst).
  Qed.

  Theorem ptable_sound (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t) (seed: val_table) :
    seed_sound act a_idx ss input seed ->
    decl_guards_sized act ->
    (forall i, List.In i (decl_instances (build_dfg ctx act)) ->
       instance_extracts ctx cost_limit act a_idx i) ->
    (forall i, List.In i (decl_instances (build_dfg ctx act)) ->
       Definitions.instance_lifts ctx cost_limit act a_idx i) ->
    forall rounds, seed_sound act a_idx ss input (ptable act seed rounds).
  Proof.
    intros Hseed Hgsz Hinst Hlift rounds.
    induction rounds as [| r IH]; [ exact Hseed | ].
    cbn [ptable]. unfold pround.
    assert (Hgen : forall l tbl,
              (forall m, List.In m l ->
                 1 <= m /\ m < length (graph (build_dfg ctx act))) ->
              seed_sound act a_idx ss input tbl ->
              seed_sound act a_idx ss input (fold_left (pfill act) l tbl)).
    { induction l as [| m l IHl]; intros tbl Hl Ht; [ exact Ht | ].
      cbn [fold_left].
      destruct (Hl m (or_introl eq_refl)) as [Hm1 Hmlen].
      exact (IHl _ (fun x Hx => Hl x (or_intror Hx))
               (pfill_sound act a_idx ss input tbl m Hgsz Hinst Hlift
                  Hm1 Hmlen Ht)). }
    apply Hgen; [ | exact IH ].
    intros m Hm. apply in_seq in Hm. split; lia.
  Qed.


  (* ---- coverage: what the table ends up holding ---- *)

  Definition tbl_has (tbl: val_table) (n: nid_t) : Prop :=
    exists v, tbl_get tbl n = Some v.

  Lemma find_map_not_none {A B} (f: A -> option B) (l: list A) (a: A) :
    List.In a l -> f a <> None -> exists b, find_map f l = Some b.
  Proof.
    induction l as [| x l IH]; intro Hin; [ destruct Hin | ].
    intro Hfa. cbn [find_map].
    destruct (f x) as [b |] eqn:Hfx; [ exists b; reflexivity | ].
    destruct Hin as [-> | Hin]; [ congruence | exact (IH Hin Hfa) ].
  Qed.

  Lemma gather_mono {A} (f g: nid_t -> option A) (ns: list nid_t) (vs: list A) :
    (forall x w, f x = Some w -> g x = Some w) ->
    gather f ns = Some vs -> gather g ns = Some vs.
  Proof.
    intro Hm. revert vs.
    induction ns as [| m ns IH]; intros vs H; [ exact H | ].
    cbn [gather] in H |- *.
    destruct (f m) as [w |] eqn:Hm'; [ | discriminate ].
    destruct (gather f ns) as [ws |] eqn:Hg; [ | discriminate ].
    rewrite (Hm m w Hm'), (IH ws eq_refl). exact H.
  Qed.

  (* A bigger table fills everything a smaller one did: an entry never moves,
     so every lookup the step made reads the same value. *)
  Lemma pstep_mono (act: tfs_action sched) (tbl tbl': val_table) (n: nid_t)
      (v: list bool) :
    (forall x w, tbl_get tbl x = Some w -> tbl_get tbl' x = Some w) ->
    pstep act (tbl_get tbl) n = Some v ->
    pstep act (tbl_get tbl') n = Some v.
  Proof.
    intros Hm Hps. unfold pstep in Hps |- *.
    destruct (Definitions.node_op ctx cost_limit act n)
      as [c | iv | dv | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa
         | dp darg den | sp stok sen | ja jb | ] eqn:Hop;
      try discriminate; try exact Hps.
    - destruct (tbl_get tbl arg) as [la |] eqn:Ha; [ | discriminate ].
      rewrite (Hm arg la Ha). exact Hps.
    - destruct (tbl_get tbl a1) as [la |] eqn:Ha; [ | discriminate ].
      destruct (tbl_get tbl a2) as [lb |] eqn:Hb; [ | discriminate ].
      rewrite (Hm a1 la Ha), (Hm a2 lb Hb). exact Hps.
    - destruct (tbl_get tbl arg) as [la |] eqn:Ha; [ | discriminate ].
      rewrite (Hm arg la Ha). exact Hps.
    - destruct (tbl_get tbl cnd) as [lc |] eqn:Hc; [ | discriminate ].
      rewrite (Hm cnd lc Hc).
      destruct lc as [| bb lc0]; [ discriminate | ].
      destruct lc0 as [| ? ?]; [ | discriminate ].
      destruct bb.
      + destruct (tbl_get tbl tid) as [lt |] eqn:Ht; [ | discriminate ].
        rewrite (Hm tid lt Ht). exact Hps.
      + destruct (tbl_get tbl eid) as [le |] eqn:He; [ | discriminate ].
        rewrite (Hm eid le He). exact Hps.
  Qed.

  Lemma pback_mono (act: tfs_action sched) (tbl tbl': val_table) (n: nid_t)
      (v: list bool) :
    (forall x w, tbl_get tbl x = Some w -> tbl_get tbl' x = Some w) ->
    pback act (tbl_get tbl) n = Some v ->
    exists v', pback act (tbl_get tbl') n = Some v'.
  Proof.
    intros Hm Hex. unfold pback in Hex |- *.
    destruct (find_map_some _ _ _ Hex) as [i [Hin Hfi]].
    apply (find_map_not_none _ _ i Hin).
    destruct (andb (Nat.eqb (di_target i) n)
                (forallb (fun l => lit_ok (fun c => match tbl_get tbl c with
                                                    | Some w => w
                                                    | None => []
                                                    end) l)
                   (di_guard i))) eqn:Hcond; [ | discriminate ].
    apply andb_prop in Hcond. destruct Hcond as [Htgt Hguards].
    destruct (gather (tbl_get tbl) (di_sources i)) as [vs |] eqn:Hg;
      [ | discriminate ].
    assert (Hguards' : forallb (fun l => lit_ok (fun c => match tbl_get tbl' c with
                                                          | Some w => w
                                                          | None => []
                                                          end) l)
                         (di_guard i) = true).
    { rewrite forallb_forall in Hguards |- *. intros l Hl.
      pose proof (Hguards l Hl) as Hl'. unfold lit_ok in Hl' |- *.
      destruct (tbl_get tbl (fst l)) as [w |] eqn:Hw; [ | discriminate ].
      rewrite (Hm (fst l) w Hw). exact Hl'. }
    rewrite Htgt, Hguards'. cbn [andb].
    rewrite (gather_mono _ _ _ _ Hm Hg). discriminate.
  Qed.

  Lemma fold_pfill_get (act: tfs_action sched) (l: list nid_t)
      (tbl: val_table) (n: nid_t) (v: list bool) :
    tbl_get tbl n = Some v ->
    tbl_get (fold_left (pfill act) l tbl) n = Some v.
  Proof.
    revert tbl. induction l as [| m l IH]; intros tbl H; [ exact H | ].
    cbn [fold_left]. exact (IH _ (pfill_get act tbl m n v H)).
  Qed.

  (* ONE ROUND fills every node the table could already fill. *)
  Lemma pround_fills (act: tfs_action sched) (tbl: val_table) (m: nid_t) :
    1 <= m ->
    m < length (graph (build_dfg ctx act)) ->
    ((exists v, pstep act (tbl_get tbl) m = Some v)
     \/ (exists v, pback act (tbl_get tbl) m = Some v)) ->
    tbl_has (pround act tbl) m.
  Proof.
    intros Hm1 Hmlen Hfill.
    assert (Hin : List.In m (List.seq 1 (length (graph (build_dfg ctx act)) - 1)))
      by (apply in_seq; lia).
    destruct (in_split _ _ Hin) as [l1 [l2 Hsplit]].
    unfold pround. rewrite Hsplit, fold_left_app. cbn [fold_left].
    set (tbl1 := fold_left (pfill act) l1 tbl) in *.
    assert (Hmono : forall x w, tbl_get tbl x = Some w -> tbl_get tbl1 x = Some w)
      by (intros x w Hx; exact (fold_pfill_get act l1 tbl x w Hx)).
    assert (Hfilled : tbl_has (pfill act tbl1 m) m).
    { unfold pfill.
      destruct (tbl_get tbl1 m) as [w |] eqn:H1; [ exists w; exact H1 | ].
      destruct (pstep act (tbl_get tbl1) m) as [w |] eqn:Hps.
      { exists w. unfold tbl_get. cbn [list_assoc].
        destruct (eq_dec m m) as [_ | Hne]; [ reflexivity | congruence ]. }
      destruct (pback act (tbl_get tbl1) m) as [w |] eqn:Hpb.
      { exists w. unfold tbl_get. cbn [list_assoc].
        destruct (eq_dec m m) as [_ | Hne]; [ reflexivity | congruence ]. }
      exfalso. destruct Hfill as [[w Hw] | [w Hw]].
      - rewrite (pstep_mono act tbl tbl1 m w Hmono Hw) in Hps. discriminate.
      - destruct (pback_mono act tbl tbl1 m w Hmono Hw) as [w' Hw'].
        rewrite Hw' in Hpb. discriminate. }
    destruct Hfilled as [w Hw]. exists w.
    exact (fold_pfill_get act l2 _ m w Hw).
  Qed.


  Lemma gather_total {A} (f: nid_t -> option A) (ns: list nid_t) :
    (forall x, List.In x ns -> exists w, f x = Some w) ->
    exists vs, gather f ns = Some vs.
  Proof.
    induction ns as [| m ns IH]; intro H; [ exists []; reflexivity | ].
    destruct (H m (or_introl eq_refl)) as [w Hw].
    destruct (IH (fun x Hx => H x (or_intror Hx))) as [vs Hvs].
    exists (w :: vs). cbn [gather]. rewrite Hw, Hvs. reflexivity.
  Qed.

  (* ONE INSTANCE, mirrored on the table: an unconditional instance whose
     sources the table holds fills its target in the next round. *)
  Lemma uncond_filled (act: tfs_action sched) (seed: val_table) (r: nat)
      (i: decl_instance) :
    Definitions.decl_in_range ctx cost_limit act ->
    List.In i (Taint.uncond_instances ctx (build_dfg ctx act)) ->
    (forall x, List.In x (di_sources i) -> tbl_has (ptable act seed r) x) ->
    tbl_has (ptable act seed (S r)) (di_target i).
  Proof.
    intros Hrng Hi Hsrc.
    assert (Hin_decl : List.In i (Taint.decl_instances ctx (build_dfg ctx act)))
      by (exact (proj1 (proj1 (filter_In _ i _) Hi))).
    assert (Hguard : di_guard i = []).
    { pose proof (proj2 (proj1 (filter_In _ i _) Hi)) as Hg. cbv beta in Hg.
      revert Hg. destruct (di_guard i) as [| l0 ls]; intro Hg;
        [ reflexivity | discriminate Hg ]. }
    destruct (Hrng i Hin_decl (di_target i) (or_introl eq_refl)) as [Ht1 Htlen].
    cbn [ptable]. apply (pround_fills act _ (di_target i) Ht1 Htlen). right.
    destruct (gather_total (tbl_get (ptable act seed r)) (di_sources i) Hsrc)
      as [vs Hvs].
    unfold pback.
    apply (find_map_not_none _ _ i Hin_decl).
    rewrite Nat.eqb_refl, Hguard. cbn [forallb andb].
    rewrite Hvs. discriminate.
  Qed.

  (* ONE SATURATION STEP: at most one round per instance it folds over. *)
  Lemma saturate_step_filled (act: tfs_action sched) (seed: val_table)
      (r0: nat) (acc: list nid_t) :
    Definitions.decl_in_range ctx cost_limit act ->
    (forall x, List.In x acc -> tbl_has (ptable act seed r0) x) ->
    forall n, List.In n (Taint.saturate_step ctx (build_dfg ctx act) acc) ->
      tbl_has (ptable act seed
                 (r0 + length (Taint.uncond_instances ctx (build_dfg ctx act)))) n.
  Proof.
    intros Hrng Hacc.
    assert (Hlater : forall r x, tbl_has (ptable act seed r) x ->
              tbl_has (ptable act seed (S r)) x).
    { intros r x [v Hv]. exists v.
      exact (ptable_get act seed r (S r) x v (Nat.le_succ_diag_r r) Hv). }
    unfold Taint.saturate_step.
    assert (Hgen : forall l acc0 r,
              (forall j, List.In j l ->
                 List.In j (Taint.uncond_instances ctx (build_dfg ctx act))) ->
              (forall x, List.In x acc0 -> tbl_has (ptable act seed r) x) ->
              forall n, List.In n
                (fold_left (fun acc i =>
                              if forallb (fun s => Taint.mem_nid s acc)
                                   (di_sources i)
                                 && negb (Taint.mem_nid (di_target i) acc)
                              then di_target i :: acc else acc) l acc0) ->
                tbl_has (ptable act seed (r + length l)) n).
    { induction l as [| i l IH]; intros acc0 r Hsub Hacc0 n Hin.
      - cbn [length]. rewrite Nat.add_0_r. exact (Hacc0 n Hin).
      - cbn [fold_left] in Hin.
        replace (r + length (i :: l)) with (S r + length l)
          by (cbn [length]; lia).
        destruct (forallb (fun s => Taint.mem_nid s acc0) (di_sources i)
                  && negb (Taint.mem_nid (di_target i) acc0)) eqn:Hf.
        + apply andb_prop in Hf. destruct Hf as [Hf _].
          refine (IH (di_target i :: acc0) (S r)
                    (fun j Hj => Hsub j (or_intror Hj)) _ n Hin).
          intros x Hx. destruct Hx as [<- | Hx]; [ | exact (Hlater r x (Hacc0 x Hx)) ].
          apply (uncond_filled act seed r i Hrng (Hsub i (or_introl eq_refl))).
          intros y Hy. rewrite forallb_forall in Hf.
          exact (Hacc0 y (IPRProof.mem_nid_In y acc0 (Hf y Hy))).
        + refine (IH acc0 (S r) (fun j Hj => Hsub j (or_intror Hj)) _ n Hin).
          intros x Hx. exact (Hlater r x (Hacc0 x Hx)). }
    intros n Hin.
    exact (Hgen (Taint.uncond_instances ctx (build_dfg ctx act)) acc r0
             (fun i Hi => Hi) Hacc n Hin).
  Qed.

  Lemma saturate_filled (act: tfs_action sched) (seed: val_table) :
    Definitions.decl_in_range ctx cost_limit act ->
    forall fuel r0 acc,
      (forall x, List.In x acc -> tbl_has (ptable act seed r0) x) ->
      forall n, List.In n (Taint.saturate ctx fuel (build_dfg ctx act) acc) ->
        tbl_has (ptable act seed
                   (r0 + fuel
                         * length (Taint.uncond_instances ctx
                                     (build_dfg ctx act)))) n.
  Proof.
    intros Hrng fuel. induction fuel as [| f IH]; intros r0 acc Hacc n Hin.
    - cbn [Taint.saturate] in Hin. rewrite Nat.mul_0_l, Nat.add_0_r.
      exact (Hacc n Hin).
    - cbn [Taint.saturate] in Hin. cbv zeta in Hin.
      destruct (Nat.eqb
                  (length (Taint.saturate_step ctx (build_dfg ctx act) acc))
                  (length acc)) eqn:Heq.
      + destruct (Hacc n Hin) as [v Hv]. exists v.
        apply (ptable_get act seed r0); [ lia | exact Hv ].
      + destruct (IH (r0 + length (Taint.uncond_instances ctx (build_dfg ctx act)))
                    (Taint.saturate_step ctx (build_dfg ctx act) acc)
                    (saturate_step_filled act seed r0 acc Hrng Hacc) n Hin)
          as [v Hv].
        exists v.
        apply (ptable_get act seed
                 (r0 + length (Taint.uncond_instances ctx (build_dfg ctx act))
                  + f * length (Taint.uncond_instances ctx
                                  (build_dfg ctx act))));
          [ lia | exact Hv ].
  Qed.


  (* ---- THE SEED: bits the published tables give outright ---- *)

  Definition pub_in_b (v: i_var) : bool :=
    match tfs_spec_inputs_class ctx v with Public => true | Secret => false end.
  Definition pub_out_b (o: o_var) : bool :=
    match tfs_spec_outputs_class ctx o with Public => true | Secret => false end.

  (* Keyed by the variable's own index, so a table carries bits and nothing a
     secret could sit in. *)
  Definition in_key (v: i_var) : nat := @finite_index _ (tfs_spec_inputs_fin ctx) v.
  Definition out_key (o: o_var) : nat := @finite_index _ (tfs_spec_outputs_fin ctx) o.

  Definition seed_node (act: tfs_action sched)
      (pv_in pv_pre: list (nat * list bool)) (n: nid_t)
    : option (nid_t * list bool) :=
    match Definitions.node_op ctx cost_limit act n with
    | DFG_Const c => Some (n, vect_to_list (Bits.of_nat (nsz act n) c))
    | DFG_Input v =>
        if pub_in_b v
        then match list_assoc pv_in (in_key v) with
             | Some bs => Some (n, resize_bits (nsz act n) bs)
             | None => None
             end
        else None
    | DFG_Var (DFG_OVar o) =>
        if pub_out_b o
        then match list_assoc pv_pre (out_key o) with
             | Some bs => Some (n, resize_bits (nsz act n) bs)
             | None => None
             end
        else None
    | _ => None
    end.

  Definition seed_local (act: tfs_action sched)
      (pv_in pv_pre: list (nat * list bool)) : val_table :=
    flat_map (fun n => match seed_node act pv_in pv_pre n with
                       | Some e => [e]
                       | None => []
                       end)
             (List.seq 1 (length (graph (build_dfg ctx act)) - 1)).

  Lemma seed_node_key (act: tfs_action sched) pv_in pv_pre m k v :
    seed_node act pv_in pv_pre m = Some (k, v) -> k = m.
  Proof.
    unfold seed_node.
    destruct (Definitions.node_op ctx cost_limit act m)
      as [c | iv | dv | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa
         | dp darg den | sp stok sen | ja jb | ];
      try discriminate.
    - intro H; injection H as <- _; reflexivity.
    - destruct (pub_in_b iv); [ | discriminate ].
      destruct (list_assoc pv_in (in_key iv)); [ | discriminate ].
      intro H; injection H as <- _; reflexivity.
    - destruct dv as [sv | ov]; [ discriminate | ].
      destruct (pub_out_b ov); [ | discriminate ].
      destruct (list_assoc pv_pre (out_key ov)); [ | discriminate ].
      intro H; injection H as <- _; reflexivity.
  Qed.


  Lemma seed_local_entry (act: tfs_action sched) pv_in pv_pre n v :
    List.In (n, v) (seed_local act pv_in pv_pre) ->
    1 <= n
    /\ n < length (graph (build_dfg ctx act))
    /\ seed_node act pv_in pv_pre n = Some (n, v).
  Proof.
    intro H. unfold seed_local in H. apply in_flat_map in H.
    destruct H as [m [Hseq Hm]].
    destruct (seed_node act pv_in pv_pre m) as [[k w] |] eqn:Hsn;
      [ | destruct Hm ].
    destruct Hm as [He | []].
    pose proof (seed_node_key act pv_in pv_pre m k w Hsn) as Hk.
    inversion He; subst.
    apply in_seq in Hseq. destruct Hseq as [Hm1 Hm2].
    split; [ exact Hm1 | split; [ lia | exact Hsn ] ].
  Qed.

  (* The tables ARE this run's published data. *)
  Definition in_published (input: sched_input_t)
      (pv_in: list (nat * list bool)) : Prop :=
    forall v, pub_in_b v = true ->
      list_assoc pv_in (in_key v) = Some (vect_to_list (input (inl v))).

  Definition pre_published (ss: sched_sys_state)
      (pv_pre: list (nat * list bool)) : Prop :=
    forall o, pub_out_b o = true ->
      list_assoc pv_pre (out_key o) = Some (vect_to_list ((snd ss).[o])).

  (* No validity anywhere: a literal, an input and an output read are stable
     for the whole action, so their bits are a fact about the run, not a cycle. *)
  Theorem seed_local_sound (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t)
      (pv_in pv_pre: list (nat * list bool)) :
    in_published input pv_in ->
    pre_published ss pv_pre ->
    seed_sound act a_idx ss input (seed_local act pv_in pv_pre).
  Proof.
    intros Hin Hpre n v Hget _.
    unfold tbl_get in Hget. apply list_assoc_In in Hget.
    destruct (seed_local_entry act pv_in pv_pre n v Hget) as [Hn1 [Hlen Hsn]].
    unfold seed_node in Hsn. unfold Definitions.node_op in Hsn.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | iv | dv | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa
         | dp darg den | sp stok sen | ja jb | ] eqn:Hop;
      try discriminate.
    - (* a literal *)
      injection Hsn as <-.
      unfold nval.
      rewrite (nre_const ctx cost_limit act a_idx n c Hn1 Hlen Hop).
      reflexivity.
    - (* a public input, read live or latched -- either way one value *)
      destruct (pub_in_b iv) eqn:Hpub; [ | discriminate ].
      destruct (list_assoc pv_in (in_key iv)) as [bs |] eqn:Hbs;
        [ | discriminate ].
      injection Hsn as <-.
      rewrite (Hin iv Hpub) in Hbs. injection Hbs as <-.
      unfold nval.
      rewrite (nre_input ctx cost_limit act a_idx n iv Hn1 Hlen Hop).
      cbn [tf_eval_expr]. apply convert_to_list.
    - (* a public output as it stood before the action *)
      destruct dv as [sv | ov]; [ discriminate | ].
      destruct (pub_out_b ov) eqn:Hpub; [ | discriminate ].
      destruct (list_assoc pv_pre (out_key ov)) as [bs |] eqn:Hbs;
        [ | discriminate ].
      injection Hsn as <-.
      rewrite (Hpre ov Hpub) in Hbs. injection Hbs as <-.
      unfold nval.
      rewrite (nre_ovar ctx cost_limit act a_idx n ov Hn1 Hlen Hop).
      cbn [tf_eval_expr]. apply convert_to_list.
  Qed.


  (* ---- THE ONE CONDITIONAL ENTRY: an output's value AFTER the action ----
     A root's cone may contain a sample buffer, whose logical value does move
     in time, so this entry alone is read at a cycle where the root is valid. *)

  Definition seed_roots (act: tfs_action sched)
      (pv_post: list (nat * list bool)) : val_table :=
    flat_map (fun e : @dfg_vars_t s_var o_var * nid_t =>
                match e with
                | (DFG_OVar o, r) =>
                    if pub_out_b o
                    then match list_assoc pv_post (out_key o) with
                         | Some bs => [(r, resize_bits (nsz act r) bs)]
                         | None => []
                         end
                    else []
                | _ => []
                end)
             (var_map (build_dfg ctx act)).

  Definition roots_published (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t)
      (pv_post: list (nat * list bool)) : Prop :=
    forall o r, pub_out_b o = true ->
      List.In (DFG_OVar o, r) (var_map (build_dfg ctx act)) ->
      Definitions.settled_at ctx cost_limit act a_idx ss input r ->
      list_assoc pv_post (out_key o)
        = Some (vect_to_list (nval ctx cost_limit act a_idx ss input (nsz act r) r)).

  Lemma seed_roots_entry (act: tfs_action sched) pv_post n v :
    List.In (n, v) (seed_roots act pv_post) ->
    exists o bs, pub_out_b o = true
              /\ List.In (DFG_OVar o, n) (var_map (build_dfg ctx act))
              /\ list_assoc pv_post (out_key o) = Some bs
              /\ v = resize_bits (nsz act n) bs.
  Proof.
    intro H. unfold seed_roots in H. apply in_flat_map in H.
    destruct H as [[dv r] [Hvm Hin]].
    destruct dv as [sv | o]; [ destruct Hin | ].
    destruct (pub_out_b o) eqn:Hpub; [ | destruct Hin ].
    destruct (list_assoc pv_post (out_key o)) as [bs |] eqn:Hbs;
      [ | destruct Hin ].
    destruct Hin as [He | []]. inversion He; subst.
    exists o, bs. split; [ exact Hpub | split; [ exact Hvm | split; [ exact Hbs | reflexivity ] ] ].
  Qed.

  Lemma seed_roots_sound (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t)
      (pv_post: list (nat * list bool)) :
    roots_published act a_idx ss input pv_post ->
    seed_sound act a_idx ss input (seed_roots act pv_post).
  Proof.
    intros Hrp n v Hget Hst.
    unfold tbl_get in Hget. apply list_assoc_In in Hget.
    destruct (seed_roots_entry act pv_post n v Hget) as [o [bs [Hpub [Hvm [Hbs ->]]]]].
    rewrite (Hrp o n Hpub Hvm Hst) in Hbs. injection Hbs as <-.
    symmetry. apply resize_bits_id. apply vect_to_list_length.
  Qed.


  (* [roots_published] from the run itself: the DFG root really does carry the
     output the spec computes, where it has settled. *)
  Theorem roots_published_of_run (act: tfs_action sched) (a_idx: a_index)
      (sp: src_sys_state) (ss: sched_sys_state)
      (input: input_t) (sinput: sched_input_t)
      (pv_post: list (nat * list bool)) :
    act_idx_aligned ctx cost_limit act a_idx ->
    (forall v, sinput (inl v) = input v) ->
    Definitions.settled ctx cost_limit act a_idx ss sinput ->
    (forall sv, (fst ss).[tf_dfg_s sv] = (fst sp).[sv]) ->
    (forall ov, (snd ss).[ov] = (snd sp).[ov]) ->
    (forall o, pub_out_b o = true ->
       list_assoc pv_post (out_key o)
         = Some (vect_to_list ((snd (spec_run act sp input)).[o]))) ->
    roots_published act a_idx ss sinput pv_post.
  Proof.
    intros Halign Hsi Hst Hs Ho Hpub o r Hpo Hvm [pi [Hpi Hrv]].
    destruct Hst as [Hans [_ [Hargs _]]].
    destruct (dfg_action_semantics ctx cost_limit act a_idx sp ss input sinput
                Halign Hsi
                ltac:(intros n_idx p tok en d av en' Ho1 Ho2 Ho3 Ho4 Hg Hv;
                      exact (Hans n_idx p tok en d av en' Ho1 Ho2 Ho3 Ho4 Hv
                               (IPRProof.guard_pi_holds ctx cost_limit act a_idx
                                  sinput en ss Hg)))
                Hargs Hs Ho) as [_ [Hout _]].
    rewrite (Hpub o Hpo). f_equal.
    unfold nval, node_ref_expr.
    rewrite (IPRProof.pub_eq_root_width ctx cost_limit act o r Hvm).
    f_equal. symmetry.
    exact (Hout o r pi Hvm
             (IPRProof.pi_holds_guard ctx cost_limit act a_idx sinput pi ss Hpi) Hrv).
  Qed.

  (* ---- what the seed holds ---- *)

  Lemma list_assoc_in_some {V} (l: list (nat * V)) (k: nat) (v: V) :
    List.In (k, v) l -> exists w, list_assoc l k = Some w.
  Proof.
    induction l as [| [k1 v1] l IH]; intro H; [ destruct H | ].
    cbn [list_assoc].
    destruct (eq_dec k k1) as [-> | Hne]; [ exists v1; reflexivity | ].
    apply IH. destruct H as [He | H]; [ injection He as -> ->; congruence | exact H ].
  Qed.

  Lemma seed_flat_get (f: nid_t -> option (nid_t * list bool)) (l: list nid_t)
      (n: nid_t) (v: list bool) :
    (forall m k w, f m = Some (k, w) -> k = m) ->
    List.In n l -> f n = Some (n, v) ->
    list_assoc (flat_map (fun m => match f m with
                                   | Some e => [e]
                                   | None => []
                                   end) l) n = Some v.
  Proof.
    intros Hkey. induction l as [| m l IH]; intros Hin Hfn; [ destruct Hin | ].
    cbn [flat_map].
    destruct (f m) as [[k w] |] eqn:Hfm.
    - pose proof (Hkey m k w Hfm) as Hk. subst k.
      cbn [List.app list_assoc].
      destruct (eq_dec n m) as [-> | Hne]; [ congruence | ].
      apply IH; [ destruct Hin as [-> | Hin]; [ congruence | exact Hin ] | exact Hfn ].
    - cbn [List.app].
      apply IH; [ destruct Hin as [-> | Hin]; [ congruence | exact Hin ] | exact Hfn ].
  Qed.

  Lemma seed_local_get (act: tfs_action sched)
      (pv_in pv_pre: list (nat * list bool)) (n: nid_t) (v: list bool) :
    1 <= n -> n < length (graph (build_dfg ctx act)) ->
    seed_node act pv_in pv_pre n = Some (n, v) ->
    tbl_get (seed_local act pv_in pv_pre) n = Some v.
  Proof.
    intros Hn1 Hnlen Hsn. unfold tbl_get, seed_local.
    apply (seed_flat_get (seed_node act pv_in pv_pre) _ n v);
      [ intros m k w Hm; exact (seed_node_key act pv_in pv_pre m k w Hm)
      | apply in_seq; lia
      | exact Hsn ].
  Qed.

  Lemma seed_roots_get (act: tfs_action sched)
      (pv_post: list (nat * list bool)) (o: o_var) (r: nid_t) (bs: list bool) :
    pub_out_b o = true ->
    List.In (DFG_OVar o, r) (var_map (build_dfg ctx act)) ->
    list_assoc pv_post (out_key o) = Some bs ->
    exists w, tbl_get (seed_roots act pv_post) r = Some w.
  Proof.
    intros Hpub Hvm Hbs. unfold tbl_get.
    apply (list_assoc_in_some _ r (resize_bits (nsz act r) bs)).
    unfold seed_roots. apply in_flat_map.
    exists (DFG_OVar o, r). split; [ exact Hvm | ].
    rewrite Hpub, Hbs. left; reflexivity.
  Qed.

  Lemma tbl_get_app_some (t1 t2: val_table) (n: nid_t) (v: list bool) :
    tbl_get t1 n = Some v \/ (exists w, tbl_get t2 n = Some w) ->
    exists w, tbl_get (t1 ++ t2) n = Some w.
  Proof.
    unfold tbl_get.
    induction t1 as [| [k1 v1] t1 IH]; intro H;
      [ destruct H as [H | H]; [ cbn in H; discriminate | exact H ] | ].
    cbn [List.app list_assoc] in H |- *.
    destruct (eq_dec n k1) as [-> | Hne]; [ exists v1; reflexivity | ].
    exact (IH H).
  Qed.

  (* ---- the seed of the taint saturation is filled ---- *)

  Lemma trivially_public_filled (act: tfs_action sched) (seed: val_table)
      (pv_in pv_pre: list (nat * list bool)) (n: nid_t) :
    (forall v, pub_in_b v = true -> exists bs, list_assoc pv_in (in_key v) = Some bs) ->
    (forall m w, tbl_get (seed_local act pv_in pv_pre) m = Some w ->
       tbl_get seed m = Some w) ->
    List.In n (Taint.trivially_public ctx (build_dfg ctx act)) ->
    tbl_has (ptable act seed 1) n.
  Proof.
    intros Htot Hsub Hin.
    unfold Taint.trivially_public in Hin. apply filter_In in Hin.
    destruct Hin as [Hseq Hop]. apply in_seq in Hseq. destruct Hseq as [Hn1 Hn2].
    assert (Hnlen : n < length (graph (build_dfg ctx act))) by lia.
    revert Hop.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | iv | dv | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa
         | dp darg den | sp stok sen | ja jb | ] eqn:Hop; intro Hfil;
      try discriminate.
    - (* a literal: one round fills it from nothing *)
      cbn [ptable]. apply (pround_fills act _ n Hn1 Hnlen). left.
      exists (vect_to_list (Bits.of_nat (nsz act n) c)).
      unfold pstep, Definitions.node_op. rewrite Hop. reflexivity.
    - (* a public input: the seed holds it *)
      assert (Hpub : pub_in_b iv = true)
        by (unfold pub_in_b; destruct (tfs_spec_inputs_class ctx iv);
            [ reflexivity | discriminate Hfil ]).
      destruct (Htot iv Hpub) as [bs Hbs].
      exists (resize_bits (nsz act n) bs).
      apply (ptable_get act seed 0 1 n _ ltac:(lia)).
      cbn [ptable]. apply Hsub.
      apply (seed_local_get act pv_in pv_pre n _ Hn1 Hnlen).
      unfold seed_node, Definitions.node_op. rewrite Hop, Hpub, Hbs. reflexivity.
  Qed.

  Lemma public_dsts_filled (act: tfs_action sched) (seed: val_table)
      (pv_post: list (nat * list bool)) (n: nid_t) :
    (forall o, pub_out_b o = true -> exists bs, list_assoc pv_post (out_key o) = Some bs) ->
    (forall m w, tbl_get (seed_roots act pv_post) m = Some w ->
       exists w', tbl_get seed m = Some w') ->
    List.In n (Taint.public_dsts ctx (build_dfg ctx act)) ->
    tbl_has (ptable act seed 1) n.
  Proof.
    intros Htot Hsub Hin.
    unfold Taint.public_dsts in Hin.
    apply in_map_iff in Hin. destruct Hin as [[dv r] [Hsnd Hfil]].
    cbn [snd] in Hsnd. subst r.
    apply filter_In in Hfil. destruct Hfil as [Hvm Hcls].
    destruct dv as [sv | ov]; [ discriminate Hcls | ].
    assert (Hpub : pub_out_b ov = true)
      by (unfold pub_out_b; destruct (tfs_spec_outputs_class ctx ov);
          [ reflexivity | discriminate Hcls ]).
    destruct (Htot ov Hpub) as [bs Hbs].
    destruct (seed_roots_get act pv_post ov n bs Hpub Hvm Hbs) as [w Hw].
    destruct (Hsub n w Hw) as [w' Hw'].
    exists w'. apply (ptable_get act seed 0 1 n _ ltac:(lia)). exact Hw'.
  Qed.

  Definition sat_rounds (act: tfs_action sched) : nat :=
    1 + length (graph (build_dfg ctx act))
        * length (Taint.uncond_instances ctx (build_dfg ctx act)).

  Lemma untainted_roots_filled (act: tfs_action sched) (seed: val_table)
      (pv_in pv_pre pv_post: list (nat * list bool)) :
    Definitions.decl_in_range ctx cost_limit act ->
    (forall v, pub_in_b v = true -> exists bs, list_assoc pv_in (in_key v) = Some bs) ->
    (forall o, pub_out_b o = true -> exists bs, list_assoc pv_post (out_key o) = Some bs) ->
    (forall m w, tbl_get (seed_local act pv_in pv_pre) m = Some w ->
       tbl_get seed m = Some w) ->
    (forall m w, tbl_get (seed_roots act pv_post) m = Some w ->
       exists w', tbl_get seed m = Some w') ->
    forall n, List.In n (Taint.untainted_roots ctx (build_dfg ctx act)) ->
      tbl_has (ptable act seed (sat_rounds act)) n.
  Proof.
    intros Hrng Hin_tot Hout_tot Hsub1 Hsub2 n Hin.
    unfold Taint.untainted_roots in Hin.
    exact (saturate_filled act seed Hrng
             (length (graph (build_dfg ctx act))) 1 _
             ltac:(intros x Hx; apply in_app_or in Hx;
                   destruct Hx as [Hx | Hx];
                   [ exact (public_dsts_filled act seed pv_post x Hout_tot Hsub2 Hx)
                   | exact (trivially_public_filled act seed pv_in pv_pre x
                              Hin_tot Hsub1 Hx) ])
             n Hin).
  Qed.

  (* An op the evaluator knows: the round trip's own nodes carry no value a
     published table speaks about, so an untainted node that is not a
     declassified root must not be one of them. *)
  Definition pstep_knows (act: tfs_action sched) (n: nid_t) : bool :=
    match Definitions.node_op ctx cost_limit act n with
    | DFG_Stall _ _ | DFG_Drive _ _ _ | DFG_Sample _ _ _ | DFG_Join _ _
    | DFG_Empty => false
    | _ => true
    end.

  (* THE COVERAGE: the table holds every untainted node, so it holds every
     selector the analysis did not call critical. *)
  Theorem untainted_filled (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t) (seed: val_table)
      (pv_in pv_pre pv_post: list (nat * list bool)) :
    seed_sound act a_idx ss input seed ->
    decl_guards_sized act ->
    (forall i, List.In i (decl_instances (build_dfg ctx act)) ->
       instance_extracts ctx cost_limit act a_idx i) ->
    (forall i, List.In i (decl_instances (build_dfg ctx act)) ->
       Definitions.instance_lifts ctx cost_limit act a_idx i) ->
    Definitions.decl_in_range ctx cost_limit act ->
    (forall v, pub_in_b v = true ->
       exists bs, list_assoc pv_in (in_key v) = Some bs) ->
    (forall o, pub_out_b o = true ->
       exists bs, list_assoc pv_pre (out_key o) = Some bs) ->
    (forall o, pub_out_b o = true ->
       exists bs, list_assoc pv_post (out_key o) = Some bs) ->
    (forall m w, tbl_get (seed_local act pv_in pv_pre) m = Some w ->
       tbl_get seed m = Some w) ->
    (forall m w, tbl_get (seed_roots act pv_post) m = Some w ->
       exists w', tbl_get seed m = Some w') ->
    (forall m, 1 <= m -> m < length (graph (build_dfg ctx act)) ->
       ~ List.In m (get_tainted ctx (build_dfg ctx act)) ->
       ~ List.In m (Taint.untainted_roots ctx (build_dfg ctx act)) ->
       pstep_knows act m = true) ->
    forall n, 1 <= n -> n < length (graph (build_dfg ctx act)) ->
      ~ List.In n (get_tainted ctx (build_dfg ctx act)) ->
      Definitions.settled_at ctx cost_limit act a_idx ss input n ->
      tbl_has (ptable act seed (n + sat_rounds act)) n.
  Proof.
    intros Hseed Hgsz Hinst Hlift Hrng Hin_tot Hpre_tot Hout_tot Hsub1 Hsub2
      Hknows n.
    induction n as [n IH] using (well_founded_induction lt_wf).
    intros Hn1 Hnlen Hnt Hst.
    pose proof (ptable_sound act a_idx ss input seed Hseed Hgsz Hinst Hlift)
      as Hsnd.
    destruct (Taint.mem_nid n (Taint.untainted_roots ctx (build_dfg ctx act)))
      eqn:Hmem.
    { (* a declassified root: the saturation reaches it *)
      destruct (untainted_roots_filled act seed pv_in pv_pre pv_post Hrng
                  Hin_tot Hout_tot Hsub1 Hsub2 n
                  (IPRProof.mem_nid_In n _ Hmem)) as [v Hv].
      exists v. apply (ptable_get act seed (sat_rounds act)); [ lia | exact Hv ]. }
    assert (Hnr : ~ List.In n (Taint.untainted_roots ctx (build_dfg ctx act)))
      by (exact (IPRProof.mem_nid_not_In n _ Hmem)).
    assert (Hnode_in : List.In (nth n (graph (build_dfg ctx act))
                                  {| nid := 0; op := DFG_Empty; sz := 0 |})
                         (graph (build_dfg ctx act)))
      by (apply nth_In; exact Hnlen).
    pose proof (node_nid_at ctx cost_limit act n Hnlen) as Hnid.
    pose proof (wfg_build_dfg ctx cost_limit act _ Hnode_in) as Hfg.
    unfold node_args_sz in Hfg.
    assert (Hnt' : ~ List.In (nid (nth n (graph (build_dfg ctx act))
                                     {| nid := 0; op := DFG_Empty; sz := 0 |}))
                     (get_tainted ctx (build_dfg ctx act)))
      by (rewrite Hnid; exact Hnt).
    assert (Hnr' : ~ List.In (nid (nth n (graph (build_dfg ctx act))
                                     {| nid := 0; op := DFG_Empty; sz := 0 |}))
                     (Taint.untainted_roots ctx (build_dfg ctx act)))
      by (rewrite Hnid; exact Hnr).
    pose proof (Hknows n Hn1 Hnlen Hnt Hnr) as Hkn.
    unfold pstep_knows, Definitions.node_op in Hkn.
    (* every argument is filled by the round before this one *)
    set (r := pred n + sat_rounds act) in *.
    assert (Hround : n + sat_rounds act = S r) by (unfold r; lia).
    assert (Harg : forall x,
              List.In x (get_args ctx (nth n (graph (build_dfg ctx act))
                                         {| nid := 0; op := DFG_Empty; sz := 0 |})) ->
              Definitions.settled_at ctx cost_limit act a_idx ss input x ->
              exists w, tbl_get (ptable act seed r) x = Some w).
    { intros x Hx Hstx.
      destruct (node_args_range ctx cost_limit act n Hn1 Hnlen x Hx) as [Hx1 Hxn].
      assert (Hxt : ~ List.In x (get_tainted ctx (build_dfg ctx act)))
        by (exact (IPRProof.arg_untainted ctx cost_limit act n x Hnlen Hnt Hnr Hx)).
      destruct (IH x Hxn Hx1 ltac:(lia) Hxt Hstx) as [w Hw].
      exists w. apply (ptable_get act seed (x + sat_rounds act));
        [ unfold r; lia | exact Hw ]. }
    rewrite Hround.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | iv | dv | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa
         | dp darg den | sp stok sen | ja jb | ] eqn:Hop;
      try discriminate Hkn.
    - (* a literal *)
      cbn [ptable]. apply (pround_fills act _ n Hn1 Hnlen). left.
      exists (vect_to_list (Bits.of_nat (nsz act n) c)).
      unfold pstep, Definitions.node_op. rewrite Hop. reflexivity.
    - (* an input: a secret one would be tainted *)
      assert (Hpub : pub_in_b iv = true).
      { unfold pub_in_b. destruct (tfs_spec_inputs_class ctx iv) eqn:Hcls;
          [ reflexivity | exfalso ].
        exact (Hnt' (IPRProof.input_secret_tainted ctx cost_limit act _ iv
                       Hnode_in Hop Hcls Hnr')). }
      destruct (Hin_tot iv Hpub) as [bs Hbs].
      exists (resize_bits (nsz act n) bs).
      apply (ptable_get act seed 0); [ lia | ]. cbn [ptable]. apply Hsub1.
      apply (seed_local_get act pv_in pv_pre n _ Hn1 Hnlen).
      unfold seed_node, Definitions.node_op. rewrite Hop, Hpub, Hbs. reflexivity.
    - (* a variable read: the state is secret, an output takes its class *)
      destruct dv as [sv | ov].
      { exfalso.
        exact (Hnt' (IPRProof.svar_tainted ctx cost_limit act _ sv
                       Hnode_in Hop Hnr')). }
      assert (Hpub : pub_out_b ov = true).
      { unfold pub_out_b. destruct (tfs_spec_outputs_class ctx ov) eqn:Hcls;
          [ reflexivity | exfalso ].
        exact (Hnt' (IPRProof.ovar_secret_tainted ctx cost_limit act _ ov
                       Hnode_in Hop Hcls Hnr')). }
      destruct (Hpre_tot ov Hpub) as [bs Hbs].
      exists (resize_bits (nsz act n) bs).
      apply (ptable_get act seed 0); [ lia | ]. cbn [ptable]. apply Hsub1.
      apply (seed_local_get act pv_in pv_pre n _ Hn1 Hnlen).
      unfold seed_node, Definitions.node_op. rewrite Hop, Hpub, Hbs. reflexivity.
    - (* a unary operation *)
      destruct (Harg arg ltac:(unfold get_args; rewrite Hop; left; reflexivity)
                  ltac:(destruct Hst as [pi [Hpi Hv]]; exists pi; split;
                        [ exact Hpi | ];
                        exact (nrv_peel_unary ctx cost_limit act a_idx n uop arg
                                 pi ss input
                                 ltac:(unfold Definitions.node_op; rewrite Hop;
                                       reflexivity)
                                 (proj1 (node_args_range ctx cost_limit act n Hn1
                                           Hnlen arg
                                           ltac:(unfold get_args; rewrite Hop;
                                                 left; reflexivity)))
                                 Hnlen Hv)))
        as [la Hla].
      cbn [ptable]. apply (pround_fills act _ n Hn1 Hnlen). left.
      unfold pstep, Definitions.node_op. rewrite Hop, Hla.
      destruct uop as [| source_size];
        [ exists (vect_to_list (Bits.neg (bits_of_list (nsz act n) la)))
        | exists (vect_to_list (convert (szB := nsz act n)
                                  (bits_of_list source_size la))) ];
        reflexivity.
    - (* a binary operation *)
      assert (Hpeel : Definitions.settled_at ctx cost_limit act a_idx ss input a1
                      /\ Definitions.settled_at ctx cost_limit act a_idx ss input a2).
      { destruct Hst as [pi [Hpi Hv]].
        destruct (node_args_range ctx cost_limit act n Hn1 Hnlen a1
                    ltac:(unfold get_args; rewrite Hop; left; reflexivity))
          as [Ha11 _].
        destruct (node_args_range ctx cost_limit act n Hn1 Hnlen a2
                    ltac:(unfold get_args; rewrite Hop; right; left; reflexivity))
          as [Ha21 _].
        destruct (nrv_peel_binary ctx cost_limit act a_idx n bop a1 a2 pi ss input
                    ltac:(unfold Definitions.node_op; rewrite Hop; reflexivity)
                    Ha11 Ha21 Hnlen Hv) as [Hv1 Hv2].
        split; [ exists pi; split; [ exact Hpi | exact Hv1 ]
               | exists pi; split; [ exact Hpi | exact Hv2 ] ]. }
      destruct (Harg a1 ltac:(unfold get_args; rewrite Hop; left; reflexivity)
                  (proj1 Hpeel)) as [la Hla].
      destruct (Harg a2 ltac:(unfold get_args; rewrite Hop; right; left; reflexivity)
                  (proj2 Hpeel)) as [lb Hlb].
      cbn [ptable]. apply (pround_fills act _ n Hn1 Hnlen). left.
      unfold pstep, Definitions.node_op. rewrite Hop, Hla, Hlb.
      eexists. reflexivity.
    - (* a resize *)
      destruct (Harg arg ltac:(unfold get_args; rewrite Hop; left; reflexivity)
                  ltac:(destruct Hst as [pi [Hpi Hv]]; exists pi; split;
                        [ exact Hpi | ];
                        exact (nrv_peel_resize ctx cost_limit act a_idx n arg
                                 pi ss input
                                 ltac:(unfold Definitions.node_op; rewrite Hop;
                                       reflexivity)
                                 (proj1 (node_args_range ctx cost_limit act n Hn1
                                           Hnlen arg
                                           ltac:(unfold get_args; rewrite Hop;
                                                 left; reflexivity)))
                                 Hnlen Hv)))
        as [la Hla].
      cbn [ptable]. apply (pround_fills act _ n Hn1 Hnlen). left.
      unfold pstep, Definitions.node_op. rewrite Hop, Hla.
      eexists. reflexivity.
    - (* a phi: the condition names the arm, and the table holds both *)
      destruct (node_args_range ctx cost_limit act n Hn1 Hnlen cnd
                  ltac:(unfold get_args; rewrite Hop; left; reflexivity))
        as [Hc1 Hc2].
      destruct (node_args_range ctx cost_limit act n Hn1 Hnlen tid
                  ltac:(unfold get_args; rewrite Hop; right; left; reflexivity))
        as [Ht1 Ht2].
      destruct (node_args_range ctx cost_limit act n Hn1 Hnlen eid
                  ltac:(unfold get_args; rewrite Hop; right; right; left; reflexivity))
        as [He1 He2].
      assert (Hopn : Definitions.node_op ctx cost_limit act n = DFG_Phi cnd tid eid)
        by (unfold Definitions.node_op; rewrite Hop; reflexivity).
      destruct (IPRProof.phi_args_settled ctx cost_limit act a_idx ss input
                  n cnd tid eid Hopn Hc1 Ht1 He1 Hnlen Hst) as [Hstc [Hstt Hste]].
      destruct (Harg cnd ltac:(unfold get_args; rewrite Hop; left; reflexivity)
                  Hstc) as [lc Hlc].
      (* the condition's entry is its one bit, because the table is sound *)
      pose proof (Hsnd r cnd lc Hlc Hstc) as Hcv.
      destruct Hfg as [Hfc [Hft Hfe]].
      destruct (wsz_node_sz ctx cost_limit act cnd 1 Hfc) as [_ Hcsz].
      rewrite Hcsz in Hcv.
      assert (Hlen1 : length lc = 1)
        by (rewrite <- Hcv; apply vect_to_list_length).
      destruct lc as [| bb lc0]; [ cbn in Hlen1; lia | ].
      destruct lc0 as [| ? ?]; [ | cbn in Hlen1; lia ].
      assert (Hcb : nval ctx cost_limit act a_idx ss input 1 cnd
                    = Definitions.bit_of bb)
        by (apply (vect_to_list_inj bool 1);
            rewrite Hcv, bit_of_to_list; reflexivity).
      cbn [ptable]. apply (pround_fills act _ n Hn1 Hnlen). left.
      unfold pstep, Definitions.node_op. rewrite Hop, Hlc.
      destruct bb.
      + destruct (Harg tid ltac:(unfold get_args; rewrite Hop; right; left;
                                 reflexivity)
                    (Hstt ltac:(unfold nval in Hcb; rewrite Hcb;
                                exact ones1_neq_zero))) as [lt Hlt].
        exists lt. exact Hlt.
      + destruct (Harg eid ltac:(unfold get_args; rewrite Hop; right; right; left;
                                 reflexivity)
                    (Hste ltac:(unfold nval in Hcb; exact Hcb))) as [le Hle].
        exists le. exact Hle.
  Qed.

  Lemma seed_sound_app (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t) (t1 t2: val_table) :
    seed_sound act a_idx ss input t1 ->
    seed_sound act a_idx ss input t2 ->
    seed_sound act a_idx ss input (t1 ++ t2).
  Proof.
    intros H1 H2 n v Hget Hst. unfold tbl_get in Hget.
    destruct (list_assoc_app t1 t2 n v Hget) as [Hg | Hg];
      [ exact (H1 n v Hg Hst) | exact (H2 n v Hg Hst) ].
  Qed.

  (* ================================================================= *)
  (* THE ATTACKER'S VALUES, over the published tables alone.             *)
  (* ================================================================= *)

  Definition pub_seed (act: tfs_action sched)
      (pv_in pv_pre pv_post: list (nat * list bool)) : val_table :=
    seed_local act pv_in pv_pre ++ seed_roots act pv_post.

  (* A forward chain descends node ids, and a declassification chain is the
     taint saturation's own, so this many rounds fill everything either
     reaches. *)
  Definition pub_rounds (act: tfs_action sched) : nat :=
    length (graph (build_dfg ctx act)) + sat_rounds act.

  Definition pub_vals (act: tfs_action sched)
      (pv_in pv_pre pv_post: list (nat * list bool)) (n: nid_t)
    : option (list bool) :=
    tbl_get (ptable act (pub_seed act pv_in pv_pre pv_post) (pub_rounds act)) n.

  Lemma pub_seed_sound (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t)
      (pv_in pv_pre pv_post: list (nat * list bool)) :
    in_published input pv_in ->
    pre_published ss pv_pre ->
    roots_published act a_idx ss input pv_post ->
    seed_sound act a_idx ss input (pub_seed act pv_in pv_pre pv_post).
  Proof.
    intros Hin Hpre Hroots. unfold pub_seed.
    exact (seed_sound_app act a_idx ss input _ _
             (seed_local_sound act a_idx ss input pv_in pv_pre Hin Hpre)
             (seed_roots_sound act a_idx ss input pv_post Hroots)).
  Qed.

  Theorem pub_vals_sound (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t)
      (pv_in pv_pre pv_post: list (nat * list bool)) :
    in_published input pv_in ->
    pre_published ss pv_pre ->
    roots_published act a_idx ss input pv_post ->
    decl_guards_sized act ->
    (forall i, List.In i (decl_instances (build_dfg ctx act)) ->
       instance_extracts ctx cost_limit act a_idx i) ->
    (forall i, List.In i (decl_instances (build_dfg ctx act)) ->
       Definitions.instance_lifts ctx cost_limit act a_idx i) ->
    Definitions.vals_sound ctx cost_limit act a_idx
      (pub_vals act pv_in pv_pre pv_post) ss input.
  Proof.
    intros Hin Hpre Hroots Hgsz Hinst Hlift n v pi Hval Hpi Hrv.
    exact (ptable_sound act a_idx ss input _
             (pub_seed_sound act a_idx ss input pv_in pv_pre pv_post
                Hin Hpre Hroots)
             Hgsz Hinst Hlift (pub_rounds act) n v Hval
             (ex_intro _ pi (conj Hpi Hrv))).
  Qed.

  (* THE DESIGN CONDITION ON THE SELECTORS: a phi the analysis does not call
     critical reads a condition the attacker can recover.  A tainted condition
     is recovered only through a GUARDED declassification, which this rules
     out, so the condition is an untainted one -- and those the table holds. *)
  Definition selectors_known (act: tfs_action sched) : Prop :=
    forall n c t e,
      Definitions.node_op ctx cost_limit act n = DFG_Phi c t e ->
      Taint.mem_nid c (get_tainted ctx (build_dfg ctx act)) = true ->
      Taint.gfacts_of (decl_facts ctx (build_dfg ctx act)) c = [].

  Theorem pub_selectors_extractable (act: tfs_action sched) (a_idx: a_index)
      (ss: sched_sys_state) (input: sched_input_t)
      (pv_in pv_pre pv_post: list (nat * list bool)) :
    in_published input pv_in ->
    pre_published ss pv_pre ->
    roots_published act a_idx ss input pv_post ->
    decl_guards_sized act ->
    (forall i, List.In i (decl_instances (build_dfg ctx act)) ->
       instance_extracts ctx cost_limit act a_idx i) ->
    (forall i, List.In i (decl_instances (build_dfg ctx act)) ->
       Definitions.instance_lifts ctx cost_limit act a_idx i) ->
    Definitions.decl_in_range ctx cost_limit act ->
    (forall v, pub_in_b v = true ->
       exists bs, list_assoc pv_in (in_key v) = Some bs) ->
    (forall o, pub_out_b o = true ->
       exists bs, list_assoc pv_pre (out_key o) = Some bs) ->
    (forall o, pub_out_b o = true ->
       exists bs, list_assoc pv_post (out_key o) = Some bs) ->
    (forall m, 1 <= m -> m < length (graph (build_dfg ctx act)) ->
       ~ List.In m (get_tainted ctx (build_dfg ctx act)) ->
       ~ List.In m (Taint.untainted_roots ctx (build_dfg ctx act)) ->
       pstep_knows act m = true) ->
    selectors_known act ->
    Definitions.selectors_extractable ctx cost_limit act a_idx
      (pub_vals act pv_in pv_pre pv_post) ss input.
  Proof.
    intros Hin Hpre Hroots Hgsz Hinst Hlift Hrng Hin_tot Hpre_tot Hout_tot
      Hknows Hsk n c t e pi Hop Hcrit Hpi Hrv.
    pose proof (pub_seed_sound act a_idx ss input pv_in pv_pre pv_post
                  Hin Hpre Hroots) as Hseed.
    (* the condition is untainted: a tainted one would have no fact to
       de-criticalise it *)
    assert (Hct : ~ List.In c (get_tainted ctx (build_dfg ctx act))).
    { destruct (Taint.mem_nid c (get_tainted ctx (build_dfg ctx act))) eqn:Hmc;
        [ | exact (IPRProof.mem_nid_not_In c _ Hmc) ].
      exfalso. unfold phi_crit in Hcrit. rewrite Hmc in Hcrit.
      cbn [andb] in Hcrit. apply Bool.negb_false_iff in Hcrit.
      unfold Taint.declassified_at in Hcrit.
      rewrite (Hsk n c t e Hop Hmc) in Hcrit. cbn [existsb] in Hcrit.
      discriminate. }
    (* and it is a node of the graph *)
    assert (Hnlen : n < length (graph (build_dfg ctx act))).
    { destruct (Nat.lt_ge_cases n (length (graph (build_dfg ctx act))))
        as [H | H]; [ exact H | exfalso ].
      unfold Definitions.node_op in Hop. rewrite nth_overflow in Hop by lia.
      discriminate. }
    assert (Hnode_in : List.In (nth n (graph (build_dfg ctx act))
                                  {| nid := 0; op := DFG_Empty; sz := 0 |})
                         (graph (build_dfg ctx act)))
      by (apply nth_In; exact Hnlen).
    assert (Hcarg : List.In c (get_args ctx (nth n (graph (build_dfg ctx act))
                                              {| nid := 0; op := DFG_Empty; sz := 0 |})))
      by (unfold get_args, Definitions.node_op in Hop |- *;
          rewrite Hop; left; reflexivity).
    pose proof (build_dfg_args_pos ctx cost_limit act) as [_ [Hargpos _]].
    assert (Hc1 : 1 <= c) by (exact (Hargpos _ Hnode_in c Hcarg)).
    pose proof (args_lt_fwd ctx cost_limit act _ Hnode_in c Hcarg) as Hcn.
    rewrite (node_nid_at ctx cost_limit act n Hnlen) in Hcn.
    (* so the table holds it, and soundness says its entry is its one bit *)
    destruct (untainted_filled act a_idx ss input
                (pub_seed act pv_in pv_pre pv_post) pv_in pv_pre pv_post
                Hseed Hgsz Hinst Hlift Hrng Hin_tot Hpre_tot Hout_tot
                ltac:(intros m w Hm; unfold pub_seed, tbl_get in Hm |- *;
                      apply list_assoc_app_l; exact Hm)
                ltac:(intros m w Hm; unfold pub_seed;
                      apply (tbl_get_app_some _ _ m w); right;
                      exists w; exact Hm)
                Hknows c Hc1 ltac:(lia) Hct
                (ex_intro _ pi (conj Hpi Hrv))) as [w Hw].
    assert (Hwv : vect_to_list (nval ctx cost_limit act a_idx ss input
                                  (nsz act c) c) = w).
    { exact (ptable_sound act a_idx ss input _ Hseed Hgsz Hinst Hlift
               (c + sat_rounds act) c w Hw
               (ex_intro _ pi (conj Hpi Hrv))). }
    pose proof (wfg_build_dfg ctx cost_limit act _ Hnode_in) as Hfg.
    unfold node_args_sz, Definitions.node_op in Hop, Hfg.
    rewrite Hop in Hfg. destruct Hfg as [Hfc _].
    destruct (wsz_node_sz ctx cost_limit act c 1 Hfc) as [_ Hcsz].
    rewrite Hcsz in Hwv.
    assert (Hlen1 : length w = 1)
      by (rewrite <- Hwv; apply vect_to_list_length).
    destruct w as [| bb w0]; [ cbn in Hlen1; lia | ].
    destruct w0 as [| ? ?]; [ | cbn in Hlen1; lia ].
    exists bb. unfold pub_vals.
    apply (ptable_get act (pub_seed act pv_in pv_pre pv_post)
             (c + sat_rounds act)); [ unfold pub_rounds; lia | exact Hw ].
  Qed.


  (* WHAT THE PUBLIC INTERFACE ASKS OF A DESIGN AND ITS TABLES: the standard
     side conditions, the tables being this run's published data, the four
     obligations the rule library discharges per declassification instance, and
     the two conditions that make the attacker's evaluator total where the
     analysis relies on it. *)
  Definition clock_readable (act: tfs_action sched) (a_idx: a_index)
      (sp0: src_sys_state) (ss0: sched_sys_state)
      (input: input_t) (resp: nat -> resp_val)
      (pv_in pv_pre pv_post: list (nat * list bool)) : Prop :=
    act_idx_aligned ctx cost_limit act a_idx
    /\ 1 < length (graph (build_dfg ctx act))
    /\ start_rel ctx cost_limit sp0 ss0
    /\ Definitions.ip_contract ctx cost_limit act input resp ss0
    (* the tables ARE this run's published data *)
    /\ (forall v, pub_in_b v = true ->
          list_assoc pv_in (in_key v) = Some (vect_to_list (input v)))
    /\ (forall o, pub_out_b o = true ->
          list_assoc pv_pre (out_key o) = Some (vect_to_list ((snd sp0).[o])))
    /\ (forall o, pub_out_b o = true ->
          list_assoc pv_post (out_key o)
            = Some (vect_to_list ((snd (spec_run act sp0 input)).[o])))
    (* the rule library's obligations *)
    /\ decl_guards_sized act
    /\ (forall i, List.In i (decl_instances (build_dfg ctx act)) ->
          instance_extracts ctx cost_limit act a_idx i)
    /\ (forall i, List.In i (decl_instances (build_dfg ctx act)) ->
          Definitions.instance_lifts ctx cost_limit act a_idx i)
    /\ Definitions.decl_in_range ctx cost_limit act
    (* the design is one the clock can read *)
    /\ (forall m, 1 <= m -> m < length (graph (build_dfg ctx act)) ->
          ~ List.In m (get_tainted ctx (build_dfg ctx act)) ->
          ~ List.In m (Taint.untainted_roots ctx (build_dfg ctx act)) ->
          pstep_knows act m = true)
    /\ selectors_known act.

  (* ================================================================= *)
  (* THE HEADLINE, OVER THE PUBLISHED TABLES.                            *)
  (* The cycle count the design takes is a function of the action, its    *)
  (* slot, and three tables of bits: the action's public inputs, and its  *)
  (* public outputs before and after.  No state, no secret input and no   *)
  (* IP answer appears among the arguments, so none can reach the result. *)
  (* ================================================================= *)
  Theorem L_over_tables (act: tfs_action sched) (a_idx: a_index)
      (sp0: src_sys_state) (ss0: sched_sys_state)
      (input: input_t) (resp: nat -> resp_val)
      (pv_in pv_pre pv_post: list (nat * list bool)) :
    clock_readable act a_idx sp0 ss0 input resp pv_in pv_pre pv_post ->
    Definitions.L ctx cost_limit act input resp ss0
    = Definitions.L_pub ctx cost_limit act a_idx
        (pub_vals act pv_in pv_pre pv_post).
  Proof.
    intros [Halign [Hlen [Hstart [Hipc [Hpin [Hppre [Hppost [Hgsz [Hinst
      [Hlift [Hrng [Hknows Hsk]]]]]]]]]]]].
    pose proof Hstart as Hsr. destruct Hsr as [Hoo [Hmm Hzz]].
    assert (Hin_k : forall k,
              in_published (sched_input ctx cost_limit input (resp k)) pv_in)
      by (intros k v Hpub; exact (Hpin v Hpub)).
    assert (Hpre_k : forall k,
              (forall i, 1 <= i <= k ->
                 ~ done_set ctx cost_limit (run_n ctx cost_limit i act input resp ss0)) ->
              pre_published (run_n ctx cost_limit k act input resp ss0) pv_pre).
    { intros k Hnd o Hpub.
      rewrite (run_preserves_ovar ctx cost_limit act input resp ss0 k Hnd o).
      rewrite Hoo. exact (Hppre o Hpub). }
    assert (Htot_in : forall v, pub_in_b v = true ->
              exists bs, list_assoc pv_in (in_key v) = Some bs)
      by (intros v Hpub; exists (vect_to_list (input v)); exact (Hpin v Hpub)).
    assert (Htot_pre : forall o, pub_out_b o = true ->
              exists bs, list_assoc pv_pre (out_key o) = Some bs)
      by (intros o Hpub; exists (vect_to_list ((snd sp0).[o])); exact (Hppre o Hpub)).
    assert (Htot_post : forall o, pub_out_b o = true ->
              exists bs, list_assoc pv_post (out_key o) = Some bs)
      by (intros o Hpub;
          exists (vect_to_list ((snd (spec_run act sp0 input)).[o]));
          exact (Hppost o Hpub)).
    assert (Hroots_k : forall k,
              (forall i, 1 <= i <= k ->
                 ~ done_set ctx cost_limit (run_n ctx cost_limit i act input resp ss0)) ->
              roots_published act a_idx
                (run_n ctx cost_limit k act input resp ss0)
                (sched_input ctx cost_limit input (resp k)) pv_post).
    { intros k Hnd.
      apply (roots_published_of_run act a_idx sp0
               (run_n ctx cost_limit k act input resp ss0) input
               (sched_input ctx cost_limit input (resp k)) pv_post Halign
               ltac:(intro v; reflexivity)
               (settled_run ctx cost_limit act a_idx input resp ss0 k Halign Hlen
                  Hzz Hnd Hipc));
        [ intro sv | intro ov | exact Hppost ].
      - rewrite (run_preserves_svar ctx cost_limit act input resp ss0 k Hnd sv).
        rewrite <- Hmm, getenv_maps_from. reflexivity.
      - rewrite (run_preserves_ovar ctx cost_limit act input resp ss0 k Hnd ov).
        rewrite Hoo. reflexivity. }
    exact (IPRProof.L_pub_correct ctx cost_limit act a_idx
             (pub_vals act pv_in pv_pre pv_post) input resp ss0
             Halign Hzz
             (fun k Hnd => pub_selectors_extractable act a_idx
                 (run_n ctx cost_limit k act input resp ss0)
                 (sched_input ctx cost_limit input (resp k))
                 pv_in pv_pre pv_post (Hin_k k) (Hpre_k k Hnd) (Hroots_k k Hnd)
                 Hgsz Hinst Hlift Hrng Htot_in Htot_pre Htot_post Hknows Hsk)
             (fun k Hnd => pub_vals_sound act a_idx
                 (run_n ctx cost_limit k act input resp ss0)
                 (sched_input ctx cost_limit input (resp k))
                 pv_in pv_pre pv_post (Hin_k k) (Hpre_k k Hnd) (Hroots_k k Hnd)
                 Hgsz Hinst Hlift)).
  Qed.

  (* ---- and the two statements a reader actually wants, over [L_pub] ---- *)

  (* THE DESIGN COMPLETES AT THE PUBLIC CYCLE: done there, and at no cycle
     before it. *)
  Corollary latency_over_tables (act: tfs_action sched) (a_idx: a_index)
      (sp0: src_sys_state) (ss0: sched_sys_state)
      (input: input_t) (resp: nat -> resp_val)
      (pv_in pv_pre pv_post: list (nat * list bool)) :
    clock_readable act a_idx sp0 ss0 input resp pv_in pv_pre pv_post ->
    Definitions.first_done ctx cost_limit act input resp ss0
      (Definitions.L_pub ctx cost_limit act a_idx
         (pub_vals act pv_in pv_pre pv_post)).
  Proof.
    intro Hcr.
    rewrite <- (L_over_tables act a_idx sp0 ss0 input resp
                  pv_in pv_pre pv_post Hcr).
    exact (IPRProof.L_first_done ctx cost_limit act sp0 ss0 input resp
             (proj1 (proj2 (proj2 Hcr)))).
  Qed.

  (* THE EMULATOR, OVER THE PUBLISHED TABLES ALONE.  Every cycle up to the
     cycle the attacker computes, the outputs are what its own two snapshots
     say: nothing on the right-hand side is data a run keeps to itself. *)
  Corollary emulator_correct_over_tables (act: tfs_action sched) (a_idx: a_index)
      (sp0: src_sys_state) (ss0: sched_sys_state)
      (input: input_t) (resp: nat -> resp_val)
      (pv_in pv_pre pv_post: list (nat * list bool)) :
    clock_readable act a_idx sp0 ss0 input resp pv_in pv_pre pv_post ->
    forall k, k <= Definitions.L_pub ctx cost_limit act a_idx
                     (pub_vals act pv_in pv_pre pv_post) ->
      forall ov, (snd (run_n ctx cost_limit k act input resp ss0)).[ov]
               = Definitions.emulate ctx (snd sp0)
                   (snd (spec_run act sp0 input))
                   (Definitions.L_pub ctx cost_limit act a_idx
                      (pub_vals act pv_in pv_pre pv_post)) k ov.
  Proof.
    intro Hcr.
    rewrite <- (L_over_tables act a_idx sp0 ss0 input resp
                  pv_in pv_pre pv_post Hcr).
    exact (IPRProof.emulator_correct_L ctx cost_limit act sp0 ss0 input resp
             (proj1 (proj2 (proj2 Hcr)))
             (proj1 (proj2 (proj2 (proj2 Hcr))))).
  Qed.

End Extract.
