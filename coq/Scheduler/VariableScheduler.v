Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.
Require Koika.BitsToLists.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Trustformer.Utils.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Export Trustformer.Scheduler.DFG.
Require Export Trustformer.Scheduler.SchedulerCore.
Require Import Trustformer.Scheduler.Contract.
Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.Program.Wf.

Import ListNotations.


(* The record obligations: the schedule writes each tag once, assigns [done] in
   the always half, and resets a duplicate-free list of registers to zero.
   SchedulerCore.v holds the lowering these are proved about. *)

Section VariableScheduler.

  Context (ctx: TFSchedContext).
  Context (cost_limit: nat).

  Local Notation states_var := (tfs_spec_states ctx).
  Local Notation states_var_eq_dec := (tfs_spec_states_eq_dec ctx).
  Local Notation states_var_fin := (tfs_spec_states_fin ctx).
  Local Notation states_var_names := (tfs_spec_states_names ctx).
  Local Notation states_var_size := (tfs_spec_states_size ctx).
  Local Notation states_var_init := (tfs_spec_states_init ctx).

  Local Notation inputs_var := (tfs_spec_inputs ctx).
  Local Notation inputs_var_eq_dec := (tfs_spec_inputs_eq_dec ctx).
  Local Notation inputs_var_fin := (tfs_spec_inputs_fin ctx).
  Local Notation inputs_var_size := (tfs_spec_inputs_size ctx).
  Local Notation inputs_var_class := (tfs_spec_inputs_class ctx).

  Local Notation outputs_var := (tfs_spec_outputs ctx).
  Local Notation outputs_var_eq_dec := (tfs_spec_outputs_eq_dec ctx).
  Local Notation outputs_var_fin := (tfs_spec_outputs_fin ctx).
  Local Notation outputs_var_size := (tfs_spec_outputs_size ctx).
  Local Notation outputs_var_class := (tfs_spec_outputs_class ctx).

  Local Notation ips_var := (tfs_spec_ips ctx).
  Local Notation ips_var_eq_dec := (tfs_spec_ips_eq_dec ctx).
  Local Notation ips_var_fin := (tfs_spec_ips_fin ctx).
  Local Notation ip_of := (tfs_spec_ip ctx).

  Local Notation spec_action := (tfs_spec_action ctx).
  Local Notation spec_action_eq_dec := (tfs_spec_action_eq_dec ctx).
  Local Notation spec_action_fin := (tfs_spec_action_fin ctx).
  Local Notation spec_action_ops := (tfs_spec_action_ops ctx).
  Local Notation spec_all_actions := (@finite_elements spec_action spec_action_fin).
  Local Notation spec_action_index := (@finite_index spec_action spec_action_fin).

  Hint Extern 0 (FiniteType states_var) => exact (tfs_spec_states_fin ctx) : typeclass_instances.
  
  Hint Extern 0 (Show states_var) => exact (tfs_spec_states_names ctx) : typeclass_instances.
  Hint Extern 0 (Show inputs_var) => exact (tfs_spec_inputs_names ctx) : typeclass_instances.
  Hint Extern 0 (Show outputs_var) => exact (tfs_spec_outputs_names ctx) : typeclass_instances.
  Hint Extern 0 (Show ips_var) => exact (tfs_spec_ips_names ctx) : typeclass_instances.


  Local Notation dfg_vars := (@dfg_vars_t states_var outputs_var).
  Local Notation dfg_op := (@dfg_op_t states_var inputs_var outputs_var ips_var).
  Local Notation dfg_node := (@dfg_node_t states_var inputs_var outputs_var ips_var).
  Local Notation dfg_state := (@dfg_state_t states_var inputs_var outputs_var ips_var).
  Local Notation get_tainted := (SchedulerCore.get_tainted ctx).
  Local Notation decl_facts := (SchedulerCore.decl_facts ctx).
  Hint Extern 0 (EqDec dfg_vars) => exact (SchedulerCore.dfg_vars_eq_dec ctx) : typeclass_instances.

  (* [SchedulerCore]'s section variables are discharged, so bind them back. *)
  Local Notation M := (SchedulerCore.M ctx).
  Local Notation bind := (SchedulerCore.bind ctx).
  Local Notation build_dfg := (SchedulerCore.build_dfg ctx).
  Local Notation dataflow_expr := (SchedulerCore.dataflow_expr ctx).
  Local Notation dataflow_ops := (SchedulerCore.dataflow_ops ctx).
  Local Notation dfg_var_size := (SchedulerCore.dfg_var_size ctx).
  Local Notation driven_ports := (SchedulerCore.driven_ports ctx).
  Local Notation emit := (SchedulerCore.emit ctx).
  Local Notation ensure_var := (SchedulerCore.ensure_var ctx).
  Local Notation get_sizes_and_idx := (SchedulerCore.get_sizes_and_idx ctx).
  Local Notation get_state := (SchedulerCore.get_state ctx).
  Local Notation get_var := (SchedulerCore.get_var ctx).
  Local Notation last_sample := (SchedulerCore.last_sample ctx).
  Local Notation merge_key := (SchedulerCore.merge_key ctx).
  Local Notation merge_loop := (SchedulerCore.merge_loop ctx).
  Local Notation merge_maps := (SchedulerCore.merge_maps ctx).
  Local Notation put_state := (SchedulerCore.put_state ctx).
  Local Notation read_var := (SchedulerCore.read_var ctx).
  Local Notation ret := (SchedulerCore.ret ctx).
  Local Notation set_var := (SchedulerCore.set_var ctx).
  Local Notation stall_chain := (SchedulerCore.stall_chain ctx).

  Context (bn : list (list (nid_t * (nat * sz_t)))).

  Local Notation tf_dfg_states := (tf_dfg_states_t (states_var:=states_var) (ips_var:=ips_var) (buffer_needs:=bn)).
  Local Notation expr_t := (@tf_expr tf_dfg_states (inputs_var + ips_var) outputs_var).
  Hint Extern 0 (Show tf_dfg_states) => exact (SchedulerCore.show_tf_dfg_states ctx bn) : typeclass_instances.
  Hint Extern 0 (FiniteType2 tf_dfg_states) => exact (SchedulerCore.tf_dfg_states_fin2 ctx bn) : typeclass_instances.
  Hint Extern 0 (FiniteType tf_dfg_states) => exact (SchedulerCore.tf_dfg_states_fin ctx bn) : typeclass_instances.

  Local Notation compile_dfg_expr_aux := (SchedulerCore.compile_dfg_expr_aux ctx bn).
  Local Notation compile_dfg_expr fuel a_idx dfg n bufs :=
    (compile_dfg_expr_aux (get_tainted dfg) (decl_facts dfg) [] fuel a_idx dfg n bufs).
  Local Notation compile_dfg_aux := (SchedulerCore.compile_dfg_aux ctx bn).
  Local Notation compile_dfg_buffers := (SchedulerCore.compile_dfg_buffers ctx bn).
  Local Notation compile_dfg_drives := (SchedulerCore.compile_dfg_drives ctx bn).
  Local Notation compile_dfg_valid := (SchedulerCore.compile_dfg_valid ctx bn).
  Local Notation done_signal := (SchedulerCore.done_signal ctx bn).
  Local Notation maps_from := (SchedulerCore.maps_from ctx bn).
  Local Notation maps_to := (SchedulerCore.maps_to ctx bn).
  Local Notation reset_states := (SchedulerCore.reset_states ctx bn).
  Local Notation schedule := (SchedulerCore.schedule ctx cost_limit bn).
  Local Notation tf_dfg_states_init := (SchedulerCore.tf_dfg_states_init ctx bn).
  Local Notation tf_dfg_states_size := (SchedulerCore.tf_dfg_states_size ctx bn).

  (* ==================================================================== *)
  (* Helper infrastructure for schedule_no_dup                            *)
  (* ==================================================================== *)

  (* --- generic list helpers --- *)

  Lemma map_fst_filter_incl {K V} (p: K*V -> bool) (l: list (K*V)) k:
    In k (map fst (filter p l)) -> In k (map fst l).
  Proof.
    induction l as [|[k0 v0] l IH]; simpl; [tauto|].
    destruct (p (k0,v0)); simpl.
    - intros [->|Hin]; [left; reflexivity | right; auto].
    - intro Hin; right; auto.
  Qed.

  Lemma NoDup_map_fst_filter {K V} (p: K*V -> bool) (l: list (K*V)):
    NoDup (map fst l) -> NoDup (map fst (filter p l)).
  Proof.
    induction l as [|[k0 v0] l IH]; simpl; intro Hnd; [constructor|].
    inversion Hnd; subst.
    destruct (p (k0,v0)); simpl.
    - constructor.
      + intro Hin. apply map_fst_filter_incl in Hin. contradiction.
      + apply IH; assumption.
    - apply IH; assumption.
  Qed.

  Lemma nodup_map_fst_cons_filter (k: dfg_vars) (v: nid_t) (l: list (dfg_vars * nid_t)):
    NoDup (map fst l) ->
    NoDup (map fst ((k,v) :: filter (fun '(k', _) => if eq_dec k' k then false else true) l)).
  Proof.
    intro Hnd. simpl. constructor.
    - intro Hin. apply in_map_iff in Hin. destruct Hin as [[k' v'] [Heq Hin]].
      simpl in Heq; subst k'. apply filter_In in Hin. destruct Hin as [_ Hp].
      change ((if eq_dec k k then false else true) = true) in Hp.
      rewrite eq_dec_refl in Hp. discriminate Hp.
    - apply NoDup_map_fst_filter; assumption.
  Qed.

  Lemma list_assoc_none_not_in {K V} `{EqDec K} (l: list (K*V)) (k: K):
    BitsToLists.list_assoc l k = None -> ~ In k (map fst l).
  Proof.
    induction l as [|[k0 v0] l IH]; simpl; [tauto|].
    destruct (eq_dec k k0) as [->|Hneq].
    - discriminate.
    - intros Hnone [Heq|Hin]; [apply Hneq; symmetry; exact Heq | apply IH; assumption].
  Qed.

  (* --- state-monad invariant plumbing --- *)

  Definition vm_nd (s: dfg_state) : Prop := NoDup (map fst (var_map s)).
  Definition preserves (P: dfg_state -> Prop) {A} (m: M A) := forall s, P s -> P (snd (m s)).

  Lemma preserves_ret P {A} (x: A): preserves P (ret x).
  Proof. intros s Hs; exact Hs. Qed.

  Lemma preserves_bind P {A B} (m: M A) (f: A -> M B):
    preserves P m -> (forall x, preserves P (f x)) -> preserves P (bind m f).
  Proof.
    intros Hm Hf s Hs. unfold bind.
    destruct (m s) as [x s'] eqn:Hms.
    assert (P s') as Hs'.
    { specialize (Hm s Hs). rewrite Hms in Hm. exact Hm. }
    apply (Hf x s' Hs').
  Qed.

  Lemma emit_vm op sz: preserves vm_nd (emit op sz).
  Proof.
    intros s Hs. unfold emit, bind, get_state, put_state, ret; simpl. exact Hs.
  Qed.

  Lemma ensure_var_vm v: preserves vm_nd (ensure_var v).
  Proof.
    intros s Hs. unfold vm_nd, ensure_var.
    cbn [emit bind get_state put_state ret snd fst var_map].
    apply nodup_map_fst_cons_filter. exact Hs.
  Qed.

  Lemma read_var_vm v: preserves vm_nd (read_var v).
  Proof.
    intros s Hs. unfold read_var, bind, get_state.
    match goal with
    | |- context [find ?P ?l] => destruct (find P l) as [nd|]
    end.
    - exact Hs.
    - apply (emit_vm (DFG_Var v) (dfg_var_size v) s Hs).
  Qed.

  Lemma get_var_vm v: preserves vm_nd (get_var v).
  Proof.
    intros s Hs. unfold get_var, bind, get_state.
    destruct (BitsToLists.list_assoc (var_map s) v).
    - exact Hs.
    - apply (read_var_vm v s Hs).
  Qed.

  Lemma set_var_vm v id: preserves vm_nd (set_var v id).
  Proof.
    intros s Hs. unfold vm_nd, set_var.
    cbn [bind get_state put_state ret snd fst var_map].
    apply nodup_map_fst_cons_filter. exact Hs.
  Qed.

  Lemma dataflow_expr_vm: forall e sz, preserves vm_nd (dataflow_expr e sz).
  Proof.
    induction e as [val | sv | iv | ov | uop e IHe
                    | bop e1 IHe1 e2 IHe2 | ec IHe1 et IHe2 ee IHe3];
      intros sz; cbn [dataflow_expr].
    - apply emit_vm.
    - apply preserves_bind; [apply get_var_vm|]. intro x.
      destruct (Nat.eqb (dfg_var_size (DFG_SVar sv)) sz); [apply preserves_ret | apply emit_vm].
    - apply preserves_bind; [apply emit_vm|]. intro x.
      destruct (Nat.eqb (inputs_var_size iv) sz); [apply preserves_ret | apply emit_vm].
    - apply preserves_bind; [apply get_var_vm|]. intro x.
      destruct (Nat.eqb (dfg_var_size (DFG_OVar ov)) sz); [apply preserves_ret | apply emit_vm].
    - destruct uop as [| source_size].
      + apply preserves_bind; [apply IHe|]. intro x. apply emit_vm.
      + apply preserves_bind; [apply IHe|]. intro x.
        apply emit_vm.
    - destruct bop;
        (apply preserves_bind; [apply IHe1| intro x1;
         apply preserves_bind; [apply IHe2| intro x2; apply emit_vm]]).
    - apply preserves_bind; [apply IHe1|]. intro xc.
      apply preserves_bind; [apply IHe2|]. intro xt.
      apply preserves_bind; [apply IHe3|]. intro xe. apply emit_vm.
  Qed.

  Lemma merge_loop_nd cond mt me: forall keys acc s,
    NoDup (map fst acc) ->
    NoDup (map fst (fst (merge_loop cond mt me keys acc s))).
  Proof.
    induction keys as [|[k kv] rest IH]; intros acc s Hnd; cbn [merge_loop].
    - exact Hnd.
    - destruct (BitsToLists.list_assoc acc k) eqn:Ha.
      + apply IH; exact Hnd.
      + unfold bind.
        destruct (merge_key cond k (BitsToLists.list_assoc mt k)
                    (BitsToLists.list_assoc me k) s) as [res_opt s1].
        destruct res_opt as [fid|].
        * apply IH. simpl. constructor.
          -- apply list_assoc_none_not_in in Ha. exact Ha.
          -- exact Hnd.
        * apply IH; exact Hnd.
  Qed.

  (* The delay chain is [emit]s all the way down, so it never touches var_map. *)
  Lemma stall_chain_vm: forall n id, preserves vm_nd (stall_chain n id).
  Proof.
    intros n id. destruct n; cbn [stall_chain].
    - apply preserves_ret.
    - apply emit_vm.
  Qed.

  Lemma dataflow_ops_vm: forall ops en, preserves vm_nd (dataflow_ops en ops).
  Proof.
    induction ops as [bop | o1 IHops1 o2 IHops2 | oc ot IHops1 oe IHops2]; intro en;
      cbn [dataflow_ops].
    - destruct bop as [ | dst expr | dst expr | pip dst expr].
      + apply preserves_ret.
      + apply preserves_bind; [apply dataflow_expr_vm|]. intro x. apply set_var_vm.
      + apply preserves_bind; [apply dataflow_expr_vm|]. intro x. apply set_var_vm.
      + (* payload, drive, ordering join, stall, sample, dest write -- only the
           LAST touches var_map; [get_state], [emit] and [ret] record nothing. *)
        apply preserves_bind; [intros s Hs; exact Hs|]. intro s0.
        apply preserves_bind; [apply dataflow_expr_vm|]. intro x.
        apply preserves_bind; [apply emit_vm|]. intro y.
        apply preserves_bind;
          [destruct (last_sample s0 pip en); [apply emit_vm | apply preserves_ret]|]. intro h.
        apply preserves_bind; [apply stall_chain_vm|]. intro z.
        apply preserves_bind; [apply emit_vm|]. intro w.
        apply set_var_vm.
    - apply preserves_bind; [apply IHops1|]. intro x. apply IHops2.
    - intros s Hs.
      unfold bind. cbn [get_state put_state].
      destruct (dataflow_expr oc 1 s) as [xc s0].


      destruct (dataflow_ops _ ot s0) as [u1 s1].
      destruct (dataflow_ops _ oe {| graph := graph s1; var_map := var_map s0 |}) as [u2 s2].
      unfold merge_maps, vm_nd.
      destruct (merge_loop xc (var_map s1) (var_map s2)
                 (var_map s1 ++ var_map s2) [] s2) as [x0 s3] eqn:Hm.
      cbn [snd var_map].
      replace x0 with (fst (merge_loop xc (var_map s1) (var_map s2)
                 (var_map s1 ++ var_map s2) [] s2)) by (rewrite Hm; reflexivity).
      apply merge_loop_nd. constructor.
  Qed.

  Lemma build_dfg_vm a: NoDup (map fst (var_map (build_dfg a))).
  Proof.
    unfold build_dfg. simpl.
    destruct (dataflow_ops [] (spec_action_ops a)
                {| graph := [{| nid := 0; op := DFG_Empty; sz := 0 |}]; var_map := [] |})
      as [u s'] eqn:Hd.
    simpl.
    assert (vm_nd s') as Hnd.
    { pose proof (dataflow_ops_vm (spec_action_ops a) []
        {| graph := [{| nid := 0; op := DFG_Empty; sz := 0 |}]; var_map := [] |}) as Hp.
      unfold preserves in Hp. specialize (Hp ltac:(unfold vm_nd; simpl; constructor)).
      rewrite Hd in Hp. exact Hp. }
    exact Hnd.
  Qed.

  (* --- generic NoDup-of-flat_map via a key --- *)

  Lemma NoDup_flat_map_key {A B} (f: A -> list B) (l: list A):
    NoDup l ->
    (forall x, In x l -> NoDup (f x)) ->
    (forall x y b, In x l -> In y l -> In b (f x) -> In b (f y) -> x = y) ->
    NoDup (flat_map f l).
  Proof.
    intros Hnd. induction Hnd as [| a l Hnotin Hnd IH]; intros Hin Hkey; simpl.
    - constructor.
    - apply NoDup_app.
      + apply Hin. left. reflexivity.
      + apply IH.
        * intros x Hx. apply Hin. right. exact Hx.
        * intros x y b Hx Hy Hbx Hby.
          apply (Hkey x y b (or_intror Hx) (or_intror Hy) Hbx Hby).
      + intros b Hba Hbrest.
        apply in_flat_map in Hbrest. destruct Hbrest as [y [Hy Hby]].
        assert (a = y) as Heq
          by apply (Hkey a y b (or_introl eq_refl) (or_intror Hy) Hba Hby).
        subst y. contradiction.
  Qed.

  Lemma nodup_map_inj_in {A K} (g: A -> K) (l: list A):
    NoDup (map g l) -> forall x y, In x l -> In y l -> g x = g y -> x = y.
  Proof.
    induction l as [|a l IH]; intros Hnd x y Hx Hy Hg; [inversion Hx|].
    simpl in Hnd. inversion Hnd; subst.
    destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
    - reflexivity.
    - exfalso. apply H1. rewrite Hg. apply in_map. exact Hy.
    - exfalso. apply H1. rewrite <- Hg. apply in_map. exact Hx.
    - apply IH; assumption.
  Qed.

  Lemma NoDup_flat_map_of_key {A B K} (g: A -> K) (f: A -> list B) (key: B -> K) (l: list A):
    NoDup (map g l) ->
    (forall x, In x l -> NoDup (f x)) ->
    (forall x b, In x l -> In b (f x) -> key b = g x) ->
    NoDup (flat_map f l).
  Proof.
    intros Hnd Hf Hkey. apply NoDup_flat_map_key.
    - apply NoDup_map_inv with (f:=g); exact Hnd.
    - exact Hf.
    - intros x y b Hx Hy Hbx Hby.
      apply (nodup_map_inj_in g l Hnd x y Hx Hy).
      rewrite <- (Hkey x b Hx Hbx). rewrite <- (Hkey y b Hy Hby). reflexivity.
  Qed.

  (* --- get_sizes_and_idx assigns indices 0,1,2,... --- *)

  Lemma fold_idx_map (dfg: dfg_state): forall nodes acc i,
    map (fun '(_, x) => fst x) (rev (fst (fold_left
      (fun '(acc0, idx) nid =>
         let node := nth nid (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |} in
         ((nid, (idx, sz node)) :: acc0, S idx)) nodes (acc, i))))
    = map (fun '(_, x) => fst x) (rev acc) ++ seq i (length nodes).
  Proof.
    induction nodes as [|nid rest IH]; intros acc i.
    - simpl. rewrite app_nil_r. reflexivity.
    - cbn [fold_left length]. rewrite IH.
      cbn [rev]. rewrite map_app. cbn [map]. cbn [seq].
      rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma gsi_idx_nodup (dfg: dfg_state) (nodes: list nid_t):
    NoDup (map (fun '(_, x) => fst x) (get_sizes_and_idx dfg nodes)).
  Proof.
    unfold get_sizes_and_idx. rewrite fold_idx_map. simpl. apply seq_NoDup.
  Qed.

  (* --- flat_map composition helpers --- *)

  Lemma flat_map_flat_map {A B C} (g: B -> list C) (h: A -> list B) (l: list A):
    flat_map g (flat_map h l) = flat_map (fun x => flat_map g (h x)) l.
  Proof.
    induction l as [|a l IH]; simpl; [reflexivity|].
    rewrite flat_map_app, IH. reflexivity.
  Qed.

  Lemma flat_map_map {A B C} (f: B -> list C) (g: A -> B) (l: list A):
    flat_map f (map g l) = flat_map (fun x => f (g x)) l.
  Proof.
    induction l as [|a l IH]; simpl; [reflexivity | rewrite IH; reflexivity].
  Qed.

  Lemma NoDup_map_Some {A} (l: list A): NoDup l -> NoDup (map Some l).
  Proof.
    induction 1 as [|x l Hx Hnd IH]; simpl; constructor; [| exact IH].
    intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Heq Hy]].
    injection Heq as ->. contradiction.
  Qed.

  (* --- the op-tag function used by tfs_ops_no_duplicates --- *)

  Notation OPTAG :=
    (fun op => match op with
       | tf_assign dst _ => [StOp dst]
       | tf_output dst _ => [OutOp dst]
       | tf_call _ dst _ => [StOp dst]
       | _ => []
       end).

  (* --- buffer-op tags --- *)

  Lemma buffers_tags_in (idx: nat) (DFG: dfg_state)
        (BUF: list (nid_t * (nat * sz_t))) t:
    In t (flat_map OPTAG (compile_dfg_buffers idx DFG BUF)) ->
    exists a' n', t = StOp (tf_dfg_b a' n') \/ t = StOp (tf_dfg_v a' n').
  Proof.
    intro Hin. apply in_flat_map in Hin. destruct Hin as [op [Hop Ht]].
    unfold compile_dfg_buffers in Hop.
    destruct (index_of_nat (length bn) idx) as [a'|]; [| destruct Hop].
    apply in_flat_map in Hop. destruct Hop as [[nid x] [_ Hop]].
    destruct (index_of_nat _ (fst x)) as [n'|]; [| destruct Hop].
    match goal with
    | Hop : In op (let '(_, _) := ?E in _) |- _ =>
        destruct E as [expr valid]
    end.
    simpl in Hop. destruct Hop as [<-|[<-|[]]]; simpl in Ht.
    - destruct Ht as [<-|[]]. exists a', n'. left. reflexivity.
    - destruct Ht as [<-|[]]. exists a', n'. right. reflexivity.
  Qed.

  Lemma buffers_tags_nodup (idx: nat) (DFG: dfg_state)
        (BUF: list (nid_t * (nat * sz_t))):
    NoDup (map (fun '(_, x) => fst x) BUF) ->
    NoDup (flat_map OPTAG (compile_dfg_buffers idx DFG BUF)).
  Proof.
    intro HBUF. unfold compile_dfg_buffers.
    destruct (index_of_nat (length bn) idx) as [a'|]; [| simpl; constructor].
    rewrite flat_map_flat_map.
    apply NoDup_flat_map_of_key
      with (g := fun '(_, x) => fst x)
           (key := fun t => match t with
                    | StOp (tf_dfg_b _ n) => index_to_nat n
                    | StOp (tf_dfg_v _ n) => index_to_nat n
                    | _ => 0
                    end).
    - exact HBUF.
    - intros [nid x] _.
      destruct (index_of_nat _ (fst x)) as [n'|]; [| simpl; constructor].
      match goal with |- context[let '(_, _) := ?E in _] => destruct E as [expr valid] end.
      simpl. apply NoDup_cons; [simpl; intros [H|[]]; discriminate H|].
      apply NoDup_cons; [simpl; tauto | apply NoDup_nil].
    - intros [nid x] b _ Hb.
      destruct (index_of_nat _ (fst x)) as [n'|] eqn:Hn; [| destruct Hb].
      match goal with
      | Hb : In b (flat_map _ (let '(_, _) := ?E in _)) |- _ =>
          destruct E as [expr valid]
      end.
      simpl in Hb. destruct Hb as [<-|[<-|[]]]; simpl;
        apply index_to_nat_of_nat in Hn; exact Hn.
  Qed.

  (* --- final-op tags --- *)

  Lemma final_tags_in (idx: nat) (DFG: dfg_state)
        (BUF: list (nid_t * (nat * sz_t))) t:
    In t (flat_map OPTAG (compile_dfg_aux idx DFG BUF)) ->
    (exists sv, t = StOp (tf_dfg_s sv)) \/ (exists ov, t = OutOp ov).
  Proof.
    intro Hin. apply in_flat_map in Hin. destruct Hin as [op [Hop Ht]].
    unfold compile_dfg_aux in Hop.
    destruct (index_of_nat (length bn) idx) as [a'|]; [| destruct Hop].
    apply in_map_iff in Hop. destruct Hop as [[var nid] [Heq _]].
    match goal with
    | Heq : (let '(_, _) := ?E in _) = op |- _ =>
        destruct E as [expr valid]
    end.
    destruct var as [sv|ov]; subst op; simpl in Ht.
    - destruct Ht as [<-|[]]. left. exists sv. reflexivity.
    - destruct Ht as [<-|[]]. right. exists ov. reflexivity.
  Qed.

  Lemma final_tags_nodup (idx: nat) (DFG: dfg_state)
        (BUF: list (nid_t * (nat * sz_t))):
    NoDup (map fst (var_map DFG)) ->
    NoDup (flat_map OPTAG (compile_dfg_aux idx DFG BUF)).
  Proof.
    intro HDFG. unfold compile_dfg_aux.
    destruct (index_of_nat (length bn) idx) as [a'|]; [| simpl; constructor].
    rewrite flat_map_map.
    apply NoDup_flat_map_of_key
      with (g := fun p => Some (fst p))
           (key := fun t => match t with
                    | StOp (tf_dfg_s sv) => Some (DFG_SVar sv)
                    | OutOp ov => Some (DFG_OVar ov)
                    | _ => None
                    end).
    - rewrite <- (map_map fst Some). apply NoDup_map_Some. exact HDFG.
    - intros [var nid] _.
      match goal with |- context[compile_dfg_expr ?f ?a ?d ?n ?b] =>
        destruct (compile_dfg_expr f a d n b) as [expr valid] end.
      destruct var as [sv|ov]; simpl; apply NoDup_cons; solve [apply NoDup_nil | simpl; tauto].
    - intros [var nid] b _ Hb.
      match goal with
      | Hb : context[compile_dfg_expr ?f ?a ?d ?n ?bf] |- _ =>
          destruct (compile_dfg_expr f a d n bf) as [expr valid]
      end.
      destruct var as [sv|ov]; simpl in Hb; destruct Hb as [<-|[]]; reflexivity.
  Qed.

  (* --- drive-op tags (SPIKE 2c, ported from P3) --- *)

  (* One [tf_assign (tf_dfg_ov p) _] per IP, so the tag list is exactly
     [map StOp (map tf_dfg_ov (driven_ports DFG))]. *)
  Lemma drives_tags_eq (idx: nat) (DFG: dfg_state)
        (BUF: list (nid_t * (nat * sz_t))):
    flat_map OPTAG (compile_dfg_drives idx DFG BUF)
    = match index_of_nat (length bn) idx with
      | None => []
      | Some _ => map (fun o => @StOp tf_dfg_states outputs_var (tf_dfg_ov o)) (driven_ports DFG)
      end.
  Proof.
    unfold compile_dfg_drives.
    destruct (index_of_nat (length bn) idx) as [a'|]; [| reflexivity].
    rewrite flat_map_map.
    induction (driven_ports DFG) as [|o l IH]; simpl;
      [reflexivity | rewrite IH; reflexivity].
  Qed.

  Lemma drives_tags_in (idx: nat) (DFG: dfg_state)
        (BUF: list (nid_t * (nat * sz_t))) t:
    In t (flat_map OPTAG (compile_dfg_drives idx DFG BUF)) ->
    exists o, t = @StOp tf_dfg_states outputs_var (tf_dfg_ov o) /\ In o (driven_ports DFG).
  Proof.
    rewrite drives_tags_eq.
    destruct (index_of_nat (length bn) idx) as [a'|]; [| intros []].
    intro Hin. apply in_map_iff in Hin. destruct Hin as [o [<- Ho]].
    exists o. split; [reflexivity | exact Ho].
  Qed.

  Lemma NoDup_map_StOp_ov (l: list ips_var):
    NoDup l -> NoDup (map (fun o => @StOp tf_dfg_states outputs_var (tf_dfg_ov o)) l).
  Proof.
    induction 1 as [|x l Hx Hnd IH]; simpl; constructor; [| exact IH].
    intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Heq Hy]].
    injection Heq as ->. contradiction.
  Qed.

  (* No hypothesis needed: [driven_ports] filters [finite_elements], which is
     NoDup by construction.  Contrast [final_tags_nodup], which must assume
     [var_map] is duplicate-free. *)
  Lemma drives_tags_nodup (idx: nat) (DFG: dfg_state)
        (BUF: list (nid_t * (nat * sz_t))):
    NoDup (flat_map OPTAG (compile_dfg_drives idx DFG BUF)).
  Proof.
    rewrite drives_tags_eq.
    destruct (index_of_nat (length bn) idx) as [a'|]; [| constructor].
    apply NoDup_map_StOp_ov. unfold driven_ports.
    apply finite_nodup.
  Qed.



  (* --- assembly --- *)

  Lemma schedule_no_dup_aux (idx: nat) (DFG: dfg_state)
        (BUF: list (nid_t * (nat * sz_t))):
    NoDup (map fst (var_map DFG)) ->
    NoDup (map (fun '(_, x) => fst x) BUF) ->
    NoDup (flat_map OPTAG
      ((compile_dfg_valid idx DFG BUF :: compile_dfg_buffers idx DFG BUF
        ++ compile_dfg_drives idx DFG BUF)
       ++ compile_dfg_aux idx DFG BUF)).
  Proof.
    intros HDFG HBUF.
    assert (Hval: forall L, flat_map OPTAG (compile_dfg_valid idx DFG BUF :: L)
      = StOp tf_dfg_done :: flat_map OPTAG L).
    { intro L. unfold compile_dfg_valid. reflexivity. }
    rewrite flat_map_app, Hval, <- app_comm_cons.
    apply NoDup_cons.
    - rewrite in_app_iff. intros [Hbd|Hf].
      + (* the always half: buffers give StOp, drives give OutOp *)
        rewrite flat_map_app, in_app_iff in Hbd. destruct Hbd as [Hb|Hd].
        * apply buffers_tags_in in Hb. destruct Hb as [a' [n' [Hb|Hb]]]; discriminate Hb.
        * apply drives_tags_in in Hd. destruct Hd as [o [Ho _]]; discriminate Ho.
      + apply final_tags_in in Hf. destruct Hf as [[sv Hf]|[ov Hf]]; discriminate Hf.
    - apply NoDup_app.
      + (* NoDup within the always half *)
        rewrite flat_map_app. apply NoDup_app.
        * apply buffers_tags_nodup. exact HBUF.
        * apply drives_tags_nodup.
        * intros x Hb Hd.
          apply buffers_tags_in in Hb. apply drives_tags_in in Hd.
          destruct Hb as [a' [n' [-> | ->]]]; destruct Hd as [o [Ho _]]; discriminate Ho.
      + apply final_tags_nodup. exact HDFG.
      + (* the always half is disjoint from the done half *)
        intros x Hx Hxf. rewrite flat_map_app, in_app_iff in Hx.
        destruct Hx as [Hxb|Hxd].
        * apply buffers_tags_in in Hxb. apply final_tags_in in Hxf.
          destruct Hxb as [a' [n' [-> | ->]]];
            destruct Hxf as [[sv Hs]|[ov Ho]]; discriminate.
        * (* A drive tag is [StOp (tf_dfg_ov o)] and a final tag is
             [StOp (tf_dfg_s sv)] or [OutOp ov] -- different constructors, so
             [discriminate] separates them. *)
          apply drives_tags_in in Hxd. apply final_tags_in in Hxf.
          destruct Hxd as [o [-> _]].
          destruct Hxf as [[sv Hs]|[ov Ho]]; discriminate.
  Qed.


  Theorem schedule_no_dup: forall a, tfs_ops_no_duplicates (fst (schedule a) ++ snd (schedule a)).
  Proof.
    intros a. unfold tfs_ops_no_duplicates, schedule. cbn [fst snd].
    apply schedule_no_dup_aux.
    - set (i := spec_action_index a).
      destruct (lt_dec i (length (map build_dfg spec_all_actions))) as [Hlt|Hge].
      + pose proof (nth_In (map build_dfg spec_all_actions)
                     {| graph := []; var_map := [] |} Hlt) as HIn.
        apply in_map_iff in HIn. destruct HIn as [a' [Heq _]].
        rewrite <- Heq. apply build_dfg_vm.
      + rewrite nth_overflow by lia. simpl. constructor.
    - set (i := spec_action_index a).
      match goal with
      | |- NoDup (map _ (nth _ ?BUFS _)) =>
        destruct (lt_dec i (length BUFS)) as [Hlt|Hge];
        [ pose proof (nth_In BUFS ([]:list (nid_t * (nat * sz_t))) Hlt) as HIn
        | rewrite nth_overflow by lia; simpl; constructor ]
      end.
      apply in_map_iff in HIn. destruct HIn as [[dfg cm] [Heq _]].
      rewrite <- Heq. apply gsi_idx_nodup.
  Qed.

  Theorem schedule_done_assigned: forall a,    In (StOp done_signal)
       (flat_map (fun op =>
          match op with
          | tf_assign dst _ => [StOp dst]
          | tf_output dst _ => [OutOp dst]
          | tf_call _ dst _ => [StOp dst]
          | _ => []
          end) (fst (schedule a))).
  Proof.
    intros a. unfold schedule, done_signal, compile_dfg_valid. cbn [fst flat_map app].
    left. reflexivity.
  Qed.

  Theorem reset_states_nodup: NoDup reset_states.
  Proof.
    unfold reset_states.
    (* recover the a-index and n-index from an element *)
    pose (a_of := fun v : tf_dfg_states =>
      match v with
      | tf_dfg_b a _ => index_to_nat a
      | tf_dfg_v a _ => index_to_nat a
      | _ => 0
      end).
    pose (n_of := fun v : tf_dfg_states =>
      match v with
      | tf_dfg_b _ n => index_to_nat n
      | tf_dfg_v _ n => index_to_nat n
      | _ => 0
      end).
    apply NoDup_flat_map_key.
    - apply seq_NoDup.
    - (* each outer chunk is NoDup *)
      intros a_idx _.
      destruct (index_of_nat (length bn) a_idx) as [a'|] eqn:Ha;
        [| constructor].
      apply NoDup_flat_map_key.
      + apply seq_NoDup.
      + (* each inner chunk [b; v] is NoDup *)
        intros n_idx _.
        destruct (index_of_nat _ n_idx) as [n'|] eqn:Hn; [| constructor].
        repeat constructor.
        * simpl. intros [H | []]. discriminate H.
        * simpl. tauto.
      + (* inner disjointness: element recovers its n-index *)
        intros x y b Hx Hy Hbx Hby.
        assert (forall m b0, In b0 (match index_of_nat _ m with
                              | Some n' => [tf_dfg_b a' n'; tf_dfg_v a' n']
                              | None => [] end) -> n_of b0 = m) as Hrec.
        { intros m b0 Hb0. destruct (index_of_nat _ m) as [n'|] eqn:Hm; [| destruct Hb0].
          apply index_to_nat_of_nat in Hm.
          simpl in Hb0. destruct Hb0 as [<- | [<- | []]]; simpl; exact Hm. }
        rewrite <- (Hrec x b Hbx). rewrite <- (Hrec y b Hby). reflexivity.
    - (* outer disjointness: element recovers its a-index *)
      intros x y b Hx Hy Hbx Hby.
      assert (forall m b0, In b0 (match index_of_nat (length bn) m with
                            | Some a' => flat_map (fun n_idx =>
                                match index_of_nat (length (nth (index_to_nat a') bn [])) n_idx with
                                | Some n' => [tf_dfg_b a' n'; tf_dfg_v a' n']
                                | None => [] end)
                                (List.seq 0 (length (nth (index_to_nat a') bn [])))
                            | None => [] end) -> a_of b0 = m) as Hrec.
      { intros m b0 Hb0. destruct (index_of_nat (length bn) m) as [a'|] eqn:Hm;
          [| destruct Hb0].
        apply index_to_nat_of_nat in Hm.
        apply in_flat_map in Hb0. destruct Hb0 as [n_idx [_ Hb0]].
        destruct (index_of_nat _ n_idx) as [n'|] eqn:Hn; [| destruct Hb0].
        simpl in Hb0. destruct Hb0 as [<- | [<- | []]]; simpl; exact Hm. }
      rewrite <- (Hrec x b Hbx). rewrite <- (Hrec y b Hby). reflexivity.
  Qed.

  Theorem reset_states_init_zero: forall v, In v reset_states -> tf_dfg_states_init v = Bits.zero.
  Proof.
    intros v Hin. unfold reset_states in Hin.
    apply in_flat_map in Hin. destruct Hin as [a_idx [_ Hin]].
    destruct (index_of_nat (length bn) a_idx) as [a_idx'|]; [|contradiction].
    apply in_flat_map in Hin. destruct Hin as [n_idx [_ Hin]].
    destruct (index_of_nat _ n_idx) as [n_idx'|]; [|contradiction].
    simpl in Hin. destruct Hin as [<-|[<-|[]]]; reflexivity.
  Qed.

  Definition tfs_schedule_bn : TFSchedule :=
    {|
      tfs_ctx := ctx;

      tfs_states := tf_dfg_states;
      tfs_states_size := tf_dfg_states_size;
      tfs_states_init := tf_dfg_states_init;
      
      (* The design's inputs plus one response per IP.  [inl] keeps the existing
         names, sizes and indices, so a design with no IP is unchanged. *)
      tfs_inputs := (inputs_var + ips_var)%type;
      tfs_inputs_size := fun v => match v with
                                  | inl x => inputs_var_size x
                                  | inr p => ip_resp_sz (ip_of p)
                                  end;
      tfs_inputs_fin := @sum_finite _ _ inputs_var_fin ips_var_fin;
      tfs_inputs_class := fun v => match v with
                                   | inl x => inputs_var_class x
                                   | inr _ => Secret
                                   end;
      tfs_inputs_resp := fun v => match v with
                                  | inl _ => None
                                  | inr p => Some p
                                  end;
      tfs_inputs_resp_size :=
        ltac:(intros v p H; destruct v; cbn in H;
              [ discriminate | injection H as <-; reflexivity ]);

      tfs_outputs := outputs_var;
      tfs_outputs_size := outputs_var_size;
      tfs_outputs_fin := outputs_var_fin;
      tfs_outputs_class := outputs_var_class;

      tfs_ips := ips_var;
      tfs_ips_fin := ips_var_fin;
      tfs_ips_names := tfs_spec_ips_names ctx;
      tfs_ip := ip_of;
      tfs_drive_reg := tf_dfg_ov;
      tfs_drive_reg_size := ltac:(reflexivity);

      tfs_action := spec_action;
      tfs_action_fin := spec_action_fin;

      tfs_map_to := maps_to;
      tfs_map_from := maps_from;

      tfs_schedule := schedule;
      tfs_done_signal := done_signal;
      tfs_reset_states := reset_states;
      tfs_schedule_no_duplicates := schedule_no_dup;
      tfs_done_signal_size := eq_refl;
      tfs_done_signal_assigned_by_always := schedule_done_assigned;
      tfs_reset_states_nodup := reset_states_nodup;
      tfs_reset_states_init_zero := reset_states_init_zero;
    |}.

End VariableScheduler.

(* The buffer table is computed once here; every function of the record closes over it. *)
Definition tfs_schedule (ctx: TFSchedContext) (cost_limit: nat) : TFSchedule :=
  tfs_schedule_bn ctx cost_limit (buffer_needs ctx cost_limit).

(* Keeps every existing use site unchanged while the taint set is computed once
   per top-level call rather than at every phi. *)
Notation compile_dfg_expr ctx cost_limit bn fuel a_idx dfg n bufs :=
  (compile_dfg_expr_aux ctx cost_limit bn (get_tainted ctx dfg) (decl_facts ctx dfg) []
     fuel a_idx dfg n bufs).

(* Same, at an explicit path: proofs that recurse into phi branches need it. *)
Notation compile_dfg_expr_at ctx cost_limit bn pi fuel a_idx dfg n bufs :=
  (compile_dfg_expr_aux ctx cost_limit bn (get_tainted ctx dfg) (decl_facts ctx dfg) pi
     fuel a_idx dfg n bufs).
