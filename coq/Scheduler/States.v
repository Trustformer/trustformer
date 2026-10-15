(*! The scheduled design's register file: [tf_dfg_states] is one register per
    spec state variable, per buffer slot (shared across actions), per validity
    bit, per IP drive port, plus [done].  Everything here is indexed by the buffer table [bn],
    which is why it sits between Buffers.v and the code generator. !*)

Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Utils.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Export Trustformer.DFG.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Build.
Require Import Trustformer.Scheduler.Cost.
Require Import Trustformer.Scheduler.Buffers.

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

Import ListNotations.

Section States.

  Context (ctx: TFSchedContext).


  Local Notation states_var := (tfs_spec_states ctx).
  Local Notation states_var_size := (tfs_spec_states_size ctx).
  Local Notation states_var_init := (tfs_spec_states_init ctx).



  Local Notation ips_var := (tfs_spec_ips ctx).
  Local Notation ips_var_fin := (tfs_spec_ips_fin ctx).
  Local Notation ip_of := (tfs_spec_ip ctx).

  Local Notation spec_action := (tfs_spec_action ctx).
  Local Notation spec_action_fin := (tfs_spec_action_fin ctx).

  
  (* The buffer table, computed once by [tfs_schedule] and passed to everything
     that mentions a register. *)
  Context (bn : list (list (nid_t * (nat * sz_t)))).

  Local Notation tf_dfg_states := (tf_dfg_states_t (states_var:=states_var) (ips_var:=ips_var) (buffer_needs:=bn) (slots:=slot_keys bn)).

  Instance show_tf_dfg_states : Show tf_dfg_states :=
    { show := fun dfg_s =>
        match dfg_s with
        | tf_dfg_s s => String.append "s_" (show s)
        | tf_dfg_b k => let '(w, r) := nth (index_to_nat k) (slot_keys bn) (0, 0) in
                        String.append "b_" (String.append (show w) (String.append "_" (show r)))
        | tf_dfg_v a_idx n_idx => String.append "v_" (String.append (show (index_to_nat a_idx)) (String.append "_" (show (index_to_nat n_idx))))
        | tf_dfg_done => "done"
        | tf_dfg_ov p => String.append "ip_" (show p)
        end }.

  Definition tf_dfg_states_size (dfg_s: tf_dfg_states) : sz_t :=
    match dfg_s with
    | tf_dfg_s s => states_var_size s
    | tf_dfg_b k => slot_width bn k
    | tf_dfg_v a_idx b_idx => 1
    | tf_dfg_done => 1
    | tf_dfg_ov p => 1 + ip_req_sz (ip_of p)
    end.

  Definition done_signal := tf_dfg_done (states_var:=states_var) (ips_var:=ips_var) (buffer_needs:=bn) (slots:=slot_keys bn).

  Definition reset_states : list tf_dfg_states :=
    map tf_dfg_b finite_elements ++
    flat_map 
      (fun a_idx => match index_of_nat (length bn) a_idx with
        | Some a_idx' =>
          flat_map (fun n_idx => match index_of_nat (length (nth (index_to_nat a_idx') bn [])) n_idx with
            | Some n_idx' => [ tf_dfg_v a_idx' n_idx' ]
            | None => [] (* should not happen *)
            end ) (List.seq 0 (length (nth (index_to_nat a_idx') bn [])))
        | None => [] (* should not happen *)
        end)
      (List.seq 0 (length bn)).
  (* EXPERIMENT: strobes are not in reset_states yet; the real implementation
     must add them, which needs NoDup_app in reset_states_nodup. *)

  Lemma reset_states_shape (v: tf_dfg_states) :
    In v reset_states -> (exists k, v = tf_dfg_b k) \/ (exists a n, v = tf_dfg_v a n).
  Proof.
    unfold reset_states. rewrite in_app_iff. intros [Hb | Hv].
    - apply in_map_iff in Hb. destruct Hb as [k [<- _]]. left. exists k. reflexivity.
    - right. apply in_flat_map in Hv. destruct Hv as [a_idx [_ Hv]].
      destruct (index_of_nat (length bn) a_idx) as [a'|]; [| contradiction].
      apply in_flat_map in Hv. destruct Hv as [n_idx [_ Hv]].
      destruct (index_of_nat _ n_idx) as [n'|]; [| contradiction].
      destruct Hv as [<- | []]. exists a', n'. reflexivity.
  Qed.

  Lemma reset_states_has_b k : In (tf_dfg_b k) reset_states.
  Proof.
    unfold reset_states. apply in_app_iff. left. apply in_map.
    change (In k (finite_elements (T := Vect.index (length (slot_keys bn))))).
    apply nth_error_In with (finite_index k). apply finite_surjective.
  Qed.

  Lemma reset_states_has_v a_idx n_idx : In (tf_dfg_v a_idx n_idx) reset_states.
  Proof.
    unfold reset_states. apply in_app_iff. right. rewrite in_flat_map.
    exists (index_to_nat a_idx). split.
    - apply in_seq. pose proof (index_to_nat_bounded a_idx). lia.
    - rewrite index_of_nat_to_nat, in_flat_map.
      exists (index_to_nat n_idx). split.
      + apply in_seq. pose proof (index_to_nat_bounded n_idx). lia.
      + rewrite index_of_nat_to_nat. left; reflexivity.
  Qed.

  Instance tf_dfg_states_fin2 : FiniteType2 tf_dfg_states.
  Proof.
    unshelve econstructor.
    - intro s. destruct s.
      + exact (0, 0).
      + exact (1, finite_index state).
      + exact (3, finite_index slot).
      + exact (4 + finite_index a_idx, finite_index n_idx).
      + exact (2, (@finite_index ips_var ips_var_fin p)).
    - refine ([ [tf_dfg_done] ] ++
              [ map tf_dfg_s finite_elements ] ++
              [ map tf_dfg_ov (@finite_elements ips_var ips_var_fin) ] ++
              [ map tf_dfg_b finite_elements ] ++
              map (fun a => map (tf_dfg_v a) finite_elements) finite_elements).
    - intros x n m EQ.
      destruct x; inversion EQ; clear EQ; subst.
      + exists [tf_dfg_done]. split; reflexivity.
      + exists (map tf_dfg_s finite_elements). split; [ reflexivity | ].
        rewrite map_nth_error with (d:=state); auto. exact (finite_surjective state).
      + exists (map tf_dfg_b finite_elements). split; [ reflexivity | ].
        rewrite map_nth_error with (d:=slot); auto. exact (finite_surjective slot).
      + exists (map (tf_dfg_v a_idx) finite_elements). split.
        * cbn [nth_error List.app]. rewrite map_nth_error with (d:=a_idx); auto.
          exact (finite_surjective a_idx).
        * rewrite map_nth_error with (d:=n_idx); auto. exact (finite_surjective n_idx).
      + exists (map tf_dfg_ov (@finite_elements ips_var ips_var_fin)). split; [ reflexivity | ].
        rewrite map_nth_error with (d:=p); auto. exact (finite_surjective p).
    - intros n l Hn m x Hm.
      destruct n as [|[|[|[|n]]]]; cbn [nth_error List.app] in Hn.
      + injection Hn as <-. destruct m as [|[|m]]; cbn in Hm; try discriminate.
        injection Hm as <-. reflexivity.
      + injection Hn as <-. apply nth_error_map_inv in Hm. destruct Hm as [s [Hs ->]].
        apply finite_elements_index in Hs. subst. reflexivity.
      + injection Hn as <-. apply nth_error_map_inv in Hm. destruct Hm as [o [Ho ->]].
        apply finite_elements_index in Ho. subst. reflexivity.
      + injection Hn as <-. apply nth_error_map_inv in Hm. destruct Hm as [k [Hk ->]].
        change (vect_to_list (all_indices (Datatypes.length (slot_keys bn))))
          with (finite_elements (T := Vect.index (length (slot_keys bn)))) in Hk.
        apply finite_elements_index in Hk. subst. reflexivity.
      + apply nth_error_map_inv in Hn. destruct Hn as [a [Ha ->]].
        apply nth_error_map_inv in Hm. destruct Hm as [k [Hk ->]].
        apply (finite_elements_index (T := Vect.index (length bn))) in Ha.
        apply (finite_elements_index (T := Vect.index (length (nth (index_to_nat a) bn [])))) in Hk.
        subst. reflexivity.
    - cbn [List.app]. repeat apply Forall_cons.
      + constructor; [ intros [] | constructor ].
      + cbn [map]. rewrite map_map. apply NoDup_map_pair. apply finite_injective.
      + cbn [map]. rewrite map_map. apply NoDup_map_pair. apply finite_injective.
      + cbn [map]. rewrite map_map. apply NoDup_map_pair. apply finite_injective.
      + apply Forall_map. apply Forall_forall. intros a_idx' _.
        rewrite map_map. apply NoDup_map_pair. apply finite_injective.
  Defined.  

  Instance tf_dfg_states_fin : FiniteType tf_dfg_states.
  Proof.
    apply FiniteType2_FiniteType.
  Defined.

  Definition maps_to (env: (ContextEnv (FT:=(tfs_spec_states_fin ctx))).(env_t) (tf_states_type states_var_size))
    : ((ContextEnv (FT:=tf_dfg_states_fin)).(env_t) (tf_states_type tf_dfg_states_size)) :=
    (ContextEnv (FT:=tf_dfg_states_fin)).(create) (
      fun s =>
        match s as s0 return (type_denote (tf_states_type tf_dfg_states_size s0)) with
        | tf_dfg_s sv => getenv ContextEnv env sv
        | tf_dfg_b _ => Bits.zero
        | tf_dfg_v a_idx n_idx => Bits.zero
        | tf_dfg_done => Bits.zero
        | tf_dfg_ov _ => Bits.zero
        end
    ).

  Definition maps_from (env: (ContextEnv (FT:=tf_dfg_states_fin)).(env_t) (tf_states_type tf_dfg_states_size))
    : ((ContextEnv (FT:=(tfs_spec_states_fin ctx))).(env_t) (tf_states_type states_var_size)) :=
    (ContextEnv (FT:=(tfs_spec_states_fin ctx))).(create) (
      fun s =>
        match s as s0 return (type_denote (tf_states_type states_var_size s0)) with
        | sv => getenv ContextEnv env (tf_dfg_s sv)
        end
    ).

  Definition tf_dfg_states_init (x: tf_dfg_states) : tf_states_type tf_dfg_states_size x :=
    match x with
    | tf_dfg_s sv => states_var_init sv
    | tf_dfg_b _ => Bits.zero
    | tf_dfg_v _ _ => Bits.zero
    | tf_dfg_done => Bits.zero
    | tf_dfg_ov _ => Bits.zero
    end.

End States.
