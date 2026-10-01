(*! The scheduled design's register file: [tf_dfg_states] is one register per
    spec state variable, per buffered node, per validity bit, per IP drive
    port, plus [done].  Everything here is indexed by the buffer table [bn],
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
  (* The buffer table, computed once by [tfs_schedule] and passed to everything
     that mentions a register. *)
  Context (bn : list (list (nid_t * (nat * sz_t)))).

  Local Notation tf_dfg_states := (tf_dfg_states_t (states_var:=states_var) (ips_var:=ips_var) (buffer_needs:=bn)).

  Instance show_tf_dfg_states : Show tf_dfg_states :=
    { show := fun dfg_s =>
        match dfg_s with
        | tf_dfg_s s => String.append "s_" (show s)
        | tf_dfg_b a_idx n_idx => String.append "b_" (String.append (show (index_to_nat a_idx)) (String.append "_" (show (index_to_nat n_idx))))
        | tf_dfg_v a_idx n_idx => String.append "v_" (String.append (show (index_to_nat a_idx)) (String.append "_" (show (index_to_nat n_idx))))
        | tf_dfg_done => "done"
        | tf_dfg_ov p => String.append "ip_" (show p)
        end }.

  Definition tf_dfg_states_size (dfg_s: tf_dfg_states) : sz_t :=
    match dfg_s with
    | tf_dfg_s s => states_var_size s
    | tf_dfg_b a_idx b_idx => snd (snd (nth (index_to_nat b_idx) (nth (index_to_nat a_idx) bn []) (0, (0, 0))))
    | tf_dfg_v a_idx b_idx => 1
    | tf_dfg_done => 1
    | tf_dfg_ov p => 1 + ip_req_sz (ip_of p)
    end.

  Definition done_signal := tf_dfg_done (states_var:=states_var) (ips_var:=ips_var) (buffer_needs:=bn).

  Definition reset_states : list tf_dfg_states :=  
    flat_map 
      (fun a_idx => match index_of_nat (length bn) a_idx with
        | Some a_idx' =>
          flat_map (fun n_idx => match index_of_nat (length (nth (index_to_nat a_idx') bn [])) n_idx with
            | Some n_idx' =>
              [ tf_dfg_b a_idx' n_idx'; tf_dfg_v a_idx' n_idx' ]
            | None => [] (* should not happen *)
            end ) (List.seq 0 (length (nth (index_to_nat a_idx') bn [])))
        | None => [] (* should not happen *)
        end)
      (List.seq 0 (length bn)).
  (* EXPERIMENT: strobes are not in reset_states yet; the real implementation
     must add them, which needs NoDup_app in reset_states_nodup. *)

  Instance tf_dfg_states_fin2 : FiniteType2 tf_dfg_states.
  Proof.  
    unshelve econstructor.
    - intro s. destruct s.
      + exact (0, 0).
      + exact (1, finite_index state).
      + exact (3 + finite_index a_idx, finite_index n_idx).
      + exact (3 + (Datatypes.length (finite_elements (T:=(Vect.index (Datatypes.length bn))))) + finite_index a_idx, finite_index n_idx).
      + exact (2, (@finite_index ips_var ips_var_fin p)).
        
    - refine ([ [tf_dfg_done] ] ++ 
              [ map tf_dfg_s finite_elements ] ++ 
              [ map tf_dfg_ov (@finite_elements ips_var ips_var_fin) ] ++ 
              map (fun a => map (tf_dfg_b a) finite_elements) finite_elements ++ 
              map (fun a => map (tf_dfg_v a) finite_elements) finite_elements).

    - intros x n m EQ.
      destruct x; inversion EQ; clear EQ; subst.
      + (* tf_dfg_done *)
        exists [tf_dfg_done]. split; auto.
      + (* tf_dfg_s *)
        exists (map tf_dfg_s finite_elements). split; auto.
        rewrite map_nth_error with (d:=state); auto. rewrite finite_surjective. reflexivity.
      + (* tf_dfg_b *)
        exists (map (tf_dfg_b a_idx) finite_elements). split; auto.
        * cbn [nth_error List.app].
          apply nth_error_app_l.
          rewrite map_nth_error with (d:=a_idx); auto.
          change (index_to_nat a_idx) with (finite_index a_idx).
          apply (finite_surjective a_idx).
        * rewrite map_nth_error with (d:=n_idx); auto. 
          change (index_to_nat n_idx) with (finite_index n_idx).
          rewrite finite_surjective. reflexivity.
      + (* tf_dfg_v *)
        exists (map (tf_dfg_v a_idx) finite_elements). split.
        * cbn [nth_error List.app].
          rewrite nth_error_app2. 
          2: {  repeat rewrite map_length. cbn. lia. }
          repeat rewrite map_length. cbn.
          rewrite Nat.add_comm, Nat.add_sub. 
          rewrite map_nth_error with (d:=a_idx); auto.
          change (index_to_nat a_idx) with (finite_index a_idx).
          change (vect_to_list (all_indices (Datatypes.length bn))) with (finite_elements (T:=Vect.index (Datatypes.length bn))).
          apply (finite_surjective a_idx).
        * rewrite map_nth_error with (d:=n_idx); auto. 
          change (index_to_nat n_idx) with (finite_index n_idx).
          rewrite finite_surjective. reflexivity.
      + (* tf_dfg_ov -- a flat group at a LITERAL index, so this is the
           [tf_dfg_s] case verbatim *)
        exists (map tf_dfg_ov (@finite_elements ips_var ips_var_fin)). split; auto.
        rewrite map_nth_error with (d:=p); auto. rewrite finite_surjective. reflexivity.
    - intros n l Hn m x Hm.
      destruct n as [|n].
      { inversion Hn; subst. destruct m; inversion Hm; subst. reflexivity. timeout 10 scongruence use: nth_error_nil unfold: tfs_spec_states. }
      destruct n as [|n].
      { inversion Hn; subst. apply nth_error_map_inv in Hm. destruct Hm as [s [Hs ?]]; subst.
        apply finite_elements_index in Hs. subst. reflexivity. }
      (* group 2 is the flat tf_dfg_ov block -- same shape as tf_dfg_s *)
      destruct n as [|n].
      { inversion Hn; subst. apply nth_error_map_inv in Hm. destruct Hm as [o [Ho ?]]; subst.
        apply finite_elements_index in Ho. subst. reflexivity. }
      
      rewrite nth_error_app2 in Hn by (simpl; lia).
      change (S (S (S n)) - Datatypes.length [[tf_dfg_done]]) with (S (S n)) in *.

      cbn [nth_error List.app] in Hn.
      destruct (lt_dec n (length (finite_elements (T := Vect.index (Datatypes.length bn))))) as [HLT | HGE].      
      + rewrite nth_error_app1 in Hn by (rewrite map_length; auto).
        apply nth_error_map_inv in Hn. destruct Hn as [a_idx' [Ha EQ_l]]; subst l.
        apply nth_error_map_inv in Hm. destruct Hm as [n_idx' [Hn' EQ_x]]; subst x.

        apply finite_elements_index in Ha.
        apply finite_elements_index in Hn'.
        subst n m. simpl. 
        reflexivity.
      + rewrite nth_error_app2 in Hn by (rewrite map_length; lia).
        repeat rewrite map_length in Hn.
        apply nth_error_map_inv in Hn. destruct Hn as [a_idx' [Ha EQ_l]]; subst l.
        apply nth_error_map_inv in Hm. destruct Hm as [n_idx' [Hn' EQ_x]]; subst x.
        apply finite_elements_index in Ha.
        apply finite_elements_index in Hn'.
        subst m. simpl. f_equal. 
        (* hammer *) timeout 10 sauto.
    - apply Forall_app; split; [| apply Forall_app; split; [| apply Forall_app; split]].
      + repeat constructor. (* hammer *) timeout 10 sfirstorder.
      + repeat constructor. cbn [map]. rewrite map_map. apply NoDup_map_pair. apply finite_injective.
      + (* the flat tf_dfg_ov block *)
        repeat constructor. cbn [map]. rewrite map_map. apply NoDup_map_pair. apply finite_injective.
      + apply Forall_app; split.
        * (* Block for tf_dfg_b *)
          apply Forall_map. apply Forall_forall. intros a_idx' Hin.
          rewrite map_map. apply NoDup_map_pair.
          apply finite_injective.
        * (* Block for tf_dfg_v *)
          apply Forall_map. apply Forall_forall. intros a_idx' Hin.
          rewrite map_map. apply NoDup_map_pair.
          apply finite_injective.
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
        | tf_dfg_b a_idx n_idx => Bits.zero
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
    | tf_dfg_b _ _ => Bits.zero
    | tf_dfg_v _ _ => Bits.zero
    | tf_dfg_done => Bits.zero
    | tf_dfg_ov _ => Bits.zero
    end.

End States.
