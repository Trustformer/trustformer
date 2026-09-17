Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.Contract.

Require Import Coq.Lists.List.
Import ListNotations.

(* VALUE-level confidentiality over action SEQUENCES: the Public outputs are a
   function of the public data and the IP's responses, with the secret registers
   outside that set.  Per-action is unsound, hence the sequence (REVIEW.md 2.4). *)

Section Confidentiality.

  Context (ctx: TFSchedContext).

  Local Notation s_var := (tfs_spec_states ctx).
  Local Notation i_var := (tfs_spec_inputs ctx).
  Local Notation o_var := (tfs_spec_outputs ctx).
  Local Notation s_sz  := (tfs_spec_states_size ctx).
  Local Notation i_sz  := (tfs_spec_inputs_size ctx).
  Local Notation o_sz  := (tfs_spec_outputs_size ctx).
  Local Notation o_cls := (tfs_spec_outputs_class ctx).

  Existing Instance tfs_spec_states_fin.
  Existing Instance tfs_spec_inputs_fin.
  Existing Instance tfs_spec_outputs_fin.

  Local Notation sys_state :=
    (ContextEnv.(env_t) (tf_states_type s_sz)
     * ContextEnv.(env_t) (tf_outputs_type o_sz))%type.
  Local Notation input_t :=
    (forall x : i_var, type_denote (tf_inputs_type i_sz x)).

  Local Notation run ops sys input :=
    (tf_ops_run s_sz i_sz o_sz ops sys input).
  Local Notation ev w e sys input :=
    (tf_eval_expr s_sz i_sz o_sz (szB := w) e sys input).

  (* ------------------------------------------------------------------- *)
  (* The attacker's view: the Public outputs, and nothing else.  Secret    *)
  (* state is deliberately unconstrained -- that is the content.           *)
  (* ------------------------------------------------------------------- *)

  Definition pub_agree (sys sys': sys_state) : Prop :=
    forall o : o_var, o_cls o = Public -> (snd sys).[o] = (snd sys').[o].

  Lemma pub_agree_refl sys : pub_agree sys sys.
  Proof. intros o _; reflexivity. Qed.

  (* ------------------------------------------------------------------- *)
  (* The criterion, decidable and syntactic.                              *)
  (* ------------------------------------------------------------------- *)

  (* "Secret-free": mentions no secret register and no read of a Secret output.
     Inputs are free at any class, since the theorem shares them between the two
     runs.  The Secret-output clause is REVIEW.md 2.4. *)
  Fixpoint sf_expr (e: @tf_expr s_var i_var o_var) : bool :=
    match e with
    | tf_const _ => true
    | tf_svar _  => false
    | tf_ivar _  => true
    | tf_ovar o  => match o_cls o with Public => true | Secret => false end
    | tf_op1 _ a => sf_expr a
    | tf_op2 _ a b => sf_expr a && sf_expr b
    | tf_expr_if c t f => sf_expr c && (sf_expr t && sf_expr f)
    end.

  (* [g] records a secret-dependent enclosing branch condition.  Under such a
     guard every Public output stays unwritten: assigning even a CONSTANT to one
     inside a branch on [dp] leaks [dp]. *)
  Fixpoint sf_ops (g: bool) (ops: @tf_ops s_var i_var o_var) : bool :=
    match ops with
    | tf_ops_base tf_nop => true
    | tf_ops_base (tf_assign _ _) => true    (* a secret register may hold anything *)
    (* A call writes its REQUEST PORT, so it classifies as a [tf_output]: under a
       secret-dependent guard a drive publishes the branch condition, and with it
       whatever secret the condition came from. *)
    | tf_ops_base (tf_call req _ _ arg _) =>
        match o_cls req with
        | Secret => true                     (* Secret request ports may be arbitrary *)
        | Public => negb g && sf_expr arg
        end
    | tf_ops_base (tf_output o e) =>
        match o_cls o with
        | Secret => true                     (* Secret outputs may be arbitrary *)
        | Public => negb g && sf_expr e
        end
    | tf_ops_cons a b => sf_ops g a && sf_ops g b
    | tf_ops_if c t f =>
        let g' := (g || negb (sf_expr c))%bool in
        sf_ops g' t && sf_ops g' f
    end.

  Definition sf_action (a: tfs_spec_action ctx) : bool :=
    sf_ops false (tfs_spec_action_ops ctx a).

  (* Two reduction lemmas, so every proof below can stay in terms of [run]
     instead of unfolding the update machinery and losing the abbreviation. *)
  Lemma run_cons (a b: @tf_ops s_var i_var o_var) sys input :
    run (tf_ops_cons a b) sys input = run b (run a sys input) input.
  Proof.
    unfold tf_ops_run. cbn [tf_ops_updates].
    destruct (tf_ops_updates _ _ _ a sys input) as [u1 s1]. cbn [snd].
    destruct (tf_ops_updates _ _ _ b s1 input) as [u2 s2]. reflexivity.
  Qed.

  Lemma run_if (c: @tf_expr s_var i_var o_var) (t f: @tf_ops s_var i_var o_var)
      sys input :
    run (tf_ops_if c t f) sys input
    = if beq_dec (ev 1 c sys input) Bits.zero
      then run f sys input else run t sys input.
  Proof.
    unfold tf_ops_run. cbn [tf_ops_updates].
    destruct (beq_dec (ev 1 c sys input) Bits.zero); reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* Soundness of the expression criterion.                               *)
  (* ------------------------------------------------------------------- *)

  Lemma sf_expr_sound (e: @tf_expr s_var i_var o_var) :
    sf_expr e = true ->
    forall (sys sys': sys_state) (input: input_t) (szB: nat),
      pub_agree sys sys' ->
      ev szB e sys input = ev szB e sys' input.
  Proof.
    induction e; intros Hsf sys sys' input szB Hpub; cbn [sf_expr] in Hsf.
    - reflexivity.
    - discriminate.
    - reflexivity.
    - cbn [tf_eval_expr].
      destruct (o_cls v) eqn:Hc; [ | discriminate ].
      rewrite (Hpub v Hc). reflexivity.
    - cbn [tf_eval_expr]. destruct op.
      + rewrite (IHe Hsf sys sys' input szB Hpub). reflexivity.
      + rewrite (IHe Hsf sys sys' input source_size Hpub). reflexivity.
    - apply andb_prop in Hsf. destruct Hsf as [H1 H2].
      cbn [tf_eval_expr]. destruct op;
        try (rewrite (IHe1 H1 sys sys' input szB Hpub),
                     (IHe2 H2 sys sys' input szB Hpub); reflexivity).
      + (* comparison: operands are evaluated at their own width *)
        rewrite (IHe1 H1 sys sys' input cmp_sz Hpub),
                (IHe2 H2 sys sys' input cmp_sz Hpub); reflexivity.
      + (* concatenation: likewise, each side at its own width *)
        rewrite (IHe1 H1 sys sys' input hi_sz Hpub),
                (IHe2 H2 sys sys' input lo_sz Hpub); reflexivity.
    - apply andb_prop in Hsf. destruct Hsf as [Hc Htf].
      apply andb_prop in Htf. destruct Htf as [Ht Hf].
      cbn [tf_eval_expr].
      rewrite (IHe1 Hc sys sys' input 1 Hpub).
      destruct (beq_dec (ev 1 e1 sys' input) Bits.zero).
      + exact (IHe3 Hf sys sys' input szB Hpub).
      + exact (IHe2 Ht sys sys' input szB Hpub).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* Under a non-secret-free guard, nothing Public moves at all.          *)
  (* ------------------------------------------------------------------- *)

  Lemma sf_ops_guarded_frozen (ops: @tf_ops s_var i_var o_var) :
    sf_ops true ops = true ->
    forall (sys: sys_state) (input: input_t) (o: o_var),
      o_cls o = Public ->
      (snd (run ops sys input)).[o] = (snd sys).[o].
  Proof.
    induction ops; intros Hsf sys input o Hc; cbn [sf_ops] in Hsf.
    - destruct op as [| d e | d e | rq rv d e szA szB fn]; cbn [tf_ops_run tf_ops_updates
        tf_op_step_updates tf_op_step_commit tf_op_step_commit_output snd].
      + reflexivity.
      + reflexivity.
      + destruct (o_cls d) eqn:Hd; [ discriminate | ].
        destruct (eq_dec d o) as [Heq | Hne].
        * subst d. rewrite Hc in Hd. discriminate.
        * rewrite get_put_neq; [ reflexivity | exact Hne ].
      + (* a call writes its REQUEST port, so this is the tf_output case *)
        destruct (o_cls rq) eqn:Hd; [ discriminate | ].
        destruct (eq_dec rq o) as [Heq | Hne].
        * subst rq. rewrite Hc in Hd. discriminate.
        * rewrite get_put_neq; [ reflexivity | exact Hne ].
    - apply andb_prop in Hsf. destruct Hsf as [H1 H2].
      rewrite run_cons, (IHops2 H2 _ input o Hc), (IHops1 H1 sys input o Hc).
      reflexivity.
    - apply andb_prop in Hsf. destruct Hsf as [Ht Hf].
      rewrite run_if. destruct (beq_dec (ev 1 cond sys input) Bits.zero).
      + exact (IHops2 Hf sys input o Hc).
      + exact (IHops1 Ht sys input o Hc).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* Soundness of the statement criterion: one action.                    *)
  (* ------------------------------------------------------------------- *)

  Lemma sf_ops_sound (ops: @tf_ops s_var i_var o_var) (g: bool) :
    sf_ops g ops = true ->
    forall (sys sys': sys_state) (input: input_t),
      pub_agree sys sys' ->
      pub_agree (run ops sys input) (run ops sys' input).
  Proof.
    revert g. induction ops; intros g Hsf sys sys' input Hpub;
      cbn [sf_ops] in Hsf.
    - destruct op as [| d e | d e | rq rv d e szA szB fn]; intros o Hc;
        cbn [tf_ops_run tf_ops_updates tf_op_step_updates tf_op_step_commit
             tf_op_step_commit_output snd].
      + exact (Hpub o Hc).
      + exact (Hpub o Hc).
      + destruct (o_cls d) eqn:Hd.
        * (* Public destination: the criterion forces a secret-free RHS *)
          destruct g; [ discriminate | ]. cbn [negb andb] in Hsf.
          destruct (eq_dec d o) as [Heq | Hne].
          -- subst d. rewrite !get_put_eq.
             exact (sf_expr_sound e Hsf sys sys' input (o_sz o) Hpub).
          -- rewrite !get_put_neq by exact Hne. exact (Hpub o Hc).
        * (* Secret destination: nothing Public moves *)
          destruct (eq_dec d o) as [Heq | Hne].
          -- subst d. rewrite Hc in Hd. discriminate.
          -- rewrite !get_put_neq by exact Hne. exact (Hpub o Hc).
      + (* a call writes its REQUEST port -- the tf_output case, on [rq] *)
        destruct (o_cls rq) eqn:Hd.
        * (* Public request port: the criterion forces a secret-free payload *)
          destruct g; [ discriminate | ]. cbn [negb andb] in Hsf.
          destruct (eq_dec rq o) as [Heq | Hne].
          -- subst rq. rewrite !get_put_eq.
             exact (sf_expr_sound e Hsf sys sys' input (o_sz o) Hpub).
          -- rewrite !get_put_neq by exact Hne. exact (Hpub o Hc).
        * (* Secret request port: nothing Public moves *)
          destruct (eq_dec rq o) as [Heq | Hne].
          -- subst rq. rewrite Hc in Hd. discriminate.
          -- rewrite !get_put_neq by exact Hne. exact (Hpub o Hc).
    - apply andb_prop in Hsf. destruct Hsf as [H1 H2].
      rewrite !run_cons.
      exact (IHops2 g H2 _ _ input (IHops1 g H1 sys sys' input Hpub)).
    - apply andb_prop in Hsf. destruct Hsf as [Ht Hf].
      rewrite !run_if.
      destruct (sf_expr cond) eqn:Hc.
      + (* the condition is public, so both runs take the SAME branch *)
        rewrite <- (sf_expr_sound cond Hc sys sys' input 1 Hpub).
        destruct (beq_dec (ev 1 cond sys input) Bits.zero).
        * exact (IHops2 _ Hf sys sys' input Hpub).
        * exact (IHops1 _ Ht sys sys' input Hpub).
      + (* the condition may be secret, so the runs may take DIFFERENT branches.
           Under [g' = true] neither branch touches a Public output, so the
           agreement carries through regardless of which is taken. *)
        rewrite Bool.orb_true_r in Ht, Hf.
        intros o Hco.
        destruct (beq_dec (ev 1 cond sys  input) Bits.zero);
        destruct (beq_dec (ev 1 cond sys' input) Bits.zero).
        * rewrite (sf_ops_guarded_frozen ops2 Hf sys input o Hco),
                  (sf_ops_guarded_frozen ops2 Hf sys' input o Hco).
          exact (Hpub o Hco).
        * rewrite (sf_ops_guarded_frozen ops2 Hf sys input o Hco),
                  (sf_ops_guarded_frozen ops1 Ht sys' input o Hco).
          exact (Hpub o Hco).
        * rewrite (sf_ops_guarded_frozen ops1 Ht sys input o Hco),
                  (sf_ops_guarded_frozen ops2 Hf sys' input o Hco).
          exact (Hpub o Hco).
        * rewrite (sf_ops_guarded_frozen ops1 Ht sys input o Hco),
                  (sf_ops_guarded_frozen ops1 Ht sys' input o Hco).
          exact (Hpub o Hco).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE THEOREM, over sequences.                                          *)
  (* ------------------------------------------------------------------- *)

  Fixpoint run_seq (acts: list (tfs_spec_action ctx))
      (sys: sys_state) (input: input_t) : sys_state :=
    match acts with
    | [] => sys
    | a :: rest =>
        run_seq rest (run (tfs_spec_action_ops ctx a) sys input) input
    end.

  Theorem seq_confidential (acts: list (tfs_spec_action ctx)) :
    (forall a, sf_action a = true) ->
    forall (sys sys': sys_state) (input: input_t),
      pub_agree sys sys' ->
      pub_agree (run_seq acts sys input) (run_seq acts sys' input).
  Proof.
    intro Hall. induction acts as [| a rest IH]; intros sys sys' input Hpub.
    - exact Hpub.
    - cbn [run_seq]. apply IH.
      exact (sf_ops_sound _ false (Hall a) sys sys' input Hpub).
  Qed.

  (* With the IP's responses held fixed, the secret registers contribute NOTHING
     to any Public port, for any command sequence.  Named for the direct flow it
     rules out, the shared-response hypothesis being MVP.md 9 A1. *)
  Corollary no_direct_secret_flow
      (acts: list (tfs_spec_action ctx)) (input: input_t)
      (secrets secrets': ContextEnv.(env_t) (tf_states_type s_sz))
      (pub: ContextEnv.(env_t) (tf_outputs_type o_sz)) :
    (forall a, sf_action a = true) ->
    forall o, o_cls o = Public ->
      (snd (run_seq acts (secrets, pub) input)).[o]
      = (snd (run_seq acts (secrets', pub) input)).[o].
  Proof.
    intro Hall.
    exact (seq_confidential acts Hall (secrets, pub) (secrets', pub) input
             (fun o _ => eq_refl)).
  Qed.

End Confidentiality.

Print Assumptions sf_expr_sound.
Print Assumptions sf_ops_guarded_frozen.
Print Assumptions sf_ops_sound.
Print Assumptions seq_confidential.
Print Assumptions no_direct_secret_flow.
