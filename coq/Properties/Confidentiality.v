Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Utils.Common.
Require Import Koika.Utils.Environments.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.Contract.

Require Import Coq.Lists.List.
Import ListNotations.

(*
    VALUE-level confidentiality, over action SEQUENCES.

    The companion to IPR.v: that file says the cycle count carries nothing
    secret, this one says the VALUES on the Public ports do not either.  They
    are deliberately separate theorems -- one is about what the outputs are, the
    other about how long they take, and conflating them is how information-flow
    arguments go wrong (agents/mars/INSIGHTS.md).

    WHY SEQUENCES.  Per-action is unsound.  [crypt_key := dp] in one action and
    [dout := crypt_key] in the next each satisfy a per-action criterion in
    isolation, and DP is published (REVIEW.md section 2.4).  The invariant that
    survives composition is "every Public output is secret-free; Secret outputs
    may be arbitrary", carried across the whole sequence.

    WHAT IS PROVED, precisely.  Two runs whose SECRET STATE differs arbitrarily,
    starting from Public outputs that agree and driven by the same inputs, end
    with Public outputs that still agree -- after any sequence of actions.  So
    no secret register ever reaches an attacker-visible port through the
    module's own wiring.

    WHAT IS NOT PROVED, and cannot be.  The input is shared between the two
    runs, which models "the crypto IP returned the same answer to both".  For
    MARS that is the assume-guarantee surface made concrete: MVP.md section 9 A1
    says crypt_res is the HMAC of the presented message, i.e. a FUNCTION of what
    the module sent.  Two runs with different DP send different keys and would
    get different answers back, so this theorem says nothing about them -- and
    it must not, because [dout = HMAC(AK, snap)] IS a function of AK by
    construction and exporting a DP-derived MAC is the entire point of
    MARS_Quote.

    The honest reading is therefore ROADMAP.md's tiers: the only route from a
    secret to a Public port is through the crypto oracle.  Everything the module
    does with its own wires is covered here; what the oracle does with the key
    is HMAC's security, not a datapath property.  Refining the shared input into
    an explicit oracle f(key, msg) is the remaining strengthening; it needs the
    trusted inputs to be computed from the trusted outputs during the run, which
    the single-step semantics does not currently express.
 *)

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

  (* "Secret-free": mentions no secret register and no read of a Secret
     output.  Inputs are allowed at any class because the theorem shares them
     between the two runs -- see the header.  A read of a Secret OUTPUT is not
     allowed, and that is the clause REVIEW.md section 2.4 is about: output
     variables are readable, so without it [crypt_key := dp] followed by
     [dout := crypt_key] would pass. *)
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

  (* [g] records that some enclosing branch condition was NOT secret-free.
     Under such a guard no Public output may be written at all -- assigning a
     CONSTANT to a public output inside a branch on [dp] leaks [dp], which is
     why the enclosing-condition clause is load-bearing rather than cosmetic. *)
  Fixpoint sf_ops (g: bool) (ops: @tf_ops s_var i_var o_var) : bool :=
    match ops with
    | tf_ops_base tf_nop => true
    | tf_ops_base (tf_assign _ _) => true    (* a secret register may hold anything *)
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
    - destruct op as [| d e | d e]; cbn [tf_ops_run tf_ops_updates
        tf_op_step_updates tf_op_step_commit tf_op_step_commit_output snd].
      + reflexivity.
      + reflexivity.
      + destruct (o_cls d) eqn:Hd; [ discriminate | ].
        destruct (eq_dec d o) as [Heq | Hne].
        * subst d. rewrite Hc in Hd. discriminate.
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
    - destruct op as [| d e | d e]; intros o Hc;
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

  (* The reading that matters: two devices whose SECRETS differ arbitrarily are
     indistinguishable on their Public ports, for any command sequence. *)
  Corollary secrets_never_reach_public
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
Print Assumptions secrets_never_reach_public.
