(*! Declassification rule: for `n = Phi c t e`, wherever `c` holds the node's
    value IS the then-branch's -- the paper's PhiAUT, the one rule with a
    NON-EMPTY guard.  Both directions, downward giving the lockbox pattern. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

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

Definition phibranch_rule {s i o p} : decl_rule s i o p :=
  fun dfg =>
    flat_map
      (fun n =>
         let dflt := {| nid := 0; op := DFG_Empty; sz := 0 |} in
         match op (nth n (graph dfg) dflt) with
         | DFG_Phi cnd tid eid =>
             (* the selected arm and the phi carry the same bits *)
             let idt := fun vs : list (list bool) => nth 0 vs [] in
             [ {| di_target := n;   di_sources := [tid]; di_guard := [(cnd, true)];
                  di_extract := idt |}
             ; {| di_target := tid; di_sources := [n];   di_guard := [(cnd, true)];
                  di_extract := idt |}
             ; {| di_target := n;   di_sources := [eid]; di_guard := [(cnd, false)];
                  di_extract := idt |}
             ; {| di_target := eid; di_sources := [n];   di_guard := [(cnd, false)];
                  di_extract := idt |} ]
         | _ => []
         end)
      (List.seq 1 (length (graph dfg) - 1)).

(* Every instance carries a selector literal, so none of them seeds the
   unconditional taint fold: [uncond_instances] keeps only empty guards. *)
Lemma phibranch_guard_nonempty {s i o p} (dfg: @dfg_state_t s i o p)
      (inst: decl_instance) :
  List.In inst (phibranch_rule dfg) -> di_guard inst <> [].
Proof.
  unfold phibranch_rule. intro Hin.
  apply in_flat_map in Hin. destruct Hin as [n [_ Hi]].
  destruct (op (nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |}))
    as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa
       | dp darg den | sp stok sen | ja jb | ];
    cbn [List.In] in Hi; try contradiction.
  destruct Hi as [Hi | [Hi | [Hi | [Hi | []]]]]; subst inst; discriminate.
Qed.

Section Soundness.
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
  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).
  Local Notation sched_input_t :=
    (forall x : tfs_inputs sched, type_denote (tf_inputs_type (tfs_inputs_size sched) x)).
  Local Notation a_index := (Vect.index (length (buffer_needs ctx cost_limit))).
  Local Notation rvalid act a_idx pi n ss input :=
    (tf_eval_expr (tfs_states_size sched) (tfs_inputs_size sched)
       (tfs_outputs_size sched) (szB := 1)
       (snd (compile_dfg_expr_at ctx (buffer_needs ctx cost_limit) pi
               (length (graph (build_dfg ctx act))) a_idx
               (build_dfg ctx act) n (sample_bufs ctx cost_limit act a_idx)))
       ss input) (only parsing).

  Local Notation nsz act n :=
    (sz (nth n (graph (build_dfg ctx act)) {| nid := 0; op := DFG_Empty; sz := 0 |})).

  (* Under the guard the phi's reference expression reduces to the branch's,
     at the branch's own width.  This is the whole content of the rule; the
     four instances are the four ways of reading the resulting equation. *)
  Lemma phi_selects (act: tfs_action sched) (a_idx: a_index) (input: sched_input_t)
      (ss: sched_sys_state) (n cnd tid eid: nid_t) (b: bool) :
    1 <= n ->
    n < length (graph (build_dfg ctx act)) ->
    op (nth n (graph (build_dfg ctx act))
          {| nid := 0; op := DFG_Empty; sz := 0 |}) = DFG_Phi cnd tid eid ->
    nval ctx cost_limit act a_idx ss input 1 cnd = bit_of b ->
    nval ctx cost_limit act a_idx ss input (nsz act n) n
    = nval ctx cost_limit act a_idx ss input (nsz act n) (if b then tid else eid).
  Proof.
    intros Hn1 Hlen Hop Hcnd.
    pose proof (nre_phi ctx cost_limit act a_idx n cnd tid eid Hn1 Hlen Hop) as Hnre.
    unfold nval in Hcnd |- *. rewrite Hnre. cbn [tf_eval_expr].
    destruct b; unfold bit_of in Hcnd.
    - assert (Hnz : beq_dec (tf_eval_expr (tfs_states_size sched) (tfs_inputs_size sched)
                               (tfs_outputs_size sched) (szB := 1)
                               (node_ref_expr ctx cost_limit act a_idx cnd) ss input)
                      Bits.zero = false).
      { rewrite Hcnd. destruct (beq_dec (Bits.ones 1) Bits.zero) eqn:Hb;
          [ | reflexivity ].
        exfalso. apply beq_dec_iff in Hb. discriminate. }
      rewrite Hnz. reflexivity.
    - assert (Hz : beq_dec (tf_eval_expr (tfs_states_size sched) (tfs_inputs_size sched)
                              (tfs_outputs_size sched) (szB := 1)
                              (node_ref_expr ctx cost_limit act a_idx cnd) ss input)
                     Bits.zero = true)
        by (rewrite Hcnd; apply beq_dec_refl).
      rewrite Hz. reflexivity.
  Qed.


  (* A rule reads a source where that source is valid.  Two of the four
     instances read the phi FROM an arm, so they want the phi's validity given
     an arm's -- the converse of [nrv_peel_phi_crit]. *)
  Definition phibranch_settled (act: tfs_action sched) (a_idx: a_index) : Prop :=
    forall n cnd tid eid,
      node_op ctx cost_limit act n = DFG_Phi cnd tid eid ->
      forall (p: list lit) (ss: sched_sys_state) (inp: sched_input_t),
        rvalid act a_idx p tid ss inp = Bits.ones 1
        \/ rvalid act a_idx p eid ss inp = Bits.ones 1 ->
        rvalid act a_idx p n ss inp = Bits.ones 1.

  Theorem phibranch_rule_sound (act: tfs_action sched) (a_idx: a_index)
      (input: sched_input_t) (i: decl_instance) :
    List.In i (phibranch_rule (build_dfg ctx act)) ->
    phibranch_settled act a_idx ->
    instance_sound ctx cost_limit act a_idx input i.
  Proof.
    unfold phibranch_rule. intros Hin Hset.
    apply in_flat_map in Hin. destruct Hin as [n [Hseq Hi]].
    apply in_seq in Hseq. destruct Hseq as [Hn1 Hn2].
    assert (Hlen : n < length (graph (build_dfg ctx act))) by lia.
    cbv zeta in Hi.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa | dp darg den | sp stok sen | ja jb | ] eqn:Hop;
      cbn [List.In] in Hi; try contradiction.

    (* widths: both branches carry the node's own width *)
    assert (Hnode_in : List.In (nth n (graph (build_dfg ctx act))
                                  {| nid := 0; op := DFG_Empty; sz := 0 |})
                         (graph (build_dfg ctx act)))
      by (apply nth_In; exact Hlen).
    pose proof (wfg_build_dfg ctx cost_limit act _ Hnode_in) as Hfg.
    unfold node_args_sz in Hfg. rewrite Hop in Hfg.
    destruct Hfg as [_ [Hft Hfe]].
    destruct (wsz_node_sz ctx cost_limit act tid _ Hft) as [_ Htsz].
    destruct (wsz_node_sz ctx cost_limit act eid _ Hfe) as [_ Hesz].

    (* the guard names the selector, so [pi_holds] is exactly its value *)
    (* generalised over the input: the two runs carry their own *)
    assert (Hsel : forall (b: bool) (inp: sched_input_t) (ss: sched_sys_state),
              pi_holds ctx cost_limit act a_idx inp [(cnd, b)] ss ->
              nval ctx cost_limit act a_idx ss inp
                (nsz act n) n
              = nval ctx cost_limit act a_idx ss inp
                (nsz act n) (if b then tid else eid)).
    { intros b inp ss Hp.
      exact (phi_selects act a_idx inp ss n cnd tid eid b Hn1 Hlen Hop
               (Hp cnd b (or_introl eq_refl))). }

    destruct (node_args_range ctx cost_limit act n Hn1 Hlen cnd
                ltac:(unfold get_args; rewrite Hop; left; reflexivity)) as [Hc1 _].
    destruct (node_args_range ctx cost_limit act n Hn1 Hlen tid
                ltac:(unfold get_args; rewrite Hop; right; left; reflexivity))
      as [Ht1 _].
    destruct (node_args_range ctx cost_limit act n Hn1 Hlen eid
                ltac:(unfold get_args; rewrite Hop; right; right; left; reflexivity))
      as [He1 _].
    assert (Hopn : node_op ctx cost_limit act n = DFG_Phi cnd tid eid)
      by (unfold Definitions.node_op; rewrite Hop; reflexivity).

    (* An arm's validity, from the phi's: the critical shape waits on both arms
       at the unextended path, the selecting one on the arm it picks. *)
    assert (Harm : forall (p: list lit) (b: bool) (inp: sched_input_t) (ss: sched_sys_state),
              pi_holds ctx cost_limit act a_idx inp [(cnd, b)] ss ->
              rvalid act a_idx p n ss inp = Bits.ones 1 ->
              rvalid act a_idx (if phi_crit (get_tainted ctx (build_dfg ctx act))
                                  (decl_facts ctx (build_dfg ctx act)) cnd p
                                then p else (cnd, b) :: p)
                (if b then tid else eid) ss inp = Bits.ones 1).
    { intros p b inp s Hp Hvn.
      destruct (phi_crit (get_tainted ctx (build_dfg ctx act))
                  (decl_facts ctx (build_dfg ctx act)) cnd p) eqn:Hcrit.
      - destruct (nrv_peel_phi_crit ctx cost_limit act a_idx n cnd tid eid p s inp
                    Hopn Hcrit Hc1 Ht1 He1 Hlen Hvn) as [_ [Htv Hev]].
        destruct b; assumption.
      - destruct (nrv_peel_phi_sel ctx cost_limit act a_idx n cnd tid eid p s inp
                    Hopn Hcrit Hc1 Ht1 He1 Hlen Hvn) as [_ [Htv Hev]].
        pose proof (Hp cnd b (or_introl eq_refl)) as Hcv.
        unfold Definitions.nval, bit_of in Hcv.
        destruct b.
        + apply Htv. rewrite Hcv. exact ones1_neq_zero.
        + apply Hev. exact Hcv. }

    (* ... and the path the arm is valid at is one the run took *)
    assert (Hpath : forall (p: list lit) (b: bool) (inp: sched_input_t) (ss: sched_sys_state),
              pi_holds ctx cost_limit act a_idx inp p ss ->
              pi_holds ctx cost_limit act a_idx inp [(cnd, b)] ss ->
              pi_holds ctx cost_limit act a_idx inp
                (if phi_crit (get_tainted ctx (build_dfg ctx act))
                     (decl_facts ctx (build_dfg ctx act)) cnd p
                 then p else (cnd, b) :: p) ss).
    { intros p b inp s Hpp Hp.
      destruct (phi_crit (get_tainted ctx (build_dfg ctx act))
                  (decl_facts ctx (build_dfg ctx act)) cnd p);
        [ exact Hpp
        | exact (pi_holds_cons ctx cost_limit act a_idx inp cnd b p s Hpp
                   (Hp cnd b (or_introl eq_refl))) ]. }

    destruct Hi as [Hi | [Hi | [Hi | [Hi | []]]]]; subst i;
      intros ss ss' input' pi0 Hpub Hp Hp' Hsrc Hpi Hpi' Hv Hv';
      cbn [di_sources di_target di_guard] in Hsrc, Hp, Hp', Hv, Hv' |- *.
    - rewrite (Hsel true input ss Hp), (Hsel true input' ss' Hp'), <- Htsz.
      exact (Hsrc tid _ (or_introl eq_refl)
               (Hpath pi0 true input  ss  Hpi  Hp )
               (Hpath pi0 true input' ss' Hpi' Hp')
               (Harm pi0 true input  ss  Hp  Hv )
               (Harm pi0 true input' ss' Hp' Hv')).
    - (* the phi read FROM the then arm *)
      rewrite Htsz, <- (Hsel true input ss Hp), <- (Hsel true input' ss' Hp').
      exact (Hsrc n pi0 (or_introl eq_refl) Hpi Hpi'
               (Hset n cnd tid eid Hopn pi0 ss  input  (or_introl Hv ))
               (Hset n cnd tid eid Hopn pi0 ss' input' (or_introl Hv'))).
    - rewrite (Hsel false input ss Hp), (Hsel false input' ss' Hp'), <- Hesz.
      exact (Hsrc eid _ (or_introl eq_refl)
               (Hpath pi0 false input  ss  Hpi  Hp )
               (Hpath pi0 false input' ss' Hpi' Hp')
               (Harm pi0 false input  ss  Hp  Hv )
               (Harm pi0 false input' ss' Hp' Hv')).
    - (* the phi read FROM the else arm *)
      rewrite Hesz, <- (Hsel false input ss Hp), <- (Hsel false input' ss' Hp').
      exact (Hsrc n pi0 (or_introl eq_refl) Hpi Hpi'
               (Hset n cnd tid eid Hopn pi0 ss  input  (or_intror Hv ))
               (Hset n cnd tid eid Hopn pi0 ss' input' (or_intror Hv'))).
  Qed.


  (* THE REVERSING FUNCTION IS CORRECT: under its own guard the phi and the arm
     it selects carry the same bits, so the identity is the inverse. *)
  Theorem phibranch_rule_extracts (act: tfs_action sched) (a_idx: a_index)
      (i: decl_instance) :
    List.In i (phibranch_rule (build_dfg ctx act)) ->
    instance_extracts ctx cost_limit act a_idx i.
  Proof.
    unfold phibranch_rule. intro Hin.
    apply in_flat_map in Hin. destruct Hin as [n [Hseq Hi]].
    apply in_seq in Hseq. destruct Hseq as [Hn1 Hn2].
    assert (Hlen : n < length (graph (build_dfg ctx act))) by lia.
    cbv zeta in Hi.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa | dp darg den | sp stok sen | ja jb | ] eqn:Hop;
      cbn [List.In] in Hi; try contradiction.

    assert (Hnode_in : List.In (nth n (graph (build_dfg ctx act))
                                  {| nid := 0; op := DFG_Empty; sz := 0 |})
                         (graph (build_dfg ctx act)))
      by (apply nth_In; exact Hlen).
    pose proof (wfg_build_dfg ctx cost_limit act _ Hnode_in) as Hfg.
    unfold node_args_sz in Hfg. rewrite Hop in Hfg.
    destruct Hfg as [_ [Hft Hfe]].
    destruct (wsz_node_sz ctx cost_limit act tid _ Hft) as [_ Htsz].
    destruct (wsz_node_sz ctx cost_limit act eid _ Hfe) as [_ Hesz].

    assert (Hsel : forall (b: bool) (inp: sched_input_t) (ss: sched_sys_state),
              pi_holds ctx cost_limit act a_idx inp [(cnd, b)] ss ->
              nval ctx cost_limit act a_idx ss inp (nsz act n) n
              = nval ctx cost_limit act a_idx ss inp
                  (nsz act n) (if b then tid else eid)).
    { intros b inp ss Hp.
      exact (phi_selects act a_idx inp ss n cnd tid eid b Hn1 Hlen Hop
               (Hp cnd b (or_introl eq_refl))). }

    destruct Hi as [Hi | [Hi | [Hi | [Hi | []]]]]; subst i;
      intros ss input Hp;
      cbn [di_sources di_target di_guard di_extract] in Hp |- *;
      cbn [map nth].
    - rewrite (Hsel true input ss Hp), <- Htsz. reflexivity.
    - rewrite Htsz, <- (Hsel true input ss Hp). reflexivity.
    - rewrite (Hsel false input ss Hp), <- Hesz. reflexivity.
    - rewrite Hesz, <- (Hsel false input ss Hp). reflexivity.
  Qed.
  (* THE SETTLEDNESS LIFT: a phi carries its condition's validity, so the
     condition of the guard has settled wherever the phi has; and under that
     guard the arm the condition names has settled too.  The two instances that
     read the phi FROM an arm use [phibranch_settled], as their soundness
     does. *)
  Theorem phibranch_rule_lifts (act: tfs_action sched) (a_idx: a_index)
      (i: decl_instance) :
    List.In i (phibranch_rule (build_dfg ctx act)) ->
    phibranch_settled act a_idx ->
    instance_in_range ctx cost_limit act i
    /\ instance_guards_sized ctx cost_limit act i
    /\ instance_lifts ctx cost_limit act a_idx i.
  Proof.
    unfold phibranch_rule. intros Hin Hset.
    apply in_flat_map in Hin. destruct Hin as [n [Hseq Hi]].
    apply in_seq in Hseq. destruct Hseq as [Hn1 Hn2].
    assert (Hlen : n < length (graph (build_dfg ctx act))) by lia.
    cbv zeta in Hi.
    destruct (op (nth n (graph (build_dfg ctx act))
                    {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | uop arg | bop a1 a2 | arg | cnd tid eid | slat sa | dp darg den | sp stok sen | ja jb | ] eqn:Hop;
      cbn [List.In] in Hi; try contradiction.
    assert (Hopn : node_op ctx cost_limit act n = DFG_Phi cnd tid eid)
      by (unfold Definitions.node_op; rewrite Hop; reflexivity).
    destruct (node_args_range ctx cost_limit act n Hn1 Hlen cnd
                ltac:(unfold get_args; rewrite Hop; left; reflexivity))
      as [Hc1 Hc2].
    destruct (node_args_range ctx cost_limit act n Hn1 Hlen tid
                ltac:(unfold get_args; rewrite Hop; right; left; reflexivity))
      as [Ht1 Ht2].
    destruct (node_args_range ctx cost_limit act n Hn1 Hlen eid
                ltac:(unfold get_args; rewrite Hop; right; right; left; reflexivity))
      as [He1 He2].
    (* the phi's own arguments, wherever the phi has settled *)
    assert (Hargs : forall (ss: sched_sys_state) (input: sched_input_t),
              Definitions.settled_at ctx cost_limit act a_idx ss input n ->
              Definitions.settled_at ctx cost_limit act a_idx ss input cnd
              /\ (Definitions.nval ctx cost_limit act a_idx ss input 1 cnd
                    <> Bits.zero ->
                  Definitions.settled_at ctx cost_limit act a_idx ss input tid)
              /\ (Definitions.nval ctx cost_limit act a_idx ss input 1 cnd
                    = Bits.zero ->
                  Definitions.settled_at ctx cost_limit act a_idx ss input eid))
      by (intros ss input Hst;
          exact (IPRProof.phi_args_settled ctx cost_limit act a_idx ss input
                   n cnd tid eid Hopn Hc1 Ht1 He1 Hlen Hst)).
    (* the guard literal is the phi's condition, which compiles at width one *)
    destruct (wsz_node_sz ctx cost_limit act cnd 1
                ltac:(pose proof (wfg_build_dfg ctx cost_limit act
                                    (nth n (graph (build_dfg ctx act))
                                       {| nid := 0; op := DFG_Empty; sz := 0 |})
                                    (nth_In _ _ Hlen)) as Hfg;
                      unfold node_args_sz in Hfg; rewrite Hop in Hfg;
                      exact (proj1 Hfg)))
      as [_ Hcsz].
    destruct Hi as [Hi | [Hi | [Hi | [Hi | []]]]]; subst i;
      (split; [ intros m Hm; cbn [di_target di_sources di_guard map List.app fst] in Hm;
                destruct Hm as [<- | [<- | [<- | []]]]; split; lia
              | split; [ intros l Hl;
                         cbn [di_guard] in Hl; destruct Hl as [<- | []];
                         cbn [fst]; exact Hcsz | ] ]);
      intros ss input Hst;
      cbn [di_target di_sources di_guard map fst] in Hst |- *.
    - (* the phi from its then-arm's value, under [cnd] *)
      split; [ intros c0 [<- | []]; exact (proj1 (Hargs ss input Hst)) | ].
      intros Hpi s Hs. destruct Hs as [<- | []].
      apply (proj1 (proj2 (Hargs ss input Hst))).
      rewrite (Hpi cnd true (or_introl eq_refl)). exact ones1_neq_zero.
    - (* the then-arm from the phi, under [cnd] *)
      destruct Hst as [pi [Hpi Hv]].
      assert (Hvn : Definitions.settled_at ctx cost_limit act a_idx ss input n)
        by (exists pi; split;
            [ exact Hpi | exact (Hset n cnd tid eid Hopn pi ss input (or_introl Hv)) ]).
      split; [ intros c0 [<- | []]; exact (proj1 (Hargs ss input Hvn)) | ].
      intros _ s Hs. destruct Hs as [<- | []]. exact Hvn.
    - (* the phi from its else-arm's value, under [not cnd] *)
      split; [ intros c0 [<- | []]; exact (proj1 (Hargs ss input Hst)) | ].
      intros Hpi s Hs. destruct Hs as [<- | []].
      apply (proj2 (proj2 (Hargs ss input Hst))).
      exact (Hpi cnd false (or_introl eq_refl)).
    - (* the else-arm from the phi, under [not cnd] *)
      destruct Hst as [pi [Hpi Hv]].
      assert (Hvn : Definitions.settled_at ctx cost_limit act a_idx ss input n)
        by (exists pi; split;
            [ exact Hpi | exact (Hset n cnd tid eid Hopn pi ss input (or_intror Hv)) ]).
      split; [ intros c0 [<- | []]; exact (proj1 (Hargs ss input Hvn)) | ].
      intros _ s Hs. destruct Hs as [<- | []]. exact Hvn.
  Qed.

End Soundness.

