(*! The attacker's recipe is right.  Every value it works out from the published
    bits is the run's own value wherever the hardware reads that node, so the
    latency it computes is the design's. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.DFG.
Require Import Trustformer.Declassification.Recover.
Require Import Trustformer.Declassification.PacketLemmas.

Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

Lemma find_map_some {A B} (f: A -> option B) (l: list A) (b: B) :
  find_map f l = Some b -> exists a, In a l /\ f a = Some b.
Proof.
  induction l as [| a l IH]; cbn [find_map]; intro H; [ discriminate | ].
  destruct (f a) as [b' |] eqn:Hfa.
  - injection H as <-. exists a. split; [ left; reflexivity | exact Hfa ].
  - destruct (IH H) as [a' [Hin Hf]].
    exists a'. split; [ right; exact Hin | exact Hf ].
Qed.

(* ================================================================= *)
(* THE RECIPE AIMS AT ANY VALUATION OBEYING OPS, PACKETS, IPs.       *)
(* ================================================================= *)
Section RecipeSound.
  Context {s_var i_var o_var p_var: Type} {p_eq: EqDec p_var}.
  Context (ips: p_var -> ip_decl).
  Context (decls: list (decl_packet s_var i_var o_var p_var)).
  Context (g: @dfg_state_t s_var i_var o_var p_var).
  Context (V: valuation g).

  Definition guard_true (en: list (nid_t * bool)) : bool :=
    forallb (fun l => Bool.eqb (nonzero (V (fst l))) (snd l)) en.

  Hypothesis Hws : well_sized g.
  Hypothesis Hcons : consistent g V.
  Hypothesis Hsample_off : forall n p tok en,
    op (node_at g n) = DFG_Sample p tok en -> guard_true en = false -> V n = Bits.zero.
  Hypothesis Hsample_on : forall n p tok en a,
    op (node_at g n) = DFG_Sample p tok en -> guard_true en = true ->
    payload_of (p_eq := p_eq) g n = Some a ->
    V n = convert (ip_fn (ips p) (convert (V a))).
  Hypothesis Hstall : forall n l a, op (node_at g n) = DFG_Stall l a -> V n = Bits.zero.
  Hypothesis Hjoin : forall n a b, op (node_at g n) = DFG_Join a b -> V n = Bits.zero.
  Hypothesis Hdrive : forall n p a en,
    op (node_at g n) = DFG_Drive p a en -> V n = convert (V a).

  Definition sound_known (k: known g) : Prop := forall n v, k n = Some v -> v = V n.

  Lemma guard_val_sound (k: known g) en b :
    sound_known k -> guard_val g k en = Some b -> guard_true en = b.
  Proof.
    intro Hk. revert b. induction en as [| [c bc] en IH]; intros b Hg; cbn [guard_val] in Hg.
    - injection Hg as <-. reflexivity.
    - destruct (k c) as [x |] eqn:Hc; [ | discriminate ].
      destruct (guard_val g k en) as [r |] eqn:Hr; [ | discriminate ].
      injection Hg as <-. unfold guard_true in *. cbn [forallb fst snd].
      rewrite <- (Hk c x Hc). f_equal. apply (IH r eq_refl).
  Qed.

  Lemma guard_true_holds en : guard_true en = true -> guard_holds g V en.
  Proof.
    unfold guard_true. intros Hg c b Hin. rewrite forallb_forall in Hg.
    specialize (Hg (c, b) Hin). cbn [fst snd] in Hg. apply Bool.eqb_prop in Hg. exact Hg.
  Qed.

  Lemma step_sound (k: known g) n v :
    sound_known k -> step (p_eq := p_eq) ips g k n = Some v -> v = V n.
  Proof.
    intros Hk Hs. pose proof (Hcons n) as Hc. unfold step in Hs. revert Hs Hc.
    destruct (op (node_at g n))
      as [c | iv | dv | uop a | bop a b | a | cnd t e | slat sa | dp darg den
         | sp tok en | ja jb | ] eqn:Hop;
      intros Hs Hc; try discriminate.
    - injection Hs as <-. symmetry. exact Hc.
    - destruct (k a) as [x |] eqn:Ha; [ | discriminate ]. cbn [option_map] in Hs.
      injection Hs as <-. rewrite (Hk a x Ha). symmetry. exact Hc.
    - destruct (k a) as [x |] eqn:Ha; [ | discriminate ].
      destruct (k b) as [y |] eqn:Hb; [ | discriminate ].
      injection Hs as <-. rewrite (Hk a x Ha), (Hk b y Hb). symmetry. exact Hc.
    - destruct (k a) as [x |] eqn:Ha; [ | discriminate ]. cbn [option_map] in Hs.
      injection Hs as <-. rewrite (Hk a x Ha). symmetry. exact Hc.
    - destruct (k cnd) as [x |] eqn:Hx; [ | discriminate ].
      pose proof (Hk cnd x Hx) as Hxv. subst x. rewrite Hc.
      destruct (nonzero (V cnd)).
      + destruct (k t) as [y |] eqn:Hy; [ | discriminate ]. cbn [option_map] in Hs.
        injection Hs as <-. rewrite (Hk t y Hy). reflexivity.
      + destruct (k e) as [y |] eqn:Hy; [ | discriminate ]. cbn [option_map] in Hs.
        injection Hs as <-. rewrite (Hk e y Hy). reflexivity.
    - injection Hs as <-. symmetry. exact (Hstall n slat sa Hop).
    - destruct (k darg) as [x |] eqn:Ha; [ | discriminate ]. cbn [option_map] in Hs.
      injection Hs as <-. rewrite (Hk darg x Ha). symmetry. exact (Hdrive n dp darg den Hop).
    - destruct (guard_val g k en) as [[|] |] eqn:Hg; try discriminate.
      + destruct (payload_of g n) as [a |] eqn:Hpl; [ | discriminate ].
        destruct (k a) as [x |] eqn:Ha; [ | discriminate ]. cbn [option_map] in Hs.
        injection Hs as <-. rewrite (Hk a x Ha).
        symmetry. exact (Hsample_on n sp tok en a Hop (guard_val_sound k en _ Hk Hg) Hpl).
      + injection Hs as <-.
        symmetry. exact (Hsample_off n sp tok en Hop (guard_val_sound k en _ Hk Hg)).
    - injection Hs as <-. symmetry. exact (Hjoin n ja jb Hop).
  Qed.

  Lemma back_sound (k: known g) n v :
    sound_known k -> back decls g k n = Some v -> v = V n.
  Proof.
    intros Hk Hb. unfold back in Hb.
    apply find_map_some in Hb. destruct Hb as [[r i] [Hin Hf]]. cbn [fst snd] in Hf.
    destruct (Nat.eq_dec (di_target i) n) as [e | ne]; [ | discriminate ].
    destruct e.
    destruct (guard_val g k (di_guard i)) as [[|] |] eqn:Hg; try discriminate.
    destruct (forallb _ (di_sources i)) eqn:Hsrc; [ | discriminate ].
    injection Hf as <-. cbn [eq_rect].
    unfold instances in Hin. apply in_flat_map in Hin. destruct Hin as [r' [_ Hin]].
    apply in_map_iff in Hin. destruct Hin as [i' [Heq Hi']]. injection Heq as -> ->.
    symmetry. apply (dp_sound r g i V (fill g k) Hws Hi' Hcons).
    - apply guard_true_holds. exact (guard_val_sound k _ true Hk Hg).
    - intros s Hs. unfold fill. rewrite forallb_forall in Hsrc. specialize (Hsrc s Hs).
      destruct (k s) as [x |] eqn:Hks; [ | discriminate ]. exact (Hk s x Hks).
  Qed.

  Theorem recover_sound (seed: known g) :
    sound_known seed ->
    forall f, sound_known (recover (p_eq := p_eq) ips decls g seed f).
  Proof.
    intros Hseed f. induction f as [| f IH]; intros n v H; cbn [recover] in H;
      [ discriminate | ].
    destruct (seed n) as [x |] eqn:Hsd; [ injection H as <-; exact (Hseed n x Hsd) | ].
    destruct (step ips g (recover ips decls g seed f) n) as [x |] eqn:Hst.
    - injection H as <-. exact (step_sound _ n x IH Hst).
    - exact (back_sound _ n v IH H).
  Qed.

  (* ---- more fuel keeps every value; the recovered nodes reach a closure ---- *)

  Lemma guard_val_mono (k1 k2: known g) en b :
    (forall m x, k1 m = Some x -> k2 m = Some x) ->
    guard_val g k1 en = Some b -> guard_val g k2 en = Some b.
  Proof.
    intro Hk. revert b. induction en as [| [c bc] en IH]; intros b Hg; cbn [guard_val] in *;
      [ exact Hg | ].
    destruct (k1 c) as [x |] eqn:Hc; [ | discriminate ].
    destruct (guard_val g k1 en) as [r |] eqn:Hr; [ | discriminate ].
    rewrite (Hk c x Hc), (IH r eq_refl). exact Hg.
  Qed.

  Lemma step_mono (k1 k2: known g) n v :
    (forall m x, k1 m = Some x -> k2 m = Some x) ->
    step (p_eq := p_eq) ips g k1 n = Some v -> step (p_eq := p_eq) ips g k2 n = Some v.
  Proof.
    intros Hk Hs. unfold step in *.
    destruct (op (node_at g n))
      as [c | iv | dv | uop a | bop a b | a | cnd t e | slat sa | dp darg den
         | sp tok en | ja jb | ];
      try exact Hs; try discriminate Hs.
    - destruct (k1 a) as [x |] eqn:E; [ | discriminate Hs ]. rewrite (Hk a x E). exact Hs.
    - destruct (k1 a) as [x |] eqn:E1; [ | discriminate Hs ].
      destruct (k1 b) as [y |] eqn:E2; [ | discriminate Hs ].
      rewrite (Hk a x E1), (Hk b y E2). exact Hs.
    - destruct (k1 a) as [x |] eqn:E; [ | discriminate Hs ]. rewrite (Hk a x E). exact Hs.
    - destruct (k1 cnd) as [x |] eqn:E; [ | discriminate Hs ]. rewrite (Hk cnd x E).
      destruct (nonzero x).
      + destruct (k1 t) as [y |] eqn:Et; [ | discriminate Hs ]. rewrite (Hk t y Et). exact Hs.
      + destruct (k1 e) as [y |] eqn:Ee; [ | discriminate Hs ]. rewrite (Hk e y Ee). exact Hs.
    - destruct (k1 darg) as [x |] eqn:E; [ | discriminate Hs ]. rewrite (Hk darg x E). exact Hs.
    - destruct (guard_val g k1 en) as [[|] |] eqn:Eg; try discriminate Hs.
      + rewrite (guard_val_mono k1 k2 en true Hk Eg).
        destruct (payload_of g n) as [a |]; [ | discriminate Hs ].
        destruct (k1 a) as [x |] eqn:E; [ | discriminate Hs ]. rewrite (Hk a x E). exact Hs.
      + rewrite (guard_val_mono k1 k2 en false Hk Eg). exact Hs.
  Qed.

  Lemma find_map_mono {A B C} (f1: A -> option B) (f2: A -> option C) (l: list A) :
    (forall a, f1 a <> None -> f2 a <> None) -> find_map f1 l <> None -> find_map f2 l <> None.
  Proof.
    intro H. induction l as [| a l IH]; cbn [find_map]; [ tauto | ].
    destruct (f2 a) eqn:E2; [ discriminate | ].
    destruct (f1 a) eqn:E1; [ | exact IH ].
    exfalso. apply (H a); [ rewrite E1; discriminate | exact E2 ].
  Qed.

  Lemma back_mono (k1 k2: known g) n :
    (forall m x, k1 m = Some x -> k2 m = Some x) ->
    back decls g k1 n <> None -> back decls g k2 n <> None.
  Proof.
    intro Hk. unfold back. apply find_map_mono. intros [r i] Hf. cbn [fst snd] in *.
    destruct (Nat.eq_dec (di_target i) n) as [e | ne]; [ | exfalso; apply Hf; reflexivity ].
    destruct (guard_val g k1 (di_guard i)) as [[|] |] eqn:Eg;
      try (exfalso; apply Hf; reflexivity).
    rewrite (guard_val_mono k1 k2 _ true Hk Eg).
    destruct (forallb _ (di_sources i)) eqn:E1; [ | exfalso; apply Hf; reflexivity ].
    replace (forallb (fun s => match k2 s with Some _ => true | None => false end)
               (di_sources i)) with true; [ discriminate | ].
    symmetry. rewrite forallb_forall in *. intros s Hs. specialize (E1 s Hs).
    destruct (k1 s) as [x |] eqn:Ex; [ | discriminate ]. rewrite (Hk s x Ex). reflexivity.
  Qed.

  (* Two sound tables agree wherever both answer, so answering is all that matters. *)
  Lemma sound_incl (k1 k2: known g) :
    sound_known k1 -> sound_known k2 ->
    (forall m, k1 m <> None -> k2 m <> None) ->
    forall m x, k1 m = Some x -> k2 m = Some x.
  Proof.
    intros H1 H2 Hd m x Hx. destruct (k2 m) as [y |] eqn:Hy.
    - rewrite (H1 m x Hx), (H2 m y Hy). reflexivity.
    - exfalso. apply (Hd m); [ rewrite Hx; discriminate | exact Hy ].
  Qed.

  Section Closure.
    Context (seed: known g).
    Hypothesis Hseed : sound_known seed.

    Local Notation K f := (recover (p_eq := p_eq) ips decls g seed f).

    Lemma recover_S f n :
      K (S f) n = match seed n with
                  | Some v => Some v
                  | None => match step ips g (K f) n with
                            | Some v => Some v
                            | None => back decls g (K f) n
                            end
                  end.
    Proof. reflexivity. Qed.

    Lemma recover_mono f n x : K f n = Some x -> K (S f) n = Some x.
    Proof.
      revert n x. induction f as [| f IH]; intros n x H; [ discriminate | ].
      pose proof (recover_sound seed Hseed (S f) n x H) as Hx.
      rewrite recover_S in H |- *.
      destruct (seed n) as [y |] eqn:Hs; [ exact H | ].
      destruct (step ips g (K f) n) as [y |] eqn:Hst.
      - rewrite (step_mono _ _ n y IH Hst). exact H.
      - destruct (step ips g (K (S f)) n) as [z |] eqn:Hst2.
        + pose proof (step_sound _ n z (recover_sound seed Hseed (S f)) Hst2) as Hz.
          rewrite Hx, Hz. reflexivity.
        + pose proof (back_mono _ _ n IH ltac:(rewrite H; discriminate)) as Hb.
          destruct (back decls g (K (S f)) n) as [w |] eqn:Hbw;
            [ | exfalso; apply Hb; reflexivity ].
          pose proof (back_sound _ n w (recover_sound seed Hseed (S f)) Hbw) as Hw.
          rewrite Hx, Hw. reflexivity.
    Qed.

    Lemma recover_mono_le f f' n x : f <= f' -> K f n = Some x -> K f' n = Some x.
    Proof.
      intro Hle. induction Hle as [| f' Hle IH]; intro H; [ exact H | ].
      exact (recover_mono f' n x (IH H)).
    Qed.

    Hypothesis Hseed_range : forall n, seed n <> None -> n < length (graph g).

    Definition universe : list nid_t :=
      List.seq 0 (length (graph g)) ++ map (fun ri => di_target (snd ri)) (instances decls g).

    Lemma recover_support f n : K f n <> None -> In n universe.
    Proof.
      unfold universe. intro H. destruct f as [| f]; [ exfalso; apply H; reflexivity | ].
      rewrite recover_S in H.
      destruct (seed n) as [x |] eqn:Hs.
      - apply in_or_app. left. apply in_seq. split; [ lia | ].
        apply Hseed_range. rewrite Hs. discriminate.
      - destruct (step ips g (K f) n) as [x |] eqn:Hst.
        + apply in_or_app. left. apply in_seq. split; [ lia | ].
          destruct (Nat.lt_ge_cases n (length (graph g))) as [Hlt | Hge]; [ lia | ].
          exfalso. unfold step, node_at in Hst. rewrite nth_overflow in Hst by exact Hge.
          discriminate.
        + apply in_or_app. right. unfold back in H.
          destruct (find_map _ (instances decls g)) as [y |] eqn:Hf;
            [ | exfalso; apply H; reflexivity ].
          apply find_map_some in Hf. destruct Hf as [[r i] [Hin Hf]]. cbn [fst snd] in Hf.
          destruct (Nat.eq_dec (di_target i) n) as [e | ne]; [ | discriminate ].
          apply in_map_iff. exists (r, i). split; [ exact e | exact Hin ].
    Qed.

    Definition defined (f: nat) (n: nid_t) : bool :=
      match K f n with Some _ => true | None => false end.

    Lemma filter_len_bound {A} (p: A -> bool) (l: list A) : length (filter p l) <= length l.
    Proof.
      induction l as [| a l IH]; cbn [filter]; [ lia | ].
      destruct (p a); cbn [length]; lia.
    Qed.

    Lemma filter_len_mono {A} (p q: A -> bool) (l: list A) :
      (forall x, p x = true -> q x = true) -> length (filter p l) <= length (filter q l).
    Proof.
      intro H. induction l as [| a l IH]; cbn [filter]; [ lia | ].
      destruct (p a) eqn:Hp; [ rewrite (H a Hp); cbn [length]; lia | ].
      destruct (q a); cbn [length]; lia.
    Qed.

    Lemma filter_len_eq {A} (p q: A -> bool) (l: list A) :
      (forall x, p x = true -> q x = true) ->
      length (filter p l) = length (filter q l) ->
      forall x, In x l -> q x = true -> p x = true.
    Proof.
      intro H. induction l as [| a l IH]; intros Heq x Hx Hq; [ destruct Hx | ].
      cbn [filter] in Heq.
      destruct (p a) eqn:Hp.
      - rewrite (H a Hp) in Heq. cbn [length] in Heq.
        destruct Hx as [<- | Hx]; [ exact Hp | exact (IH ltac:(lia) x Hx Hq) ].
      - destruct (q a) eqn:Hqa.
        + exfalso. cbn [length] in Heq. pose proof (filter_len_mono p q l H). lia.
        + destruct Hx as [<- | Hx]; [ rewrite Hqa in Hq; discriminate | exact (IH Heq x Hx Hq) ].
    Qed.

    Definition count (f: nat) : nat := length (filter (defined f) universe).

    Definition stable_at (j: nat) : Prop := forall n, K (S j) n <> None -> K j n <> None.

    Lemma defined_mono f n : defined f n = true -> defined (S f) n = true.
    Proof.
      unfold defined. destruct (K f n) as [x |] eqn:E; [ | discriminate ].
      rewrite (recover_mono f n x E). reflexivity.
    Qed.

    Lemma stable_or_grow j : (exists j0, j0 <= j /\ stable_at j0) \/ j <= count j.
    Proof.
      induction j as [| j IH]; [ right; lia | ].
      destruct IH as [[j0 [Hle Hst]] | Hc]; [ left; exists j0; split; [ lia | exact Hst ] | ].
      destruct (Nat.eq_dec (count (S j)) (count j)) as [Heq | Hne].
      - left. exists j. split; [ lia | ]. intros n Hn.
        assert (Hd : defined (S j) n = true)
          by (unfold defined; destruct (K (S j) n); [ reflexivity | exfalso; apply Hn; reflexivity ]).
        pose proof (filter_len_eq (defined j) (defined (S j)) universe (defined_mono j)
                      (eq_sym Heq) n (recover_support (S j) n Hn) Hd) as Hj.
        unfold defined in Hj. destruct (K j n); [ discriminate | discriminate Hj ].
      - right. pose proof (filter_len_mono (defined j) (defined (S j)) universe (defined_mono j)).
        unfold count in *. lia.
    Qed.

    Lemma stable_forever j0 : stable_at j0 -> forall i n, K (i + j0) n <> None -> K j0 n <> None.
    Proof.
      intros Hst i. induction i as [| i IH]; intros n Hn; [ exact Hn | ].
      apply Hst.
      assert (Hincl : forall m x, K (i + j0) m = Some x -> K j0 m = Some x).
      { apply sound_incl; [ apply recover_sound; exact Hseed | apply recover_sound; exact Hseed
                          | exact IH ]. }
      change (S i + j0) with (S (i + j0)) in Hn. rewrite recover_S in Hn |- *.
      destruct (seed n) as [x |]; [ discriminate | ].
      destruct (step ips g (K (i + j0)) n) as [x |] eqn:Hst1.
      - rewrite (step_mono _ _ n x Hincl Hst1). discriminate.
      - destruct (step ips g (K j0) n) as [y |]; [ discriminate | ].
        exact (back_mono _ _ n Hincl Hn).
    Qed.

    (* Any value the recipe reaches with some fuel, it reaches with [S |universe|]. *)
    Theorem recover_closed f n x :
      K f n = Some x -> K (S (length universe)) n = Some x.
    Proof.
      intro H.
      destruct (stable_or_grow (S (length universe))) as [[j0 [Hle Hst]] | Hc].
      - destruct (Nat.le_gt_cases f j0) as [Hfj | Hfj].
        + exact (recover_mono_le j0 _ n x Hle (recover_mono_le f j0 n x Hfj H)).
        + pose proof (stable_forever j0 Hst (f - j0) n) as Hs.
          replace (f - j0 + j0) with f in Hs by lia.
          specialize (Hs ltac:(rewrite H; discriminate)).
          destruct (K j0 n) as [y |] eqn:Hy; [ | exfalso; apply Hs; reflexivity ].
          pose proof (recover_mono_le j0 _ n y Hle Hy) as Hy'.
          rewrite Hy'. f_equal.
          rewrite (recover_sound seed Hseed _ n y Hy), (recover_sound seed Hseed f n x H).
          reflexivity.
      - exfalso. unfold count in Hc.
        pose proof (filter_len_bound (defined (S (length universe))) universe). lia.
    Qed.
  End Closure.
End RecipeSound.

Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Theorems.Definitions.
Require Import Trustformer.Theorems.Internal.ProofDefinitions.
Require Import Trustformer.Theorems.Internal.SchedulerRoundTrip.
Require Import Trustformer.Theorems.Internal.IPRProof.

Lemma guard_true_ext {s i o p} (g: @dfg_state_t s i o p) (V1 V2: valuation g) en :
  (forall l, In l en -> V1 (fst l) = V2 (fst l)) -> guard_true g V1 en = guard_true g V2 en.
Proof.
  induction en as [| l en IH]; intro H; [ reflexivity | ].
  unfold guard_true in *. cbn [forallb].
  rewrite (H l (or_introl eq_refl)), IH; [ reflexivity | ].
  intros l' Hl'. exact (H l' (or_intror Hl')).
Qed.

(* ================================================================= *)
(* THE RUN'S IDEAL VALUES: nodes once ready, IP answers [ip_fn].     *)
(* ================================================================= *)
Section Ideal.
  Context (ctx: TFSchedContext) (cost_limit: nat).

  Local Notation sched := (tfs_schedule ctx cost_limit).
  Local Notation i_var := (tfs_spec_inputs ctx).
  Local Notation o_var := (tfs_spec_outputs ctx).
  Local Notation s_sz := (tfs_spec_states_size ctx).
  Local Notation i_sz := (tfs_spec_inputs_size ctx).
  Local Notation o_sz := (tfs_spec_outputs_size ctx).
  Local Notation src_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation src_sys_state :=
    (ContextEnv.(env_t) (tf_states_type s_sz) * src_out_env)%type.
  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).
  Local Notation peq := (tfs_spec_ips_eq_dec ctx).

  Context (act: tfs_action sched) (sp0: src_sys_state) (input: input_t).

  Local Notation G := (build_dfg ctx act).

  Fixpoint videal_f (f: nat) (n: nid_t) : bits_t (node_sz G n) :=
    match f with
    | 0 => Bits.zero
    | S f' =>
        match op (node_at G n) with
        | DFG_Const c => Bits.of_nat _ c
        | DFG_Input v => convert (input v)
        | DFG_Var (DFG_SVar sv) => convert ((fst sp0).[sv])
        | DFG_Var (DFG_OVar ov) => convert ((snd sp0).[ov])
        | DFG_Unary uop a => op1_bits uop _ _ (videal_f f' a)
        | DFG_Resize a => convert (videal_f f' a)
        | DFG_Binary bop a b => op2_bits bop _ _ _ (videal_f f' a) (videal_f f' b)
        | DFG_Phi c t e =>
            if nonzero (videal_f f' c) then convert (videal_f f' t)
            else convert (videal_f f' e)
        | DFG_Drive _ a _ => convert (videal_f f' a)
        | DFG_Sample p _ en =>
            if guard_true G (videal_f f') en then
              match payload_of (p_eq := peq) G n with
              | Some a => convert (ip_fn (tfs_spec_ip ctx p) (convert (videal_f f' a)))
              | None => Bits.zero
              end
            else Bits.zero
        | _ => Bits.zero
        end
    end.

  Definition videal (n: nid_t) : bits_t (node_sz G n) := videal_f (S n) n.

  (* ---- every node depends only on nodes below it ---- *)

  Lemma arg_below n a :
    op (node_at G n) <> DFG_Empty -> In a (get_args ctx (node_at G n)) -> a < n.
  Proof.
    intros Hne Hin. destruct (node_op_pos ctx cost_limit act n Hne) as [_ Hlen].
    exact (arg_lt_of_op ctx cost_limit act n a Hlen Hin).
  Qed.

  Lemma drive_of_sample_drive n :
    drive_of (p_eq := peq) G n = ProofDefinitions.sample_drive ctx cost_limit act n.
  Proof. reflexivity. Qed.

  Lemma sample_drive_below n p tok en d :
    op (node_at G n) = DFG_Sample p tok en ->
    ProofDefinitions.sample_drive ctx cost_limit act n = Some d -> d < n.
  Proof.
    intros Hop Hd.
    assert (Htok : tok < n)
      by (apply (arg_below n tok); [ rewrite Hop; discriminate
                                   | unfold get_args; rewrite Hop; left; reflexivity ]).
    unfold ProofDefinitions.sample_drive, AttackerClock.node_op in Hd.
    change (op (node_at G n)) with (op (nth n (graph G) {| nid := 0; op := DFG_Empty; sz := 0 |}))
      in Hop.
    rewrite Hop in Hd.
    assert (Hhead : forall h, ProofDefinitions.sample_drive_head ctx cost_limit act p h = Some d -> d <= h).
    { intros h Hh. unfold ProofDefinitions.sample_drive_head, AttackerClock.node_op in Hh.
      destruct (op (nth h (graph G) {| nid := 0; op := DFG_Empty; sz := 0 |}))
        as [c | v | v | uop x | bop x y | x | c t e | sl x | dp x den | sp x sen | jd jb | ]
        eqn:Hoh; try discriminate.
      - destruct (eq_dec dp p); [ injection Hh as Hhd; lia | discriminate ].
      - destruct (op (nth jd (graph G) {| nid := 0; op := DFG_Empty; sz := 0 |}))
          as [c | v | v | uop x | bop x y | x | c t e | sl x | dp x den | sp x sen | ja jc | ];
          try discriminate.
        destruct (eq_dec dp p); [ injection Hh as Hjd | discriminate ].
        subst jd. apply Nat.lt_le_incl. apply (arg_below h d).
        + change (op (node_at G h))
            with (op (nth h (graph G) {| nid := 0; op := DFG_Empty; sz := 0 |})).
          rewrite Hoh. discriminate.
        + unfold get_args, node_at. rewrite Hoh. left. reflexivity. }
    destruct (op (nth tok (graph G) {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | v | v | uop x | bop x y | x | c t e | sl hd | dp x den | sp x sen | ja jc | ]
      eqn:Hot; try (pose proof (Hhead tok Hd); lia).
    pose proof (Hhead _ Hd) as Hdh.
    assert (Hht : hd < tok).
    { apply (arg_below tok hd).
      + change (op (node_at G tok))
          with (op (nth tok (graph G) {| nid := 0; op := DFG_Empty; sz := 0 |})).
        rewrite Hot. discriminate.
      + unfold get_args, node_at. rewrite Hot. left. reflexivity. }
    lia.
  Qed.

  Lemma sample_lits_below n p tok en l :
    op (node_at G n) = DFG_Sample p tok en -> In l en -> fst l < n.
  Proof.
    intros Hop Hl.
    destruct (sample_has_drive ctx cost_limit act n p tok en Hop) as [d [arg [Hsd Hdop]]].
    pose proof (sample_drive_below n p tok en d Hop Hsd) as Hdn.
    assert (Hld : fst l < d).
    { apply (arg_below d (fst l)).
      + change (op (node_at G d)) with (AttackerClock.node_op ctx cost_limit act d).
        rewrite Hdop. discriminate.
      + unfold get_args. change (op (node_at G d)) with (AttackerClock.node_op ctx cost_limit act d).
        rewrite Hdop. right. exact (in_map fst en l Hl). }
    lia.
  Qed.

  Lemma payload_below n p tok en a :
    op (node_at G n) = DFG_Sample p tok en -> payload_of (p_eq := peq) G n = Some a -> a < n.
  Proof.
    intros Hop Hpl. unfold payload_of in Hpl. rewrite drive_of_sample_drive in Hpl.
    destruct (ProofDefinitions.sample_drive ctx cost_limit act n) as [d |] eqn:Hsd;
      [ | discriminate ].
    pose proof (sample_drive_below n p tok en d Hop Hsd) as Hdn.
    destruct (op (node_at G d)) eqn:Hdop; try discriminate.
    injection Hpl as ->.
    assert (Had : a < d).
    { apply (arg_below d a); [ rewrite Hdop; discriminate | ].
      unfold get_args. rewrite Hdop. left. reflexivity. }
    lia.
  Qed.

  Lemma videal_f_irrel : forall n f, n < f -> videal_f f n = videal n.
  Proof.
    intro n. induction n as [n IH] using lt_wf_ind. intros f Hf.
    unfold videal. destruct f as [| f]; [ lia | ]. cbn [videal_f].
    destruct (op (node_at G n)) as [c | iv | [sv | ov] | uop a | bop a b | a | cnd t e
                                   | slat sa | dp a den | sp tok en | ja jb | ] eqn:Hop;
      try reflexivity.
    all: assert (Hne : op (node_at G n) <> DFG_Empty) by (rewrite Hop; discriminate).
    all: try (assert (Ha : a < n) by (apply (arg_below n a Hne); unfold get_args; rewrite Hop;
                                      left; reflexivity);
              rewrite (IH a Ha f ltac:(lia)), (IH a Ha n ltac:(lia))).
    - reflexivity.
    - assert (Hb : b < n) by (apply (arg_below n b Hne); unfold get_args; rewrite Hop;
                              right; left; reflexivity).
      rewrite (IH b Hb f ltac:(lia)), (IH b Hb n ltac:(lia)). reflexivity.
    - reflexivity.
    - assert (Hc : cnd < n) by (apply (arg_below n cnd Hne); unfold get_args; rewrite Hop;
                                left; reflexivity).
      assert (Ht : t < n) by (apply (arg_below n t Hne); unfold get_args; rewrite Hop;
                              right; left; reflexivity).
      assert (He : e < n) by (apply (arg_below n e Hne); unfold get_args; rewrite Hop;
                              right; right; left; reflexivity).
      rewrite (IH cnd Hc f ltac:(lia)), (IH cnd Hc n ltac:(lia)),
              (IH t Ht f ltac:(lia)), (IH t Ht n ltac:(lia)),
              (IH e He f ltac:(lia)), (IH e He n ltac:(lia)).
      reflexivity.
    - reflexivity.
    - rewrite (guard_true_ext G (videal_f f) (videal_f n) en).
      + destruct (guard_true G (videal_f n) en); [ | reflexivity ].
        destruct (payload_of G n) as [a |] eqn:Hpl; [ | reflexivity ].
        pose proof (payload_below n sp tok en a Hop Hpl) as Ha.
        rewrite (IH a Ha f ltac:(lia)), (IH a Ha n ltac:(lia)). reflexivity.
      + intros l Hl. pose proof (sample_lits_below n sp tok en l Hop Hl) as Hln.
        rewrite (IH (fst l) Hln f ltac:(lia)), (IH (fst l) Hln n ltac:(lia)). reflexivity.
  Qed.

  (* ---- the ideal values obey the graph ---- *)

  Lemma videal_unfold n :
    videal n = videal_f (S n) n.
  Proof. reflexivity. Qed.

  Lemma videal_consistent : consistent G videal.
  Proof.
    intro n.
    destruct (op (node_at G n)) as [c | iv | dv | uop a | bop a b | a | cnd t e
                                   | slat sa | dp darg den | sp tok en | ja jb | ] eqn:Hop;
      try exact I.
    all: assert (Hne : op (node_at G n) <> DFG_Empty) by (rewrite Hop; discriminate).
    all: rewrite videal_unfold; cbn [videal_f]; rewrite Hop; cbn beta iota.
    - reflexivity.
    - assert (Ha : a < n) by (apply (arg_below n a Hne); unfold get_args; rewrite Hop;
                              left; reflexivity).
      rewrite (videal_f_irrel a n Ha). reflexivity.
    - assert (Ha : a < n) by (apply (arg_below n a Hne); unfold get_args; rewrite Hop;
                              left; reflexivity).
      assert (Hb : b < n) by (apply (arg_below n b Hne); unfold get_args; rewrite Hop;
                              right; left; reflexivity).
      rewrite (videal_f_irrel a n Ha), (videal_f_irrel b n Hb). reflexivity.
    - assert (Ha : a < n) by (apply (arg_below n a Hne); unfold get_args; rewrite Hop;
                              left; reflexivity).
      rewrite (videal_f_irrel a n Ha). reflexivity.
    - assert (Hc : cnd < n) by (apply (arg_below n cnd Hne); unfold get_args; rewrite Hop;
                                left; reflexivity).
      assert (Ht : t < n) by (apply (arg_below n t Hne); unfold get_args; rewrite Hop;
                              right; left; reflexivity).
      assert (He : e < n) by (apply (arg_below n e Hne); unfold get_args; rewrite Hop;
                              right; right; left; reflexivity).
      rewrite (videal_f_irrel cnd n Hc), (videal_f_irrel t n Ht), (videal_f_irrel e n He).
      reflexivity.
  Qed.

  Lemma videal_guard n sp tok en :
    op (node_at G n) = DFG_Sample sp tok en ->
    guard_true G (videal_f n) en = guard_true G videal en.
  Proof.
    intro Hop. apply guard_true_ext. intros l Hl.
    exact (videal_f_irrel (fst l) n (sample_lits_below n sp tok en l Hop Hl)).
  Qed.

  Lemma videal_sample_off n sp tok en :
    op (node_at G n) = DFG_Sample sp tok en ->
    guard_true G videal en = false -> videal n = Bits.zero.
  Proof.
    intros Hop Hg. rewrite videal_unfold. cbn [videal_f]. rewrite Hop. cbn beta iota.
    rewrite (videal_guard n sp tok en Hop), Hg. reflexivity.
  Qed.

  Lemma videal_sample_on n sp tok en a :
    op (node_at G n) = DFG_Sample sp tok en ->
    guard_true G videal en = true ->
    payload_of (p_eq := peq) G n = Some a ->
    videal n = convert (ip_fn (tfs_spec_ip ctx sp) (convert (videal a))).
  Proof.
    intros Hop Hg Hpl. rewrite videal_unfold. cbn [videal_f]. rewrite Hop. cbn beta iota.
    rewrite (videal_guard n sp tok en Hop), Hg, Hpl.
    rewrite (videal_f_irrel a n (payload_below n sp tok en a Hop Hpl)). reflexivity.
  Qed.


  Lemma videal_stall n l a : op (node_at G n) = DFG_Stall l a -> videal n = Bits.zero.
  Proof. intro Hop. rewrite videal_unfold. cbn [videal_f]. rewrite Hop. reflexivity. Qed.

  Lemma videal_join n a b : op (node_at G n) = DFG_Join a b -> videal n = Bits.zero.
  Proof. intro Hop. rewrite videal_unfold. cbn [videal_f]. rewrite Hop. reflexivity. Qed.

  Lemma videal_drive n p a en :
    op (node_at G n) = DFG_Drive p a en -> videal n = convert (videal a).
  Proof.
    intro Hop. rewrite videal_unfold. cbn [videal_f]. rewrite Hop. cbv beta iota.
    rewrite (videal_f_irrel a n); [ reflexivity | ].
    apply (arg_below n a); [ rewrite Hop; discriminate | ].
    unfold get_args. rewrite Hop. left. reflexivity.
  Qed.
  (* ---- the compiled graph is well-sized ---- *)

  Lemma build_well_sized : well_sized G.
  Proof.
    intro n. unfold node_sz, node_at.
    destruct (Nat.lt_ge_cases n (length (graph G))) as [Hlt | Hge];
      [ | rewrite nth_overflow by exact Hge; exact I ].
    pose proof (wfg_build_dfg ctx cost_limit act _
                  (nth_In _ {| nid := 0; op := DFG_Empty; sz := 0 |} Hlt)) as Hfg.
    unfold node_args_sz in Hfg.
    destruct (op (nth n (graph G) {| nid := 0; op := DFG_Empty; sz := 0 |}))
      as [c | iv | dv | uop a | bop a b | a | cnd t e | slat sa | dp darg den
         | sp tok en | ja jb | ];
      try exact I.
    - destruct uop; exact (proj2 (wsz_node_sz ctx cost_limit act _ _ Hfg)).
    - destruct bop; destruct Hfg as [H1 H2]; split;
        first [ exact (proj2 (wsz_node_sz ctx cost_limit act _ _ H1))
              | exact (proj2 (wsz_node_sz ctx cost_limit act _ _ H2)) ].
    - destruct Hfg as [Hc [Ht He]].
      split; [ exact (proj2 (wsz_node_sz ctx cost_limit act _ _ Hc)) | ].
      split; [ exact (proj2 (wsz_node_sz ctx cost_limit act _ _ Ht))
             | exact (proj2 (wsz_node_sz ctx cost_limit act _ _ He)) ].
  Qed.

  (* ---- the published bits are ideal values ---- *)

  Lemma seed_sound (post: src_out_env) :
    (forall o r, tfs_spec_outputs_class ctx o = Public ->
       In (DFG_OVar o, r) (var_map G) ->
       convert (szB := node_sz G r) (post.[o]) = videal r) ->
    sound_known G videal
      (seed i_sz o_sz G (seen_in ctx (observe ctx input (snd sp0) post))
                        (seen_pre ctx (observe ctx input (snd sp0) post))
                        (seen_post ctx (observe ctx input (snd sp0) post))).
  Proof.
    intros Hroots n v Hs. unfold seed in Hs.
    assert (Hroot : find_map
                      (fun e => match e with
                                | (DFG_OVar o, r) =>
                                    if Nat.eqb r n
                                    then option_map convert
                                           (seen_post ctx (observe ctx input (snd sp0) post) o)
                                    else None
                                | _ => None
                                end) (var_map G) = Some v -> v = videal n).
    { intro Hf. apply find_map_some in Hf. destruct Hf as [[[sv | o] r] [Hin Hf]];
        [ discriminate | ].
      destruct (Nat.eqb r n) eqn:Hrn; [ | discriminate ]. apply Nat.eqb_eq in Hrn. subst r.
      cbn [seen_post observe] in Hf.
      destruct (tfs_spec_outputs_class ctx o) eqn:Hcls; [ | discriminate ].
      cbn [option_map] in Hf. injection Hf as <-. exact (Hroots o n Hcls Hin). }
    destruct (op (node_at G n)) as [c | iv | [sv | ov] | uop a | bop a b | a | cnd t e
                                   | slat sa | dp darg den | sp tok en | ja jb | ] eqn:Hop;
      try exact (Hroot Hs).
    - cbn [seen_in observe] in Hs.
      destruct (tfs_spec_inputs_class ctx iv); [ | exact (Hroot Hs) ].
      cbn [option_map] in Hs. injection Hs as <-.
      rewrite videal_unfold. cbn [videal_f]. rewrite Hop. reflexivity.
    - cbn [seen_pre observe] in Hs.
      destruct (tfs_spec_outputs_class ctx ov); [ | exact (Hroot Hs) ].
      cbn [option_map] in Hs. injection Hs as <-.
      rewrite videal_unfold. cbn [videal_f]. rewrite Hop. reflexivity.
  Qed.
End Ideal.

(* ================================================================= *)
(* THE HARDWARE READS THE IDEAL VALUE WHEREVER A NODE IS READY.        *)
(* ================================================================= *)
Section Settled.
  Context (ctx: TFSchedContext) (cost_limit: nat).

  Local Notation sched := (tfs_schedule ctx cost_limit).
  Local Notation i_var := (tfs_spec_inputs ctx).
  Local Notation s_sz := (tfs_spec_states_size ctx).
  Local Notation i_sz := (tfs_spec_inputs_size ctx).
  Local Notation o_sz := (tfs_spec_outputs_size ctx).
  Local Notation src_out_env := (ContextEnv.(env_t) (tf_outputs_type o_sz)).
  Local Notation src_sys_state :=
    (ContextEnv.(env_t) (tf_states_type s_sz) * src_out_env)%type.
  Local Notation sched_sys_state :=
    (ContextEnv.(env_t) (tf_states_type (tfs_states_size sched)) * src_out_env)%type.
  Local Notation input_t := (forall x : i_var, type_denote (tf_inputs_type i_sz x)).
  Local Notation resp_val :=
    (forall p : tfs_ips sched, bits_t (ip_resp_sz (tfs_ip sched p))).
  Local Notation spec_run act sp input :=
    (tf_ops_run s_sz i_sz o_sz (tfs_spec_ip ctx) (tfs_spec_action_ops ctx act) sp input).
  Local Notation a_index := (Vect.index (length (buffer_needs ctx cost_limit))).
  Local Notation rvalid act a_idx pi n ss input :=
    (tf_eval_expr (tfs_states_size sched) (tfs_inputs_size sched)
       (tfs_outputs_size sched) (szB := 1)
       (snd (compile_dfg_expr_at ctx (buffer_needs ctx cost_limit) pi
               (length (graph (build_dfg ctx act))) a_idx
               (build_dfg ctx act) n (sample_bufs ctx cost_limit act a_idx)))
       ss input) (only parsing).

  Context (act: tfs_action sched) (a_idx: a_index) (sp0: src_sys_state)
          (ss0: sched_sys_state) (input: input_t) (resp: nat -> resp_val).
  Hypothesis Halign : act_idx_aligned ctx cost_limit act a_idx.
  Hypothesis Hstart : start_rel ctx cost_limit sp0 ss0.
  Hypothesis Hipc : IRDefinitions.ip_contract ctx cost_limit act input resp ss0.

  Local Notation G := (build_dfg ctx act).
  Local Notation V := (videal ctx cost_limit act sp0 input).
  Local Notation ssk k := (run_n ctx cost_limit k act input resp ss0).
  Local Notation sik k := (sched_input ctx cost_limit input (resp k)).

  Lemma op_range n : op (node_at G n) <> DFG_Empty -> 1 <= n /\ n < length (graph G).
  Proof. exact (node_op_pos ctx cost_limit act n). Qed.

  Lemma valid_empty n pi ss inp :
    op (node_at G n) = DFG_Empty -> rvalid act a_idx pi n ss inp <> Bits.ones 1.
  Proof.
    intro Hop. unfold node_at in Hop.
    assert (Hns : BitsToLists.list_assoc (sample_bufs ctx cost_limit act a_idx) n = None).
    { apply not_sample_not_in_sample_bufs.
      unfold ProofDefinitions.is_sample_of, AttackerClock.node_op. rewrite Hop. reflexivity. }
    destruct (length (graph G)) as [| f]; cbn [compile_dfg_expr_aux].
    - cbn. discriminate.
    - rewrite Hns. cbv beta iota zeta. rewrite Hop. cbn. discriminate.
  Qed.

  Lemma nre_join n ja jb :
    1 <= n -> n < length (graph G) ->
    op (node_at G n) = DFG_Join ja jb ->
    node_ref_expr ctx cost_limit act a_idx n = tf_const 0.
  Proof.
    intros H1 H2 Hop. unfold node_at in Hop.
    rewrite (nre_unfold ctx cost_limit act a_idx n H1 H2).
    cbn [compile_dfg_expr_aux].
    rewrite (not_sample_not_in_sample_bufs ctx cost_limit act a_idx n
              ltac:(unfold ProofDefinitions.is_sample_of, AttackerClock.node_op; rewrite Hop; reflexivity)).
    cbv beta iota zeta. rewrite Hop.
    destruct (compile_dfg_expr_aux _ _ _ _ _ _ _ _ ja _).
    destruct (compile_dfg_expr_aux _ _ _ _ _ _ _ _ jb _). reflexivity.
  Qed.

  Theorem videal_settled k :
    (forall i, 1 <= i <= k -> ~ done_set ctx cost_limit (ssk i)) ->
    forall n pi,
      pi_holds ctx cost_limit act a_idx (sik k) pi (ssk k) ->
      rvalid act a_idx pi n (ssk k) (sik k) = Bits.ones 1 ->
      nval ctx cost_limit act a_idx (ssk k) (sik k) (node_sz G n) n = V n.
  Proof.
    intros Hnd n. induction n as [n IH] using lt_wf_ind. intros pi Hpi Hv.
    pose proof (videal_consistent ctx cost_limit act sp0 input n) as Hc.
    pose proof (build_well_sized ctx cost_limit act n) as Hw.
    destruct Hstart as [Hoo [Hmm Hzz]].
    revert Hc Hw.
    destruct (op (node_at G n)) as [c | iv | [sv | ov] | uop a | bop a b | a | cnd t e
                                   | slat sa | dp darg den | sp tok en | ja jb | ] eqn:Hop;
      intros Hc Hw.
    all: try (exfalso; exact (valid_empty n pi _ _ Hop Hv)).
    all: destruct (op_range n ltac:(rewrite Hop; discriminate)) as [Hn1 Hnlen].
    all: assert (Hop' := Hop); unfold node_at in Hop'.
    - (* constant *)
      rewrite Hc. unfold nval. rewrite (nre_const ctx cost_limit act a_idx n c Hn1 Hnlen Hop').
      reflexivity.
    - (* input *)
      rewrite videal_unfold. cbn [videal_f]. rewrite Hop.
      unfold nval. rewrite (nre_input ctx cost_limit act a_idx n iv Hn1 Hnlen Hop').
      reflexivity.
    - (* state read: the register still holds the start value *)
      rewrite videal_unfold. cbn [videal_f]. rewrite Hop. cbv beta iota.
      unfold nval. rewrite (nre_svar ctx cost_limit act a_idx n sv Hn1 Hnlen Hop').
      cbn [tf_eval_expr].
      match goal with
      | |- @convert ?w1 ?w2 _ = _ =>
          transitivity (@convert w1 w2 ((fst ss0).[tf_dfg_s sv]));
            [ f_equal; exact (run_preserves_svar ctx cost_limit act input resp ss0 k Hnd sv) | ]
      end.
      rewrite <- Hmm, getenv_maps_from. reflexivity.
    - (* output read: the outputs stand at the start value *)
      rewrite videal_unfold. cbn [videal_f]. rewrite Hop. cbv beta iota.
      unfold nval. rewrite (nre_ovar ctx cost_limit act a_idx n ov Hn1 Hnlen Hop').
      cbn [tf_eval_expr].
      match goal with
      | |- @convert ?w1 ?w2 _ = _ =>
          transitivity (@convert w1 w2 ((snd ss0).[ov]));
            [ f_equal; exact (run_preserves_ovar ctx cost_limit act input resp ss0 k Hnd ov) | ]
      end.
      rewrite Hoo. reflexivity.
    - (* unary *)
      destruct (node_args_range ctx cost_limit act n Hn1 Hnlen a
                  ltac:(unfold get_args; rewrite Hop'; left; reflexivity)) as [Ha1 Ha].
      pose proof (nrv_peel_unary ctx cost_limit act a_idx n uop a pi (ssk k) (sik k)
                    Hop' Ha1 Hnlen Hv) as Hva.
      rewrite Hc, <- (IH a Ha pi Hpi Hva).
      unfold nval. rewrite (nre_unary ctx cost_limit act a_idx n uop a Hn1 Hnlen Hop').
      unfold node_sz, node_at in Hw |- *.
      destruct uop as [| s]; cbn [tf_eval_expr op1_bits]; rewrite Hw, convert_id; reflexivity.
    - (* binary *)
      destruct (node_args_range ctx cost_limit act n Hn1 Hnlen a
                  ltac:(unfold get_args; rewrite Hop'; left; reflexivity)) as [Ha1 Ha].
      destruct (node_args_range ctx cost_limit act n Hn1 Hnlen b
                  ltac:(unfold get_args; rewrite Hop'; right; left; reflexivity)) as [Hb1 Hb].
      destruct (nrv_peel_binary ctx cost_limit act a_idx n bop a b pi (ssk k) (sik k)
                  Hop' Ha1 Hb1 Hnlen Hv) as [Hva Hvb].
      rewrite Hc, <- (IH a Ha pi Hpi Hva), <- (IH b Hb pi Hpi Hvb).
      unfold nval. rewrite (nre_binary ctx cost_limit act a_idx n bop a b Hn1 Hnlen Hop').
      unfold node_sz, node_at in Hw |- *.
      destruct bop as [ | | | | | | szC cop | hz lz ]; destruct Hw as [H1 H2];
        rewrite H1, H2; cbn [tf_eval_expr op2_bits]; rewrite ?convert_id; try reflexivity.
      all: destruct cop; reflexivity.
    - (* resize *)
      destruct (node_args_range ctx cost_limit act n Hn1 Hnlen a
                  ltac:(unfold get_args; rewrite Hop'; left; reflexivity)) as [Ha1 Ha].
      pose proof (nrv_peel_resize ctx cost_limit act a_idx n a pi (ssk k) (sik k)
                    Hop' Ha1 Hnlen Hv) as Hva.
      rewrite Hc, <- (IH a Ha pi Hpi Hva).
      unfold nval. rewrite (nre_resize ctx cost_limit act a_idx n a Hn1 Hnlen Hop').
      reflexivity.
    - (* phi: the arm the condition selects *)
      destruct (node_args_range ctx cost_limit act n Hn1 Hnlen cnd
                  ltac:(unfold get_args; rewrite Hop'; left; reflexivity)) as [Hc1 Hcn].
      destruct (node_args_range ctx cost_limit act n Hn1 Hnlen t
                  ltac:(unfold get_args; rewrite Hop'; right; left; reflexivity)) as [Ht1 Htn].
      destruct (node_args_range ctx cost_limit act n Hn1 Hnlen e
                  ltac:(unfold get_args; rewrite Hop'; right; right; left; reflexivity))
        as [He1 Hen].
      destruct Hw as [Hcsz [Htsz Hesz]].
      assert (Hvc : rvalid act a_idx pi cnd (ssk k) (sik k) = Bits.ones 1).
      { destruct (phi_crit (get_tainted ctx G) (decl_facts ctx G) cnd pi) eqn:Hcrit.
        - exact (proj1 (nrv_peel_phi_crit ctx cost_limit act a_idx n cnd t e pi (ssk k) (sik k)
                          Hop' Hcrit Hc1 Ht1 He1 Hnlen Hv)).
        - exact (proj1 (nrv_peel_phi_sel ctx cost_limit act a_idx n cnd t e pi (ssk k) (sik k)
                          Hop' Hcrit Hc1 Ht1 He1 Hnlen Hv)). }
      pose proof (IH cnd Hcn pi Hpi Hvc) as IHc.
      rewrite Hc. unfold nval at 1.
      rewrite (nre_phi ctx cost_limit act a_idx n cnd t e Hn1 Hnlen Hop'). cbn [tf_eval_expr].
      match goal with
      | |- (if @beq_dec ?T ?E ?x ?z then _ else _) = _ =>
          assert (Hcb : nonzero (V cnd) = negb (@beq_dec T E x z));
          [ rewrite <- IHc, Hcsz; reflexivity
          | rewrite Hcb; destruct (@beq_dec T E x z) eqn:Hbz; cbn [negb] ]
      end.
      + (* the condition reads false: the else arm *)
        apply beq_dec_iff in Hbz.
        assert (IHe : nval ctx cost_limit act a_idx (ssk k) (sik k) (node_sz G e) e = V e).
        { destruct (phi_crit (get_tainted ctx G) (decl_facts ctx G) cnd pi) eqn:Hcrit.
          - exact (IH e Hen pi Hpi
                     (proj2 (proj2 (nrv_peel_phi_crit ctx cost_limit act a_idx n cnd t e pi
                                      (ssk k) (sik k) Hop' Hcrit Hc1 Ht1 He1 Hnlen Hv)))).
          - apply (IH e Hen ((cnd, false) :: pi)).
            + apply (pi_holds_cons ctx cost_limit act a_idx (sik k) cnd false pi (ssk k) Hpi).
              exact Hbz.
            + exact (proj2 (proj2 (nrv_peel_phi_sel ctx cost_limit act a_idx n cnd t e pi
                                     (ssk k) (sik k) Hop' Hcrit Hc1 Ht1 He1 Hnlen Hv)) Hbz). }
        rewrite <- IHe, Hesz, convert_id. reflexivity.
      + (* the condition reads true: the then arm *)
        apply beq_dec_false_iff in Hbz.
        assert (IHt : nval ctx cost_limit act a_idx (ssk k) (sik k) (node_sz G t) t = V t).
        { destruct (phi_crit (get_tainted ctx G) (decl_facts ctx G) cnd pi) eqn:Hcrit.
          - exact (IH t Htn pi Hpi
                     (proj1 (proj2 (nrv_peel_phi_crit ctx cost_limit act a_idx n cnd t e pi
                                      (ssk k) (sik k) Hop' Hcrit Hc1 Ht1 He1 Hnlen Hv)))).
          - apply (IH t Htn ((cnd, true) :: pi)).
            + apply (pi_holds_cons ctx cost_limit act a_idx (sik k) cnd true pi (ssk k) Hpi).
              destruct (SchedulerSimulationLemmas.bits1_cases
                          (nval ctx cost_limit act a_idx (ssk k) (sik k) 1 cnd)) as [Ho | Hz];
                [ exact Ho | exfalso; exact (Hbz Hz) ].
            + exact (proj1 (proj2 (nrv_peel_phi_sel ctx cost_limit act a_idx n cnd t e pi
                                     (ssk k) (sik k) Hop' Hcrit Hc1 Ht1 He1 Hnlen Hv)) Hbz). }
        rewrite <- IHt, Htsz, convert_id. reflexivity.
    - (* stall: a counter, read as zero *)
      rewrite videal_unfold. cbn [videal_f]. rewrite Hop.
      unfold nval. rewrite (nre_stall ctx cost_limit act a_idx n slat sa Hn1 Hnlen Hop').
      reflexivity.
    - (* drive: its argument's value *)
      destruct (node_args_range ctx cost_limit act n Hn1 Hnlen darg
                  ltac:(unfold get_args; rewrite Hop'; left; reflexivity)) as [Ha1 Ha].
      pose proof (nrv_peel_drive ctx cost_limit act a_idx n dp darg den pi (ssk k) (sik k)
                    Hop' Ha1 Hnlen Hv) as Hva.
      pose proof (wfg_build_dfg ctx cost_limit act _ (nth_In _ {| nid := 0; op := DFG_Empty; sz := 0 |} Hnlen))
        as Hfg.
      unfold node_args_sz in Hfg. rewrite Hop' in Hfg.
      destruct (wsz_node_sz ctx cost_limit act darg _ Hfg) as [_ Hdsz].
      rewrite videal_unfold. cbn [videal_f]. rewrite Hop. cbv beta iota.
      rewrite (videal_f_irrel ctx cost_limit act sp0 input darg n Ha).
      rewrite <- (IH darg Ha pi Hpi Hva).
      unfold nval. rewrite (nre_drive ctx cost_limit act a_idx n dp darg den Hn1 Hnlen Hop').
      unfold node_sz, node_at. rewrite Hdsz, convert_id. reflexivity.
    - (* sample: the answer the round trip latched *)
      assert (Hlen2 : 1 < length (graph G)) by lia.
      assert (Hsam : is_sample_of ctx cost_limit act n = true)
        by (unfold ProofDefinitions.is_sample_of, AttackerClock.node_op; rewrite Hop'; reflexivity).
      destruct (sample_index ctx cost_limit act a_idx n Halign Hsam) as [n_idx Hvid].
      assert (Hopn : AttackerClock.node_op ctx cost_limit act n = DFG_Sample sp tok en)
        by exact Hop'.
      destruct (sample_has_drive ctx cost_limit act n sp tok en Hopn) as [d [av [Hsd Hdop]]].
      pose proof (sample_drive_below ctx cost_limit act n sp tok en d Hop Hsd) as Hdn.
      assert (Hpl : payload_of (p_eq := tfs_spec_ips_eq_dec ctx) G n = Some av).
      { unfold payload_of. rewrite drive_of_sample_drive, Hsd.
        change (op (node_at G d)) with (AttackerClock.node_op ctx cost_limit act d).
        rewrite Hdop. reflexivity. }
      destruct (node_op_pos ctx cost_limit act d ltac:(rewrite Hdop; discriminate))
        as [Hd1 Hdlen].
      unfold AttackerClock.node_op in Hdop.
      assert (Hain : In av (get_args ctx (nth d (graph G) {| nid := 0; op := DFG_Empty; sz := 0 |})))
        by (unfold get_args; rewrite Hdop; left; reflexivity).
      destruct (node_args_range ctx cost_limit act d Hd1 Hdlen av Hain) as [Hav1 Havd].
      pose proof (wfg_build_dfg ctx cost_limit act _
                    (nth_In _ {| nid := 0; op := DFG_Empty; sz := 0 |} Hdlen)) as Hfgd.
      unfold node_args_sz in Hfgd. rewrite Hdop in Hfgd.
      destruct (wsz_node_sz ctx cost_limit act av _ Hfgd) as [_ Havsz].
      pose proof (drives_sized_holds ctx cost_limit act d sp av en Hdop) as Hdz.
      assert (Hreg : (fst (ssk k)).[tf_dfg_v a_idx n_idx] = Bits.ones 1).
      { rewrite <- Hvid in Hv.
        rewrite (sample_ref_is_register ctx cost_limit act a_idx n_idx Halign
                   ltac:(rewrite Hvid; exact Hsam) pi (length (graph G))
                   ltac:(rewrite Hvid; exact Hnlen)) in Hv.
        cbn [snd] in Hv. rewrite eval1_svar_v in Hv. exact Hv. }
      destruct (settled_run ctx cost_limit act a_idx input resp ss0 k Halign Hlen2 Hzz Hnd Hipc)
        as [Hans [Hzer [Hargs Hgrd]]].
      assert (Hopv : AttackerClock.node_op ctx cost_limit act (vreg_nid ctx cost_limit a_idx n_idx)
                     = DFG_Sample sp tok en) by (rewrite Hvid; exact Hopn).
      assert (Hsdv : ProofDefinitions.sample_drive ctx cost_limit act (vreg_nid ctx cost_limit a_idx n_idx) = Some d)
        by (rewrite Hvid; exact Hsd).
      (* the guard's literals are ready, so each reads its ideal bit *)
      assert (Hlit : forall l, In l en ->
                nval ctx cost_limit act a_idx (ssk k) (sik k) 1 (fst l)
                = ProofDefinitions.bit_of (nonzero (V (fst l)))).
      { intros l Hl.
        apply (bit_of_nonzero
                 (fun w => nval ctx cost_limit act a_idx (ssk k) (sik k) w (fst l))
                 (node_sz G (fst l))).
        - exact (guards_sized_holds ctx cost_limit act d sp av en Hdop l Hl).
        - apply (IH (fst l) (sample_lits_below ctx cost_limit act n sp tok en l Hop Hl) []).
          + exact (pi_holds_nil ctx cost_limit act a_idx (sik k) (ssk k)).
          + exact (Hgrd n_idx sp tok en Hopv Hreg l Hl). }
      assert (Hguard : guard_true G V en = true
                       <-> pi_holds ctx cost_limit act a_idx (sik k) en (ssk k)).
      { unfold guard_true. rewrite forallb_forall. split.
        - intros H c b Hin. pose proof (Hlit (c, b) Hin) as Hl. cbn [fst] in Hl. rewrite Hl.
          specialize (H (c, b) Hin). cbn [fst snd] in H. apply Bool.eqb_prop in H.
          rewrite H. reflexivity.
        - intros H [c b] Hin. cbn [fst snd]. pose proof (H c b Hin) as Hcb.
          pose proof (Hlit (c, b) Hin) as Hl. cbn [fst] in Hl. rewrite Hl in Hcb.
          destruct (nonzero (V c)), b; first [ reflexivity | discriminate Hcb ]. }
      assert (Hnre : node_ref_expr ctx cost_limit act a_idx n = tf_svar (tf_dfg_b a_idx n_idx)).
      { rewrite <- Hvid. apply (nre_sample ctx cost_limit act a_idx n_idx Halign).
        rewrite Hvid. exact Hsam. }
      destruct (guard_true G V en) eqn:Hg.
      + (* the call ran: the latch holds [ip_fn] of the request *)
        pose proof (proj1 Hguard eq_refl) as Hgh.
        rewrite (videal_sample_on ctx cost_limit act sp0 input n sp tok en av Hop Hg Hpl).
        pose proof (Hargs n_idx sp tok en d av en Hopv Hsdv Hdop Hreg) as Hvav.
        rewrite <- (IH av ltac:(lia) [] (pi_holds_nil ctx cost_limit act a_idx (sik k) (ssk k))
                      Hvav).
        pose proof (Hans n_idx sp tok en d av en Hopv Hsdv Hdop Hdz Hreg Hgh) as Hb.
        unfold nval at 1. rewrite Hnre. cbn [tf_eval_expr].
        match goal with
        | |- @convert ?w1 ?w2 ?r = _ =>
            transitivity (@convert w1 w2 (convert (szB := w1) (ip_fn (tfs_spec_ip ctx sp)
               (tf_eval_expr (tfs_states_size sched) (tfs_inputs_size sched)
                  (tfs_outputs_size sched) (szB := ip_req_sz (tfs_spec_ip ctx sp))
                  (node_ref_expr ctx cost_limit act a_idx av) (ssk k) (sik k)))));
            [ f_equal; exact Hb | ]
        end.
        rewrite convert_twice
          by (rewrite (buffer_register_node_size ctx cost_limit act a_idx n_idx Halign), Hvid;
              reflexivity).
        unfold nval, node_sz, node_at. rewrite Havsz, Hdz, convert_id. reflexivity.
      + (* the call was skipped: the latch still reads zero *)
        assert (Hng : ~ pi_holds ctx cost_limit act a_idx (sik k) en (ssk k))
          by (intro H; apply Hguard in H; discriminate H).
        rewrite (videal_sample_off ctx cost_limit act sp0 input n sp tok en Hop Hg).
        pose proof (Hzer n_idx sp tok en Hopv Hreg Hng) as Hz.
        unfold nval. rewrite Hnre. cbn [tf_eval_expr].
        match goal with
        | |- @convert ?w1 ?w2 ?r = _ =>
            transitivity (@convert w1 w2 (@Bits.zero w1)); [ f_equal; exact Hz | ]
        end.
        rewrite convert_zero
          by (rewrite (buffer_register_node_size ctx cost_limit act a_idx n_idx Halign), Hvid;
              reflexivity).
        reflexivity.
    - (* join: an ordering edge, read as zero *)
      rewrite videal_unfold. cbn [videal_f]. rewrite Hop.
      unfold nval. rewrite (nre_join n ja jb Hn1 Hnlen Hop).
      reflexivity.
  Qed.

  (* A public output's root, wherever it is ready, holds the output's value
     after the action. *)
  Lemma root_post k o r pi :
    (forall i, 1 <= i <= k -> ~ done_set ctx cost_limit (ssk i)) ->
    1 < length (graph G) ->
    In (DFG_OVar o, r) (var_map G) ->
    pi_holds ctx cost_limit act a_idx (sik k) pi (ssk k) ->
    rvalid act a_idx pi r (ssk k) (sik k) = Bits.ones 1 ->
    convert (szB := node_sz G r) ((snd (spec_run act sp0 input)).[o]) = V r.
  Proof.
    intros Hnd Hlen Hvm Hpi Hrv.
    rewrite <- (videal_settled k Hnd r pi Hpi Hrv).
    destruct Hstart as [Hoo [Hmm Hzz]].
    destruct (settled_run ctx cost_limit act a_idx input resp ss0 k Halign Hlen Hzz Hnd Hipc)
      as [Hans [_ [Hargs _]]].
    destruct (dfg_action_semantics ctx cost_limit act a_idx sp0 (ssk k) input (sik k)
                Halign (fun v => eq_refl)
                ltac:(intros n_idx p tok en d av en' Ho1 Ho2 Ho3 Ho4 Hg Hv;
                      exact (Hans n_idx p tok en d av en' Ho1 Ho2 Ho3 Ho4 Hv
                               (guard_pi_holds ctx cost_limit act a_idx (sik k) en (ssk k) Hg)))
                Hargs
                ltac:(intro sv; rewrite (run_preserves_svar ctx cost_limit act input resp ss0 k Hnd sv);
                      rewrite <- Hmm, getenv_maps_from; reflexivity)
                ltac:(intro ov; rewrite (run_preserves_ovar ctx cost_limit act input resp ss0 k Hnd ov);
                      rewrite Hoo; reflexivity))
      as [_ [Hout _]].
    pose proof (Hout o r pi Hvm (pi_holds_guard ctx cost_limit act a_idx (sik k) pi (ssk k) Hpi) Hrv)
      as Ho.
    unfold nval, node_ref_expr, node_sz, node_at.
    rewrite (root_width ctx cost_limit act o r Hvm), convert_id.
    symmetry. exact Ho.
  Qed.

  (* The roots were ready on the cycle before done, so each holds its output. *)
  Lemma roots_ideal o r :
    tfs_spec_outputs_class ctx o = Public ->
    In (DFG_OVar o, r) (var_map G) ->
    convert (szB := node_sz G r) ((snd (spec_run act sp0 input)).[o]) = V r.
  Proof.
    intros _ Hvm.
    pose proof Hstart as Hst. destruct Hst as [Hoo [Hmm Hzz]].
    destruct (L_first_done ctx cost_limit act sp0 ss0 input resp Hstart)
      as [HL0 [Hdone Hbefore]].
    destruct (ProofDefinitions.L ctx cost_limit act input resp ss0) as [| m].
    - lia.
    - assert (Hnd : forall i, 1 <= i <= m -> ~ done_set ctx cost_limit (ssk i))
        by (intros i Hi; apply Hbefore; lia).
      pose proof (proj1 (build_dfg_args_pos ctx cost_limit act) _ r Hvm) as Hr1.
      pose proof (proj1 (wsz_node_sz ctx cost_limit act r _
                           (wvsz_build_dfg ctx cost_limit act _ r Hvm))) as Hrlen.
      pose proof (sched_step_done_valid ctx cost_limit act a_idx (ssk m) (sik m) r Halign Hdone
                    (in_map snd _ _ Hvm)) as Hfull.
      destruct (valid_settled_run ctx cost_limit act a_idx input resp ss0 m Halign
                  (fun q => Hzz (tf_dfg_v a_idx q) I)) as [_ [Hrefs Hvs]].
      destruct (full_table_sample_bufs ctx cost_limit act a_idx Halign) as [Hft1 Hft2].
      pose proof (compile_subst_ref_valid_gen_at ctx cost_limit act a_idx (ssk m) (sik m)
                    Halign Hvs Hrefs (nth (index_to_nat a_idx) (buffer_needs ctx cost_limit) [])
                    (fun e He => He) (length (graph G)) r []
                    (fun x _ Hx => Hft1 x Hx) (fun x mm msz _ Hx Hs => Hft2 x mm msz Hx Hs)
                    Hr1 Hrlen Hrlen Hfull) as Hrv.
      exact (root_post m o r [] Hnd ltac:(lia) Hvm
               (pi_holds_nil ctx cost_limit act a_idx (sik m) (ssk m)) Hrv).
  Qed.

  Local Notation view := (observe ctx input (snd sp0) (snd (spec_run act sp0 input))).
  Local Notation rvals :=
    (recovered ctx cost_limit act (seen_in ctx view) (seen_pre ctx view) (seen_post ctx view)).

  (* EVERYTHING THE RECIPE RECOVERS IS AN IDEAL VALUE. *)
  Lemma recovered_ideal n v :
    rvals n = Some v -> v = V n.
  Proof.
    apply (recover_sound (p_eq := tfs_spec_ips_eq_dec ctx) (tfs_spec_ip ctx) (tfs_spec_decls ctx)
             G V (build_well_sized ctx cost_limit act)
             (videal_consistent ctx cost_limit act sp0 input)
             (videal_sample_off ctx cost_limit act sp0 input)
             (videal_sample_on ctx cost_limit act sp0 input)
             (videal_stall ctx cost_limit act sp0 input)
             (videal_join ctx cost_limit act sp0 input)
             (videal_drive ctx cost_limit act sp0 input)).
    exact (seed_sound ctx cost_limit act sp0 input _ roots_ideal).
  Qed.

  Theorem recovered_vals_sound k :
    (forall i, 1 <= i <= k -> ~ done_set ctx cost_limit (ssk i)) ->
    vals_sound ctx cost_limit act a_idx rvals (ssk k) (sik k).
  Proof.
    intros Hnd n v pi Hval Hpi Hrv.
    rewrite (recovered_ideal n v Hval). exact (videal_settled k Hnd n pi Hpi Hrv).
  Qed.

  (* ================================================================= *)
  (* COVERAGE: the recipe reaches every value the hardware reads.        *)
  (* ================================================================= *)

  Local Notation peq := (tfs_spec_ips_eq_dec ctx).
  Local Notation seedv := (Recover.seed i_sz o_sz G (seen_in ctx view) (seen_pre ctx view)
                                        (seen_post ctx view)).
  Local Notation Kf f := (recover (p_eq := peq) (tfs_spec_ip ctx) (tfs_spec_decls ctx) G seedv f).

  Lemma seedv_sound : sound_known G V seedv.
  Proof. exact (seed_sound ctx cost_limit act sp0 input _ roots_ideal). Qed.

  Lemma seedv_range n : seedv n <> None -> n < length (graph G).
  Proof.
    intro H. destruct (Nat.lt_ge_cases n (length (graph G))) as [Hlt | Hge]; [ exact Hlt | exfalso ].
    unfold Recover.seed, node_at in H. rewrite nth_overflow in H by exact Hge. cbn beta iota in H.
    match type of H with
    | context [find_map ?F ?L] => destruct (find_map F L) as [y |] eqn:Hf; [ | apply H; reflexivity ]
    end.
    apply find_map_some in Hf. destruct Hf as [[[sv | o] r] [Hin Hf]]; [ discriminate | ].
    destruct (Nat.eqb r n) eqn:Hrn; [ | discriminate ]. apply Nat.eqb_eq in Hrn. subst r.
    pose proof (proj1 (wsz_node_sz ctx cost_limit act n _
                         (wvsz_build_dfg ctx cost_limit act _ n Hin))). lia.
  Qed.

  Local Ltac recipe_hyps :=
    exact (build_well_sized ctx cost_limit act)
    || exact (videal_consistent ctx cost_limit act sp0 input)
    || exact (videal_sample_off ctx cost_limit act sp0 input)
    || exact (videal_sample_on ctx cost_limit act sp0 input)
    || exact (videal_stall ctx cost_limit act sp0 input)
    || exact (videal_join ctx cost_limit act sp0 input)
    || exact (videal_drive ctx cost_limit act sp0 input).

  Lemma Kf_mono_le f f' n x : f <= f' -> Kf f n = Some x -> Kf f' n = Some x.
  Proof.
    apply (recover_mono_le (p_eq := peq) (tfs_spec_ip ctx) (tfs_spec_decls ctx) G V);
      try recipe_hyps; exact seedv_sound.
  Qed.

  Definition reached (n: nid_t) : Prop := exists f x, Kf f n = Some x.

  Lemma reached_rounds n : reached n -> exists y, rvals n = Some y.
  Proof.
    intros [f [x H]].
    pose proof (recover_closed (p_eq := peq) (tfs_spec_ip ctx) (tfs_spec_decls ctx) G V
                  ltac:(recipe_hyps) ltac:(recipe_hyps) ltac:(recipe_hyps) ltac:(recipe_hyps)
                  ltac:(recipe_hyps) ltac:(recipe_hyps) ltac:(recipe_hyps)
                  seedv seedv_sound seedv_range f n x H) as Hc.
    exists x. unfold recovered.
    apply (Kf_mono_le (S (length (universe (tfs_spec_decls ctx) G))) _ n x); [ | exact Hc ].
    unfold rounds, universe. rewrite app_length, seq_length, map_length. nia.
  Qed.

  Lemma reached_all (l: list nid_t) :
    (forall m, In m l -> reached m) -> exists f, forall m, In m l -> exists x, Kf f m = Some x.
  Proof.
    induction l as [| a l IH]; intro H; [ exists 0; intros m [] | ].
    destruct (H a (or_introl eq_refl)) as [fa [xa Ha]].
    destruct (IH (fun m Hm => H m (or_intror Hm))) as [fl Hl].
    exists (Nat.max fa fl). intros m [<- | Hm].
    - exists xa. exact (Kf_mono_le fa (Nat.max fa fl) a xa ltac:(lia) Ha).
    - destruct (Hl m Hm) as [x Hx]. exists x. exact (Kf_mono_le fl (Nat.max fa fl) m x ltac:(lia) Hx).
  Qed.

  Lemma reached_of_seed n : seedv n <> None -> reached n.
  Proof.
    intro H. destruct (seedv n) as [v |] eqn:Hs; [ | exfalso; apply H; reflexivity ].
    exists 1, v. rewrite recover_S, Hs. reflexivity.
  Qed.

  Lemma reached_of_step f n : step (p_eq := peq) (tfs_spec_ip ctx) G (Kf f) n <> None -> reached n.
  Proof.
    intro H. exists (S f). rewrite recover_S.
    destruct (seedv n) as [v |]; [ exists v; reflexivity | ].
    destruct (step (tfs_spec_ip ctx) G (Kf f) n) as [v |]; [ exists v; reflexivity | ].
    exfalso. apply H. reflexivity.
  Qed.

  Lemma reached_of_back f n : back (tfs_spec_decls ctx) G (Kf f) n <> None -> reached n.
  Proof.
    intro H. exists (S f). rewrite recover_S.
    destruct (seedv n) as [v |]; [ exists v; reflexivity | ].
    destruct (step (tfs_spec_ip ctx) G (Kf f) n) as [v |]; [ exists v; reflexivity | ].
    destruct (back (tfs_spec_decls ctx) G (Kf f) n) as [v |]; [ exists v; reflexivity | ].
    exfalso. apply H. reflexivity.
  Qed.

  Lemma find_map_in {A B} (f: A -> option B) (l: list A) a :
    In a l -> f a <> None -> find_map f l <> None.
  Proof.
    induction l as [| b l IH]; intros Hin Hf; [ destruct Hin | ]. cbn [find_map].
    destruct (f b) eqn:Hb; [ discriminate | ].
    destruct Hin as [<- | Hin]; [ exfalso; apply Hf; exact Hb | exact (IH Hin Hf) ].
  Qed.

  Lemma guard_val_some (k: known G) en :
    (forall l, In l en -> k (fst l) <> None) -> guard_val G k en <> None.
  Proof.
    induction en as [| [c b] en IH]; intro H; cbn [guard_val]; [ discriminate | ].
    destruct (k c) as [x |] eqn:Hc; [ | exfalso; apply (H (c, b) (or_introl eq_refl)); exact Hc ].
    destruct (guard_val G k en) as [r |]; [ discriminate | ].
    exfalso. apply IH; [ intros l Hl; exact (H l (or_intror Hl)) | reflexivity ].
  Qed.

  Lemma decl_instance_packet i :
    In i (Taint.decl_instances ctx G) ->
    exists r, In (r, i) (instances (tfs_spec_decls ctx) G).
  Proof.
    unfold Taint.decl_instances. intro Hi. apply filter_In in Hi. destruct Hi as [Hi _].
    apply in_flat_map in Hi. destruct Hi as [r [Hr Hi]].
    exists r. unfold instances. apply in_flat_map. exists r. split; [ exact Hr | ].
    apply in_map. exact Hi.
  Qed.

  (* An instance whose guard is known to hold and whose sources are known fires. *)
  Lemma back_fires f r i :
    In (r, i) (instances (tfs_spec_decls ctx) G) ->
    guard_val G (Kf f) (di_guard i) = Some true ->
    (forall s, In s (di_sources i) -> Kf f s <> None) ->
    back (tfs_spec_decls ctx) G (Kf f) (di_target i) <> None.
  Proof.
    intros Hin Hg Hs. unfold back. apply (find_map_in _ _ (r, i) Hin). cbn [fst snd].
    destruct (Nat.eq_dec (di_target i) (di_target i)) as [e | ne]; [ | exfalso; apply ne; reflexivity ].
    rewrite Hg.
    replace (forallb _ (di_sources i)) with true; [ discriminate | ].
    symmetry. apply forallb_forall. intros s Hsi.
    destruct (Kf f s) eqn:E; [ reflexivity | exfalso; exact (Hs s Hsi E) ].
  Qed.

  Lemma roots_reached n : In n (untainted_roots ctx G) -> reached n.
  Proof.
    unfold untainted_roots.
    assert (Hbase : forall m, In m (public_dsts ctx G ++ trivially_public ctx G) -> reached m).
    { intros m Hm. apply in_app_or in Hm. destruct Hm as [Hd | Ht].
      - unfold public_dsts in Hd. apply in_map_iff in Hd.
        destruct Hd as [[v r] [Hr Hf]]. cbn [snd] in Hr. subst r.
        apply filter_In in Hf. destruct Hf as [Hvm Hpub].
        destruct v as [sv | o]; [ discriminate | ].
        apply reached_of_seed. unfold Recover.seed.
        destruct (match op (node_at G m) with
                  | DFG_Input v => _ | DFG_Var (DFG_OVar o0) => _ | _ => None end);
          [ discriminate | ].
        apply (find_map_in _ _ (DFG_OVar o, m) Hvm). rewrite Nat.eqb_refl.
        cbn [seen_post observe]. destruct (tfs_spec_outputs_class ctx o); [ discriminate | ].
        discriminate Hpub.
      - unfold trivially_public in Ht. apply filter_In in Ht. destruct Ht as [_ Hop].
        destruct (op (nth m (graph G) {| nid := 0; op := DFG_Empty; sz := 0 |})) eqn:Hm;
          try discriminate.
        + apply (reached_of_step 0). unfold step, node_at. rewrite Hm. discriminate.
        + apply reached_of_seed. unfold Recover.seed, node_at. rewrite Hm.
          cbn [seen_in observe]. destruct (tfs_spec_inputs_class ctx v); [ discriminate | ].
          discriminate Hop. }
    revert Hbase. generalize (public_dsts ctx G ++ trivially_public ctx G) as acc.
    generalize (length (graph G)) as fuel.
    induction fuel as [| fuel IH]; intros acc Hacc Hin; [ exact (Hacc n Hin) | ].
    cbn [saturate] in Hin. cbv zeta in Hin.
    assert (Hstep : forall m, In m (saturate_step ctx G acc) -> reached m).
    { unfold saturate_step.
      assert (Hgen : forall l acc0,
                (forall i, In i l -> In i (uncond_instances ctx G)) ->
                (forall m, In m acc0 -> reached m) ->
                forall m, In m (fold_left (fun acc i =>
                                  if forallb (fun s => mem_nid s acc) (di_sources i)
                                     && negb (mem_nid (di_target i) acc)
                                  then di_target i :: acc else acc) l acc0) -> reached m).
      { induction l as [| i l IHl]; intros acc0 Hsub Hacc0 m Hm; [ exact (Hacc0 m Hm) | ].
        cbn [fold_left] in Hm.
        destruct (forallb (fun s => mem_nid s acc0) (di_sources i)
                  && negb (mem_nid (di_target i) acc0)) eqn:Hf;
          [ | exact (IHl _ (fun j Hj => Hsub j (or_intror Hj)) Hacc0 m Hm) ].
        apply andb_prop in Hf. destruct Hf as [Hf _]. rewrite forallb_forall in Hf.
        apply (IHl (di_target i :: acc0) (fun j Hj => Hsub j (or_intror Hj))); [ | exact Hm ].
        intros x [<- | Hx]; [ | exact (Hacc0 x Hx) ].
        pose proof (Hsub i (or_introl eq_refl)) as Hu.
        unfold uncond_instances in Hu. apply filter_In in Hu. destruct Hu as [Hdi Hng].
        destruct (decl_instance_packet i Hdi) as [r Hri].
        destruct (reached_all (di_sources i)
                    (fun s Hs => Hacc0 s (IPRProof.mem_nid_In s acc0 (Hf s Hs))))
          as [f Hfs].
        apply (reached_of_back f). apply (back_fires f r i Hri).
        - destruct (di_guard i); [ reflexivity | discriminate Hng ].
        - intros s Hs. destruct (Hfs s Hs) as [x Hx]. rewrite Hx. discriminate. }
      exact (Hgen _ acc (fun i Hi => Hi) Hacc). }
    destruct (Nat.eqb (length (saturate_step ctx G acc)) (length acc));
      [ exact (Hacc n Hin) | exact (IH _ Hstep Hin) ].
  Qed.

  (* EVERY UNTAINTED NODE IS REACHED: the attacker can compute it. *)
  Theorem untainted_reached n :
    1 <= n -> n < length (graph G) -> ~ In n (get_tainted ctx G) -> reached n.
  Proof.
    induction n as [n IH] using lt_wf_ind. intros Hn1 Hnlen Hnt.
    destruct (in_dec Nat.eq_dec n (untainted_roots ctx G)) as [Hr | Hnr];
      [ exact (roots_reached n Hr) | ].
    assert (IHa : forall a, In a (get_args ctx (node_at G n)) -> reached a).
    { intros a Ha.
      destruct (node_args_range ctx cost_limit act n Hn1 Hnlen a Ha) as [Ha1 Han].
      exact (IH a Han Ha1 ltac:(lia) (arg_untainted ctx cost_limit act n a Hnlen Hnt Hnr Ha)). }
    assert (Hnode : In (node_at G n) (graph G)) by (apply nth_In; exact Hnlen).
    assert (Hnid : nid (node_at G n) = n) by exact (node_nid_at ctx cost_limit act n Hnlen).
    destruct (op (node_at G n)) as [c | iv | [sv | ov] | uop a | bop a b | a | cnd t e
                                   | slat sa | dp darg den | sp tok en | ja jb | ] eqn:Hop.
    - apply (reached_of_step 0). unfold step. rewrite Hop. discriminate.
    - destruct (tfs_spec_inputs_class ctx iv) eqn:Hcls.
      + apply reached_of_seed. unfold Recover.seed. rewrite Hop.
        cbn [seen_in observe]. rewrite Hcls. discriminate.
      + exfalso. apply Hnt. rewrite <- Hnid.
        apply (input_secret_tainted ctx cost_limit act _ iv Hnode Hop Hcls). rewrite Hnid. exact Hnr.
    - exfalso. apply Hnt. rewrite <- Hnid.
      apply (svar_tainted ctx cost_limit act _ sv Hnode Hop). rewrite Hnid. exact Hnr.
    - destruct (tfs_spec_outputs_class ctx ov) eqn:Hcls.
      + apply reached_of_seed. unfold Recover.seed. rewrite Hop.
        cbn [seen_pre observe]. rewrite Hcls. discriminate.
      + exfalso. apply Hnt. rewrite <- Hnid.
        apply (ovar_secret_tainted ctx cost_limit act _ ov Hnode Hop Hcls). rewrite Hnid. exact Hnr.
    - destruct (reached_all [a] (fun m Hm => IHa m ltac:(unfold get_args; rewrite Hop; exact Hm)))
        as [f Hf].
      apply (reached_of_step f). unfold step. rewrite Hop.
      destruct (Hf a (or_introl eq_refl)) as [x Hx]. rewrite Hx. discriminate.
    - destruct (reached_all [a; b] (fun m Hm => IHa m ltac:(unfold get_args; rewrite Hop; exact Hm)))
        as [f Hf].
      apply (reached_of_step f). unfold step. rewrite Hop.
      destruct (Hf a (or_introl eq_refl)) as [x Hx]. destruct (Hf b (or_intror (or_introl eq_refl))) as [y Hy].
      rewrite Hx, Hy. discriminate.
    - destruct (reached_all [a] (fun m Hm => IHa m ltac:(unfold get_args; rewrite Hop; exact Hm)))
        as [f Hf].
      apply (reached_of_step f). unfold step. rewrite Hop.
      destruct (Hf a (or_introl eq_refl)) as [x Hx]. rewrite Hx. discriminate.
    - destruct (reached_all [cnd; t; e]
                  (fun m Hm => IHa m ltac:(unfold get_args; rewrite Hop; exact Hm))) as [f Hf].
      apply (reached_of_step f). unfold step. rewrite Hop.
      destruct (Hf cnd (or_introl eq_refl)) as [x Hx]. rewrite Hx.
      destruct (Hf t (or_intror (or_introl eq_refl))) as [y Hy].
      destruct (Hf e (or_intror (or_intror (or_introl eq_refl)))) as [z Hz].
      destruct (nonzero x); [ rewrite Hy | rewrite Hz ]; discriminate.
    - apply (reached_of_step 0). unfold step. rewrite Hop. discriminate.
    - destruct (reached_all [darg] (fun m Hm => IHa m ltac:(unfold get_args; rewrite Hop; destruct Hm as [<- | []]; left; reflexivity)))
        as [f Hf].
      apply (reached_of_step f). unfold step. rewrite Hop.
      destruct (Hf darg (or_introl eq_refl)) as [x Hx]. rewrite Hx. discriminate.
    - (* an IP answer: its request and its path condition are untainted *)
      assert (Hopn : AttackerClock.node_op ctx cost_limit act n = DFG_Sample sp tok en) by exact Hop.
      destruct (sample_has_drive ctx cost_limit act n sp tok en Hopn) as [d [av [Hsd Hdop]]].
      pose proof (sample_drive_untainted ctx cost_limit act n d
                    (plumbing_not_root_holds ctx cost_limit act) Hnlen Hsd Hnt Hnr) as Hdt.
      pose proof (sample_drive_below ctx cost_limit act n sp tok en d Hop Hsd) as Hdn.
      destruct (node_op_pos ctx cost_limit act d ltac:(rewrite Hdop; discriminate)) as [Hd1 Hdlen].
      assert (Hdnr : ~ In d (untainted_roots ctx G))
        by (apply (plumbing_not_root_holds ctx cost_limit act);
            unfold ProofDefinitions.is_plumbing; rewrite Hdop; reflexivity).
      assert (Hdargs : forall x, In x (av :: map fst en) -> reached x).
      { intros x Hx.
        assert (Hxin : In x (get_args ctx (nth d (graph G) {| nid := 0; op := DFG_Empty; sz := 0 |})))
          by (unfold get_args; unfold AttackerClock.node_op in Hdop; rewrite Hdop; exact Hx).
        destruct (node_args_range ctx cost_limit act d Hd1 Hdlen x Hxin) as [Hx1 Hxd].
        exact (IH x ltac:(lia) Hx1 ltac:(lia) (arg_untainted ctx cost_limit act d x Hdlen Hdt Hdnr Hxin)). }
      destruct (reached_all _ Hdargs) as [f Hf].
      apply (reached_of_step f). unfold step. rewrite Hop.
      destruct (guard_val G (Kf f) en) as [[|] |] eqn:Hg.
      + assert (Hpl : payload_of (p_eq := peq) G n = Some av).
        { unfold payload_of. rewrite drive_of_sample_drive, Hsd.
          change (op (node_at G d)) with (AttackerClock.node_op ctx cost_limit act d).
          rewrite Hdop. reflexivity. }
        rewrite Hpl. destruct (Hf av (or_introl eq_refl)) as [x Hx]. rewrite Hx. discriminate.
      + discriminate.
      + exfalso. apply (guard_val_some (Kf f) en); [ | exact Hg ].
        intros l Hl. destruct (Hf (fst l) (or_intror (in_map fst en l Hl))) as [x Hx].
        rewrite Hx. discriminate.
    - apply (reached_of_step 0). unfold step. rewrite Hop. discriminate.
    - exfalso. pose proof (proj2 (proj2 (build_dfg_args_pos ctx cost_limit act)) _ Hnode Hop).
      lia.
  Qed.

  Lemma Kf_sound f : sound_known G V (Kf f).
  Proof.
    apply (recover_sound (p_eq := peq) (tfs_spec_ip ctx) (tfs_spec_decls ctx) G V);
      try recipe_hyps; exact seedv_sound.
  Qed.

  (* ---- recoveries that hold on some paths only ---- *)

  Definition lit_known (l: lit) : Prop := reached (fst l) /\ nonzero (V (fst l)) = snd l.

  Definition facts_ok (base: list gfact) : Prop :=
    forall c g, In (c, g) base -> (forall l, In l g -> lit_known l) -> reached c.

  Lemma guard_incl_known g gs :
    guard_incl g gs = true -> (forall l, In l gs -> lit_known l) -> forall l, In l g -> lit_known l.
  Proof.
    unfold guard_incl. rewrite forallb_forall. intros Hi H l Hl.
    specialize (Hi l Hl). apply existsb_exists in Hi. destruct Hi as [l' [Hl' Heq]].
    unfold lit_eqb in Heq. apply andb_prop in Heq. destruct Heq as [Hc Hb].
    apply Nat.eqb_eq in Hc. apply Bool.eqb_prop in Hb.
    destruct l as [c b], l' as [c' b']. cbn [fst snd] in Hc, Hb. subst c' b'. exact (H _ Hl').
  Qed.

  (* A guard whose literals are known reads true in the recipe. *)
  Lemma guard_val_known (gd: list lit) :
    (forall l, In l gd -> lit_known l) -> exists f, guard_val G (Kf f) gd = Some true.
  Proof.
    intro H.
    destruct (reached_all (map fst gd)
                (fun m Hm => let '(ex_intro _ l (conj Hl Hin)) := proj1 (in_map_iff fst gd m) Hm in
                             eq_ind (fst l) reached (proj1 (H l Hin)) m Hl)) as [f Hf].
    exists f. induction gd as [| [c b] gd IHg]; cbn [guard_val]; [ reflexivity | ].
    destruct (Hf c (or_introl eq_refl)) as [x Hx]. rewrite Hx.
    rewrite IHg.
    - destruct (H (c, b) (or_introl eq_refl)) as [_ Hb]. cbn [fst snd] in Hb.
      rewrite (Kf_sound f c x Hx), Hb, Bool.eqb_reflx. reflexivity.
    - intros l Hl. exact (H l (or_intror Hl)).
    - intros m Hm. exact (Hf m (or_intror Hm)).
  Qed.


  Lemma gfold_facts_ok i combos :
    (forall gs, In gs combos ->
       (forall l, In l (di_guard i ++ gs) -> lit_known l) -> reached (di_target i)) ->
    forall acc0, facts_ok acc0 -> facts_ok (fold_left (gadd_of i) combos acc0).
  Proof.
    induction combos as [| gs combos IHc]; intros Hnew acc0 Hacc0; cbn [fold_left];
      [ exact Hacc0 | ].
    apply IHc; [ intros gs' Hgs'; apply Hnew; right; exact Hgs' | ].
    unfold gadd_of. destruct (gsubsumed acc0 (di_target i) (di_guard i ++ gs)); [ exact Hacc0 | ].
    intros c g Hin. apply in_app_or in Hin. destruct Hin as [Hin | [Heq | []]].
    - exact (Hacc0 c g Hin).
    - injection Heq as <- <-. exact (Hnew gs (or_introl eq_refl)).
  Qed.
  Lemma gstep1_facts_ok acc i :
    In i (Taint.decl_instances ctx G) -> facts_ok acc -> facts_ok (gstep1 acc i).
  Proof.
    intros Hi Hacc. unfold gstep1.
    assert (Hnew : forall gs, In gs (gcombine acc (di_sources i)) ->
              (forall l, In l (di_guard i ++ gs) -> lit_known l) -> reached (di_target i)).
    { intros gs Hgs Hlits.
      assert (Hsrc : forall s, In s (di_sources i) -> reached s).
      { intros s Hs. destruct (IPRProof.gcombine_sound acc (di_sources i) gs Hgs s Hs)
          as [g [Hg Hincl]].
        apply (Hacc s g Hg). apply (guard_incl_known g gs Hincl).
        intros l Hl. apply Hlits. apply in_or_app. right. exact Hl. }
      destruct (reached_all (di_sources i) Hsrc) as [f1 Hf1].
      destruct (guard_val_known (di_guard i)
                  (fun l Hl => Hlits l (in_or_app _ _ _ (or_introl Hl)))) as [f2 Hf2].
      destruct (decl_instance_packet i Hi) as [r Hri].
      apply (reached_of_back (Nat.max f1 f2)). apply (back_fires (Nat.max f1 f2) r i Hri).
      - apply (guard_val_mono G
                 (Kf f2) (Kf (Nat.max f1 f2))); [ | exact Hf2 ].
        intros m x Hx. exact (Kf_mono_le f2 _ m x (Nat.le_max_r _ _) Hx).
      - intros s Hs. destruct (Hf1 s Hs) as [x Hx].
        rewrite (Kf_mono_le f1 _ s x (Nat.le_max_l _ _) Hx). discriminate. }
    exact (gfold_facts_ok i _ Hnew acc Hacc).
  Qed.

  Lemma decl_facts_ok : facts_ok (decl_facts ctx G).
  Proof.
    unfold decl_facts.
    assert (Hbase : facts_ok (map (fun n => (n, @nil lit)) (untainted_roots ctx G))).
    { intros c g Hin _. apply in_map_iff in Hin. destruct Hin as [n [Heq Hn]].
      injection Heq as <- <-. exact (roots_reached n Hn). }
    revert Hbase. generalize (map (fun n => (n, @nil lit)) (untainted_roots ctx G)) as base.
    generalize (length (graph G)) as fuel.
    induction fuel as [| fuel IH]; intros base Hbase; cbn [gsaturate]; [ exact Hbase | ].
    cbv zeta.
    assert (Hstep : facts_ok (gsaturate_step ctx G base)).
    { unfold gsaturate_step.
      assert (Hgen : forall l b0, (forall i, In i l -> In i (Taint.decl_instances ctx G)) ->
                       facts_ok b0 -> facts_ok (fold_left gstep1 l b0)).
      { induction l as [| i l IHl]; intros b0 Hl Hb0; cbn [fold_left]; [ exact Hb0 | ].
        apply IHl; [ intros j Hj; apply Hl; right; exact Hj | ].
        exact (gstep1_facts_ok b0 i (Hl i (or_introl eq_refl)) Hb0). }
      exact (Hgen _ base (fun i Hi => Hi) Hbase). }
    match goal with |- context [if ?b then _ else _] => destruct b end;
      [ exact Hbase | exact (IH _ Hstep) ].
  Qed.

  Lemma path_ok_suffix k pre l rest :
    path_ok ctx cost_limit act a_idx (ssk k) (sik k) (pre ++ l :: rest) ->
    path_ok ctx cost_limit act a_idx (ssk k) (sik k) rest
    /\ (exists n t e, AttackerClock.node_op ctx cost_limit act n = DFG_Phi (fst l) t e
          /\ phi_crit (get_tainted ctx G) (decl_facts ctx G) (fst l) rest = false)
    /\ pi_holds ctx cost_limit act a_idx (sik k) rest (ssk k)
    /\ rvalid act a_idx rest (fst l) (ssk k) (sik k) = Bits.ones 1.
  Proof.
    induction pre as [| [c0 b0] pre IH]; intro Hp.
    - destruct l as [c b]. exact Hp.
    - exact (IH (proj1 Hp)).
  Qed.

  (* A phi condition read at a well-formed path is reached: untainted, or
     declassified under a guard whose literals the path already settled. *)
  Theorem selector_reached k :
    (forall i, 1 <= i <= k -> ~ done_set ctx cost_limit (ssk i)) ->
    forall len pi c, length pi <= len ->
      path_ok ctx cost_limit act a_idx (ssk k) (sik k) pi ->
      (exists n t e, AttackerClock.node_op ctx cost_limit act n = DFG_Phi c t e
         /\ phi_crit (get_tainted ctx G) (decl_facts ctx G) c pi = false) ->
      pi_holds ctx cost_limit act a_idx (sik k) pi (ssk k) ->
      rvalid act a_idx pi c (ssk k) (sik k) = Bits.ones 1 ->
      reached c.
  Proof.
    intros Hnd len. induction len as [| len IH];
      intros pi c Hlen Hpok [n [t [e [Hop Hcrit]]]] Hpi Hrv.
    all: destruct (node_op_pos ctx cost_limit act n ltac:(rewrite Hop; discriminate))
           as [Hn1 Hnlen].
    all: assert (Hcin : In c (get_args ctx (nth n (graph G) {| nid := 0; op := DFG_Empty; sz := 0 |})))
           by (unfold get_args; unfold AttackerClock.node_op in Hop; rewrite Hop; left; reflexivity).
    all: destruct (node_args_range ctx cost_limit act n Hn1 Hnlen c Hcin) as [Hc1 Hcn].
    all: destruct (Taint.mem_nid c (get_tainted ctx G)) eqn:Hmt;
      [ | exact (untainted_reached c Hc1 ltac:(lia) (IPRProof.mem_nid_not_In c _ Hmt)) ].
    all: unfold phi_crit in Hcrit; rewrite Hmt in Hcrit; cbn [andb] in Hcrit;
         apply Bool.negb_false_iff in Hcrit; unfold Taint.declassified_at in Hcrit;
         apply existsb_exists in Hcrit; destruct Hcrit as [g [Hg Hincl]];
         apply (decl_facts_ok c g (IPRProof.gfacts_of_In _ c g Hg)).
    all: intros l Hl;
         assert (Hlp : In l pi)
           by (unfold guard_incl in Hincl; rewrite forallb_forall in Hincl;
               specialize (Hincl l Hl); apply existsb_exists in Hincl;
               destruct Hincl as [l' [Hl' Heq]]; unfold lit_eqb in Heq;
               apply andb_prop in Heq; destruct Heq as [Hc Hb];
               apply Nat.eqb_eq in Hc; apply Bool.eqb_prop in Hb;
               destruct l as [c0 b0], l' as [c1 b1]; cbn [fst snd] in Hc, Hb;
               subst c1 b1; exact Hl').
    - destruct pi; [ destruct Hlp | cbn [length] in Hlen; lia ].
    - destruct (in_split l pi Hlp) as [pre [rest Hsplit]].
      rewrite Hsplit in Hpok.
      destruct (path_ok_suffix k pre l rest Hpok) as [Hpr [Hphi [Hpir Hrvl]]].
      assert (Hrl : length rest <= len)
        by (rewrite Hsplit, app_length in Hlen; cbn [length] in Hlen; lia).
      split; [ exact (IH rest (fst l) Hrl Hpr Hphi Hpir Hrvl) | ].
      (* the path holds the literal, and the literal is settled where it was read *)
      pose proof (Hpi (fst l) (snd l) ltac:(destruct l; exact Hlp)) as Hbit.
      pose proof (videal_settled k Hnd (fst l) rest Hpir Hrvl) as Hset.
      destruct Hphi as [m [tm [em [Hopm _]]]].
      destruct (node_op_pos ctx cost_limit act m ltac:(rewrite Hopm; discriminate))
        as [_ Hmlen].
      pose proof (wfg_build_dfg ctx cost_limit act _
                    (nth_In _ {| nid := 0; op := DFG_Empty; sz := 0 |} Hmlen)) as Hfg.
      unfold node_args_sz in Hfg. unfold AttackerClock.node_op in Hopm. rewrite Hopm in Hfg.
      destruct Hfg as [Hcw _].
      pose proof (proj2 (wsz_node_sz ctx cost_limit act _ _ Hcw)) as Hw1.
      pose proof (bit_of_nonzero
                    (fun w => nval ctx cost_limit act a_idx (ssk k) (sik k) w (fst l))
                    (node_sz G (fst l)) (V (fst l)) Hw1 Hset) as Hbit2.
      cbn beta in Hbit2. rewrite Hbit2 in Hbit.
      destruct (nonzero (V (fst l))), (snd l); first [ reflexivity | discriminate Hbit ].
  Qed.

  (* THE RECIPE HAS EVERY SELECTOR A SELECTING PHI READS. *)
  Theorem recovered_selectors k :
    (forall i, 1 <= i <= k -> ~ done_set ctx cost_limit (ssk i)) ->
    selectors_extractable ctx cost_limit act a_idx rvals
      (ssk k) (sik k).
  Proof.
    intros Hnd n c t e pi Hop Hcrit Hpi Hpok Hrv.
    apply reached_rounds.
    exact (selector_reached k Hnd (length pi) pi c (le_n _) Hpok
             (ex_intro _ n (ex_intro _ t (ex_intro _ e (conj Hop Hcrit)))) Hpi Hrv).
  Qed.

  (* THE CLOCK IS PUBLIC: the design's latency is the one the attacker
     computes from what it sees. *)
  Theorem L_is_public :
    ProofDefinitions.L ctx cost_limit act input resp ss0 = L_pub ctx cost_limit act view.
  Proof.
    rewrite (L_pub_at_slot ctx cost_limit act a_idx view Halign).
    exact (L_pub_correct ctx cost_limit act a_idx rvals
             input resp ss0 Halign (proj2 (proj2 Hstart)) recovered_selectors
             recovered_vals_sound).
  Qed.
End Settled.

(* Every action has its row in the buffer table: the scheduler builds one per
   action, in the action type's own order. *)
Lemma act_slot_exists (ctx: TFSchedContext) (cost_limit: nat)
    (act: tfs_action (tfs_schedule ctx cost_limit)) :
  exists a_idx, act_idx_aligned ctx cost_limit act a_idx.
Proof.
  unfold act_idx_aligned.
  assert (Hlt : @finite_index _ (tfs_spec_action_fin ctx) act
                < length (buffer_needs ctx cost_limit)).
  { unfold buffer_needs. cbv zeta.
    rewrite map_length, combine_length, !map_length, Nat.min_id.
    apply nth_error_Some. rewrite finite_surjective. discriminate. }
  destruct (Vect.index_of_nat_bounded Hlt) as [a_idx Ha].
  exists a_idx. exact (Vect.index_to_nat_of_nat _ _ Ha).
Qed.
