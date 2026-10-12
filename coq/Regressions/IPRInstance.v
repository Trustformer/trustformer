(* Regression for the IPR results on the classic timing side channel, a password
   check branching on a secret: pins that the branch is tainted, [L] computable,
   and the theorems instantiate -- the [Definition]s below catch signature drift. *)

Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import Trustformer.Theorems.IPRDefinitions.
Require Import Trustformer.Theorems.Internal.ProofDefinitions.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Backend.Lowering.
Require Import Trustformer.Theorems.Internal.SchedulerRoundTrip.
Require Import Trustformer.Theorems.IPR.
Require Import Trustformer.Theorems.Internal.IPRProof.
Require Trustformer.Declassification.Extract.

Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

Section FunctionalSpecification.

  Definition sz := 32.

  Inductive fs_action := fs_check.

  Definition fs_action_encoding (a: fs_action) : bits_t 16 :=
    match a with fs_check => Bits.of_nat 16 1 end.

  Lemma fs_action_encoding_inj :
    forall a1 a2, fs_action_encoding a1 = fs_action_encoding a2 -> a1 = a2.
  Proof. intros a1 a2 _. destruct a1; destruct a2; reflexivity. Qed.

  Inductive fs_states := fs_secret | fs_count.
  Inductive fs_inputs := fs_guess.
  Inductive fs_outputs := fs_ok.

  Definition fs_states_size  (_: fs_states)  : nat := sz.
  Definition fs_inputs_size  (_: fs_inputs)  : nat := sz.
  Definition fs_outputs_size (_: fs_outputs) : nat := sz.

  Definition fs_states_t := tf_states_type fs_states_size.

  Definition fs_states_init (x: fs_states) : fs_states_t x :=
    match x with fs_secret => Bits.zero | fs_count => Bits.zero end.

  (* The branch condition reads [fs_secret], so a naive compilation would take a
     different number of cycles for a correct and an incorrect guess. *)
  Definition fs_transitions (act: fs_action)
      : @tf_ops fs_states fs_inputs fs_outputs Empty_set :=
    match act with
    | fs_check =>
        {[
          (if $fs_secret ==[sz] $fs_guess then
             let $fs_count := $fs_count + #1;
             let $fs_ok := #1
           else
             let $fs_ok := #0)
        ]}
    end.

End FunctionalSpecification.

Section Context.

  Definition tfs_ctx : TFSchedContext := {|
    tfs_spec_states      := fs_states;
    tfs_spec_states_fin  := _;
    tfs_spec_states_size := fs_states_size;
    tfs_spec_states_init := fs_states_init;

    tfs_spec_inputs      := fs_inputs;
    tfs_spec_inputs_fin  := _;
    tfs_spec_inputs_size := fs_inputs_size;
    tfs_spec_inputs_class := fun _ => Public;
    tfs_spec_outputs      := fs_outputs;
    tfs_spec_outputs_fin  := _;
    tfs_spec_outputs_size := fs_outputs_size;
    tfs_spec_outputs_class := fun _ => Public;
    tfs_spec_action     := fs_action;
    tfs_spec_action_fin := _;
    tfs_spec_action_ops := fs_transitions;
    (* no attached IP: no call names a response port here *)
    tfs_spec_ips := Empty_set;
    tfs_spec_ip := no_ips;
    tfs_spec_decls := []
  |}.

  Definition cost := 5.

  Definition check_dfg := build_dfg tfs_ctx fs_check.

End Context.

Section TaintPins.

  (* The secret reaches the branch, so the roots are not all untainted: a
     latency-noninterference claim here is not free. *)
  Definition tainted_nodes := get_tainted tfs_ctx check_dfg.

  Goal tainted_nodes <> [].
  Proof. vm_compute. discriminate. Qed.

End TaintPins.

Section TheoremInstantiation.

  Local Notation sched := (tfs_schedule tfs_ctx cost).

  (* [L] is a total function into [nat] (so the paper can write [L act input pre
     post]) but not practically reducible: [vm_compute] here exceeds 300s, so
     reason symbolically via [L_first_done]. *)
  Definition check_latency := L tfs_ctx cost.

  (* Signature regression.  Each of these fails to type check if the
     corresponding theorem's hypotheses change. *)

  Definition reg_L_first_done := L_first_done tfs_ctx cost.

  Definition reg_emulator := emulator_correct_L tfs_ctx cost.

  (* This context attaches no IP, so the response stream is a function out of
     [Empty_set] and its datasheet obligation is vacuous. *)
  Definition no_resp : nat -> forall p : tfs_ips sched,
      bits_t (ip_resp_sz (tfs_ip sched p)) :=
    fun _ p => match p with end.

  (* [L_is_public], fully instantiated: for this context, two runs of [fs_check]
     that agree on the outputs before and after finish on the same cycle, no
     matter what [fs_secret] holds. *)
  Theorem check_latency_is_public :
    forall a_idx input sp0 sp0' ss0 ss0',
      act_idx_aligned tfs_ctx cost fs_check a_idx ->
      start_rel tfs_ctx cost sp0  ss0  ->
      start_rel tfs_ctx cost sp0' ss0' ->
      (forall ov, (snd sp0).[ov] = (snd sp0').[ov]) ->
      (forall ov, (snd (tf_ops_run (tfs_spec_states_size tfs_ctx)
                          (tfs_spec_inputs_size tfs_ctx)
                          (tfs_spec_outputs_size tfs_ctx)
                          (tfs_spec_ip tfs_ctx)
                          (tfs_spec_action_ops tfs_ctx fs_check) sp0 input)).[ov]
                = (snd (tf_ops_run (tfs_spec_states_size tfs_ctx)
                          (tfs_spec_inputs_size tfs_ctx)
                          (tfs_spec_outputs_size tfs_ctx)
                          (tfs_spec_ip tfs_ctx)
                          (tfs_spec_action_ops tfs_ctx fs_check) sp0' input)).[ov]) ->
      check_latency fs_check input no_resp ss0
      = check_latency fs_check input no_resp ss0'.
  Proof.
    intros a_idx input sp0 sp0' ss0 ss0' Halign Hst Hst' Hpre Hpost.
    (* this context attaches no IP, so the datasheet obligation is vacuous *)
    assert (Hipc : forall ss, IRDefinitions.ip_contract tfs_ctx cost fs_check input no_resp ss)
      by (intros ss p; destruct p).
    (* both runs show the attacker the same view, so they finish together *)
    assert (Hpre_eq : snd sp0 = snd sp0') by (apply equiv_eq; exact Hpre).
    assert (Hpost_eq : snd (tf_ops_run (tfs_spec_states_size tfs_ctx)
                              (tfs_spec_inputs_size tfs_ctx)
                              (tfs_spec_outputs_size tfs_ctx)
                              (tfs_spec_ip tfs_ctx)
                              (tfs_spec_action_ops tfs_ctx fs_check) sp0 input)
                       = snd (tf_ops_run (tfs_spec_states_size tfs_ctx)
                              (tfs_spec_inputs_size tfs_ctx)
                              (tfs_spec_outputs_size tfs_ctx)
                              (tfs_spec_ip tfs_ctx)
                              (tfs_spec_action_ops tfs_ctx fs_check) sp0' input))
      by (apply equiv_eq; exact Hpost).
    unfold check_latency.
    rewrite (Extract.L_is_public tfs_ctx cost fs_check a_idx sp0 ss0 input no_resp
               Halign Hst (Hipc ss0) _ (fun _ => eq_refl) (fun _ => eq_refl) (fun _ => eq_refl)),
            (Extract.L_is_public tfs_ctx cost fs_check a_idx sp0' ss0' input no_resp
               Halign Hst' (Hipc ss0') _ (fun _ => eq_refl) (fun _ => eq_refl) (fun _ => eq_refl)).
    rewrite Hpre_eq, Hpost_eq. reflexivity.
  Qed.

  Local Instance fs_action_names : Show fs_action := {| show _ := "check"%string |}.

  (* This context attaches no IP, so every IP model meets the datasheet. *)
  Lemma no_ip_datasheet ip :
    IPRDefinitions.datasheet tfs_ctx cost 16 fs_action_encoding fs_action_encoding_inj fs_action_names ip.
  Proof. intro p. destruct p. Qed.

  (* The headline, fully instantiated: IPR, verbatim from upstream, for the password
     check and any source on secure ports. *)
  Definition check_ipr ip src :=
    IPR.ipr tfs_ctx cost 16 fs_action_encoding fs_action_encoding_inj fs_action_names ip src
      (no_ip_datasheet ip).

End TheoremInstantiation.

Section DatasheetInhabited.

  Context (ctx: TFSchedContext) (cost_limit: nat).
  Local Notation sched := (tfs_schedule ctx cost_limit).
  Context (enc_sz: nat) (enc: tfs_action sched -> bits_t enc_sz)
          (enc_inj: forall a b, enc a = enc b -> a = b) (names: Show (tfs_action sched)).
  Local Notation tsched := (tf_sched_ctx (IPRDefinitions.synth ctx cost_limit enc_sz enc enc_inj names)).

  (* The datasheet can be met: an IP that answers each request
     exactly [lat] cycles on meets it, for every design. *)
  Definition ideal_ip : IPRDefinitions.trusted_ip ctx cost_limit enc_sz enc enc_inj names :=
    fun p h => match nth_error (rev h) (pred (ip_lat (tfs_ip tsched p))) with
               | Some q => ip_fn (tfs_ip tsched p) (Bits.slice 0 (ip_req_sz (tfs_ip tsched p)) q)
               | None => Bits.zero
               end.

  Lemma ideal_ip_datasheet :
    IPRDefinitions.datasheet ctx cost_limit enc_sz enc enc_inj names ideal_ip.
  Proof.
    intros p h t q. cbv zeta. intros _ Hlen _. unfold ideal_ip.
    rewrite rev_app_distr. cbn [rev]. rewrite <- app_assoc.
    rewrite nth_error_app2 by (rewrite rev_length; lia).
    rewrite rev_length, Hlen, Nat.sub_diag. reflexivity.
  Qed.

End DatasheetInhabited.

