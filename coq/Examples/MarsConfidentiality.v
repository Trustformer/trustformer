Require Import Koika.Frontend.
Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Properties.Confidentiality.
Require Import Trustformer.Examples.Mars.

Require Import Coq.Lists.List.
Import ListNotations.

(*
    Stage 5: discharge the value-level confidentiality criterion for the MARS
    module, and show in the same file that the criterion is not vacuous.
 *)

Section MarsDischarge.

  (* The criterion is decidable, so the module's obligation is a computation.
     Every action: every assignment to a Public output has a secret-free
     right-hand side, and every enclosing branch condition is secret-free. *)
  Theorem mars_secret_free : forall a, sf_action tfs_ctx a = true.
  Proof. intro a; destruct a; vm_compute; reflexivity. Qed.

  (* Hence, for MARS: with the crypto IP's responses held fixed, PS, DP and AK
     contribute nothing to any Public port, for any command sequence.  The
     module's Public outputs are a function of the public data and what the IP
     handed back -- the secret registers are not among the arguments.

     This is NOT "two MARS devices with different seeds look alike".  They do
     not: a different DP yields a different AK and therefore a different
     MARS_Quote signature, which is the entire purpose of the command.  Those
     runs violate the shared-input hypothesis.  What is ruled out is the module
     routing a secret to an attacker-visible port through its own wiring, so
     that every DP-dependence of [dout] factors through the IP (MVP.md
     section 9, A1). *)
  Theorem mars_no_direct_secret_flow
      (acts: list (tfs_spec_action tfs_ctx))
      (input: forall x, bits_t (fs_inputs_size x))
      (secrets secrets': ContextEnv.(env_t) (tf_states_type fs_states_size))
      (pub: ContextEnv.(env_t) (tf_outputs_type fs_outputs_size)) :
    forall o, fs_outputs_class o = Public ->
      (snd (run_seq tfs_ctx acts (secrets, pub) input)).[o]
      = (snd (run_seq tfs_ctx acts (secrets', pub) input)).[o].
  Proof.
    exact (no_direct_secret_flow tfs_ctx acts input secrets secrets' pub
             mars_secret_free).
  Qed.

End MarsDischarge.

(* ---------------------------------------------------------------------- *)
(* The criterion is not vacuous: REVIEW.md section 2.4's counterexample,    *)
(* mechanised.  Output variables are readable, so a secret parked in a      *)
(* Secret output in one action and read out in the NEXT passes any          *)
(* per-action check.  The criterion rejects it, and the leak is real.       *)
(* ---------------------------------------------------------------------- *)

Section NotVacuous.

  Definition cw := 32.

  Inductive c_action  := act_stash | act_leak.
  Inductive c_states  := st_secret.
  Inductive c_inputs  := in_x.
  Inductive c_outputs := out_key | out_pub.

  Definition c_states_size  (_: c_states)  : nat := cw.
  Definition c_inputs_size  (_: c_inputs)  : nat := cw.
  Definition c_outputs_size (_: c_outputs) : nat := cw.

  Definition c_states_init (x: c_states) : tf_states_type c_states_size x :=
    match x with st_secret => Bits.zero end.

  Definition c_ops (a: c_action) : @tf_ops c_states c_inputs c_outputs Empty_set :=
    match a with
    (* legitimate: a secret may be handed to the crypto port *)
    | act_stash => {[ let $out_key := $st_secret ]}
    (* the leak: reading it back out into a Public result *)
    | act_leak  => {[ let $out_pub := $out_key ]}
    end.

  Definition c_ctx : TFSchedContext := {|
      tfs_spec_states := c_states;   tfs_spec_states_fin := _;
      tfs_spec_states_size := c_states_size;
      tfs_spec_states_init := c_states_init;

      tfs_spec_inputs := c_inputs;   tfs_spec_inputs_fin := _;
      tfs_spec_inputs_size := c_inputs_size;
      tfs_spec_inputs_class := fun _ => Public;

      tfs_spec_outputs := c_outputs; tfs_spec_outputs_fin := _;
      tfs_spec_outputs_size := c_outputs_size;
      tfs_spec_outputs_class := fun x => match x with
                                         | out_key => Secret
                                         | out_pub => Public
                                         end;

      tfs_spec_action := c_action;   tfs_spec_action_fin := _;
      tfs_spec_action_ops := c_ops;
      (* no attached IP: no call names a response port here *)
      (* no IP drives any port here, so nothing can conflict with one *)
      tfs_spec_ips := Empty_set;
      tfs_spec_ip := no_ips;
      tfs_spec_decls := []
  |}.

  (* Stashing into a Secret output is fine on its own... *)
  Example stash_accepted : sf_action c_ctx act_stash = true.
  Proof. vm_compute. reflexivity. Qed.

  (* ...and reading it back into a Public one is exactly what the criterion
     forbids.  Without the "no read of a Secret output" clause both actions
     would pass and the composition would still leak. *)
  Example leak_rejected : sf_action c_ctx act_leak = false.
  Proof. vm_compute. reflexivity. Qed.

  (* And the leak is real, not merely un-provable: run the two actions in
     sequence from two states differing only in the secret, and the PUBLIC
     output takes two different values. *)
  Definition c_pub0 : ContextEnv.(env_t) (tf_outputs_type c_outputs_size) :=
    ContextEnv.(create) (fun _ => Bits.zero).
  Definition c_in (x: c_inputs) : bits_t (c_inputs_size x) := Bits.zero.

  Definition c_run (v: nat) :=
    run_seq c_ctx [act_stash; act_leak]
      (ContextEnv.(putenv) (ContextEnv.(create) c_states_init)
         st_secret (Bits.of_nat cw v), c_pub0) c_in.

  Example leak_is_real :
    (snd (c_run 1)).[out_pub] <> (snd (c_run 2)).[out_pub].
  Proof. vm_compute. discriminate. Qed.

End NotVacuous.

Print Assumptions mars_secret_free.
Print Assumptions mars_no_direct_secret_flow.
