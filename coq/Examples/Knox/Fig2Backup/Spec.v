Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Coq.NArith.NArith.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Backend.Lowering.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Macros.
Require Trustformer.Theorems.ConfidentialityDefinitions.
Require Trustformer.Theorems.IPR.

Require Import Coq.Lists.List.
Import ListNotations.

(* Knox (Athalye et al., OSDI'22), Fig. 2: a PIN-protected backup that allows at
   most 10 wrong guesses. *)

Section FunctionalSpecification.

    Definition PIN_SZ := 32.
    Definition SECRET_SZ := 128.
    Definition CNT_SZ := 8.
    Definition STATUS_SZ := 8.
    Definition GUESS_LIMIT := 10.

    Definition ST_OK := 1.
    Definition ST_BAD_PIN := 2.
    Definition ST_NO_GUESSES := 3.

    Inductive fs_action := act_store | act_retrieve.

    Inductive fs_states := st_pin | st_secret | st_bad_guesses.
    Inductive fs_inputs := in_pin | in_secret.
    Inductive fs_outputs := out_status | out_data.

    Definition fs_states_size (x: fs_states) : nat :=
      match x with
      | st_pin => PIN_SZ
      | st_secret => SECRET_SZ
      | st_bad_guesses => CNT_SZ
      end.

    Definition fs_inputs_size (x: fs_inputs) : nat :=
      match x with
      | in_pin => PIN_SZ
      | in_secret => SECRET_SZ
      end.

    Definition fs_outputs_size (x: fs_outputs) : nat :=
      match x with
      | out_status => STATUS_SZ
      | out_data => SECRET_SZ
      end.

    Definition fs_states_init (x: fs_states) : tf_states_type fs_states_size x :=
      Bits.zero.

    Local Notation OPS := (@tf_ops fs_states fs_inputs fs_outputs Empty_set).

    Definition fs_ops (a: fs_action) : OPS :=
      match a with
      | act_store =>
          {[ `mk_clear_outputs`;
             let $st_secret := $in_secret;
             let $st_pin := $in_pin;
             let $st_bad_guesses := #0 ]}
      | act_retrieve =>
          {[ `mk_clear_outputs`;
             if ($st_bad_guesses >=[CNT_SZ] #GUESS_LIMIT) then
               let $out_status := #ST_NO_GUESSES
             else
               (if ($in_pin ==[PIN_SZ] $st_pin) then
                  let $st_bad_guesses := #0;
                  let $out_status := #ST_OK;
                  let $out_data := $st_secret
                else
                  let $st_bad_guesses := $st_bad_guesses + #1;
                  let $out_status := #ST_BAD_PIN) ]}
      end.

End FunctionalSpecification.

Section Checks.

    Definition sysst := (ContextEnv.(env_t) (tf_states_type fs_states_size)
                         * ContextEnv.(env_t) (tf_outputs_type fs_outputs_size))%type.

    Definition initial : sysst :=
      (ContextEnv.(create) fs_states_init, ContextEnv.(create) (fun _ => Bits.zero)).

    Definition inp (pin secret: N) (x: fs_inputs) : bits_t (fs_inputs_size x) :=
      match x with
      | in_pin => Bits.of_N PIN_SZ pin
      | in_secret => Bits.of_N SECRET_SZ secret
      end.

    Definition run (a: fs_action) (pin secret: N) (s: sysst) : sysst :=
      tf_ops_run fs_states_size fs_inputs_size fs_outputs_size no_ips (fs_ops a) s (inp pin secret).

    Definition store (new_secret new_pin: N) : sysst -> sysst := run act_store new_pin new_secret.
    Definition retrieve (guess: N) : sysst -> sysst := run act_retrieve guess 0xFEED.

    Fixpoint iter (n: nat) (f: sysst -> sysst) (s: sysst) : sysst :=
      match n with 0 => s | S k => iter k f (f s) end.

    Definition status (s: sysst) : N := Bits.to_N (ContextEnv.(getenv) (snd s) out_status).
    Definition data (s: sysst) : N := Bits.to_N (ContextEnv.(getenv) (snd s) out_data).
    Definition bad (s: sysst) : N := Bits.to_N (ContextEnv.(getenv) (fst s) st_bad_guesses).
    Definition pin_of (s: sysst) : N := Bits.to_N (ContextEnv.(getenv) (fst s) st_pin).
    Definition secret_of (s: sysst) : N := Bits.to_N (ContextEnv.(getenv) (fst s) st_secret).

    Definition obs (s: sysst) : N * N * N := (status s, data s, bad s).

    Example fresh_retrieve_zero : obs (retrieve 0 initial) = (1, 0, 0)%N.
    Proof. vm_compute. reflexivity. Qed.
    Example fresh_retrieve_wrong : obs (retrieve 5 initial) = (2, 0, 1)%N.
    Proof. vm_compute. reflexivity. Qed.

    Definition s1 := store 1337 1234 initial.
    Example store_returns_nothing : obs s1 = (0, 0, 0)%N.
    Proof. vm_compute. reflexivity. Qed.
    Example store_writes : (pin_of s1, secret_of s1) = (1234, 1337)%N.
    Proof. vm_compute. reflexivity. Qed.

    Example rkt_correct : obs (retrieve 1234 s1) = (1, 1337, 0)%N.
    Proof. vm_compute. reflexivity. Qed.
    Example rkt_bad : obs (retrieve 1111 s1) = (2, 0, 1)%N.
    Proof. vm_compute. reflexivity. Qed.
    Example rkt_one_bad_ok : obs (retrieve 1234 (retrieve 1111 s1)) = (1, 1337, 0)%N.
    Proof. vm_compute. reflexivity. Qed.
    Example rkt_limit : obs (retrieve 1234 (iter 10 (retrieve 1111) s1)) = (3, 0, 10)%N.
    Proof. vm_compute. reflexivity. Qed.

    Definition s9 := iter 9 (retrieve 1111) s1.
    Example nine_wrong : obs s9 = (2, 0, 9)%N.
    Proof. vm_compute. reflexivity. Qed.
    Example tenth_correct : obs (retrieve 1234 s9) = (1, 1337, 0)%N.
    Proof. vm_compute. reflexivity. Qed.
    Example tenth_wrong : obs (retrieve 1111 s9) = (2, 0, 10)%N.
    Proof. vm_compute. reflexivity. Qed.

    Definition s10 := iter 10 (retrieve 1111) s1.
    Example locked_correct : obs (retrieve 1234 s10) = (3, 0, 10)%N.
    Proof. vm_compute. reflexivity. Qed.
    Example locked_state_unchanged :
      List.map (fun g => fst (retrieve g s10)) [1234; 1111; 0]%N = [fst s10; fst s10; fst s10].
    Proof. vm_compute. reflexivity. Qed.
    Example locked_saturates : obs (iter 300 (retrieve 1111) s10) = (3, 0, 10)%N.
    Proof. vm_compute. reflexivity. Qed.

    Definition s_reset9 := retrieve 1234 s9.
    Example relock_tenth_wrong : obs (iter 10 (retrieve 1111) s_reset9) = (2, 0, 10)%N.
    Proof. vm_compute. reflexivity. Qed.
    Example relock_locked : obs (retrieve 1234 (iter 10 (retrieve 1111) s_reset9)) = (3, 0, 10)%N.
    Proof. vm_compute. reflexivity. Qed.

    Definition s_re := store 7 55 s10.
    Example restore_returns_nothing : obs s_re = (0, 0, 0)%N.
    Proof. vm_compute. reflexivity. Qed.
    Example restore_unlocks : obs (retrieve 55 s_re) = (1, 7, 0)%N.
    Proof. vm_compute. reflexivity. Qed.
    Example restore_old_pin_dead : obs (retrieve 1234 s_re) = (2, 0, 1)%N.
    Proof. vm_compute. reflexivity. Qed.

    Example store_zero_is_reset :
      List.map (store 0 0) [s1; s9; s10; retrieve 1234 s1] = [initial; initial; initial; initial].
    Proof. vm_compute. reflexivity. Qed.

    Definition wipe (s: sysst) : sysst := (fst s, snd initial).
    Definition prev_states : list sysst :=
      [retrieve 1234 s1; retrieve 1111 s1; retrieve 1234 s10; s1; initial].
    Definition next_calls : list (sysst -> sysst) :=
      [store 7 55; retrieve 1234; retrieve 1111; retrieve 0].
    Example no_stale_outputs :
      List.map (fun s => List.map (fun f => (status (f s), data (f s))) next_calls) prev_states
      = List.map (fun s => List.map (fun f => (status (f (wipe s)), data (f (wipe s)))) next_calls)
                 prev_states.
    Proof. vm_compute. reflexivity. Qed.
    Example no_stale_fail : obs (retrieve 1111 (retrieve 1234 s1)) = (2, 0, 1)%N.
    Proof. vm_compute. reflexivity. Qed.
    Example no_stale_store : obs (store 7 55 (retrieve 1234 s1)) = (0, 0, 0)%N.
    Proof. vm_compute. reflexivity. Qed.

    Definition released : list (sysst * N * N) :=
      [(retrieve 1234 s9, 1337, 1234); (retrieve 55 s_re, 7, 55); (retrieve 0 initial, 0, 0);
       (retrieve 9 (store 0xC0FFEE00_11223344_55667788_99AABBCC 9 initial),
        0xC0FFEE00_11223344_55667788_99AABBCC, 9)]%N.
    Example host_wipe_state :
      List.map (fun '(s, sec, p) => fst (store sec p s)) released
      = List.map (fun '(s, _, _) => fst s) released.
    Proof. vm_compute. reflexivity. Qed.
    Example host_wipe_ports :
      List.map (fun '(s, sec, p) => (status (store sec p s), data (store sec p s))) released
      = [(0, 0); (0, 0); (0, 0); (0, 0)]%N.
    Proof. vm_compute. reflexivity. Qed.

    Definition s_hi := store 42 2147484882 initial.
    Example hi_pin_low_bits_only : obs (retrieve 1234 s_hi) = (2, 0, 1)%N.
    Proof. vm_compute. reflexivity. Qed.
    Example hi_pin_exact : obs (retrieve 2147484882 s_hi) = (1, 42, 0)%N.
    Proof. vm_compute. reflexivity. Qed.
    Definition s_ones := store 1 0xFFFFFFFF initial.
    Example ones_pin :
      List.map (fun g => status (retrieve g s_ones)) [0xFFFFFFFF; 0x7FFFFFFF; 0xFFFFFFFE; 0]%N
      = [1; 2; 2; 2]%N.
    Proof. vm_compute. reflexivity. Qed.

    Definition SECRET_MAX : N := 0xFFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF.
    Definition SECRET_MIX : N := 0xC0FFEE00_11223344_55667788_99AABBCC.
    Example secret_max : data (retrieve 9 (store SECRET_MAX 9 initial)) = SECRET_MAX.
    Proof. vm_compute. reflexivity. Qed.
    Example secret_mix : data (retrieve 9 (store SECRET_MIX 9 initial)) = SECRET_MIX.
    Proof. vm_compute. reflexivity. Qed.

    Example retrieve_ignores_secret_input :
      List.map (fun '(s, g) => run act_retrieve g 0 s) [(s1, 1234); (s1, 1111); (s10, 1234)]%N
      = List.map (fun '(s, g) => run act_retrieve g SECRET_MAX s) [(s1, 1234); (s1, 1111); (s10, 1234)]%N.
    Proof. vm_compute. reflexivity. Qed.

End Checks.

Section Instance.

    Definition tfs_ctx : TFSchedContext := {|
        tfs_spec_states := fs_states;
        tfs_spec_states_fin := _;
        tfs_spec_states_size := fs_states_size;
        tfs_spec_states_init := fs_states_init;

        tfs_spec_inputs := fs_inputs;
        tfs_spec_inputs_fin := _;
        tfs_spec_inputs_size := fs_inputs_size;
        tfs_spec_inputs_class := fun _ => Public;
        tfs_spec_outputs := fs_outputs;
        tfs_spec_outputs_fin := _;
        tfs_spec_outputs_size := fs_outputs_size;
        tfs_spec_outputs_class := fun _ => Public;
        tfs_spec_action := fs_action;
        tfs_spec_action_fin := _;
        tfs_spec_action_ops := fs_ops;
        tfs_spec_ips := Empty_set;
        tfs_spec_ip := no_ips;
        tfs_spec_decls := []
    |}.

    Definition CL := 10.

    Definition tf_ctx : TFSynthContext := mk_synth_ctx (tfs_schedule tfs_ctx CL).

    Example cmd_width : tf_action_reg_size tf_ctx = 2.
    Proof. reflexivity. Qed.
    Example cmd_codes :
      List.map (fun a => Bits.to_nat (tf_action_encoding tf_ctx a)) [act_store; act_retrieve] = [0; 1].
    Proof. vm_compute. reflexivity. Qed.

    Example sf_store : ConfidentialityDefinitions.sf_action tfs_ctx act_store = true.
    Proof. vm_compute. reflexivity. Qed.
    Example sf_retrieve : ConfidentialityDefinitions.sf_action tfs_ctx act_retrieve = false.
    Proof. vm_compute. reflexivity. Qed.

    Definition ipr_here := IPR.ipr tfs_ctx CL _ _
      (tf_action_encoding_inj tf_ctx) (tf_action_names tf_ctx).

    Definition package := Lowering.package tf_ctx "Knox_Fig2Backup".

End Instance.

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Knox_Fig2Backup.ml" prog.
