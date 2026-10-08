Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Backend.Lowering.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Macros.
Require Trustformer.Theorems.IPR.
Require Trustformer.Theorems.Synthesis.
Require Trustformer.Theorems.SchedulerSimulation.

Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Import ListNotations.

(* Knox's PIN-protected backup HSM (sec. 7.1.1, knox-hsm pin-protected-backup):
   four slots, each with its own guess limit. *)

Section FunctionalSpecification.

  Definition PIN_SZ := 32.
  Definition DATA_SZ := 128.
  Definition CNT_SZ := 8.
  Definition SLOT_SZ := 8.
  Definition GUESS_LIMIT := 10.

  Inductive slot := S0 | S1 | S2 | S3.

  Inductive pb_action := act_status | act_delete | act_store | act_retrieve.

  Inductive pb_states :=
  | st_valid (k: slot) | st_bad (k: slot) | st_pin (k: slot) | st_data (k: slot).
  Inductive pb_inputs := in_slot | in_pin | in_data.
  Inductive pb_outputs := out_ok | out_data.

  Definition pb_states_size (x: pb_states) : nat :=
    match x with
    | st_valid _ => 1 | st_bad _ => CNT_SZ | st_pin _ => PIN_SZ | st_data _ => DATA_SZ
    end.
  Definition pb_inputs_size (x: pb_inputs) : nat :=
    match x with in_slot => SLOT_SZ | in_pin => PIN_SZ | in_data => DATA_SZ end.
  Definition pb_outputs_size (x: pb_outputs) : nat :=
    match x with out_ok => 1 | out_data => DATA_SZ end.

  Definition pb_states_init (x: pb_states) : tf_states_type pb_states_size x := Bits.zero.

  Local Notation OPS := (@tf_ops pb_states pb_inputs pb_outputs Empty_set).

  Definition on_slot (body: slot -> OPS) : OPS :=
    {[ `mk_clear_outputs`;
       `mk_switch SLOT_SZ (tf_ivar in_slot) body {[ pass ]}` ]}.

  Definition status_slot (k: slot) : OPS :=
    {[ let $out_ok := $(st_valid k) ]}.

  Definition delete_slot (k: slot) : OPS :=
    {[ let $out_ok := $(st_valid k);
       let $(st_valid k) := #0; let $(st_bad k) := #0;
       let $(st_pin k) := #0; let $(st_data k) := #0 ]}.

  Definition store_slot (k: slot) : OPS :=
    {[ if ($(st_valid k) ==[1] #1) then pass
       else (let $(st_valid k) := #1; let $(st_bad k) := #0;
             let $(st_pin k) := $in_pin; let $(st_data k) := $in_data;
             let $out_ok := #1) ]}.

  Definition retrieve_slot (k: slot) : OPS :=
    {[ if (($(st_valid k) ==[1] #1) & ($(st_bad k) <[CNT_SZ] #GUESS_LIMIT)) then
         (if ($(st_pin k) ==[PIN_SZ] $in_pin) then
            let $out_ok := #1; let $out_data := $(st_data k); let $(st_bad k) := #0
          else
            let $(st_bad k) := $(st_bad k) + #1)
       else pass ]}.

  Definition pb_ops (a: pb_action) : OPS :=
    match a with
    | act_status => on_slot status_slot
    | act_delete => on_slot delete_slot
    | act_store => on_slot store_slot
    | act_retrieve => on_slot retrieve_slot
    end.

End FunctionalSpecification.

Section Checks.

  Local Notation OPS := (@tf_ops pb_states pb_inputs pb_outputs Empty_set).

  Definition native_status : OPS := {[
    (let $out_ok := #0; let $out_data := #0);
    if ($in_slot ==[8] #0) then let $out_ok := $(st_valid S0)
    else if ($in_slot ==[8] #1) then let $out_ok := $(st_valid S1)
    else if ($in_slot ==[8] #2) then let $out_ok := $(st_valid S2)
    else if ($in_slot ==[8] #3) then let $out_ok := $(st_valid S3)
    else pass ]}.

  Definition native_delete : OPS := {[
    (let $out_ok := #0; let $out_data := #0);
    if ($in_slot ==[8] #0) then
      let $out_ok := $(st_valid S0); let $(st_valid S0) := #0; let $(st_bad S0) := #0;
      let $(st_pin S0) := #0; let $(st_data S0) := #0
    else if ($in_slot ==[8] #1) then
      let $out_ok := $(st_valid S1); let $(st_valid S1) := #0; let $(st_bad S1) := #0;
      let $(st_pin S1) := #0; let $(st_data S1) := #0
    else if ($in_slot ==[8] #2) then
      let $out_ok := $(st_valid S2); let $(st_valid S2) := #0; let $(st_bad S2) := #0;
      let $(st_pin S2) := #0; let $(st_data S2) := #0
    else if ($in_slot ==[8] #3) then
      let $out_ok := $(st_valid S3); let $(st_valid S3) := #0; let $(st_bad S3) := #0;
      let $(st_pin S3) := #0; let $(st_data S3) := #0
    else pass ]}.

  Definition native_store : OPS := {[
    (let $out_ok := #0; let $out_data := #0);
    if ($in_slot ==[8] #0) then
      (if ($(st_valid S0) ==[1] #1) then pass
       else (let $(st_valid S0) := #1; let $(st_bad S0) := #0;
             let $(st_pin S0) := $in_pin; let $(st_data S0) := $in_data; let $out_ok := #1))
    else if ($in_slot ==[8] #1) then
      (if ($(st_valid S1) ==[1] #1) then pass
       else (let $(st_valid S1) := #1; let $(st_bad S1) := #0;
             let $(st_pin S1) := $in_pin; let $(st_data S1) := $in_data; let $out_ok := #1))
    else if ($in_slot ==[8] #2) then
      (if ($(st_valid S2) ==[1] #1) then pass
       else (let $(st_valid S2) := #1; let $(st_bad S2) := #0;
             let $(st_pin S2) := $in_pin; let $(st_data S2) := $in_data; let $out_ok := #1))
    else if ($in_slot ==[8] #3) then
      (if ($(st_valid S3) ==[1] #1) then pass
       else (let $(st_valid S3) := #1; let $(st_bad S3) := #0;
             let $(st_pin S3) := $in_pin; let $(st_data S3) := $in_data; let $out_ok := #1))
    else pass ]}.

  Definition native_retrieve : OPS := {[
    (let $out_ok := #0; let $out_data := #0);
    if ($in_slot ==[8] #0) then
      (if (($(st_valid S0) ==[1] #1) & ($(st_bad S0) <[8] #10)) then
         (if ($(st_pin S0) ==[32] $in_pin) then
            let $out_ok := #1; let $out_data := $(st_data S0); let $(st_bad S0) := #0
          else let $(st_bad S0) := $(st_bad S0) + #1)
       else pass)
    else if ($in_slot ==[8] #1) then
      (if (($(st_valid S1) ==[1] #1) & ($(st_bad S1) <[8] #10)) then
         (if ($(st_pin S1) ==[32] $in_pin) then
            let $out_ok := #1; let $out_data := $(st_data S1); let $(st_bad S1) := #0
          else let $(st_bad S1) := $(st_bad S1) + #1)
       else pass)
    else if ($in_slot ==[8] #2) then
      (if (($(st_valid S2) ==[1] #1) & ($(st_bad S2) <[8] #10)) then
         (if ($(st_pin S2) ==[32] $in_pin) then
            let $out_ok := #1; let $out_data := $(st_data S2); let $(st_bad S2) := #0
          else let $(st_bad S2) := $(st_bad S2) + #1)
       else pass)
    else if ($in_slot ==[8] #3) then
      (if (($(st_valid S3) ==[1] #1) & ($(st_bad S3) <[8] #10)) then
         (if ($(st_pin S3) ==[32] $in_pin) then
            let $out_ok := #1; let $out_data := $(st_data S3); let $(st_bad S3) := #0
          else let $(st_bad S3) := $(st_bad S3) + #1)
       else pass)
    else pass ]}.

  Example macro_is_handwritten :
    pb_ops act_status = native_status /\ pb_ops act_delete = native_delete
    /\ pb_ops act_store = native_store /\ pb_ops act_retrieve = native_retrieve.
  Proof. vm_compute. repeat split. Qed.

  Definition sysst := (ContextEnv.(env_t) (tf_states_type pb_states_size)
                       * ContextEnv.(env_t) (tf_outputs_type pb_outputs_size))%type.

  Definition initial : sysst :=
    (ContextEnv.(create) pb_states_init, ContextEnv.(create) (fun _ => Bits.zero)).

  Definition inp (k pin: N) (data: bits_t DATA_SZ) (x: pb_inputs)
    : bits_t (pb_inputs_size x) :=
    match x with
    | in_slot => Bits.of_N SLOT_SZ k
    | in_pin => Bits.of_N PIN_SZ pin
    | in_data => data
    end.

  Definition step (a: pb_action) (s: sysst) i : sysst :=
    tf_ops_run pb_states_size pb_inputs_size pb_outputs_size no_ips (pb_ops a) s i.

  Definition JUNK : bits_t DATA_SZ := Bits.of_N DATA_SZ 77.
  Definition status (k: N) (s: sysst) := step act_status s (inp k 99 JUNK).
  Definition delete (k: N) (s: sysst) := step act_delete s (inp k 99 JUNK).
  Definition store (k pin data: N) (s: sysst) := step act_store s (inp k pin (Bits.of_N DATA_SZ data)).
  Definition retrieve (k pin: N) (s: sysst) := step act_retrieve s (inp k pin JUNK).

  Fixpoint iter (n: nat) (f: sysst -> sysst) (s: sysst) :=
    match n with 0 => s | S n' => iter n' f (f s) end.

  Definition ret (s: sysst) := (Bits.to_N (ContextEnv.(getenv) (snd s) out_ok),
                                Bits.to_N (ContextEnv.(getenv) (snd s) out_data)).
  Definition bad (k: slot) (s: sysst) := Bits.to_N (ContextEnv.(getenv) (fst s) (st_bad k)).
  Definition entry (k: slot) (s: sysst) :=
    (Bits.to_N (ContextEnv.(getenv) (fst s) (st_valid k)), bad k s,
     Bits.to_N (ContextEnv.(getenv) (fst s) (st_pin k)),
     Bits.to_N (ContextEnv.(getenv) (fst s) (st_data k))).
  Definition unchanged (s s': sysst) := fst s' = fst s.

  Example k_status_s0 : ret (status 0 initial) = (0, 0)%N.
  Proof. vm_compute. reflexivity. Qed.
  Definition s1 := store 3 1234 1337 initial.
  Example k_store_ok : ret s1 = (1, 0)%N.
  Proof. vm_compute. reflexivity. Qed.
  Example k_status : ret (status 3 s1) = (1, 0)%N.
  Proof. vm_compute. reflexivity. Qed.
  Example k_correct : ret (retrieve 3 1234 s1) = (1, 1337)%N.
  Proof. vm_compute. reflexivity. Qed.
  Example k_bad : ret (retrieve 3 1111 s1) = (0, 0)%N.
  Proof. vm_compute. reflexivity. Qed.
  Example k_one_bad_ok : ret (retrieve 3 1234 (retrieve 3 1111 s1)) = (1, 1337)%N.
  Proof. vm_compute. reflexivity. Qed.
  Example k_deletion : ret (retrieve 3 1234 (delete 3 s1)) = (0, 0)%N.
  Proof. vm_compute. reflexivity. Qed.
  Definition guess10 := iter GUESS_LIMIT (retrieve 3 1111) s1.
  Example k_limit : ret (retrieve 3 1234 guess10) = (0, 0)%N.
  Proof. vm_compute. reflexivity. Qed.

  Example store_entry : entry S3 s1 = (1, 0, 1234, 1337)%N /\ entry S2 s1 = (0, 0, 0, 0)%N.
  Proof. vm_compute. split; reflexivity. Qed.

  Example del_was_valid : ret (delete 3 s1) = (1, 0)%N.
  Proof. vm_compute. reflexivity. Qed.
  Example del_empty : ret (delete 2 s1) = (0, 0)%N /\ unchanged s1 (delete 2 s1).
  Proof. vm_compute. split; reflexivity. Qed.
  Example del_resets_e0 : entry S3 (delete 3 (iter 3 (retrieve 3 1111) s1)) = (0, 0, 0, 0)%N.
  Proof. vm_compute. reflexivity. Qed.

  Example store_occupied : ret (store 3 55 66 s1) = (0, 0)%N /\ unchanged s1 (store 3 55 66 s1).
  Proof. vm_compute. split; reflexivity. Qed.

  Example cnt_three : bad S3 (iter 3 (retrieve 3 1111) s1) = 3%N.
  Proof. vm_compute. reflexivity. Qed.
  Example cnt_reset : bad S3 (retrieve 3 1234 (iter 3 (retrieve 3 1111) s1)) = 0%N.
  Proof. vm_compute. reflexivity. Qed.
  Example nine_then_ok : ret (retrieve 3 1234 (iter 9 (retrieve 3 1111) s1)) = (1, 1337)%N.
  Proof. vm_compute. reflexivity. Qed.
  Example ten_exact : bad S3 guess10 = 10%N.
  Proof. vm_compute. reflexivity. Qed.
  Example locked_sat : bad S3 (iter 20 (retrieve 3 1111) s1) = 10%N.
  Proof. vm_compute. reflexivity. Qed.
  Example locked_unchanged : unchanged guess10 (retrieve 3 1234 guess10)
                             /\ unchanged guess10 (retrieve 3 1111 guess10).
  Proof. vm_compute. split; reflexivity. Qed.
  Example locked_status : ret (status 3 guess10) = (1, 0)%N.
  Proof. vm_compute. reflexivity. Qed.
  Example relock_by_delete : ret (retrieve 3 4321 (store 3 4321 9 (delete 3 guess10))) = (1, 9)%N.
  Proof. vm_compute. reflexivity. Qed.

  Example empty_pin0 : ret (retrieve 1 0 s1) = (0, 0)%N /\ unchanged s1 (retrieve 1 0 s1).
  Proof. vm_compute. split; reflexivity. Qed.

  Example independent : entry S0 (iter 4 (retrieve 3 1111) (store 0 5 6 s1)) = (1, 0, 5, 6)%N.
  Proof. vm_compute. reflexivity. Qed.
  Example each_slot :
    List.map (fun k => ret (retrieve k (100 + k) (store k (100 + k) (k + 7) initial))) [0; 1; 2; 3]%N
    = [(1, 7); (1, 8); (1, 9); (1, 10)]%N.
  Proof. vm_compute. reflexivity. Qed.

  Example oob_status : ret (status 4 s1) = (0, 0)%N.
  Proof. vm_compute. reflexivity. Qed.
  Example oob_delete : ret (delete 255 s1) = (0, 0)%N /\ unchanged s1 (delete 255 s1).
  Proof. vm_compute. split; reflexivity. Qed.
  Example oob_store : ret (store 4 1 2 s1) = (0, 0)%N /\ unchanged s1 (store 4 1 2 s1).
  Proof. vm_compute. split; reflexivity. Qed.
  Example oob_store_alias : ret (store 131 1 2 initial) = (0, 0)%N
                            /\ unchanged initial (store 131 1 2 initial).
  Proof. vm_compute. split; reflexivity. Qed.
  Example oob_retrieve : ret (retrieve 200 1234 s1) = (0, 0)%N /\ unchanged s1 (retrieve 200 1234 s1).
  Proof. vm_compute. split; reflexivity. Qed.
  Example oob_retrieve_alias : ret (retrieve 131 1234 s1) = (0, 0)%N
                               /\ unchanged s1 (retrieve 131 1234 s1).
  Proof. vm_compute. split; reflexivity. Qed.

  Definition with_bad (n: N) : sysst :=
    (ContextEnv.(putenv) (fst s1) (st_bad S3) (Bits.of_N CNT_SZ n), snd s1).
  Example sym_locked :
    List.map (fun n => (ret (retrieve 3 1234 (with_bad n)),
                        bad S3 (retrieve 3 1234 (with_bad n)),
                        bad S3 (retrieve 3 1111 (with_bad n)))) [200; 255]%N
    = [((0, 0), 200, 200); ((0, 0), 255, 255)]%N.
  Proof. vm_compute. reflexivity. Qed.

  Example pin_bit31 : ret (retrieve 3 2147484882 s1) = (0, 0)%N.
  Proof. vm_compute. reflexivity. Qed.
  Definition s_max := step act_store initial (inp 0 4294967295 (Bits.ones DATA_SZ)).
  Example wide_data :
    ContextEnv.(getenv) (snd (retrieve 0 4294967295 s_max)) out_data = Bits.ones DATA_SZ.
  Proof. vm_compute. reflexivity. Qed.

  Definition s_ok := retrieve 3 1234 s1.
  Example stale_cleared :
    [ret (status 3 s_ok); ret (retrieve 3 1111 s_ok); ret (retrieve 9 1234 s_ok);
     ret (store 1 1 1 s_ok); ret (delete 2 s_ok); ret (status 200 s_ok)]
    = [(1, 0); (0, 0); (0, 0); (1, 0); (0, 0); (0, 0)]%N.
  Proof. vm_compute. reflexivity. Qed.

End Checks.

Section Instance.

  Definition tfs_ctx : TFSchedContext := {|
      tfs_spec_states := pb_states;
      tfs_spec_states_fin := _;
      tfs_spec_states_size := pb_states_size;
      tfs_spec_states_init := pb_states_init;
      tfs_spec_inputs := pb_inputs;
      tfs_spec_inputs_fin := _;
      tfs_spec_inputs_size := pb_inputs_size;
      tfs_spec_inputs_class := fun _ => Public;
      tfs_spec_outputs := pb_outputs;
      tfs_spec_outputs_fin := _;
      tfs_spec_outputs_size := pb_outputs_size;
      tfs_spec_outputs_class := fun _ => Public;
      tfs_spec_action := pb_action;
      tfs_spec_action_fin := _;
      tfs_spec_action_ops := pb_ops;
      tfs_spec_ips := Empty_set;
      tfs_spec_ip := no_ips;
      tfs_spec_decls := []
  |}.

  Definition CL := 10.

  Definition tf_ctx : TFSynthContext := mk_synth_ctx (tfs_schedule tfs_ctx CL).

  Example derived_codes :
    tf_action_reg_size tf_ctx = 3
    /\ List.map (fun a => Bits.to_nat (tf_action_encoding tf_ctx a))
                [act_status; act_delete; act_store; act_retrieve] = [0; 1; 2; 3].
  Proof. vm_compute. split; reflexivity. Qed.

  Definition ipr_here := IPR.emulator_correct tfs_ctx CL.
  Definition sched_here := SchedulerSimulation.variable_scheduler_correct tfs_ctx CL.
  Definition synth_here := Synthesis.synthesis_correct tf_ctx.
  Definition init_here := Synthesis.initial_state_matches tf_ctx.

  Definition package := Lowering.package tf_ctx "Knox_PinBackup".

End Instance.

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Knox_PinBackup.ml" prog.
