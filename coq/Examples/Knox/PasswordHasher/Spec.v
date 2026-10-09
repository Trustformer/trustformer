Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Backend.Lowering.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Macros.
Require Trustformer.Theorems.Definitions.
Require Trustformer.Theorems.IPR.

Require Import Coq.Lists.List.
Import ListNotations.

(* Knox's password hasher (sec. 7.1.2, knox-hsm password-hasher): get-hash is
   SHA-256(secret || msg) over trusted SHA-256 IP.  That is spec.rkt's order; the
   paper's Fig. 13 has the reverse. *)

Section FunctionalSpecification.

    Section Sha256.
      Local Open Scope N_scope.

      Definition M32 : N := 0xFFFFFFFF.
      Definition add32 (a b: N) : N := N.land (a + b) M32.
      Definition ror32 (x k: N) : N := N.lor (N.shiftr x k) (N.land (N.shiftl x (32 - k)) M32).
      Definition not32 (x: N) : N := N.lxor x M32.

      Definition Ch  x y z := N.lxor (N.land x y) (N.land (not32 x) z).
      Definition Maj x y z := N.lxor (N.lxor (N.land x y) (N.land x z)) (N.land y z).
      Definition Sum0 x := N.lxor (N.lxor (ror32 x 2) (ror32 x 13)) (ror32 x 22).
      Definition Sum1 x := N.lxor (N.lxor (ror32 x 6) (ror32 x 11)) (ror32 x 25).
      Definition sig0 x := N.lxor (N.lxor (ror32 x 7) (ror32 x 18)) (N.shiftr x 3).
      Definition sig1 x := N.lxor (N.lxor (ror32 x 17) (ror32 x 19)) (N.shiftr x 10).

      Definition K : list N :=
        [0x428a2f98; 0x71374491; 0xb5c0fbcf; 0xe9b5dba5; 0x3956c25b; 0x59f111f1; 0x923f82a4; 0xab1c5ed5;
         0xd807aa98; 0x12835b01; 0x243185be; 0x550c7dc3; 0x72be5d74; 0x80deb1fe; 0x9bdc06a7; 0xc19bf174;
         0xe49b69c1; 0xefbe4786; 0x0fc19dc6; 0x240ca1cc; 0x2de92c6f; 0x4a7484aa; 0x5cb0a9dc; 0x76f988da;
         0x983e5152; 0xa831c66d; 0xb00327c8; 0xbf597fc7; 0xc6e00bf3; 0xd5a79147; 0x06ca6351; 0x14292967;
         0x27b70a85; 0x2e1b2138; 0x4d2c6dfc; 0x53380d13; 0x650a7354; 0x766a0abb; 0x81c2c92e; 0x92722c85;
         0xa2bfe8a1; 0xa81a664b; 0xc24b8b70; 0xc76c51a3; 0xd192e819; 0xd6990624; 0xf40e3585; 0x106aa070;
         0x19a4c116; 0x1e376c08; 0x2748774c; 0x34b0bcb5; 0x391c0cb3; 0x4ed8aa4a; 0x5b9cca4f; 0x682e6ff3;
         0x748f82ee; 0x78a5636f; 0x84c87814; 0x8cc70208; 0x90befffa; 0xa4506ceb; 0xbef9a3f7; 0xc67178f2].

      Definition IV : list N :=
        [0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a; 0x510e527f; 0x9b05688c; 0x1f83d9ab; 0x5be0cd19].

      Definition word (m: N) (t: nat) : N := N.land (N.shiftr m (N.of_nat (32 * (15 - t)))) M32.

      Fixpoint sched (n: nat) (w: list N) : list N :=
        match n with
        | O => w
        | S n' =>
            let wt := add32 (add32 (sig1 (nth 1 w 0)) (nth 6 w 0))
                            (add32 (sig0 (nth 14 w 0)) (nth 15 w 0)) in
            sched n' (wt :: w)
        end.
      Definition schedule (m: N) : list N :=
        rev (sched 48 (rev (map (word m) (seq 0 16)))).

      Definition st8 : Type := (N * N * N * N * N * N * N * N)%type.
      Definition round (s: st8) (kw: N * N) : st8 :=
        let '(a, b, c, d, e, f, g, h) := s in
        let '(k, w) := kw in
        let T1 := add32 (add32 (add32 h (Sum1 e)) (add32 (Ch e f g) k)) w in
        let T2 := add32 (Sum0 a) (Maj a b c) in
        (add32 T1 T2, a, b, c, add32 d T1, e, f, g).

      Definition iv8 : st8 :=
        (nth 0 IV 0, nth 1 IV 0, nth 2 IV 0, nth 3 IV 0,
         nth 4 IV 0, nth 5 IV 0, nth 6 IV 0, nth 7 IV 0).

      Definition cat32 (acc w: N) : N := N.lor (N.shiftl acc 32) w.

      Definition sha256_block_N (m: N) : N :=
        let '(a, b, c, d, e, f, g, h) := fold_left round (combine K (schedule m)) iv8 in
        fold_left cat32
          [add32 a (nth 0 IV 0); add32 b (nth 1 IV 0); add32 c (nth 2 IV 0); add32 d (nth 3 IV 0);
           add32 e (nth 4 IV 0); add32 f (nth 5 IV 0); add32 g (nth 6 IV 0); add32 h (nth 7 IV 0)] 0.
    End Sha256.

    Definition sha256_block (b: bits_t 512) : bits_t 256 :=
      Bits.of_N 256 (sha256_block_N (Bits.to_N b)).

    Definition SECRET_SZ := 160.
    Definition MSG_SZ := 256.
    Definition DIGEST_SZ := 256.
    Definition BLOCK_SZ := 512.

    Inductive fs_action := act_set_secret | act_get_hash.

    Inductive fs_states := st_secret | st_dig.
    Inductive fs_inputs := in_secret | in_msg.
    Inductive fs_outputs := out_ok | out_digest.
    Inductive fs_ips := ip_sha_blk.

    Definition fs_states_size (x: fs_states) : nat :=
      match x with st_secret => SECRET_SZ | st_dig => DIGEST_SZ end.
    Definition fs_inputs_size (x: fs_inputs) : nat :=
      match x with in_secret => SECRET_SZ | in_msg => MSG_SZ end.
    Definition fs_outputs_size (x: fs_outputs) : nat :=
      match x with out_ok => 1 | out_digest => DIGEST_SZ end.

    Definition fs_states_init (x: fs_states) : tf_states_type fs_states_size x :=
      Bits.zero.

    Definition fs_ip (p: fs_ips) : ip_decl :=
      match p with
      | ip_sha_blk => {| ip_req_sz := BLOCK_SZ; ip_resp_sz := DIGEST_SZ;
                         ip_lat := 72; ip_lat_pos := ltac:(lia);
                         ip_fn := sha256_block |}
      end.

    Local Notation E := (@tf_expr fs_states fs_inputs fs_outputs).
    Local Notation OPS := (@tf_ops fs_states fs_inputs fs_outputs fs_ips).

    Definition PAD_TAIL : E := mk_hex "80000000_00000000_000001a0"%string.

    Definition padded_block : E :=
      {[ $st_secret ++[SECRET_SZ, 352] ($in_msg ++[MSG_SZ, 96] `PAD_TAIL`) ]}.

    Definition fs_ops (a: fs_action) : OPS :=
      match a with
      | act_set_secret =>
          {[ `mk_clear_outputs`;
             let $st_secret := $in_secret;
             let $out_ok := #1 ]}
      | act_get_hash =>
          {[ `mk_clear_outputs`;
             let $st_dig := call ip_sha_blk (`padded_block`);
             let $out_digest := $st_dig;
             let $st_dig := #0 ]}
      end.

End FunctionalSpecification.

Section Checks.
    Local Open Scope N_scope.

    Example sha_abc :
      sha256_block_N (N.shiftl 0x61626380 480 + 24)
      = 0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad.
    Proof. vm_compute. reflexivity. Qed.
    Example sha_empty :
      sha256_block_N (N.shiftl 1 511)
      = 0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855.
    Proof. vm_compute. reflexivity. Qed.

    Definition sysst := (ContextEnv.(env_t) (tf_states_type fs_states_size)
                         * ContextEnv.(env_t) (tf_outputs_type fs_outputs_size))%type.

    Definition initial : sysst :=
      (ContextEnv.(create) fs_states_init, ContextEnv.(create) (fun _ => Bits.zero)).

    Definition inp (secret msg: N) (x: fs_inputs) : bits_t (fs_inputs_size x) :=
      match x with
      | in_secret => Bits.of_N SECRET_SZ secret
      | in_msg => Bits.of_N MSG_SZ msg
      end.

    Definition run (a: fs_action) (secret msg: N) (s: sysst) : sysst :=
      tf_ops_run fs_states_size fs_inputs_size fs_outputs_size fs_ip (fs_ops a) s (inp secret msg).

    Definition set_secret (k: N) : sysst -> sysst := run act_set_secret k 0xFEED.
    Definition get_hash (m: N) : sysst -> sysst := run act_get_hash 0xBEEF m.

    Definition ok (s: sysst) : N := Bits.to_N (ContextEnv.(getenv) (snd s) out_ok).
    Definition digest (s: sysst) : N := Bits.to_N (ContextEnv.(getenv) (snd s) out_digest).
    Definition secret_of (s: sysst) : N := Bits.to_N (ContextEnv.(getenv) (fst s) st_secret).
    Definition dig_reg (s: sysst) : N := Bits.to_N (ContextEnv.(getenv) (fst s) st_dig).

    Definition obs (s: sysst) : N * N := (ok s, digest s).

    Definition KMSG := 0x0123456789abcdef.
    Definition SW := 0x0102030405060708090a0b0c0d0e0f1011121314.
    Definition MW := 0x2122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40.

    Definition H_KNOX  := 0xc4162593dac170ed49fe1a7aca6837761be71e95d470407696a1666790d967ab.
    Definition H_PAPER := 0x57d35d26c9b263c00c9b0ef045be94e6677e5ad05103d0b86317b0d937ffddb8.

    Example power_on : (obs initial, secret_of initial, dig_reg initial) = ((0, 0), 0, 0).
    Proof. vm_compute. reflexivity. Qed.

    Definition s1 := set_secret 1337 initial.
    Example knox_set : obs s1 = (1, 0).
    Proof. vm_compute. reflexivity. Qed.
    Example knox_vector : obs (get_hash KMSG s1) = (0, H_KNOX).
    Proof. vm_compute. reflexivity. Qed.

    Example not_paper_order : digest (get_hash KMSG s1) <> H_PAPER.
    Proof. vm_compute. discriminate. Qed.

    Example fresh_vector : obs (get_hash KMSG initial)
      = (0, 0xc98d239b456aacb44548032f0455c46828573d9fc14a7d0983e3582f2648e883).
    Proof. vm_compute. reflexivity. Qed.
    Example zero_zero : digest (get_hash 0 initial)
      = 0x7955cb2de90dd9efc6df9fdbf5f5d10c114f4135a9a6b52db1003be749e32f7a.
    Proof. vm_compute. reflexivity. Qed.

    Example secret_msb : digest (get_hash 0 (set_secret (N.shiftl 1 159) initial))
      = 0x2871774b49f3973020fa3e9090d7091c60b7589284463d132f338df722f665e3.
    Proof. vm_compute. reflexivity. Qed.
    Example msg_lsb : digest (get_hash 1 initial)
      = 0xaeadacea552de15142e357824da1048a52e0441789294224808010e7a7a6a16c.
    Proof. vm_compute. reflexivity. Qed.

    Example wide_vector : digest (get_hash MW (set_secret SW initial))
      = 0x8912b86c5a100e7e585d035fae01084c71ca937b7bf8b0104fba06e5cc00021c.
    Proof. vm_compute. reflexivity. Qed.
    Example ones_vector : digest (get_hash (N.ones 256) (set_secret (N.ones 160) initial))
      = 0x01028783afa8d55efe67c3967e5405a39640fede4405133b3f1f86a8edcd07dd.
    Proof. vm_compute. reflexivity. Qed.

    Definition states : list sysst :=
      [initial; s1; set_secret SW initial; get_hash MW (set_secret SW initial);
       set_secret (N.ones 160) (get_hash KMSG s1)].
    Example get_hash_pure :
      List.map (fun s => fst (get_hash MW s)) states = List.map fst states.
    Proof. vm_compute. reflexivity. Qed.
    Example scratch_cleared :
      List.map (fun s => dig_reg (get_hash KMSG s)) states = [0; 0; 0; 0; 0].
    Proof. vm_compute. reflexivity. Qed.

    Example two_gets : obs (get_hash MW (get_hash KMSG s1))
      = (0, 0x1979af1ec0e1d683797013adb301df16c92b40123073686665fcf7940b0b5706).
    Proof. vm_compute. reflexivity. Qed.
    Example get_idempotent :
      get_hash MW (get_hash MW (set_secret SW initial)) = get_hash MW (set_secret SW initial).
    Proof. vm_compute. reflexivity. Qed.

    Example set_replaces : obs (get_hash KMSG (set_secret 1337 (set_secret SW initial))) = (0, H_KNOX).
    Proof. vm_compute. reflexivity. Qed.
    Example set_forgets_history :
      List.map (fun s => set_secret 1337 s) states = List.map (fun _ => set_secret 1337 initial) states.
    Proof. vm_compute. reflexivity. Qed.

    Example set_ignores_msg_port :
      run act_set_secret 1337 MW initial = run act_set_secret 1337 0 initial.
    Proof. vm_compute. reflexivity. Qed.
    Example get_ignores_secret_port :
      run act_get_hash 1337 MW (set_secret SW initial) = run act_get_hash 0 MW (set_secret SW initial).
    Proof. vm_compute. reflexivity. Qed.

    Definition wipe (s: sysst) : sysst := (fst s, snd initial).
    Definition next_calls : list (sysst -> sysst) := [set_secret 7; get_hash KMSG; get_hash 0].
    Example no_stale_outputs :
      List.map (fun s => List.map (fun f => obs (f s)) next_calls) states
      = List.map (fun s => List.map (fun f => obs (f (wipe s))) next_calls) states.
    Proof. vm_compute. reflexivity. Qed.
    Example no_stale_digest : obs (set_secret 1337 (get_hash MW (set_secret SW initial))) = (1, 0).
    Proof. vm_compute. reflexivity. Qed.

    Definition used : list (sysst * N) :=
      [(get_hash KMSG s1, 1337); (get_hash MW (set_secret SW initial), SW);
       (get_hash 0 initial, 0); (get_hash MW (get_hash KMSG s1), 1337)].
    Example host_wipe_state :
      List.map (fun '(s, k) => fst (set_secret k s)) used = List.map (fun '(s, _) => fst s) used.
    Proof. vm_compute. reflexivity. Qed.
    Example host_wipe_ports :
      List.map (fun '(s, k) => obs (set_secret k s)) used = [(1, 0); (1, 0); (1, 0); (1, 0)].
    Proof. vm_compute. reflexivity. Qed.

    Example reset_state_is_set_zero :
      List.map (fun s => fst (set_secret 0 s)) states = List.map (fun _ => fst initial) states.
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
        tfs_spec_ips := fs_ips;
        tfs_spec_ips_fin := _;
        tfs_spec_ip := fs_ip;
        tfs_spec_decls := []
    |}.

    Definition CL := 10.

    Definition tf_ctx : TFSynthContext := mk_synth_ctx (tfs_schedule tfs_ctx CL).

    Example cmd_width : tf_action_reg_size tf_ctx = 2%nat.
    Proof. reflexivity. Qed.
    Example cmd_codes :
      List.map (fun a => Bits.to_nat (tf_action_encoding tf_ctx a)) [act_set_secret; act_get_hash]
      = [0; 1]%nat.
    Proof. vm_compute. reflexivity. Qed.

    Example sf_set_secret : Definitions.sf_action tfs_ctx act_set_secret = true.
    Proof. vm_compute. reflexivity. Qed.
    Example sf_get_hash : Definitions.sf_action tfs_ctx act_get_hash = false.
    Proof. vm_compute. reflexivity. Qed.

    Definition ipr_here := IPR.ipr tfs_ctx CL _ _
      (tf_action_encoding_inj tf_ctx) (tf_action_names tf_ctx).

    Definition package := Lowering.package tf_ctx "Knox_PwHasher".

End Instance.

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Knox_PwHasher.ml" prog.
