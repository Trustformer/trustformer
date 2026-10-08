Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Coq.NArith.NArith.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Backend.Lowering.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Macros.
Require Trustformer.Theorems.IPR.

Require Import Coq.Lists.List.
Import ListNotations.

(* Knox's RFC 6238 TOTP token (sec. 7.1.3, knox-hsm otp): HMAC, truncation and
   mod 10^6 in the DSL over a two-block SHA-1 IP, which only a simulation model
   (sim/sha1_2blk_model.sv) implements so far. *)

Section FunctionalSpecification.

    Definition SECRET_SZ := 160.
    Definition CTR_SZ := 64.
    Definition CODE_SZ := 32.

    Section Sha1.
      Local Open Scope N_scope.

      Definition M32 : N := 0xFFFFFFFF.
      Definition add32 (a b: N) : N := N.land (a + b) M32.
      Definition rol32 (x k: N) : N := N.land (N.lor (N.shiftl x k) (N.shiftr x (32 - k))) M32.
      Definition not32 (x: N) : N := N.lxor x M32.

      Definition f1 (t: nat) (x y z: N) : N :=
        if Nat.ltb t 20 then N.lxor (N.land x y) (N.land (not32 x) z)
        else if Nat.ltb t 40 then N.lxor (N.lxor x y) z
        else if Nat.ltb t 60 then N.lxor (N.lxor (N.land x y) (N.land x z)) (N.land y z)
        else N.lxor (N.lxor x y) z.
      Definition K1 (t: nat) : N :=
        if Nat.ltb t 20 then 0x5a827999 else if Nat.ltb t 40 then 0x6ed9eba1
        else if Nat.ltb t 60 then 0x8f1bbcdc else 0xca62c1d6.

      Definition word (m: N) (t: nat) : N :=
        N.land (N.shiftr m (N.of_nat (32 * (15 - t)))) M32.

      Fixpoint sched (n: nat) (w: list N) : list N :=
        match n with
        | O => w
        | S n' =>
            let wt := rol32 (N.lxor (N.lxor (nth 2 w 0) (nth 7 w 0))
                                    (N.lxor (nth 13 w 0) (nth 15 w 0))) 1 in
            sched n' (wt :: w)
        end.
      Definition schedule (m: N) : list N := rev (sched 64 (rev (map (word m) (seq 0 16)))).

      Definition st5 : Type := (N * N * N * N * N)%type.
      Definition round (s: st5) (tw: nat * N) : st5 :=
        let '(a, b, c, d, e) := s in
        let '(t, w) := tw in
        let T := add32 (add32 (add32 (rol32 a 5) (f1 t b c d)) (add32 e (K1 t))) w in
        (T, a, rol32 b 30, c, d).
      Definition compress (h: st5) (m: N) : st5 :=
        let '(a, b, c, d, e) := fold_left round (combine (seq 0 80) (schedule m)) h in
        let '(h0, h1, h2, h3, h4) := h in
        (add32 a h0, add32 b h1, add32 c h2, add32 d h3, add32 e h4).
      Definition iv5 : st5 := (0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0).
      Definition digest5 (h: st5) : N :=
        let '(a, b, c, d, e) := h in
        N.lor (N.shiftl (N.lor (N.shiftl (N.lor (N.shiftl (N.lor (N.shiftl a 32) b) 32) c) 32) d) 32) e.

      Definition sha1_2blk_N (b1 b2: N) : N := digest5 (compress (compress iv5 b1) b2).
    End Sha1.

    Inductive otp_action := act_set_secret | act_otp | act_audit.

    Inductive otp_states := st_secret | st_maxctr | st_hs | st_tmp.
    Inductive otp_inputs := in_secret | in_ctr.
    Inductive otp_outputs := out_set_ok | out_code | out_max_ctr.
    Inductive otp_ips := ip_sha1.

    Definition otp_ssz (x: otp_states) : nat :=
      match x with
      | st_secret => SECRET_SZ
      | st_maxctr => CTR_SZ
      | st_hs => 160
      | st_tmp => CODE_SZ
      end.
    Definition otp_isz (x: otp_inputs) : nat :=
      match x with in_secret => SECRET_SZ | in_ctr => CTR_SZ end.
    Definition otp_osz (x: otp_outputs) : nat :=
      match x with out_set_ok => 1 | out_code => CODE_SZ | out_max_ctr => CTR_SZ end.

    Definition otp_init (x: otp_states) : tf_states_type otp_ssz x := Bits.zero.

    Definition sha1_ip_fn (req: bits_t 1024) : bits_t 160 :=
      let r := Bits.to_N req in
      Bits.of_N 160 (sha1_2blk_N (N.shiftr r 512) (N.land r (N.ones 512))).

    Definition otp_ip (p: otp_ips) : ip_decl :=
      match p with
      | ip_sha1 => {| ip_req_sz := 1024; ip_resp_sz := 160;
                      ip_lat := 180; ip_lat_pos := ltac:(lia); ip_fn := sha1_ip_fn |}
      end.

    Local Notation E := (@tf_expr otp_states otp_inputs otp_outputs).
    Local Notation OPS := (@tf_ops otp_states otp_inputs otp_outputs otp_ips).

    Definition kpad (c: nat) : E :=
      tf_op2 (tf_concat 160 352)
        (tf_op2 tf_xor (tf_svar st_secret) (mk_rep 20 c))
        (mk_rep 44 c).
    Definition ipad_blk : E := kpad 54.
    Definition opad_blk : E := kpad 92.
    Definition pad_in : E := tf_op2 (tf_concat 1 447) (tf_const 1) (tf_const 576).
    Definition pad_out : E := tf_op2 (tf_concat 1 351) (tf_const 1) (tf_const 672).

    Fixpoint dt_aux (n: nat) (hs: E) : E :=
      match n with
      | 0 => tf_const 0
      | S o => tf_expr_if (tf_op2 (tf_cmp 4 tf_eq) hs (tf_const o))
                          (mk_zext 31 CODE_SZ (mk_slice (158 - 8 * o) (128 - 8 * o) hs))
                          (dt_aux o hs)
      end.
    Definition dt (hs: E) : E := dt_aux 16 hs.

    Definition otp_finish : OPS :=
      {[ let $st_tmp := `dt (tf_svar st_hs)`;
         `mk_urem_const st_tmp CODE_SZ 1000000`;
         let $out_code := $st_tmp;
         let $st_maxctr := $in_ctr;
         let $st_hs := #0;
         let $st_tmp := #0 ]}.

    Definition otp_ops (act: otp_action) : OPS :=
      match act with
      | act_set_secret =>
          {[ `mk_clear_outputs`;
             let $st_secret := $in_secret;
             let $out_set_ok := #1 ]}
      | act_otp =>
          {[ `mk_clear_outputs`;
             if ($in_ctr <[CTR_SZ] $st_maxctr) then
               let $out_code := #0
             else
               let $st_hs := call ip_sha1 (`ipad_blk` ++[512, 512] ($in_ctr ++[64, 448] `pad_in`));
               let $st_hs := call ip_sha1 (`opad_blk` ++[512, 512] ($st_hs ++[160, 352] `pad_out`));
               `otp_finish` ]}
      | act_audit =>
          {[ `mk_clear_outputs`;
             let $out_max_ctr := $st_maxctr ]}
      end.

    Definition otp_step := tf_ops_run otp_ssz otp_isz otp_osz otp_ip.

End FunctionalSpecification.

Section Checks.
    Local Open Scope N_scope.

    Fixpoint rep_byte (b: N) (n: nat) : N :=
      match n with O => 0 | S n' => N.lor (N.shiftl (rep_byte b n') 8) b end.

    Definition hmac_sha1_N (key msg: N) : N :=
      let kblk := N.shiftl key 352 in
      let ih := digest5 (compress (compress iv5 (N.lxor kblk (rep_byte 0x36 64)))
                                  (N.lor (N.lor (N.shiftl msg 448) (N.shiftl 1 447)) 576)) in
      digest5 (compress (compress iv5 (N.lxor kblk (rep_byte 0x5c 64)))
                        (N.lor (N.lor (N.shiftl ih 352) (N.shiftl 1 351)) 672)).

    Definition get_byte_N (v off: N) : N := N.land (N.shiftr v (8 * (19 - off))) 255.
    Definition dt_N (hs: N) : N :=
      let off := N.land hs 15 in
      N.lor (N.lor (N.shiftl (N.land (get_byte_N hs off) 0x7f) 24)
                   (N.shiftl (get_byte_N hs (off + 1)) 16))
            (N.lor (N.shiftl (get_byte_N hs (off + 2)) 8) (get_byte_N hs (off + 3))).
    Definition hotp_N (key c: N) : N := N.modulo (dt_N (hmac_sha1_N key c)) 1000000.

    Example sha1_abc : digest5 (compress iv5 (N.shiftl 0x61626380 480 + 24))
                       = 0xa9993e364706816aba3e25717850c26c9cd0d89d.
    Proof. vm_compute. reflexivity. Qed.
    Example hmac_rfc2202 : hmac_sha1_N (rep_byte 0x0b 20) 0x4869205468657265
                           = 0xb617318655057264e28bc0b6fb378c8ef146be00.
    Proof. vm_compute. reflexivity. Qed.
    Definition RFCK : N := 0x3132333435363738393031323334353637383930.
    Example hmac_rfc4226_0 : hmac_sha1_N RFCK 0 = 0xcc93cf18508d94934c64b65d8ba7667fb7cde4b0.
    Proof. vm_compute. reflexivity. Qed.
    Definition RFC4226_HOTP : list N :=
      [755224; 287082; 359152; 969429; 338314; 254676; 287922; 162583; 399871; 520489].
    Example hotp_ref_rfc4226 : map (hotp_N RFCK) (map N.of_nat (seq 0 10)) = RFC4226_HOTP.
    Proof. vm_compute. reflexivity. Qed.
    Definition hmac_via_2blk_N (k c: N) : N :=
      let inner := sha1_2blk_N (N.lxor (N.shiftl k 352) (rep_byte 0x36 64))
                               (N.lor (N.lor (N.shiftl c 448) (N.shiftl 1 447)) 576) in
      sha1_2blk_N (N.lxor (N.shiftl k 352) (rep_byte 0x5c 64))
                  (N.lor (N.lor (N.shiftl inner 352) (N.shiftl 1 351)) 672).
    Example hmac_via_2blk :
      map (fun kc => hmac_via_2blk_N (fst kc) (snd kc)) [(RFCK, 7); (N.ones 160, N.ones 64)]
      = map (fun kc => hmac_sha1_N (fst kc) (snd kc)) [(RFCK, 7); (N.ones 160, N.ones 64)].
    Proof. vm_compute. reflexivity. Qed.

    Definition sysst := (ContextEnv.(env_t) (tf_states_type otp_ssz)
                         * ContextEnv.(env_t) (tf_outputs_type otp_osz))%type.
    Definition initial : sysst :=
      (ContextEnv.(create) otp_init, ContextEnv.(create) (fun _ => Bits.zero)).

    Definition inp (secret ctr: N) (x: otp_inputs) : bits_t (otp_isz x) :=
      match x with
      | in_secret => Bits.of_N SECRET_SZ secret
      | in_ctr => Bits.of_N CTR_SZ ctr
      end.

    Definition set_secret (k: N) (s: sysst) := otp_step (otp_ops act_set_secret) s (inp k 77).
    Definition otp (c: N) (s: sysst) := otp_step (otp_ops act_otp) s (inp 77 c).
    Definition audit (s: sysst) := otp_step (otp_ops act_audit) s (inp 77 77).

    Definition outp (o: otp_outputs) (s: sysst) : N := Bits.to_N (ContextEnv.(getenv) (snd s) o).
    Definition code := outp out_code.
    Definition ports (s: sysst) := (outp out_set_ok s, outp out_code s, outp out_max_ctr s).
    Definition knox_state (s: sysst) :=
      (Bits.to_N (ContextEnv.(getenv) (fst s) st_secret),
       Bits.to_N (ContextEnv.(getenv) (fst s) st_maxctr)).
    Definition scratch (s: sysst) :=
      (Bits.to_N (ContextEnv.(getenv) (fst s) st_hs),
       Bits.to_N (ContextEnv.(getenv) (fst s) st_tmp)).

    Fixpoint run_otps (cs: list N) (s: sysst) : list N :=
      match cs with
      | [] => []
      | c :: cs' => let s' := otp c s in code s' :: run_otps cs' s'
      end.

    Example dsl_rfc4226 :
      run_otps (map N.of_nat (seq 0 10)) (set_secret RFCK initial) = RFC4226_HOTP.
    Proof. vm_compute. reflexivity. Qed.

    Definition RFC6238_T : list N :=
      [0x1; 0x23523EC; 0x23523ED; 0x273EF07; 0x3F940AA; 0x27BC86AA].
    Definition RFC6238_TOTP6 : list N := [287082; 81804; 50471; 5924; 279037; 353130].
    Example dsl_rfc6238 : run_otps RFC6238_T (set_secret RFCK initial) = RFC6238_TOTP6.
    Proof. vm_compute. reflexivity. Qed.

    Definition s1 := set_secret 0x1337 initial.
    Definition s2 := otp 1234 s1.
    Example knox_t1 : code s2 = 451349.                        Proof. vm_compute. reflexivity. Qed.
    Example knox_t2 : code (otp 1 s2) = 0.                     Proof. vm_compute. reflexivity. Qed.
    Example knox_t3 : code (otp 9999 s2) = 910689.             Proof. vm_compute. reflexivity. Qed.
    Example knox_t4 : outp out_max_ctr (audit s2) = 1234.      Proof. vm_compute. reflexivity. Qed.
    Definition s3 := set_secret 0xcafe s2.
    Example knox_t5 : code (otp 1 s3) = 0.                     Proof. vm_compute. reflexivity. Qed.

    Example set_returns : ports s3 = (1, 0, 0).                Proof. vm_compute. reflexivity. Qed.
    Example set_keeps_bound : knox_state s3 = (0xcafe, 1234).  Proof. vm_compute. reflexivity. Qed.
    Example reject_pure : fst (otp 1 s2) = fst s2.             Proof. vm_compute. reflexivity. Qed.
    Example equal_accepted : code (otp 1234 s2) = 451349.      Proof. vm_compute. reflexivity. Qed.
    Example accept_state : knox_state (otp 9999 s2) = (0x1337, 9999).
    Proof. vm_compute. reflexivity. Qed.
    Example accept_scratch : scratch (otp 9999 s2) = (0, 0).   Proof. vm_compute. reflexivity. Qed.
    Example fresh_otp : code (otp 0 initial) = hotp_N 0 0.     Proof. vm_compute. reflexivity. Qed.
    Example fresh_otp_value : hotp_N 0 0 = 328482.             Proof. vm_compute. reflexivity. Qed.
    Example fresh_audit : ports (audit initial) = (0, 0, 0).   Proof. vm_compute. reflexivity. Qed.
    Definition sMax := otp (N.ones 64) (set_secret (N.ones 160) initial).
    Example max_accepted : code sMax = hotp_N (N.ones 160) (N.ones 64).
    Proof. vm_compute. reflexivity. Qed.
    Example max_value : hotp_N (N.ones 160) (N.ones 64) = 995544.
    Proof. vm_compute. reflexivity. Qed.
    Example max_rejects : code (otp (N.ones 64 - 1) sMax) = 0.          Proof. vm_compute. reflexivity. Qed.
    Example max_audit : outp out_max_ctr (audit sMax) = N.ones 64.      Proof. vm_compute. reflexivity. Qed.
    Example hi_word : code (otp (N.ones 32) (otp (N.shiftl 1 32) s1)) = 0.
    Proof. vm_compute. reflexivity. Qed.

    Definition s4 := otp 9999 s2.
    Example ports_after_otp : ports s4 = (0, 910689, 0).                Proof. vm_compute. reflexivity. Qed.
    Example ports_after_reject : ports (otp 5 s4) = (0, 0, 0).          Proof. vm_compute. reflexivity. Qed.
    Example ports_after_audit : ports (audit s4) = (0, 0, 9999).        Proof. vm_compute. reflexivity. Qed.
    Example ports_after_set : ports (set_secret 1 (audit s4)) = (1, 0, 0).
    Proof. vm_compute. reflexivity. Qed.

    Definition SW : N := 0x0102030405060708090a0b0c0d0e0f1011121314.
    Definition cs8 := map N.of_nat (seq 0 8).
    Example dsl_eq_ref_8 : run_otps cs8 (set_secret SW initial) = map (hotp_N SW) cs8.
    Proof. vm_compute. reflexivity. Qed.

    Definition finish (hs: N) : N :=
      code (otp_step otp_finish
              (ContextEnv.(putenv) (fst s1) st_hs (Bits.of_N 160 hs), snd s1) (inp 77 5000)).
    Definition ref_code (hs: N) : N :=
      let o := N.land hs 15 in
      N.modulo (N.land (N.shiftr hs (128 - 8 * o)) (N.ones 31)) 1000000.

    Definition mk_hs (o v: N) : N :=
      let sh := 128 - 8 * o in
      let x := N.lor (N.land (N.ones 160) (N.lxor (N.ones 160) (N.shiftl (N.ones 32) sh)))
                     (N.shiftl (N.land v (N.ones 32)) sh) in
      N.lor (N.land x (N.lxor (N.ones 160) 15)) o.

    Definition vals : list N :=
      flat_map (fun i => [N.shiftl 1000000 i; N.shiftl 1000000 i - 1]) (map N.of_nat (seq 0 12))
      ++ [0; 1; 999999; 2147483647; 2147000000; 2146999999; 123456789].
    Definition vals2 : list N := vals ++ map (fun v => N.lor v (N.shiftl 1 31)) vals.
    Definition edge_hs : list N :=
      map (fun kv => mk_hs (N.modulo (fst kv) 16) (snd kv))
          (combine (map N.of_nat (seq 0 62)) vals2).
    Fixpoint lcg (n: nat) (x: N) : list N :=
      match n with
      | O => []
      | S n' => let x' := N.land (x * 0x5851f42d4c957f2d14057b7ef767814f + 0x9e3779b97f4a7c15)
                                 (N.ones 160) in
                x' :: lcg n' x'
      end.
    Definition rand_hs : list N := lcg 32 0x0123456789abcdef.

    Example edge_sizes : (List.length vals2, List.length edge_hs) = (62%nat, 62%nat).
    Proof. vm_compute. reflexivity. Qed.
    Example ref_is_knox :
      forallb (fun hs => N.eqb (ref_code hs) (N.modulo (dt_N hs) 1000000)) (edge_hs ++ rand_hs) = true.
    Proof. vm_compute. reflexivity. Qed.
    Example mk_hs_places :
      forallb (fun hv => N.eqb (dt_N (fst hv)) (N.land (snd hv) (N.ones 31)))
              (combine edge_hs vals2) = true.
    Proof. vm_compute. reflexivity. Qed.
    Definition mismatches (l: list N) := filter (fun hs => negb (N.eqb (finish hs) (ref_code hs))) l.
    Example dt_mod_edges : mismatches edge_hs = [].
    Proof. vm_compute. reflexivity. Qed.
    Example dt_mod_random : mismatches rand_hs = [].
    Proof. vm_compute. reflexivity. Qed.

End Checks.

Section Instance.

    Definition tfs_ctx : TFSchedContext := {|
        tfs_spec_states := otp_states;
        tfs_spec_states_fin := _;
        tfs_spec_states_size := otp_ssz;
        tfs_spec_states_init := otp_init;
        tfs_spec_inputs := otp_inputs;
        tfs_spec_inputs_fin := _;
        tfs_spec_inputs_size := otp_isz;
        tfs_spec_inputs_class := fun _ => Public;
        tfs_spec_outputs := otp_outputs;
        tfs_spec_outputs_fin := _;
        tfs_spec_outputs_size := otp_osz;
        tfs_spec_outputs_class := fun _ => Public;
        tfs_spec_action := otp_action;
        tfs_spec_action_fin := _;
        tfs_spec_action_ops := otp_ops;
        tfs_spec_ips := otp_ips;
        tfs_spec_ips_fin := _;
        tfs_spec_ip := otp_ip;
        tfs_spec_decls := []
    |}.

    Definition CL := 10.

    Definition tf_ctx : TFSynthContext := mk_synth_ctx (tfs_schedule tfs_ctx CL).
    Example derived_reg_size : tf_action_reg_size tf_ctx = 2%nat.
    Proof. reflexivity. Qed.

    Definition ipr_here := IPR.circuit_emulated tfs_ctx CL _ _
      (tf_action_encoding_inj tf_ctx) (tf_action_names tf_ctx).

    Definition package := Lowering.package tf_ctx "Knox_Otp".

End Instance.

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Knox_Otp.ml" prog.
