Require Import Koika.Frontend.
Require Import Koika.Std.
Require Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.Backend.Lowering.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.

Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Lists.List.
Import ListNotations.

(* A TCG MARS device, Profile [TF-MARS-S256-P2-V2], over two PCRs.  One command =
   one action: a crypto round trip is a [tf_call] inside the command that needs
   it.  Each of the 13 MARS_CC codes has an arm, and every arm writes [out_rc].
   Sources: TCG MARS Library Specification v1 r14 (sections cited inline) and
   the TCG reference emulator (mars.c, mars.h, hw_sha2.c). *)

Section FunctionalSpecification.

    Definition digest_sz := 256.        (* PROFILE_LEN_DIGEST = 32 bytes *)
    Definition arg_sz    := 16.
    Definition rc_sz     := 16.
    Definition msg_sz    := 1024.       (* widest MARS message: the 100-byte snapshot *)


    Definition hmac_msg_sz := 512.      (* longest HMAC message: the 42-byte KDF frame *)
    Definition len_sz      := 16.       (* the byte length that rides with a request *)

    (* What the two IPs compute: section parameters, so every result below holds
       for any pair of functions, SHA-256 and HMAC-SHA256 among them. *)
    Variable sha_f  : bits_t (len_sz + msg_sz) -> bits_t digest_sz.
    Variable hmac_f : bits_t (len_sz + digest_sz + hmac_msg_sz) -> bits_t digest_sz.

    (* Key-derivation labels, spec section 5.5 Table 2.  The label alone
       separates the next DP from the three leaf kinds, and a Sign key ('U')
       from an attestation key ('R'), which is why the framing stays inside
       the verified module. *)
    Definition MARS_LX := 88.   (* 'X' -- bytes for external use, MARS_Derive *)
    Definition MARS_LD := 68.   (* 'D' -- DP from PS, and the next DP *)
    Definition MARS_LU := 85.   (* 'U' -- unrestricted key, Sign and SignatureVerify *)
    Definition MARS_LR := 82.   (* 'R' -- restricted AK, Quote and SignatureVerify *)

    (* Table 4 response codes (spec section 6.2). *)
    Definition MARS_RC_SUCCESS := 0.
    Definition MARS_RC_FAILURE := 2.
    Definition MARS_RC_BUFFER  := 4.
    Definition MARS_RC_COMMAND := 5.
    Definition MARS_RC_VALUE   := 6.
    Definition MARS_RC_REG     := 7.

    (* Table 6 property tags (spec section 8.1.2). *)
    Definition MARS_PT_PCR        := 1.
    Definition MARS_PT_TSR        := 2.
    Definition MARS_PT_LEN_DIGEST := 3.
    Definition MARS_PT_LEN_SIGN   := 4.
    Definition MARS_PT_LEN_KSYM   := 5.
    Definition MARS_PT_LEN_KPUB   := 6.
    Definition MARS_PT_LEN_KPRV   := 7.
    Definition MARS_PT_ALG_HASH   := 8.
    Definition MARS_PT_ALG_SIGN   := 9.
    Definition MARS_PT_ALG_SKDF   := 10.
    Definition MARS_PT_ALG_AKDF   := 11.

    (* The Profile.  Symmetric only, so ALG_AKDF is TPM_ALG_ERROR, both
       asymmetric key lengths are zero, and MARS_PublicRead falls outside it
       (Table 5: M* only with CryptAkdf). *)
    Definition PROFILE_COUNT_PCR  := 2.
    Definition PROFILE_COUNT_TSR  := 0.
    Definition PROFILE_LEN_DIGEST := 32.
    Definition PROFILE_LEN_SIGN   := 32.
    Definition PROFILE_LEN_KSYM   := 32.
    Definition PROFILE_LEN_KPUB   := 0.
    Definition PROFILE_LEN_KPRV   := 0.
    Definition PROFILE_ALG_HASH   := 11.   (* TPM_ALG_SHA256          0x0B *)
    Definition PROFILE_ALG_SIGN   := 5.    (* TPM_ALG_HMAC            0x05 *)
    Definition PROFILE_ALG_SKDF   := 34.   (* TPM_ALG_KDF1_SP800_108  0x22 *)
    Definition PROFILE_ALG_AKDF   := 0.    (* TPM_ALG_ERROR                *)

    (* One action per MARS_CC code (mars.h L105-118).  Codes 0..12 are the
       specification's; MARS_Init takes a Profile-declared code. *)
    Inductive fs_action :=
    | act_selftest           (* MARS_CC_SelfTest          0 *)
    | act_capabilityget      (* MARS_CC_CapabilityGet     1 *)
    | act_sequencehash       (* MARS_CC_SequenceHash      2 *)
    | act_sequenceupdate     (* MARS_CC_SequenceUpdate    3 *)
    | act_sequencecomplete   (* MARS_CC_SequenceComplete  4 *)
    | act_pcrextend          (* MARS_CC_PcrExtend         5 *)
    | act_regread            (* MARS_CC_RegRead           6 *)
    | act_derive             (* MARS_CC_Derive            7 *)
    | act_dpderive           (* MARS_CC_DpDerive          8 *)
    | act_publicread         (* MARS_CC_PublicRead        9 *)
    | act_quote              (* MARS_CC_Quote            10 *)
    | act_sign               (* MARS_CC_Sign             11 *)
    | act_signatureverify    (* MARS_CC_SignatureVerify  12 *)
    | act_init               (* Profile-specific     0xFFFF *)
    .

    (* MSB first, 16 bits. *)
    Definition fs_action_encoding (a: fs_action) : bits_t 16 :=
    match a with
    | act_selftest         => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | act_capabilityget    => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1
    | act_sequencehash     => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0
    | act_sequenceupdate   => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1
    | act_sequencecomplete => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0
    | act_pcrextend        => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~1
    | act_regread          => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0
    | act_derive           => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1
    | act_dpderive         => Ob~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0
    | act_publicread       => Ob~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~1
    | act_quote            => Ob~0~0~0~0~0~0~0~0~0~0~0~0~1~0~1~0
    | act_sign             => Ob~0~0~0~0~0~0~0~0~0~0~0~0~1~0~1~1
    | act_signatureverify  => Ob~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0~0
    (* 0xFFFF, clear of the 0..12 range: MARS_Init is a permanent Profile command. *)
    | act_init             => Ob~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
    end.

    Lemma fs_action_encoding_inj :
        forall a1 a2,
        fs_action_encoding a1 = fs_action_encoding a2 ->
        a1 = a2.
    Proof.
        intros. unfold fs_action_encoding in H.
        destruct a1; destruct a2; try reflexivity; try discriminate.
    Qed.

    (* Secrets: the attacker model is secrets = states_var. *)
    Inductive fs_states :=
    | st_ps
    | st_dp
    | st_ak            (* a leaf key: Quote's AK, Sign's and Verify's key *)
    (* Destinations for a [tf_call]: a call writes a STATE var, and two calls in
       one action need two of them. *)
    | st_dig           (* a SHA result: the extended PCR, the SHA known answer *)
    | st_snap          (* CryptSnapshot: the device snapshot *)
    | st_sig           (* a leaf value: a MAC, Derive's bytes, the HMAC known answer *)
    .

    Inductive fs_inputs :=
    | in_pt            (* MARS_CapabilityGet: property tag        *)
    | in_idx           (* MARS_RegRead / MARS_PcrExtend: index    *)
    | in_dig           (* PcrExtend, Sign, SignatureVerify: digest *)

    (* Platform-driven, so [Secret]: the platform module drives them, apart
       from the host bus (spec section 5.8).  [in_ps] is the Primary Seed. *)
    | in_ps
    | in_init_req
    (* Arguments of Quote, Derive, DpDerive, Sign and SignatureVerify *)
    | in_regsel        (* Quote, Derive, DpDerive: regSelect *)
    | in_nonce         (* Quote *)
    | in_ctx           (* all five *)
    | in_nlen          (* Quote: the nonce's length *)
    | in_ctxlen        (* all five: the ctx's length *)
    (* MARS_SignatureVerify *)
    | in_sig
    | in_restricted
    (* Platform-driven: 1 = the platform detected an internal error (5.6).
       Read as a command under [guard_failure] is accepted, so the platform
       holds it high until such a command is accepted. *)
    | in_fault
    .

    (* PCRs are OUTPUT variables: MARS_RegRead hands them out, and Public keeps
       the Quote datapath untainted. *)
    Inductive fs_outputs :=
    (* Public: results *)
    | out_rc
    | out_cap
    | out_dout
    | out_result     (* MARS_SignatureVerify: 1 = the MAC matches *)
    (* Public: device state *)
    | out_pcr0
    | out_pcr1
    | out_failure

    | out_st         (* 0 = uninitialized, 1 = DP is valid       *)
    | out_snap       (* the last successful MARS_Quote's snapshot *)
    .

    Definition fs_states_size (x: fs_states) : nat :=
    match x with
    | st_ps => digest_sz
    | st_dp => digest_sz
    | st_ak => digest_sz
    | st_dig => digest_sz
    | st_snap => digest_sz
    | st_sig => digest_sz
    end.

    Definition fs_inputs_size (x: fs_inputs) : nat :=
    match x with
    | in_pt          => arg_sz
    | in_idx         => arg_sz
    | in_dig         => digest_sz
    | in_ps         => digest_sz
    | in_init_req   => 1
    | in_regsel     => 32
    | in_nonce      => digest_sz
    | in_ctx        => digest_sz
    | in_nlen       => arg_sz
    | in_ctxlen     => arg_sz
    | in_sig        => digest_sz
    | in_restricted => 1
    | in_fault      => 1
    end.

    Definition fs_outputs_size (x: fs_outputs) : nat :=
    match x with
    | out_rc        => rc_sz
    | out_cap       => 16
    | out_dout      => digest_sz
    | out_result    => 1
    | out_pcr0      => digest_sz
    | out_pcr1      => digest_sz
    | out_failure   => 1

    | out_st        => 1
    | out_snap      => digest_sz
    end.

    (* Confidentiality classification (Contract.v [port_class]).  [Secret] marks
       a port outside what the guarantee quantifies over: it may carry a secret
       and stays off the memory map.  DP and AK travel over IP links, which are
       internal to the device.  Spec section 5.8. *)
    Definition fs_inputs_class (x: fs_inputs) : port_class :=
    match x with
    | in_pt | in_idx | in_dig                            => Public
    | in_ps | in_init_req | in_fault                     => Secret
    (* command arguments are the host's own *)
    | in_regsel | in_nonce | in_ctx | in_nlen | in_ctxlen
    | in_sig | in_restricted                             => Public
    end.

    Definition fs_outputs_class (x: fs_outputs) : port_class :=
    match x with
    (* results and device state the host reads over the bus *)
    | out_rc | out_cap | out_dout | out_result
    | out_pcr0 | out_pcr1 | out_failure | out_st | out_snap => Public
    end.

    (* The two attached IPs.  A request is ONE word, so a multi-field request is
       packed: SHA takes [len || msg], HMAC takes [len || key || msg].  [ip_fn]
       is the section parameter [sha_f] / [hmac_f]; the extraction plugs in
       [placeholder_digest]. *)
    Definition placeholder_digest {n} (v: bits_t n) : bits_t digest_sz :=
      Bits.slice 0 digest_sz v.

    Inductive fs_ips := ip_sha | ip_hmac.

    (* [ip_lat] is measured on external/glue over secworks/sha256_core -- 135
       and 269 cycles -- plus margin. *)
    Definition fs_ip (p: fs_ips) : ip_decl :=
      match p with
      | ip_sha  => {| ip_req_sz  := len_sz + msg_sz;
                      ip_resp_sz := digest_sz;
                      ip_lat     := 140;
                      ip_lat_pos := ltac:(lia);
                      ip_fn      := sha_f |}
      | ip_hmac => {| ip_req_sz  := len_sz + digest_sz + hmac_msg_sz;
                      ip_resp_sz := digest_sz;
                      ip_lat     := 275;
                      ip_lat_pos := ltac:(lia);
                      ip_fn      := hmac_f |}
      end.

    Definition fs_states_t := tf_states_type fs_states_size.

    Definition fs_states_init (x: fs_states) : (fs_states_t x) :=
    match x with
    | st_ps => Bits.zero
    | st_dp => Bits.zero
    | st_ak => Bits.zero
    | st_dig => Bits.zero
    | st_snap => Bits.zero
    | st_sig => Bits.zero
    end.

    (* The dispatcher (spec section 8; normative in 5.3.1): in failure mode every
       command but MARS_CapabilityGet answers MARS_RC_FAILURE, ahead of the
       unsupported-command check.  A platform fault at accept enters failure
       mode (5.6), checked under the public bit so failure-mode answers stay
       public. *)
    Definition guard_failure (body: @tf_ops fs_states fs_inputs fs_outputs fs_ips)
        : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
    {[
        if ($out_failure ==[1] #1) then
            let $out_rc := #MARS_RC_FAILURE
        else if ($in_fault ==[1] #1) then
            let $out_failure := #1;
            let $out_rc      := #MARS_RC_FAILURE
        else `body`
    ]}.
    (* PcrExtend hashes PCR[i] || in_dig -- 64 bytes -- left-aligned in the
       1024-bit port.  Two concatenations: the 512-bit message, then the
       zero padding out to the port width. *)
    Definition ext_msg (pcr: fs_outputs) : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 (tf_concat 512 512)
          (tf_op2 (tf_concat digest_sz digest_sz) (tf_ovar pcr) (tf_ivar in_dig))
          (tf_const 0).

    (* Profile, after 5.4: past the failure checks, every implemented MARS_CC
       command but MARS_CapabilityGet answers MARS_RC_VALUE until _MARS_Init
       COMPLETES, which also keeps every derivation off a zero DP.
       [in_init_req] authorises STARTING an initialization; [out_st] records
       that one finished. *)
    Definition guard_init (body: @tf_ops fs_states fs_inputs fs_outputs fs_ips)
        : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
    {[
        if ($out_st ==[1] #0)
        then let $out_rc := #MARS_RC_VALUE
        else `body`
    ]}.

    (* CryptSkdf's framing, pinned by the Profile from hw_sha2.c:
       HMAC(parent, [1]_4 || label || 0x00 || ctx || [8192]_4).  CryptDpInit
       takes parent = PS, label = MARS_LD 'D', ctx = "prd": 13 bytes,
       left-aligned in the 512-bit port.  Byte-sized constants keep
       [tf_const]'s unary nat small -- a 24-bit literal costs ~1s to elaborate. *)
    Definition dpinit_msg : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 (tf_concat 104 408)
          (tf_op2 (tf_concat 32 72) (tf_const 1)
            (tf_op2 (tf_concat 8 64) (tf_const MARS_LD)     (* 'D' *)
              (tf_op2 (tf_concat 8 56) (tf_const 0)
                (tf_op2 (tf_concat 8 48) (tf_const 112)     (* 'p' *)
                  (tf_op2 (tf_concat 8 40) (tf_const 114)   (* 'r' *)
                    (tf_op2 (tf_concat 8 32) (tf_const 100) (* 'd' *)
                      (tf_const 8192)))))))                 (* [L]_4, L = 8192 *)
          (tf_const 0).

    (* CryptSnapshot, spec section 5.6.9 / reference mars.c:
       regSelect (4 bytes, BIG ENDIAN) || REG[i] for each selected i || [tail].
       Four shapes over two PCRs, three lengths -- 36 / 68 / 68 / 100 bytes,
       left-aligned in the 1024-bit SHA port.  [tail] is Quote's nonce, or the
       ctx of Derive and DpDerive. *)
    Definition snap_none (tail: fs_inputs) : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 (tf_concat 288 736)
          (tf_op2 (tf_concat 32 256) (tf_ivar in_regsel) (tf_ivar tail))
          (tf_const 0).

    Definition snap_one (tail: fs_inputs) (pcr: fs_outputs)
        : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 (tf_concat 544 480)
          (tf_op2 (tf_concat 32 512) (tf_ivar in_regsel)
            (tf_op2 (tf_concat digest_sz digest_sz) (tf_ovar pcr) (tf_ivar tail)))
          (tf_const 0).

    Definition snap_both (tail: fs_inputs) : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 (tf_concat 800 224)
          (tf_op2 (tf_concat 32 768) (tf_ivar in_regsel)
            (tf_op2 (tf_concat digest_sz 512) (tf_ovar out_pcr0)
              (tf_op2 (tf_concat digest_sz digest_sz) (tf_ovar out_pcr1)
                (tf_ivar tail))))
          (tf_const 0).

    (* CryptSkdf's frame over a 32-byte [ctx] under a one-byte [label]: 42 bytes. *)
    Definition skdf_msg (label ctx: @tf_expr fs_states fs_inputs fs_outputs)
        : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 (tf_concat 336 176)
          (tf_op2 (tf_concat 32 304) (tf_const 1)
            (tf_op2 (tf_concat 8 296) label
              (tf_op2 (tf_concat 8 288) (tf_const 0)
                (tf_op2 (tf_concat digest_sz 32) ctx
                  (tf_const 8192)))))
          (tf_const 0).

    (* CryptXkdf is CryptSkdf in this Profile (5.6.7), over the host's [in_ctx]. *)
    Definition xkdf_msg (label: @tf_expr fs_states fs_inputs fs_outputs)
        : @tf_expr fs_states fs_inputs fs_outputs :=
        skdf_msg label (tf_ivar in_ctx).

    (* CryptSign's message for Quote: the 32-byte snapshot, left-aligned. *)
    Definition sign_msg : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 (tf_concat digest_sz 256) (tf_svar st_snap) (tf_const 0).

    (* CryptSign's message for Sign and SignatureVerify: the host's digest. *)
    Definition dig_msg : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 (tf_concat digest_sz 256) (tf_ivar in_dig) (tf_const 0).

    (* SignatureVerify's label (8.5.3): 'R' for a restricted key, else 'U'. *)
    Definition vfy_label : @tf_expr fs_states fs_inputs fs_outputs :=
        {[ if ($in_restricted ==[1] #1) then #MARS_LR else #MARS_LU ]}.

    (* A 256-bit constant, most significant byte first; byte-sized [tf_const]s
       keep the unary nat small. *)
    Fixpoint bytes_be (bs: list nat) : @tf_expr fs_states fs_inputs fs_outputs :=
        match bs with
        | []        => tf_const 0
        | [b]       => tf_const b
        | b :: rest => tf_op2 (tf_concat 8 (8 * List.length rest))
                              (tf_const b) (bytes_be rest)
        end.

    (* CryptSelfTest's known answers (5.6.1), one per IP, at lengths the commands
       use: SHA-256 over 64 zero bytes, HMAC-SHA256 under a zero key over 32
       zero bytes. *)
    Definition kat_sha : @tf_expr fs_states fs_inputs fs_outputs := bytes_be
      [0xf5; 0xa5; 0xfd; 0x42; 0xd1; 0x6a; 0x20; 0x30; 0x27; 0x98; 0xef; 0x6e;
       0xd3; 0x09; 0x97; 0x9b; 0x43; 0x00; 0x3d; 0x23; 0x20; 0xd9; 0xf0; 0xe8;
       0xea; 0x98; 0x31; 0xa9; 0x27; 0x59; 0xfb; 0x4b].
    Definition kat_hmac : @tf_expr fs_states fs_inputs fs_outputs := bytes_be
      [0x33; 0xad; 0x0a; 0x1c; 0x60; 0x7e; 0xc0; 0x3b; 0x09; 0xe6; 0xcd; 0x98;
       0x93; 0x68; 0x0c; 0xe2; 0x10; 0xad; 0xf3; 0x00; 0xaa; 0x1f; 0x26; 0x60;
       0xe1; 0xb2; 0x2e; 0x10; 0xf1; 0x70; 0xf9; 0x2a].

    (* A request is one word, so [ip_req_sz] is one number and the IP glue
       unpacks: SHA takes [len || msg], HMAC [len || key || msg].  [len] is an
       expression because message shapes differ in length. *)
    Definition call_sha (dst: fs_states)
                        (len msg: @tf_expr fs_states fs_inputs fs_outputs)
        : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
      tf_ops_base (tf_call ip_sha dst
        (tf_op2 (tf_concat len_sz msg_sz) len msg)).

    Definition call_hmac (dst: fs_states)
                         (len key msg: @tf_expr fs_states fs_inputs fs_outputs)
        : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
      tf_ops_base (tf_call ip_hmac dst
        (tf_op2 (tf_concat len_sz (digest_sz + hmac_msg_sz)) len
          (tf_op2 (tf_concat digest_sz hmac_msg_sz) key msg))).

    (* CryptDpInit (5.6.8): DP := CryptSkdf(PS, 'D', "prd"). *)
    Definition dp_init : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
        call_hmac st_dp (tf_const 13) (tf_svar st_ps) dpinit_msg.

    (* CryptSnapshot over [tail] into [st_snap], then [k].  Callers answer
       MARS_RC_REG for regSelect > 3 first, so the last arm is regSelect = 3. *)
    Definition with_snapshot (tail: fs_inputs)
                             (k: @tf_ops fs_states fs_inputs fs_outputs fs_ips)
        : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
    {[
        if ($in_regsel ==[32] #0) then
            `call_sha st_snap (tf_const 36) (snap_none tail)`; `k`
        else if ($in_regsel ==[32] #1) then
            `call_sha st_snap (tf_const 68) (snap_one tail out_pcr0)`; `k`
        else if ($in_regsel ==[32] #2) then
            `call_sha st_snap (tf_const 68) (snap_one tail out_pcr1)`; `k`
        else
            `call_sha st_snap (tf_const 100) (snap_both tail)`; `k`
    ]}.

    (* CryptXkdf(key, DP, label, ctx) into [st_ak], then CryptSign(key, msg)
       into [st_sig]. *)
    Definition xkdf_sign (label msg: @tf_expr fs_states fs_inputs fs_outputs)
        : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
    {[
        `call_hmac st_ak  (tf_const 42) (tf_svar st_dp) (xkdf_msg label)`;
        `call_hmac st_sig (tf_const 32) (tf_svar st_ak) msg`
    ]}.

    (* Zeroes the leaf state [st_ak] and [st_sig] as the command ends (5.5,
       p.15).  The last HMAC request and its answer stay on the internal IP
       link, a Secret port pair, until the next HMAC call replaces them. *)
    Definition forget_leaves : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
    {[
        let $st_ak  := #0;
        let $st_sig := #0
    ]}.

    Definition quote_sign : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
    {[
        `xkdf_sign (tf_const MARS_LR) sign_msg`;
        let $out_snap := $st_snap;
        let $out_dout := $st_sig;
        let $out_rc   := #MARS_RC_SUCCESS;
        `forget_leaves`
    ]}.

    (* MARS_Derive's tail: CryptSkdf(DP, 'X', snapshot) out to the host. *)
    Definition derive_x : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
    {[
        `call_hmac st_sig (tf_const 42) (tf_svar st_dp)
                   (skdf_msg (tf_const MARS_LX) (tf_svar st_snap))`;
        let $out_dout := $st_sig;
        let $out_rc   := #MARS_RC_SUCCESS;
        `forget_leaves`
    ]}.

    (* MARS_DpDerive's tail: DP := CryptSkdf(DP, 'D', snapshot). *)
    Definition dp_extend : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
    {[
        `call_hmac st_dp (tf_const 42) (tf_svar st_dp)
                   (skdf_msg (tf_const MARS_LD) (tf_svar st_snap))`;
        let $out_rc := #MARS_RC_SUCCESS
    ]}.

    Definition unsupported : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
        guard_failure {[ let $out_rc := #MARS_RC_COMMAND ]}.

    (* An output HOLDS its value until an action writes it, so every command
       first clears the RESULT registers.  The other outputs carry device state
       across commands. *)
    Definition clear_results (body: @tf_ops fs_states fs_inputs fs_outputs fs_ips)
        : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
    {[
        let $out_dout   := #0;
        let $out_cap    := #0;
        let $out_result := #0;
        `body`
    ]}.

    (* One arm per command code; [fs_transitions] below wraps it for the scheduler. *)
    Definition fs_command
        (act: fs_action)
        :
        (@tf_ops fs_states fs_inputs fs_outputs fs_ips)
        :=
        match act with

        (* MARS_SelfTest -- spec section 8.1.1: failure = failure || !CryptSelfTest.
           Each call runs every test (5.6.1), so [fullTest] is implied; a
           mismatch enters failure mode until _MARS_Init (5.3.1). *)
        | act_selftest =>
            guard_failure (guard_init {[
                `call_sha  st_dig (tf_const 64) (tf_const 0)`;
                `call_hmac st_sig (tf_const 32) (tf_const 0) (tf_const 0)`;
                if (($st_dig !=[digest_sz] `kat_sha`) | ($st_sig !=[digest_sz] `kat_hmac`)) then
                    let $out_failure := #1;
                    let $out_rc      := #MARS_RC_FAILURE
                else
                    let $out_rc := #MARS_RC_SUCCESS
            ]})

        (* MARS_CapabilityGet -- spec section 8.1.2.  Section 5.3.1 exempts it
           from failure mode, so it runs unguarded.  All eleven Table 6 tags,
           then MARS_RC_VALUE. *)
        | act_capabilityget =>
            {[
                if ($in_pt ==[arg_sz] #MARS_PT_PCR) then
                    let $out_cap := #PROFILE_COUNT_PCR;
                    let $out_rc  := #MARS_RC_SUCCESS
                else if ($in_pt ==[arg_sz] #MARS_PT_TSR) then
                    let $out_cap := #PROFILE_COUNT_TSR;
                    let $out_rc  := #MARS_RC_SUCCESS
                else if ($in_pt ==[arg_sz] #MARS_PT_LEN_DIGEST) then
                    let $out_cap := #PROFILE_LEN_DIGEST;
                    let $out_rc  := #MARS_RC_SUCCESS
                else if ($in_pt ==[arg_sz] #MARS_PT_LEN_SIGN) then
                    let $out_cap := #PROFILE_LEN_SIGN;
                    let $out_rc  := #MARS_RC_SUCCESS
                else if ($in_pt ==[arg_sz] #MARS_PT_LEN_KSYM) then
                    let $out_cap := #PROFILE_LEN_KSYM;
                    let $out_rc  := #MARS_RC_SUCCESS
                else if ($in_pt ==[arg_sz] #MARS_PT_LEN_KPUB) then
                    let $out_cap := #PROFILE_LEN_KPUB;
                    let $out_rc  := #MARS_RC_SUCCESS
                else if ($in_pt ==[arg_sz] #MARS_PT_LEN_KPRV) then
                    let $out_cap := #PROFILE_LEN_KPRV;
                    let $out_rc  := #MARS_RC_SUCCESS
                else if ($in_pt ==[arg_sz] #MARS_PT_ALG_HASH) then
                    let $out_cap := #PROFILE_ALG_HASH;
                    let $out_rc  := #MARS_RC_SUCCESS
                else if ($in_pt ==[arg_sz] #MARS_PT_ALG_SIGN) then
                    let $out_cap := #PROFILE_ALG_SIGN;
                    let $out_rc  := #MARS_RC_SUCCESS
                else if ($in_pt ==[arg_sz] #MARS_PT_ALG_SKDF) then
                    let $out_cap := #PROFILE_ALG_SKDF;
                    let $out_rc  := #MARS_RC_SUCCESS
                else if ($in_pt ==[arg_sz] #MARS_PT_ALG_AKDF) then
                    let $out_cap := #PROFILE_ALG_AKDF;
                    let $out_rc  := #MARS_RC_SUCCESS
                else
                    let $out_rc := #MARS_RC_VALUE
            ]}

        (* MARS_RegRead -- spec section 8.3.2.  An out-of-range index gives
           MARS_RC_REG (7) and [out_dout] reads zero from [clear_results].  The
           host contract either way: check out_rc before using out_dout. *)
        | act_regread =>
            guard_failure (guard_init {[
                if ($in_idx ==[arg_sz] #0) then
                    let $out_dout := $out_pcr0;
                    let $out_rc   := #MARS_RC_SUCCESS
                else if ($in_idx ==[arg_sz] #1) then
                    let $out_dout := $out_pcr1;
                    let $out_rc   := #MARS_RC_SUCCESS
                else
                    let $out_rc := #MARS_RC_REG
            ]})

        (* MARS_PcrExtend -- spec section 8.3.1.  ONE action: build PCR[i] ||
           in_dig, call SHA, write the answer back to the PCR. *)
        | act_pcrextend =>
            guard_failure (guard_init {[
                if ($in_idx ==[arg_sz] #0) then
                    `call_sha st_dig (tf_const 64) (ext_msg out_pcr0)`;
                    let $out_pcr0 := $st_dig;
                    let $out_rc   := #MARS_RC_SUCCESS
                else if ($in_idx ==[arg_sz] #1) then
                    `call_sha st_dig (tf_const 64) (ext_msg out_pcr1)`;
                    let $out_pcr1 := $st_dig;
                    let $out_rc   := #MARS_RC_SUCCESS
                else
                    let $out_rc := #MARS_RC_REG
            ]})
        (* _MARS_Init -- spec section 5.4.  Gated on [in_init_req], which the
           platform drives (section 5.8), and it runs unguarded because it is
           what clears failure mode.  The DP derivation is a call. *)
        | act_init =>
            {[
                if ($in_init_req ==[1] #1) then
                    let $st_ps          := $in_ps;
                    let $out_failure    := #0;
                    let $out_pcr0       := #0;
                    let $out_pcr1       := #0;
                    (* statement order is sequential, so [st_ps] reads the seed assigned above *)
                    `dp_init`;
                    (* the last step of the reset sequence: DP is valid from here *)
                    let $st_ak  := #0;
                    let $out_st := #1;
                    let $out_rc := #MARS_RC_SUCCESS
                else
                    let $out_rc := #MARS_RC_VALUE
            ]}

        (* Sequence primitives, spec section 8.2: outside this Profile. *)
        | act_sequencehash     => unsupported
        | act_sequenceupdate   => unsupported
        | act_sequencecomplete => unsupported

        (* MARS_Derive -- spec section 8.4.1: REG, then BUFFER (the Profile's
           ctx is 32 bytes), then CryptSkdf(DP, 'X', snapshot over ctx). *)
        | act_derive =>
            guard_failure (guard_init {[
                if ($in_regsel >[32] #3) then
                    let $out_rc := #MARS_RC_REG
                else if ($in_ctxlen !=[arg_sz] #32) then
                    let $out_rc := #MARS_RC_BUFFER
                else
                    `with_snapshot in_ctx derive_x`
            ]})

        (* MARS_DpDerive -- spec section 8.4.2: REG first.  Profile: ctxlen 0
           stands for a NULL ctx, which resets DP through CryptDpInit (5.6.8);
           ctxlen 32 extends DP over the snapshot; any other length is BUFFER. *)
        | act_dpderive =>
            guard_failure (guard_init {[
                if ($in_regsel >[32] #3) then
                    let $out_rc := #MARS_RC_REG
                else if ($in_ctxlen ==[arg_sz] #0) then
                    `dp_init`;
                    let $out_rc := #MARS_RC_SUCCESS
                else if ($in_ctxlen !=[arg_sz] #32) then
                    let $out_rc := #MARS_RC_BUFFER
                else
                    `with_snapshot in_ctx dp_extend`
            ]})

        (* MARS_PublicRead -- Table 5 makes it mandatory where CryptAkdf exists; this
           symmetric Profile answers MARS_RC_COMMAND. *)
        | act_publicread       => unsupported

        (* MARS_Quote -- spec section 8.5.1: REG, then BUFFER (the Profile's
           nonce and ctx are 32 bytes each).  Three round trips in one action:
           snap = SHA(regSelect || REGs || nonce), AK = HMAC(DP, kdf frame),
           sig = HMAC(AK, snap) -- the sequenced and chained cases at once. *)
        | act_quote =>
            guard_failure (guard_init {[
                if ($in_regsel >[32] #3) then
                    let $out_rc := #MARS_RC_REG
                else if (($in_nlen !=[arg_sz] #32) | ($in_ctxlen !=[arg_sz] #32)) then
                    let $out_rc := #MARS_RC_BUFFER
                else
                    `with_snapshot in_nonce quote_sign`
            ]})

        (* MARS_Sign -- spec section 8.5.2: key = CryptXkdf(DP, 'U', ctx), then
           sig = HMAC(key, dig) over the host's digest. *)
        | act_sign =>
            guard_failure (guard_init {[
                if ($in_ctxlen !=[arg_sz] #32) then
                    let $out_rc := #MARS_RC_BUFFER
                else
                    `xkdf_sign (tf_const MARS_LU) dig_msg`;
                    let $out_dout := $st_sig;
                    let $out_rc   := #MARS_RC_SUCCESS;
                    `forget_leaves`
            ]})

        (* MARS_SignatureVerify -- spec section 8.5.3.  The label is a mux inside
           the KDF frame, so both key kinds share one round trip; CryptVerify
           recomputes the MAC, and the 1-bit verdict is all that leaves. *)
        | act_signatureverify =>
            guard_failure (guard_init {[
                if ($in_ctxlen !=[arg_sz] #32) then
                    let $out_rc := #MARS_RC_BUFFER
                else
                    `xkdf_sign vfy_label dig_msg`;
                    let $out_result := ($st_sig ==[digest_sz] $in_sig);
                    let $out_rc     := #MARS_RC_SUCCESS;
                    `forget_leaves`
            ]})
        end.

    Definition fs_transitions (act: fs_action)
        : (@tf_ops fs_states fs_inputs fs_outputs fs_ips) :=
        clear_results (fs_command act).

    Definition fs_step := tf_ops_run fs_states_size fs_inputs_size fs_outputs_size no_ips.

End FunctionalSpecification.

Section Instance.

    Variable sha_f  : bits_t (len_sz + msg_sz) -> bits_t digest_sz.
    Variable hmac_f : bits_t (len_sz + digest_sz + hmac_msg_sz) -> bits_t digest_sz.

    Definition tfs_ctx : TFSchedContext := {|
        tfs_spec_states := fs_states;
        tfs_spec_states_fin := _;
        tfs_spec_states_size := fs_states_size;
        tfs_spec_states_init := fs_states_init;

        tfs_spec_inputs := fs_inputs;
        tfs_spec_inputs_fin := _;
        tfs_spec_inputs_size := fs_inputs_size;
        tfs_spec_inputs_class := fs_inputs_class;
        tfs_spec_outputs := fs_outputs;
        tfs_spec_outputs_fin := _;
        tfs_spec_outputs_size := fs_outputs_size;
        tfs_spec_outputs_class := fs_outputs_class;
        tfs_spec_action := fs_action;
        tfs_spec_action_fin := _;
        tfs_spec_action_ops := fs_transitions;

        tfs_spec_ips := fs_ips;
        tfs_spec_ips_fin := _;
        tfs_spec_ip := fs_ip sha_f hmac_f;

        (* Pinned empty: one unsound declassification rule unbalances a
           secret-dependent phi. *)
        tfs_spec_decls := []
    |}.

    (* The call structure, per command: SHA drives, HMAC drives, and the
       deepest target cycle, which the success path sets.  A round trip lives
       inside the command that needs it, one per payload choice. *)
    Definition n_calls (a: fs_action) (p: fs_ips) : nat :=
      List.length (drive_nodes tfs_ctx (build_dfg tfs_ctx a) p).
    Definition call_depth (a: fs_action) : nat :=
      fold_left (fun m p => Nat.max m (snd p))
        (calc_target_cycle 40 (calc_backward_cost tfs_ctx 40 (build_dfg tfs_ctx a))) 0.

    (* One arm per snapshot shape on disjoint guards: 550 = max(140, 275) + 275,
       the snapshot SHA overlapping the AK derivation. *)
    Example quote_shape :
      (n_calls act_quote ip_sha, n_calls act_quote ip_hmac, call_depth act_quote) = (4, 8, 550).
    Proof. vm_compute. reflexivity. Qed.

    (* 550 = 275 + 275: the signing key, then the MAC under it *)
    Example sign_shape :
      (n_calls act_sign ip_sha, n_calls act_sign ip_hmac, call_depth act_sign) = (0, 2, 550).
    Proof. vm_compute. reflexivity. Qed.

    Example verify_shape :
      (n_calls act_signatureverify ip_sha, n_calls act_signatureverify ip_hmac,
       call_depth act_signatureverify) = (0, 2, 550).
    Proof. vm_compute. reflexivity. Qed.

    (* 415 = 140 + 275: the snapshot, then the derivation over it *)
    Example derive_shape :
      (n_calls act_derive ip_sha, n_calls act_derive ip_hmac, call_depth act_derive) = (4, 4, 415).
    Proof. vm_compute. reflexivity. Qed.

    (* the four extend arms plus the CryptDpInit arm *)
    Example dpderive_shape :
      (n_calls act_dpderive ip_sha, n_calls act_dpderive ip_hmac, call_depth act_dpderive) = (4, 5, 415).
    Proof. vm_compute. reflexivity. Qed.

    (* 275 = max(140, 275): the two known-answer tests overlap *)
    Example selftest_shape :
      (n_calls act_selftest ip_sha, n_calls act_selftest ip_hmac, call_depth act_selftest) = (1, 1, 275).
    Proof. vm_compute. reflexivity. Qed.

    (* one arm per index *)
    Example ext_shape :
      (n_calls act_pcrextend ip_sha, n_calls act_pcrextend ip_hmac, call_depth act_pcrextend) = (2, 0, 140).
    Proof. vm_compute. reflexivity. Qed.

    Example init_shape :
      (n_calls act_init ip_sha, n_calls act_init ip_hmac, call_depth act_init) = (0, 1, 275).
    Proof. vm_compute. reflexivity. Qed.

    (* RegRead is crypto-free: zero drives on either IP *)
    Example regread_shape :
      (n_calls act_regread ip_sha, n_calls act_regread ip_hmac) = (0, 0).
    Proof. vm_compute. reflexivity. Qed.

    Definition tf_schedule := tfs_schedule tfs_ctx 10.

    Definition tf_ctx : TFSynthContext := {|
        tf_sched_ctx := tf_schedule;

        tf_action_encoding := fs_action_encoding;
        tf_action_encoding_inj := fs_action_encoding_inj;
    |}.

  Definition package := Lowering.package tf_ctx "Example_MarsV2".

End Instance.

(* Extraction, with [placeholder_digest] standing in for both IP functions. *)

Definition prog :=
  Interop.Backends.register (package (@placeholder_digest _) (@placeholder_digest _)).
Set Extraction Output Directory "build".
Extraction "Example_MarsV2.ml" prog.
