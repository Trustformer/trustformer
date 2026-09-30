Require Import Koika.Frontend.
Require Import Koika.Std.
Require Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.TypedSynthesis.
Require Import Trustformer.Scheduler.Contract.
Require Import Trustformer.Scheduler.VariableScheduler.

Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

(* A minimal TCG MARS device, Profile [TF-MARS-S256-P2], over two PCRs.  One
   command = one action: a crypto round trip is a [tf_call] inside the command
   that needs it.  Every MARS_CC code has an arm, so [out_rc] is always written
   (REVIEW.md 3.4).  Sources: spec/mars-library-v1r14.md 5.3.1, 8.1.2, 8.3.2;
   reference-emulator/c/mars.c and mars.h. *)

Section FunctionalSpecification.

    Definition digest_sz := 256.        (* PROFILE_LEN_DIGEST = 32 bytes *)
    Definition arg_sz    := 16.
    Definition rc_sz     := 16.
    Definition msg_sz    := 1024.       (* widest MARS message: the 100-byte snapshot *)


    Definition hmac_msg_sz := 512.      (* longest HMAC message: the 42-byte KDF frame *)
    Definition len_sz      := 16.       (* the byte length that rides with a request *)


    (* Key-derivation labels, spec section 5.5.  The label is the ONLY thing
       separating a restricted attestation key from an unrestricted signing
       key, which is why the framing stays inside the verified module. *)
    Definition MARS_LD := 68.   (* 'D' -- DP from PS *)
    Definition MARS_LR := 82.   (* 'R' -- restricted AK, used by Quote *)

    (* Table 4 response codes (spec section 6.2). *)
    Definition MARS_RC_SUCCESS := 0.
    Definition MARS_RC_FAILURE := 2.
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

    (* The Profile itself (MVP.md section 2).  Symmetric only, so ALG_AKDF is
       TPM_ALG_ERROR, both asymmetric key lengths are zero, and MARS_PublicRead
       falls outside it. *)
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
    | st_ak
    (* Destinations for a [tf_call]: a call writes a STATE var, and two calls in
       one action need two of them. *)
    | st_dig           (* a SHA result: the extended PCR *)
    | st_snap          (* MARS_Quote: the device snapshot *)
    | st_sig           (* MARS_Quote: the signature *)
    .

    Inductive fs_inputs :=
    | in_pt            (* MARS_CapabilityGet: property tag        *)
    | in_idx           (* MARS_RegRead / MARS_PcrExtend: index    *)
    | in_dig           (* MARS_PcrExtend: the digest to extend    *)

    (* Platform-driven, so both are [Secret], which delivers "never bus-mapped"
       (spec section 5.8).  [in_ps] is the Primary Seed. *)
    | in_ps
    | in_init_req
    (* MARS_Quote *)
    | in_regsel
    | in_nonce
    | in_ctx
    | in_nlen
    | in_ctxlen
    .

    (* PCRs are OUTPUT variables: MARS_RegRead hands them out, and Public keeps
       the Quote datapath untainted.  MVP.md section 6.1. *)
    Inductive fs_outputs :=
    (* Public: results *)
    | out_rc
    | out_cap
    | out_dout
    (* Public: device state *)
    | out_pcr0
    | out_pcr1
    | out_failure

    | out_st         (* 0 = uninitialized, 1 = DP is valid       *)
    | out_snap       (* MARS_Quote: the device snapshot           *)
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
    end.

    Definition fs_outputs_size (x: fs_outputs) : nat :=
    match x with
    | out_rc        => rc_sz
    | out_cap       => 16
    | out_dout      => digest_sz
    | out_pcr0      => digest_sz
    | out_pcr1      => digest_sz
    | out_failure   => 1

    | out_st        => 1
    | out_snap      => digest_sz
    end.

    (* Confidentiality classification (Contract.v [port_class]).  [Secret] means
       "outside what the guarantee quantifies over, so it may carry a secret and
       stays off the memory map"; the guarantee is about which ports it COVERS.
       An IP link is a port of neither side, so DP and AK cross no declared
       port.  Spec section 5.8. *)
    Definition fs_inputs_class (x: fs_inputs) : port_class :=
    match x with
    | in_pt | in_idx | in_dig                            => Public
    | in_ps | in_init_req                                => Secret
    (* Quote's arguments are the host's own. *)
    | in_regsel | in_nonce | in_ctx | in_nlen | in_ctxlen => Public
    end.

    Definition fs_outputs_class (x: fs_outputs) : port_class :=
    match x with
    (* handshake bits an observer could see on the bus edge anyway *)
    | out_rc | out_cap | out_dout | out_pcr0 | out_pcr1 | out_failure
    | out_st | out_snap => Public
    end.

    (* The two attached IPs.  A request is ONE word, so a multi-field request is
       packed: SHA takes [len || msg], HMAC takes [len || key || msg].  [ip_fn]
       is the spec's claim about what the block computes; the circuit samples
       the wire, so the placeholder below is marked as one.  Proving a call
       computes the right thing is a separate lemma, deferred. *)
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
                      ip_fn      := placeholder_digest |}
      | ip_hmac => {| ip_req_sz  := len_sz + digest_sz + hmac_msg_sz;
                      ip_resp_sz := digest_sz;
                      ip_lat     := 275;
                      ip_lat_pos := ltac:(lia);
                      ip_fn      := placeholder_digest |}
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

    (* The dispatcher's out_failure-mode rule (spec section 8, informative comment;
       normative in section 5.3.1): in out_failure mode every command except
       MARS_CapabilityGet returns MARS_RC_FAILURE, and it does so BEFORE the
       unsupported-command check. *)
    Definition guard_failure (body: @tf_ops fs_states fs_inputs fs_outputs fs_ips)
        : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
    {[
        if ($out_failure ==[1] #1)
        then let $out_rc := #MARS_RC_FAILURE
        else `body`
    ]}.
    (* PcrExtend hashes PCR[i] || in_dig -- 64 bytes -- left-aligned in the
       1024-bit port.  Two concatenations: the 512-bit message, then the
       zero padding out to the port width. *)
    Definition ext_msg (pcr: fs_outputs) : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 (tf_concat 512 512)
          (tf_op2 (tf_concat digest_sz digest_sz) (tf_ovar pcr) (tf_ivar in_dig))
          (tf_const 0).

    (* Commands are refused until _MARS_Init COMPLETES, which keeps MARS_Quote
       from deriving AK = KDF(0,'R',ctx) off a zero DP (REVIEW.md section 2.2).
       [in_init_req] authorises STARTING an initialization; [out_st] records
       that one finished (MVP.md section 2.2 deviation 3).  MARS_CapabilityGet
       is exempt: every value it returns is a Profile constant. *)
    Definition guard_init (body: @tf_ops fs_states fs_inputs fs_outputs fs_ips)
        : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
    {[
        if ($out_st ==[1] #0)
        then let $out_rc := #MARS_RC_VALUE
        else `body`
    ]}.

    (* CryptSkdf's framing, pinned by the Profile from hw_sha2.c (MVP.md 2):
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
       regSelect (4 bytes, BIG ENDIAN) || REG[i] for each selected i || nonce.
       The Profile pins the endianness (MVP.md section 2).  Four shapes over two
       PCRs, three lengths -- 36 / 68 / 68 / 100 bytes, left-aligned in the
       1024-bit SHA port.  The trailing field is the NONCE. *)
    Definition snap_none : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 (tf_concat 288 736)
          (tf_op2 (tf_concat 32 256) (tf_ivar in_regsel) (tf_ivar in_nonce))
          (tf_const 0).

    Definition snap_one (pcr: fs_outputs) : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 (tf_concat 544 480)
          (tf_op2 (tf_concat 32 512) (tf_ivar in_regsel)
            (tf_op2 (tf_concat digest_sz digest_sz) (tf_ovar pcr) (tf_ivar in_nonce)))
          (tf_const 0).

    Definition snap_both : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 (tf_concat 800 224)
          (tf_op2 (tf_concat 32 768) (tf_ivar in_regsel)
            (tf_op2 (tf_concat digest_sz 512) (tf_ovar out_pcr0)
              (tf_op2 (tf_concat digest_sz digest_sz) (tf_ovar out_pcr1)
                (tf_ivar in_nonce))))
          (tf_const 0).

    (* The AK derivation frame: [dpinit_msg]'s CryptSkdf shape over a 32-byte
       [in_ctx].  42 bytes. *)

    Definition ak_kdf_msg : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 (tf_concat 336 176)
          (tf_op2 (tf_concat 32 304) (tf_const 1)
            (tf_op2 (tf_concat 8 296) (tf_const MARS_LR)
              (tf_op2 (tf_concat 8 288) (tf_const 0)
                (tf_op2 (tf_concat digest_sz 32) (tf_ivar in_ctx)
                  (tf_const 8192)))))
          (tf_const 0).

    (* CryptSign's message: the 32-byte snapshot the SHA call wrote, left-aligned. *)
    Definition sign_msg : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 (tf_concat digest_sz 256) (tf_svar st_snap) (tf_const 0).

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

    Definition quote_sign : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
    {[
        `call_hmac st_ak  (tf_const 42) (tf_svar st_dp) ak_kdf_msg`;
        `call_hmac st_sig (tf_const 32) (tf_svar st_ak) sign_msg`;
        let $out_snap := $st_snap;
        let $out_dout := $st_sig;
        let $out_rc   := #MARS_RC_SUCCESS
    ]}.

    Definition unsupported : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
        guard_failure {[ let $out_rc := #MARS_RC_COMMAND ]}.

    (* An output HOLDS its value until an action writes it, so a Quote's
       signature would keep driving 256 wires until the next RegRead.  Every
       command clears the RESULT registers first.  The scope is exactly these
       two: [out_pcr0]/[out_pcr1]/[out_failure]/[out_st] carry device state
       across commands (MVP.md section 6.1).  Costs +1 node on CapabilityGet. *)
    Definition clear_results (body: @tf_ops fs_states fs_inputs fs_outputs fs_ips)
        : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
    {[
        let $out_dout := #0;
        let $out_cap  := #0;
        `body`
    ]}.

    (* One arm per command code; [fs_transitions] below wraps it for the scheduler. *)
    Definition fs_command
        (act: fs_action)
        :
        (@tf_ops fs_states fs_inputs fs_outputs fs_ips)
        :=
        match act with

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
                    (* Statement order is sequential (REVIEW.md section 4), so
                       [st_ps] reads the seed assigned above. *)
                    `call_hmac st_dp (tf_const 13) (tf_svar st_ps) dpinit_msg`;
                    (* the last step of the reset sequence: DP is valid from here *)
                    let $st_ak  := #0;
                    let $out_st := #1;
                    let $out_rc := #MARS_RC_SUCCESS
                else
                    let $out_rc := #MARS_RC_VALUE
            ]}

        | act_selftest         => unsupported
        | act_sequencehash     => unsupported
        | act_sequenceupdate   => unsupported
        | act_sequencecomplete => unsupported
        | act_derive           => unsupported
        | act_dpderive         => unsupported
        | act_publicread       => unsupported
        (* MARS_Quote -- spec section 8.5.1.  Three round trips in one action:
           snap = SHA(regSelect || REGs || nonce), AK = HMAC(DP, kdf frame),
           sig = HMAC(AK, snap) -- the sequenced and chained cases at once.
           regSelect picks the snapshot's SHAPE inside the payload, so one SHA
           call covers all four arms. *)
        | act_quote =>
            guard_failure (guard_init {[
                if ($in_nlen !=[arg_sz] #32) then
                    let $out_rc := #MARS_RC_VALUE
                else if ($in_ctxlen !=[arg_sz] #32) then
                    let $out_rc := #MARS_RC_VALUE
                else if ($in_regsel ==[32] #0) then
                    `call_sha st_snap (tf_const 36) snap_none`; `quote_sign`
                else if ($in_regsel ==[32] #1) then
                    `call_sha st_snap (tf_const 68) (snap_one out_pcr0)`; `quote_sign`
                else if ($in_regsel ==[32] #2) then
                    `call_sha st_snap (tf_const 68) (snap_one out_pcr1)`; `quote_sign`
                else if ($in_regsel ==[32] #3) then
                    `call_sha st_snap (tf_const 100) snap_both`; `quote_sign`
                else
                    (* regSelect reaches past PROFILE_COUNT_REG -- mars.c *)
                    let $out_rc := #MARS_RC_REG
            ]})
        | act_sign             => unsupported
        | act_signatureverify  => unsupported
        end.

    Definition fs_transitions (act: fs_action)
        : (@tf_ops fs_states fs_inputs fs_outputs fs_ips) :=
        clear_results (fs_command act).

    Definition fs_step := tf_ops_run fs_states_size fs_inputs_size fs_outputs_size no_ips.

End FunctionalSpecification.

Section TypedSynthesis.

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
        tfs_spec_ip := fs_ip;

        (* Pinned empty: one unsound declassification rule unbalances a
           secret-dependent phi.  REVIEW.md section 4. *)
        tfs_spec_decls := []
    |}.

    (* The call structure, per command: a round trip lives inside the command
       that needs it, at one round trip per payload choice. *)
    Definition qdfg := build_dfg tfs_ctx act_quote.
    (* One arm per snapshot shape, so four SHA drives on disjoint guards;
       [quote_depth] pins the depth they add up to. *)
    Example quote_four_sha  : List.length (drive_nodes tfs_ctx qdfg ip_sha)  = 4.
    Proof. vm_compute. reflexivity. Qed.
    Example quote_eight_hmac : List.length (drive_nodes tfs_ctx qdfg ip_hmac) = 8.
    Proof. vm_compute. reflexivity. Qed.

    (* Disjoint guards keep the four arms at one round trip:
       550 = max(140, 275) + 275, the snapshot SHA overlapping the AK
       derivation, with only the signature waiting for both. *)
    Definition qcycles := calc_target_cycle 40 (calc_backward_cost tfs_ctx 40 qdfg).
    Example quote_depth :
      fold_left (fun a p => Nat.max a (snd p)) qcycles 0 = 550.
    Proof. vm_compute. reflexivity. Qed.

    (* one arm per index *)
    Definition edfg := build_dfg tfs_ctx act_pcrextend.
    Example ext_two_sha : List.length (drive_nodes tfs_ctx edfg ip_sha)  = 2.
    Proof. vm_compute. reflexivity. Qed.
    Example ext_no_hmac : List.length (drive_nodes tfs_ctx edfg ip_hmac) = 0.
    Proof. vm_compute. reflexivity. Qed.

    Definition idfg := build_dfg tfs_ctx act_init.
    Example init_one_hmac : List.length (drive_nodes tfs_ctx idfg ip_hmac) = 1.
    Proof. vm_compute. reflexivity. Qed.

    (* a crypto-free command asks for nothing *)
    Definition rdfg := build_dfg tfs_ctx act_regread.
    Example regread_no_calls :
      List.length (drive_nodes tfs_ctx rdfg ip_sha)
      + List.length (drive_nodes tfs_ctx rdfg ip_hmac) = 0.
    Proof. vm_compute. reflexivity. Qed.

    Definition tf_schedule := tfs_schedule tfs_ctx 10.

    Definition tf_ctx : TFSynthContext := {|
        tf_sched_ctx := tf_schedule;

        tf_action_encoding := fs_action_encoding;
        tf_action_encoding_inj := fs_action_encoding_inj;
    |}.

  Definition package := TypedSynthesis.package tf_ctx "Example_Mars".

End TypedSynthesis.

(* Extraction *)

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Example_Mars.ml" prog.
