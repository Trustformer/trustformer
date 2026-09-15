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

(*
    ONE COMMAND = ONE ACTION.  A crypto round trip is a [tf_call] inside the
    command that needs it, so MARS_Continue is gone and with it out_pend, the
    request/active/tag handshake bits and the crypto port groups.  The
    sequential design it replaces is Examples/MarsSeq.v, which the oracle
    validated and which this is checked against.

    A minimal TCG MARS device, Profile [TF-MARS-S256-P2].

    STAGE 1 of agents/mars/MVP.md section 8: the two crypto-free commands,
    [MARS_CapabilityGet] and [MARS_RegRead], over two PCRs.  Every other
    MARS_CC code has an explicit arm returning MARS_RC_COMMAND -- an
    unrecognized code fires no rule, and [out_rc] would then retain the previous
    command's value (REVIEW.md section 3.4).

    Normative sources: spec/mars-library-v1r14.md sections 5.3.1, 8.1.2, 8.3.2;
    reference-emulator/c/mars.c and mars.h.
 *)

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
       TPM_ALG_ERROR and both asymmetric key lengths are zero, which is what
       excludes MARS_PublicRead. *)
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
       specification's; MARS_Init and MARS_Continue take Profile-declared codes
       >= 13 and arrive in Stage 2. *)
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
    (* 0xFFFF, deliberately not adjacent to the 0..12 range: MARS_Init is a
       PERMANENT Profile command and never has to be renumbered. *)
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

    (* Secrets.  Unused in Stage 1: PS arrives at Init and DP/AK are derived by
       the crypto port, both of which are Stage 2 onwards.  Declared here so the
       attacker model (secrets = states_var) is fixed from the first commit. *)
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
    (* The crypto results no longer arrive on inputs: an IP response is the
       scheduler's own port, named by the IP rather than declared here. *)

    (* From the platform, not from software.  [in_ps] is the Primary Seed and is
       secret outright; [in_init_req] leaks nothing, but software must never be
       able to drive it (spec section 5.8) -- and [Secret] already delivers
       "never bus-mapped", which is the protection wanted. *)
    | in_ps
    | in_init_req
    (* MARS_Quote *)
    | in_regsel
    | in_nonce
    | in_ctx
    | in_nlen
    | in_ctxlen
    .

    (* PCRs are OUTPUT variables, not state variables: they are meant to be
       public (MARS_RegRead hands them out), and making them secret would taint
       the whole Quote datapath.  MVP.md section 6.1. *)
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
    (* [out_ctx] is GONE: it existed only because inputs are re-sampled on
       every step, so a multi-step command could mix two invocations'
       arguments.  One action reads [in_ctx] once. *)
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
       "outside what the confidentiality guarantee quantifies over, therefore may
       carry a secret, therefore never memory-mapped".  Spec section 5.8 requires
       exactly this for the crypto port: DP and AK cross it.

       Every port here is Public: the crypto port groups are gone, so nothing
       carrying a secret crosses the design's own ports any more.  An IP link
       nothing, and the guarantee is about which ports are COVERED.

       construction. *)


    Definition fs_inputs_class (x: fs_inputs) : port_class :=
    match x with
    | in_pt | in_idx | in_dig => Public


    | in_ps | in_init_req                      => Secret
    (* Quote's arguments are the host's own; nothing secret about them. *)
    | in_regsel | in_nonce | in_ctx | in_nlen | in_ctxlen => Public
    end.

    Definition fs_outputs_class (x: fs_outputs) : port_class :=
    match x with
    (* handshake bits an observer could see on the bus edge anyway *)
    | out_rc | out_cap | out_dout | out_pcr0 | out_pcr1 | out_failure
    | out_st | out_snap => Public

    end.

    (* The two attached IPs.  A request is ONE word, so a multi-field request
       is packed: SHA takes [len || msg], HMAC takes [len || key || msg].

       [ip_fn] is the SPEC's claim about what the block computes.  Nothing in
       the lowering reads it -- the circuit samples the wire -- so a real
       SHA-256 model is not needed to synthesize, and the placeholder below is
       marked rather than hidden.  Proving a call computes the right thing is
       a separate lemma, deferred. *)
    Definition placeholder_digest {n} (v: bits_t n) : bits_t digest_sz :=
      Bits.slice 0 digest_sz v.

    Inductive fs_ips := ip_sha | ip_hmac.

    Definition fs_ip (p: fs_ips) : ip_decl :=
      match p with
      | ip_sha  => {| ip_req_sz  := len_sz + msg_sz;
                      ip_resp_sz := digest_sz;
                      ip_lat     := 3;
                      ip_fn      := placeholder_digest |}
      | ip_hmac => {| ip_req_sz  := len_sz + digest_sz + hmac_msg_sz;
                      ip_resp_sz := digest_sz;
                      ip_lat     := 5;
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

    (* Commands are refused until _MARS_Init has COMPLETED.  This is what stops
       MARS_Quote deriving AK = KDF(0,'R',ctx) from a zero DP, which anyone could
       compute (REVIEW.md section 2.2).

       [out_st] is not redundant with [in_init_req]: the request authorises
       STARTING an initialization, [out_st] records that one finished, and Init
       is a KDF round trip -- so there is a window where the request is asserted
       and DP is still zero.  MVP.md section 2.2 deviation 3.

       MARS_CapabilityGet is exempt, on the same rule that exempts it from
       failure mode: it always answers.  It reads no state a pending step or an
       uninitialized DP could affect -- every value it returns is a Profile
       constant. *)
    Definition guard_init (body: @tf_ops fs_states fs_inputs fs_outputs fs_ips)
        : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
    {[
        if ($out_st ==[1] #0)
        then let $out_rc := #MARS_RC_VALUE
        else `body`
    ]}.

    (* CryptSkdf's framing, from reference-emulator/c/hw_sha2.c -- the spec text
       does not give it, so the Profile pins it (MVP.md section 2):

         HMAC(parent, [1]_4 || label || 0x00 || ctx || [8192]_4)

       For CryptDpInit the parent is PS, the label is MARS_LD = 'D' and the
       context is the three bytes "prd".  13 bytes, left-aligned in the 512-bit
       port.  Built from byte-sized constants on purpose: [tf_const] carries a
       unary nat, so "prd" as one 24-bit literal (7369828) would be ~1s of
       [N.of_nat] per elaboration where three 8-bit ones are free. *)
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

         regSelect (4 bytes, BIG ENDIAN) || REG[i] for each selected i || nonce

       Big-endian regSelect is informative in the spec and comes from the
       reference implementation, so the Profile pins it (MVP.md section 2).
       Four shapes over two PCRs, three distinct lengths: 36 / 68 / 68 / 100
       bytes, left-aligned in the 1024-bit SHA port.

       Note the trailing field is the NONCE, not the context: MARS_Quote calls
       CryptSnapshot(snapshot, regSelect, nonce, nlen).  The context goes to the
       KDF at the next step, which is a different message entirely. *)
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

    (* The AK derivation frame: same CryptSkdf shape as [dpinit_msg], with a
       32-byte context instead of the three-byte "prd".  42 bytes.  Reads
       [in_ctx] directly -- one action, so there is nothing to latch. *)

    Definition ak_kdf_msg : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 (tf_concat 336 176)
          (tf_op2 (tf_concat 32 304) (tf_const 1)
            (tf_op2 (tf_concat 8 296) (tf_const MARS_LR)
              (tf_op2 (tf_concat 8 288) (tf_const 0)
                (tf_op2 (tf_concat digest_sz 32) (tf_ivar in_ctx)
                  (tf_const 8192)))))
          (tf_const 0).

    (* CryptSign's message is the 32-byte snapshot, left-aligned -- read from
       the state var the snapshot call wrote. *)
    Definition sign_msg : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 (tf_concat digest_sz 256) (tf_svar st_snap) (tf_const 0).

    (* A request is one word.  SHA takes [len || msg]; HMAC takes
       [len || key || msg].  The IP glue unpacks -- which is what a single
       request bus means, and the reason [ip_req_sz] is one number.

       [len] is an EXPRESSION, so a command that chooses between message shapes
       chooses inside the PAYLOAD and still issues one call.  Branching around
       the call instead is correct but costly: a drive is emitted by the call,
       not by the branch, so every arm's request reaches the IP and the drives
       are SEQUENCED -- N arms, N round trips.  Example_BranchCallSpike measures
       exactly that. *)
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

    (* The index and regSelect choose a PAYLOAD, not whether to call.  Lifting
       the choice into the message keeps each command at one call per IP. *)
    Definition ext_sel_msg : @tf_expr fs_states fs_inputs fs_outputs :=
      tf_expr_if (tf_op2 (tf_cmp arg_sz tf_eq) (tf_ivar in_idx) (tf_const 0))
        (ext_msg out_pcr0) (ext_msg out_pcr1).

    Definition snap_len : @tf_expr fs_states fs_inputs fs_outputs :=
      tf_expr_if (tf_op2 (tf_cmp 32 tf_eq) (tf_ivar in_regsel) (tf_const 0))
        (tf_const 36)
        (tf_expr_if (tf_op2 (tf_cmp 32 tf_eq) (tf_ivar in_regsel) (tf_const 3))
          (tf_const 100) (tf_const 68)).

    Definition snap_msg : @tf_expr fs_states fs_inputs fs_outputs :=
      tf_expr_if (tf_op2 (tf_cmp 32 tf_eq) (tf_ivar in_regsel) (tf_const 0))
        snap_none
        (tf_expr_if (tf_op2 (tf_cmp 32 tf_eq) (tf_ivar in_regsel) (tf_const 1))
          (snap_one out_pcr0)
          (tf_expr_if (tf_op2 (tf_cmp 32 tf_eq) (tf_ivar in_regsel) (tf_const 2))
            (snap_one out_pcr1) snap_both)).

    Definition quote_ok : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
    {[
        let $out_snap := $st_snap;
        let $out_dout := $st_sig;
        let $out_rc   := #MARS_RC_SUCCESS
    ]}.

    Definition unsupported : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
        guard_failure {[ let $out_rc := #MARS_RC_COMMAND ]}.

    (* An output variable HOLDS its value unless an action writes it, so a stale
       result survives every command that does not overwrite it -- after a Quote,
       [out_dout] would keep driving the signature on 256 wires until the next
       RegRead.  Every command therefore clears the RESULT registers first.

       Scope matters, and only these two (later [snap]) may be cleared:
         - [out_pcr0]/[out_pcr1]/[out_failure] -- and later [out_st]/[out_pend] -- are
           outputs only because non-secret state is modelled that way
           (MVP.md section 6.1).  Clearing them per command would wipe the
           measurement chain on every command.
         - the trusted crypt_* ports must stay STABLE from the request arm to
           the completion arm, so clearing them at command start would destroy
           an in-flight request.  Their rule is the opposite shape: zeroize at
           sequence end and in every error arm (REVIEW.md section 2.7).

       Measured free: +1 node on CapabilityGet, +0 on RegRead, +2 on an excluded
       command; no change to buffers or to any action's cycle bounds. *)
    Definition clear_results (body: @tf_ops fs_states fs_inputs fs_outputs fs_ips)
        : @tf_ops fs_states fs_inputs fs_outputs fs_ips :=
    {[
        let $out_dout := #0;
        let $out_cap  := #0;
        `body`
    ]}.

    (* One arm per command code.  Wrapped by [fs_transitions] below, which is
       the only definition the scheduler sees. *)
    Definition fs_command
        (act: fs_action)
        :
        (@tf_ops fs_states fs_inputs fs_outputs fs_ips)
        :=
        match act with

        (* MARS_CapabilityGet -- spec section 8.1.2.  Note there is NO out_failure
           guard: section 5.3.1 excludes this command from out_failure mode.  All
           eleven Table 6 tags, then MARS_RC_VALUE. *)
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

        (* MARS_RegRead -- spec section 8.3.2.  An out-of-range index is
           MARS_RC_REG (7), not MARS_RC_VALUE, and [out_dout] reads zero because
           [clear_results] already cleared it.  The C emulator instead leaves
           the CALLER's buffer untouched, which has no analogue on an MMIO
           result register; either way the host contract is the same, "check out_rc
           before using out_dout". *)
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

        (* MARS_PcrExtend -- spec section 8.3.1.  ONE action and ONE call: the
           index chooses the MESSAGE, not whether to call.  An out-of-range
           index still issues a request whose answer is discarded, which keeps
           the command's cycle count independent of the index. *)
        | act_pcrextend =>
            guard_failure (guard_init {[
                `call_sha st_dig (tf_const 64) ext_sel_msg`;
                if ($in_idx ==[arg_sz] #0) then
                    let $out_pcr0 := $st_dig;
                    let $out_rc   := #MARS_RC_SUCCESS
                else if ($in_idx ==[arg_sz] #1) then
                    let $out_pcr1 := $st_dig;
                    let $out_rc   := #MARS_RC_SUCCESS
                else
                    let $out_rc := #MARS_RC_REG
            ]})
        (* _MARS_Init -- spec section 5.4.  Gated on a protected input the platform
           drives, never software (section 5.8), and exempt from the failure and
           init guards: it is what clears failure mode.  ONE action now -- the
           DP derivation is a call, not a second command. *)
        | act_init =>
            {[
                if ($in_init_req ==[1] #1) then
                    let $st_ps          := $in_ps;
                    let $out_failure    := #0;
                    let $out_pcr0       := #0;
                    let $out_pcr1       := #0;
                    (* [st_ps] was just assigned, and statement order is
                       genuinely sequential (REVIEW.md section 4), so this reads
                       the NEW seed rather than the previous one. *)
                    `call_hmac st_dp (tf_const 13) (tf_svar st_ps) dpinit_msg`;
                    (* the last step of the reset sequence: DP is valid from
                       here on, and it is valid in THIS action *)
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
        (* MARS_Quote -- spec section 8.5.1.  THREE round trips, ONE action:

             snap = SHA (regSelect || REGs || nonce)
             AK   = HMAC(DP, [1]||'R'||0||ctx||[L])
             sig  = HMAC(AK, snap)

           Two are on the same IP and the third reads the second's result, so
           this is the sequenced and the chained case at once -- the shapes
           Example_TwoCallSpike and Example_ChainedCallSpike measure.

           regSelect picks the snapshot's SHAPE, inside the payload, so there is
           still exactly one SHA call.  Four arms around the call would be four
           round trips.

           REVIEW.md section 2.1's hazard is gone rather than defended against.
           It was that consecutive ARMS assign to [st_ak] and then to
           [out_dout], so one cycle of staleness would publish the Attestation
           Key in clear.  There are no consecutive arms: the scheduler orders
           the three samples by the data dependency between them. *)
        | act_quote =>
            guard_failure (guard_init {[
                `call_sha st_snap snap_len snap_msg`;
                `call_hmac st_ak  (tf_const 42) (tf_svar st_dp) ak_kdf_msg`;
                `call_hmac st_sig (tf_const 32) (tf_svar st_ak) sign_msg`;
                if ($in_nlen !=[arg_sz] #32) then
                    let $out_rc := #MARS_RC_VALUE
                else if ($in_ctxlen !=[arg_sz] #32) then
                    let $out_rc := #MARS_RC_VALUE
                else if ($in_regsel ==[32] #0) then `quote_ok`
                else if ($in_regsel ==[32] #1) then `quote_ok`
                else if ($in_regsel ==[32] #2) then `quote_ok`
                else if ($in_regsel ==[32] #3) then `quote_ok`
                else
                    (* regSelect names a register this Profile does not
                       implement -- mars.c: regSelect >> PROFILE_COUNT_REG *)
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

        (* Pinned empty, and it must stay empty: one unsound user-supplied
           declassification rule unbalances a secret-dependent phi.
           REVIEW.md section 4. *)
        (* no attached IP: no call names a response port here *)
        (* no IP drives any port here, so nothing can conflict with one *)
        tfs_spec_ips := fs_ips;
        tfs_spec_ips_fin := _;
        tfs_spec_ip := fs_ip;

        tfs_spec_decls := []
    |}.

    (* The call structure, per command.  This is the property the one-action
       form is FOR: a crypto round trip lives inside the command that needs it,
       and choosing a payload does not multiply the round trips. *)
    Definition qdfg := build_dfg tfs_ctx act_quote.
    (* two on one IP, and the third reads the second's result *)
    Example quote_one_sha  : List.length (drive_nodes tfs_ctx qdfg ip_sha)  = 1.
    Proof. vm_compute. reflexivity. Qed.
    Example quote_two_hmac : List.length (drive_nodes tfs_ctx qdfg ip_hmac) = 2.
    Proof. vm_compute. reflexivity. Qed.

    (* four snapshot shapes, still ONE request *)
    Definition edfg := build_dfg tfs_ctx act_pcrextend.
    Example ext_one_sha : List.length (drive_nodes tfs_ctx edfg ip_sha)  = 1.
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

    Definition R := TypedSynthesis.R tf_ctx.

    Definition r := TypedSynthesis.r tf_ctx.

    Definition Sigma := TypedSynthesis.Sigma tf_ctx.

    Definition system_schedule := TypedSynthesis.system_schedule tf_ctx.

    Definition ext_fn_specs := TypedSynthesis.ext_fn_specs tf_ctx.

    Instance ext_fn_names : Show _ := TypedSynthesis.ext_fn_names tf_ctx.

    Definition package :=
      {| ip_koika := {| koika_reg_types := R;
                        koika_reg_names := TypedSynthesis.reg_names tf_ctx;
                        koika_reg_init := r;
                        koika_reg_finite := TypedSynthesis._reg_t_finite tf_ctx;
                        koika_ext_fn_types := Sigma;
                        koika_rules := TypedSynthesis.rules tf_ctx;
                        koika_rule_names := TypedSynthesis.rule_names tf_ctx;
                        koika_rule_external := (fun _ => false);
                        koika_scheduler := system_schedule;
                        koika_module_name := "Example_Mars" |};

      ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn; efs_method := false |};
                  sp_prelude := None |};

      ip_verilog := {| vp_ext_fn_specs := ext_fn_specs |} |}.

End TypedSynthesis.

(* Extraction *)

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Example_Mars.ml" prog.
