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

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

(*
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
    Definition pend_sz   := 8.

    Definition hmac_msg_sz := 512.      (* longest HMAC message: the 42-byte KDF frame *)

    (* out_pend -- which step of which command is in flight; 0 is idle.  DPINIT,
       SNAP, KDF and SIGN arrive with Init and Quote at Stage 4. *)
    Definition PEND_IDLE   := 0.
    Definition PEND_EXT0   := 1.
    Definition PEND_EXT1   := 2.
    Definition PEND_DPINIT := 3.

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
    | act_continue           (* Profile-specific         13 *)
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
    | act_continue         => Ob~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0~1
    (* 0xFFFF, deliberately not adjacent to the 0..12 range.  MARS_Init is a
       PERMANENT Profile command; MARS_Continue is scaffolding that disappears
       at V4.  Parking Init at the far end means removing Continue leaves a
       clean 0..12 + 0xFFFF space instead of a hole, and Init never has to be
       renumbered -- which would be a breaking change for any host. *)
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
    .

    Inductive fs_inputs :=
    | in_pt            (* MARS_CapabilityGet: property tag        *)
    | in_idx           (* MARS_RegRead / MARS_PcrExtend: index    *)
    | in_dig           (* MARS_PcrExtend: the digest to extend    *)
    (* From the crypto IPs.  Secret, and NOT to be memory-mapped -- the port
       names now say so (_sec_). *)
    | in_sha_res
    | in_sha_valid
    | in_sha_tag       (* echoes the out_sha_req this result answers  *)
    | in_hmac_res
    | in_hmac_valid
    | in_hmac_tag
    (* From the platform, not from software.  [in_ps] is the Primary Seed and is
       secret outright; [in_init_req] leaks nothing, but software must never be
       able to drive it (spec section 5.8) -- and [Secret] already delivers
       "never bus-mapped", which is the protection wanted. *)
    | in_ps
    | in_init_req
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
    | out_pend       (* which crypto step is in flight; 0 = idle *)
    | out_armed      (* two-phase arming, REVIEW.md section 2.1  *)
    | out_st         (* 0 = uninitialized, 1 = DP is valid       *)
    | out_sha_req       (* toggles on each new SHA-256 request      *)
    | out_sha_active    (* a SHA-256 request is outstanding         *)
    | out_hmac_req
    | out_hmac_active
    (* Secret: the crypto ports.  ONE GROUP PER ATTACHED IP, not one group
       multiplexed by an opcode: the two cores genuinely differ (sha256_core
       takes raw blocks and needs no key; hmac_core takes finalize/final_len and
       does), a shared group would force a lowest-common-denominator interface,
       and per-IP groups are the shape V3/V4 converges on anyway.  It also lets
       each group be right-sized -- SHA needs no key, HMAC's longest message is
       the 42-byte KDF frame. *)
    | out_sha_msg
    | out_sha_len
    | out_hmac_key
    | out_hmac_msg
    | out_hmac_len
    .

    Definition fs_states_size (x: fs_states) : nat :=
    match x with
    | st_ps => digest_sz
    | st_dp => digest_sz
    | st_ak => digest_sz
    end.

    Definition fs_inputs_size (x: fs_inputs) : nat :=
    match x with
    | in_pt          => arg_sz
    | in_idx         => arg_sz
    | in_dig         => digest_sz
    | in_sha_res    => digest_sz
    | in_sha_valid  => 1
    | in_sha_tag    => 1
    | in_hmac_res   => digest_sz
    | in_hmac_valid => 1
    | in_hmac_tag   => 1
    | in_ps         => digest_sz
    | in_init_req   => 1
    end.

    Definition fs_outputs_size (x: fs_outputs) : nat :=
    match x with
    | out_rc        => rc_sz
    | out_cap       => 16
    | out_dout      => digest_sz
    | out_pcr0      => digest_sz
    | out_pcr1      => digest_sz
    | out_failure   => 1
    | out_pend      => pend_sz
    | out_armed     => 1
    | out_st        => 1
    | out_sha_req     => 1
    | out_sha_active  => 1
    | out_hmac_req    => 1
    | out_hmac_active => 1
    | out_sha_msg     => msg_sz
    | out_sha_len     => 16
    | out_hmac_key    => digest_sz
    | out_hmac_msg    => hmac_msg_sz
    | out_hmac_len    => 16
    end.

    (* Confidentiality classification (Contract.v [port_class]).  [Secret] means
       "outside what the confidentiality guarantee quantifies over, therefore may
       carry a secret, therefore never memory-mapped".  Spec section 5.8 requires
       exactly this for the crypto port: DP and AK cross it.

       [out_sha_len] and [out_sha_active] carry nothing sensitive today and are still
       [Secret] -- they are part of the port group, over-classifying costs
       nothing, and the guarantee is about which ports are COVERED.

       [out_sha_req] is genuinely [Public]: it is one toggle bit an attacker may
       observe.  Note that class and wiring are independent -- [out_sha_req] is
       Public and goes to the IP; [out_rc] is Public and goes to the bus. *)
    Definition fs_inputs_class (x: fs_inputs) : port_class :=
    match x with
    | in_pt | in_idx | in_dig => Public
    | in_sha_res  | in_sha_valid  | in_sha_tag  => Secret
    | in_hmac_res | in_hmac_valid | in_hmac_tag => Secret
    | in_ps | in_init_req                      => Secret
    end.

    Definition fs_outputs_class (x: fs_outputs) : port_class :=
    match x with
    (* handshake bits an observer could see on the bus edge anyway *)
    | out_rc | out_cap | out_dout | out_pcr0 | out_pcr1 | out_failure
    | out_pend | out_armed | out_st
    | out_sha_req | out_sha_active | out_hmac_req | out_hmac_active => Public
    (* everything carrying data *)
    | out_sha_msg | out_sha_len
    | out_hmac_key | out_hmac_msg | out_hmac_len => Secret
    end.

    Definition fs_states_t := tf_states_type fs_states_size.

    Definition fs_states_init (x: fs_states) : (fs_states_t x) :=
    match x with
    | st_ps => Bits.zero
    | st_dp => Bits.zero
    | st_ak => Bits.zero
    end.

    (* The dispatcher's out_failure-mode rule (spec section 8, informative comment;
       normative in section 5.3.1): in out_failure mode every command except
       MARS_CapabilityGet returns MARS_RC_FAILURE, and it does so BEFORE the
       unsupported-command check. *)
    Definition guard_failure (body: @tf_ops fs_states fs_inputs fs_outputs)
        : @tf_ops fs_states fs_inputs fs_outputs :=
    {[
        if ($out_failure ==[1] #1)
        then let $out_rc := #MARS_RC_FAILURE
        else `body`
    ]}.

    (* Interleaving is refused, not merely discouraged: any command issued while
       a crypto step is in flight is rejected and leaves [out_pend] and the request
       untouched (MVP.md section 5.3).  MARS_Continue is the exception by
       construction -- it is the thing that advances [out_pend] -- and an excluded
       command answers MARS_RC_COMMAND regardless, since there is nothing to
       refuse.  Busy is never an out_rc of its own: section 6.2 has no BUSY code and
       3 is Reserved, so the host reads busy from [out_pend] (REVIEW.md 3.2). *)
    Definition guard_busy (body: @tf_ops fs_states fs_inputs fs_outputs)
        : @tf_ops fs_states fs_inputs fs_outputs :=
    {[
        if ($out_pend !=[pend_sz] #PEND_IDLE)
        then let $out_rc := #MARS_RC_VALUE
        else `body`
    ]}.

    (* PcrExtend hashes PCR[i] || in_dig -- 64 bytes -- left-aligned in the
       1024-bit port.  Two concatenations: the 512-bit message, then the
       zero padding out to the port width. *)
    Definition ext_msg (pcr: fs_outputs) : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 (tf_concat 512 512)
          (tf_op2 (tf_concat digest_sz digest_sz) (tf_ovar pcr) (tf_ivar in_dig))
          (tf_const 0).

    (* Per-group handshake predicates.  [out_armed] stays global -- [out_pend]
       holds one value, so at most one group is ever outstanding -- while
       [_active] says WHICH group, and doubles as the signal the adapter watches
       to know the result was consumed (MVP.md section 9, A7). *)
    Definition resp_ok (v_valid v_tag: fs_inputs) (o_req o_active: fs_outputs)
        : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 tf_and
          (tf_op2 tf_and (tf_ovar out_armed) (tf_ovar o_active))
          (tf_op2 tf_and (tf_ivar v_valid)
            (tf_op2 (tf_cmp 1 tf_eq) (tf_ivar v_tag) (tf_ovar o_req))).

    (* A response for a request that is not the outstanding one.  Keyed on
       [_active], not [out_armed]: the core that holds [done] high across
       requests is precisely the one the module never armed, so an armed-keyed
       test would miss the case it exists for. *)
    Definition violation (v_valid v_tag: fs_inputs) (o_req o_active: fs_outputs)
        : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 tf_and
          (tf_op2 tf_and (tf_ovar o_active) (tf_ivar v_valid))
          (tf_op2 (tf_cmp 1 tf_neq) (tf_ivar v_tag) (tf_ovar o_req)).

    (* Issue a request: drive the port, flip the request bit, record the step.

       [out_armed] is set ONLY while in_sha_valid is low.  That is the whole
       two-phase arming fix (REVIEW.md section 2.1): a core that holds [done]
       high from its previous request cannot satisfy arm-and-fire, so the module
       WEDGES instead of latching a stale result.

       "Wedged" is this campaign's term (MVP.md section 6, REVIEW.md section
       2.8) for the state where [out_pend] is nonzero forever: a step is recorded as
       in flight, so every command is refused, and no Continue can clear it
       because the completion guard can never be satisfied.  It is deliberate
       and it is fail-stop -- at Stage 4's KDF->SIGN step, latching a stale
       result instead would publish the Attestation Key on [out_dout].  The only
       recovery is _MARS_Init, which clears [out_pend] unconditionally (Stage 4). *)
    Definition issue_sha (step: nat)
                     (msg: @tf_expr fs_states fs_inputs fs_outputs) (len: nat)
        : @tf_ops fs_states fs_inputs fs_outputs :=
    {[
        let $out_sha_msg    := `msg`;
        let $out_sha_len    := #len;
        let $out_sha_active := #1;
        let $out_sha_req    := !$out_sha_req;
        let $out_pend       := #step;
        let $out_armed      := ($in_sha_valid ==[1] #0);
        let $out_rc         := #MARS_RC_SUCCESS
    ]}.

    (* A response counts only if the module out_armed it, the IP asserts valid, AND
       the tag echoes the request bit that was driven at issue.  [tf_ovar] reads
       the pre-cycle value, so [out_sha_req] here is the one that was sent. *)

    (* A protocol violation by the crypto IP or its glue: a step IS outstanding
       and the IP asserts valid for a DIFFERENT request.  Spec section 5.6
       requires out_failure mode on "any other internal error", and an answer to a
       request that is not the outstanding one is exactly that.

       Keyed on [out_pend], not on [out_armed], deliberately.  The dangerous case is the
       core that holds [done] high across requests: the module then never out_armed,
       so an out_armed-keyed test would miss it and the device would sit silently
       wedged.  Keying on [out_pend] catches both that and a genuine mismatch, while
       still excluding the two harmless cases -- an early Continue (valid low)
       and a spurious Continue with nothing outstanding (out_pend = 0). *)

    (* Enter out_failure mode.  Zeroizes like [finish] -- a faulting IP is precisely
       when nothing should be left driven on the trusted port (REVIEW.md section
       2.7) -- and clears [out_pend] so the device is in ONE unambiguous stuck state
       (failed) rather than two overlapping ones (failed and wedged).  Every
       command except MARS_CapabilityGet now answers MARS_RC_FAILURE until
       _MARS_Init reinitializes (spec section 5.3.1). *)
    (* Zeroize every group, whichever one misbehaved: a faulting IP is exactly
       when nothing should be left driven on any trusted port. *)
    Definition zeroize : @tf_ops fs_states fs_inputs fs_outputs :=
    {[
        let $out_sha_msg     := #0;
        let $out_sha_active  := #0;
        let $out_hmac_key    := #0;
        let $out_hmac_msg    := #0;
        let $out_hmac_active := #0
    ]}.

    Definition fault : @tf_ops fs_states fs_inputs fs_outputs :=
    {[
        `zeroize`;
        let $out_pend    := #PEND_IDLE;
        let $out_armed   := #0;
        let $out_failure := #1;
        let $out_rc      := #MARS_RC_FAILURE
    ]}.

    (* End of a sequence: zeroize the trusted ports and disarm.  The ports hold
       their value indefinitely otherwise, which is how AK would stay driven on
       256 wires after a Quote (REVIEW.md section 2.7). *)
    Definition finish : @tf_ops fs_states fs_inputs fs_outputs :=
    {[
        `zeroize`;
        let $out_pend  := #PEND_IDLE;
        let $out_armed := #0;
        let $out_rc    := #MARS_RC_SUCCESS
    ]}.

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
    Definition guard_init (body: @tf_ops fs_states fs_inputs fs_outputs)
        : @tf_ops fs_states fs_inputs fs_outputs :=
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
            (tf_op2 (tf_concat 8 64) (tf_const 68)          (* 'D' = MARS_LD *)
              (tf_op2 (tf_concat 8 56) (tf_const 0)
                (tf_op2 (tf_concat 8 48) (tf_const 112)     (* 'p' *)
                  (tf_op2 (tf_concat 8 40) (tf_const 114)   (* 'r' *)
                    (tf_op2 (tf_concat 8 32) (tf_const 100) (* 'd' *)
                      (tf_const 8192)))))))                 (* [L]_4, L = 8192 *)
          (tf_const 0).

    Definition issue_hmac (step: nat)
                     (key msg: @tf_expr fs_states fs_inputs fs_outputs) (len: nat)
        : @tf_ops fs_states fs_inputs fs_outputs :=
    {[
        let $out_hmac_key    := `key`;
        let $out_hmac_msg    := `msg`;
        let $out_hmac_len    := #len;
        let $out_hmac_active := #1;
        let $out_hmac_req    := !$out_hmac_req;
        let $out_pend        := #step;
        let $out_armed       := ($in_hmac_valid ==[1] #0);
        let $out_rc          := #MARS_RC_SUCCESS
    ]}.

    (* A command this Profile excludes (spec section 7).  Eight of the thirteen
       codes are excluded outright; PcrExtend and Quote are in the Profile but
       not yet built, and answer MARS_RC_COMMAND until they are. *)
    Definition unsupported : @tf_ops fs_states fs_inputs fs_outputs :=
        guard_failure {[ let $out_rc := #MARS_RC_COMMAND ]}.

    (* An output variable HOLDS its value unless an action writes it, so a stale
       result survives every command that does not overwrite it -- after a Quote,
       [out_dout] would keep driving the signature on 256 wires until the next
       RegRead.  Every command therefore clears the RESULT registers first.

       Scope matters, and only these two (later [snap]) may be cleared:
         - [out_pcr0]/[out_pcr1]/[out_failure] -- and later [st]/[out_pend]/[out_armed] -- are
           outputs only because non-secret state is modelled that way
           (MVP.md section 6.1).  Clearing them per command would wipe the
           measurement chain on every command.
         - the trusted crypt_* ports must stay STABLE from the request arm to
           the completion arm, so clearing them at command start would destroy
           an in-flight request.  Their rule is the opposite shape: zeroize at
           sequence end and in every error arm (REVIEW.md section 2.7).

       Measured free: +1 node on CapabilityGet, +0 on RegRead, +2 on an excluded
       command; no change to buffers or to any action's cycle bounds. *)
    Definition clear_results (body: @tf_ops fs_states fs_inputs fs_outputs)
        : @tf_ops fs_states fs_inputs fs_outputs :=
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
        (@tf_ops fs_states fs_inputs fs_outputs)
        :=
        match act with

        (* MARS_CapabilityGet -- spec section 8.1.2.  Note there is NO out_failure
           guard: section 5.3.1 excludes this command from out_failure mode.  All
           eleven Table 6 tags, then MARS_RC_VALUE. *)
        | act_capabilityget =>
            guard_busy {[
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
            guard_failure (guard_init (guard_busy {[
                if ($in_idx ==[arg_sz] #0) then
                    let $out_dout := $out_pcr0;
                    let $out_rc   := #MARS_RC_SUCCESS
                else if ($in_idx ==[arg_sz] #1) then
                    let $out_dout := $out_pcr1;
                    let $out_rc   := #MARS_RC_SUCCESS
                else
                    let $out_rc := #MARS_RC_REG
            ]}))

        (* MARS_PcrExtend -- spec section 8.3.1.  Step 1 of 2: validate, build
           PCR[i] || in_dig, and issue.  Step 2 is MARS_Continue.  [out_pend] carries
           which PCR, so the index needs no separate latch -- which matters,
           because an input is re-sampled on every step. *)
        | act_pcrextend =>
            guard_failure (guard_init (guard_busy {[
                if ($in_idx ==[arg_sz] #0) then
                    `issue_sha PEND_EXT0 (ext_msg out_pcr0) 64`
                else if ($in_idx ==[arg_sz] #1) then
                    `issue_sha PEND_EXT1 (ext_msg out_pcr1) 64`
                else
                    let $out_rc := #MARS_RC_REG
            ]}))

        (* MARS_Continue -- Profile-specific, not a TCG command.  Advances
           whatever [out_pend] names, and does NOTHING otherwise: glue that pulses
           Continue spuriously, repeatedly or never cannot make the module do
           anything it did not itself start.  A second Continue after a
           completed step finds out_pend = 0 and is refused. *)
        (* NOT gated on [out_st]: the Continue that completes _MARS_Init runs
           while st is still 0, so an init gate here would make initialization
           impossible.  Safe, because Continue only ever advances something the
           module itself started -- with [out_pend] = 0 it does nothing. *)
        | act_continue =>
            guard_failure {[
                if `violation in_sha_valid in_sha_tag out_sha_req out_sha_active` then
                    `fault`
                else if `resp_ok in_sha_valid in_sha_tag out_sha_req out_sha_active` then
                    if ($out_pend ==[pend_sz] #PEND_EXT0) then
                        let $out_pcr0 := $in_sha_res;
                        `finish`
                    else if ($out_pend ==[pend_sz] #PEND_EXT1) then
                        let $out_pcr1 := $in_sha_res;
                        `finish`
                    else
                        let $out_rc := #MARS_RC_VALUE
                else if `violation in_hmac_valid in_hmac_tag out_hmac_req out_hmac_active` then
                    `fault`
                else if `resp_ok in_hmac_valid in_hmac_tag out_hmac_req out_hmac_active` then
                    if ($out_pend ==[pend_sz] #PEND_DPINIT) then
                        (* the only writer of [out_st], and the last step of the
                           reset sequence: DP is valid from here on *)
                        let $st_dp  := $in_hmac_res;
                        let $out_st := #1;
                        `finish`
                    else
                        let $out_rc := #MARS_RC_VALUE
                else
                    let $out_rc := #MARS_RC_VALUE
            ]}

        (* _MARS_Init -- spec section 5.4.  Not a TCG command: it is gated on a
           protected input the platform drives, never software (section 5.8).

           Exempt from all three guards, and each exemption is load-bearing:
             - from [guard_failure], because section 5.3.1 says failure mode
               persists "until reinitialized" -- so Init is what clears it;
             - from [guard_busy] and from [guard_init], because Init is the ONLY
               recovery from a wedged crypto step (REVIEW.md section 2.8), and a
               gate on [out_st = 0] would make the wedge permanent.

           Protection therefore comes entirely from [in_init_req] being a Secret
           input that is never memory-mapped, which is exactly where spec
           section 5.8 puts it.  This refines MVP.md section 6.3 step 3, which
           also gated Init on [st = 0]. *)
        | act_init =>
            {[
                if ($in_init_req ==[1] #1) then
                    let $st_ps          := $in_ps;
                    let $st_ak          := #0;
                    let $out_st         := #0;
                    let $out_failure    := #0;
                    let $out_pcr0       := #0;
                    let $out_pcr1       := #0;
                    let $out_sha_msg    := #0;
                    let $out_sha_active := #0;
                    (* [st_ps] was just assigned, and statement order is
                       genuinely sequential (REVIEW.md section 4), so this reads
                       the NEW seed rather than the previous one. *)
                    `issue_hmac PEND_DPINIT (tf_svar st_ps) dpinit_msg 13`
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
        | act_quote            => unsupported
        | act_sign             => unsupported
        | act_signatureverify  => unsupported
        end.

    Definition fs_transitions (act: fs_action)
        : (@tf_ops fs_states fs_inputs fs_outputs) :=
        clear_results (fs_command act).

    Definition fs_step := tf_ops_run fs_states_size fs_inputs_size fs_outputs_size.

End FunctionalSpecification.

(* Differential vectors.  Expected values come from
   reference-emulator/c/mars.c with PROFILE_COUNT_PCR set to 2, i.e. the
   Profile of MVP.md section 2.  These are the specification-level oracle
   checks; the Verilog-level ones run against python/ in the test bench. *)
Section Vectors.

    (* Vectors thread the WHOLE system state, not just the outputs: DP is a
       state variable, so it has to survive from the Init request to the
       Continue that completes it. *)
    Definition sys_t := (ContextEnv.(env_t) (tf_states_type fs_states_size)
                         * ContextEnv.(env_t) (tf_outputs_type fs_outputs_size))%type.

    Definition s_zero : ContextEnv.(env_t) (tf_states_type fs_states_size) :=
        ContextEnv.(create) fs_states_init.

    Definition sys_zero : sys_t :=
        (s_zero, ContextEnv.(create) (fun _ => Bits.zero)).

    Definition with_out (sys: sys_t) (v: fs_outputs)
        (x: bits_t (fs_outputs_size v)) : sys_t :=
        (fst sys, ContextEnv.(putenv) (snd sys) v x).

    (* Full input vector. *)
    Definition arg_full (pt idx dig res: nat) (valid tag: bool)
                        (hres: nat) (hvalid htag: bool)
                        (ps: nat) (ireq: bool)
        (x : fs_inputs) : bits_t (fs_inputs_size x) :=
        match x with
        | in_pt         => Bits.of_nat arg_sz pt
        | in_idx        => Bits.of_nat arg_sz idx
        | in_dig        => Bits.of_nat digest_sz dig
        | in_sha_res    => Bits.of_nat digest_sz res
        | in_sha_valid  => if valid then Ob~1 else Ob~0
        | in_sha_tag    => if tag then Ob~1 else Ob~0
        | in_hmac_res   => Bits.of_nat digest_sz hres
        | in_hmac_valid => if hvalid then Ob~1 else Ob~0
        | in_hmac_tag   => if htag then Ob~1 else Ob~0
        | in_ps         => Bits.of_nat digest_sz ps
        | in_init_req   => if ireq then Ob~1 else Ob~0
        end.

    Definition arg (pt idx : nat) :=
        arg_full pt idx 0 0 false false 0 false false 0 false.

    Definition step (act: fs_action)
        (input: forall x, bits_t (fs_inputs_size x)) (sys: sys_t) : sys_t :=
        fs_step (fs_transitions act) sys input.

    Definition run_in := step.

    Definition run (act: fs_action) (pt idx : nat) (sys: sys_t) : sys_t :=
        step act (arg pt idx) sys.

    Definition get (sys: sys_t) v := ContextEnv.(getenv) (snd sys) v.

    Definition rc_of (act: fs_action) (pt idx : nat) sys :=
        get (run act pt idx sys) out_rc.
    Definition cap_of (act: fs_action) (pt idx : nat) sys :=
        get (run act pt idx sys) out_cap.
    Definition dout_of (act: fs_action) (pt idx : nat) sys :=
        get (run act pt idx sys) out_dout.

    (* ---- boot ---------------------------------------------------------- *)
    (* The reset sequence of spec section 5.4, as two strobes: the platform
       asserts init_req and the wrapper issues Init, then the glue advances it
       when the HMAC core answers.  Everything after this point starts from a
       device that has actually been initialized -- which it must, because the
       [st] gate refuses every command except MARS_CapabilityGet before it. *)
    Definition arg_boot := arg_full 0 0 0 0 false false 0 false false 5 true.
    Definition arg_hmac (r: nat) (v t: bool) :=
        arg_full 0 0 0 0 false false r v t 0 false.

    Definition sys_init  : sys_t := step act_init arg_boot sys_zero.
    Definition sys_ready : sys_t := step act_continue (arg_hmac 77 true true) sys_init.

    (* [o_zero] keeps its name: it is still the uninitialized device, which is
       the right base for the MARS_CapabilityGet vectors, since that command is
       exempt from the init gate. *)
    Definition o_zero := sys_zero.

    (* MARS_CapabilityGet: all eleven Table 6 tags. *)
    Example cap_pcr : cap_of act_capabilityget MARS_PT_PCR 0 o_zero
                      = Bits.of_nat 16 2.
    Proof. reflexivity. Qed.
    Example cap_tsr : cap_of act_capabilityget MARS_PT_TSR 0 o_zero
                      = Bits.of_nat 16 0.
    Proof. reflexivity. Qed.
    Example cap_len_digest : cap_of act_capabilityget MARS_PT_LEN_DIGEST 0 o_zero
                      = Bits.of_nat 16 32.
    Proof. reflexivity. Qed.
    Example cap_len_sign : cap_of act_capabilityget MARS_PT_LEN_SIGN 0 o_zero
                      = Bits.of_nat 16 32.
    Proof. reflexivity. Qed.
    Example cap_len_ksym : cap_of act_capabilityget MARS_PT_LEN_KSYM 0 o_zero
                      = Bits.of_nat 16 32.
    Proof. reflexivity. Qed.
    Example cap_len_kpub : cap_of act_capabilityget MARS_PT_LEN_KPUB 0 o_zero
                      = Bits.of_nat 16 0.
    Proof. reflexivity. Qed.
    Example cap_len_kprv : cap_of act_capabilityget MARS_PT_LEN_KPRV 0 o_zero
                      = Bits.of_nat 16 0.
    Proof. reflexivity. Qed.
    Example cap_alg_hash : cap_of act_capabilityget MARS_PT_ALG_HASH 0 o_zero
                      = Bits.of_nat 16 11.
    Proof. reflexivity. Qed.
    Example cap_alg_sign : cap_of act_capabilityget MARS_PT_ALG_SIGN 0 o_zero
                      = Bits.of_nat 16 5.
    Proof. reflexivity. Qed.
    Example cap_alg_skdf : cap_of act_capabilityget MARS_PT_ALG_SKDF 0 o_zero
                      = Bits.of_nat 16 34.
    Proof. reflexivity. Qed.
    Example cap_alg_akdf : cap_of act_capabilityget MARS_PT_ALG_AKDF 0 o_zero
                      = Bits.of_nat 16 0.
    Proof. reflexivity. Qed.

    Example cap_rc_success : rc_of act_capabilityget MARS_PT_ALG_AKDF 0 o_zero
                      = Bits.of_nat 16 MARS_RC_SUCCESS.
    Proof. reflexivity. Qed.

    (* in_pt = 0 and in_pt = 12 bracket Table 6: both MARS_RC_VALUE. *)
    Example cap_rc_value_low : rc_of act_capabilityget 0 0 o_zero
                      = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example cap_rc_value_high : rc_of act_capabilityget 12 0 o_zero
                      = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.

    Example cap_rc_value_13 : rc_of act_capabilityget 13 0 o_zero
                      = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.

    (* An invalid tag clears [out_cap] rather than leaving it stale: no command may
       return a previous command's result.  This is where the module and the C
       emulator DIVERGE by design -- oracle/stage1.expected shows the 0x0fff
       sentinel surviving in_pt = 0, 12 and 13, because there the sentinel lives in
       the CALLER's buffer, which an MMIO result register has no analogue for.
       Either way the host contract is the same: check out_rc before using out_cap. *)
    Definition o_cap_sentinel := with_out o_zero out_cap (Bits.of_nat 16 4095).
    Example cap_cleared_on_invalid : cap_of act_capabilityget 0 0 o_cap_sentinel
                      = Bits.zero.
    Proof. reflexivity. Qed.

    (* And a stale result never survives a command that does not produce one:
       RegRead clears [out_cap], CapabilityGet clears [out_dout]. *)
    Example regread_clears_cap : cap_of act_regread 0 0 o_cap_sentinel
                      = Bits.zero.
    Proof. reflexivity. Qed.
    Example unsupported_clears_cap : cap_of act_sequencehash 0 0 o_cap_sentinel
                      = Bits.zero.
    Proof. reflexivity. Qed.

    (* MARS_RegRead over two distinguishable PCRs, on an INITIALIZED device --
       every command but MARS_CapabilityGet needs one now. *)
    Definition o_pcrs :=
        with_out (with_out sys_ready out_pcr0 (Bits.of_nat digest_sz 42))
                 out_pcr1 (Bits.of_nat digest_sz 99).

    Example reg_read_0 : dout_of act_regread 0 0 o_pcrs
                      = Bits.of_nat digest_sz 42.
    Proof. reflexivity. Qed.
    Example reg_read_1 : dout_of act_regread 0 1 o_pcrs
                      = Bits.of_nat digest_sz 99.
    Proof. reflexivity. Qed.
    Example reg_read_0_rc : rc_of act_regread 0 0 o_pcrs
                      = Bits.of_nat 16 MARS_RC_SUCCESS.
    Proof. reflexivity. Qed.

    (* regIndex = 2 is out of range for PROFILE_COUNT_REG = 2: MARS_RC_REG,
       and [out_dout] must not change. *)
    Example reg_read_2_rc : rc_of act_regread 0 2 o_pcrs
                      = Bits.of_nat 16 MARS_RC_REG.
    Proof. reflexivity. Qed.
    Example reg_read_2_dout : dout_of act_regread 0 2 o_pcrs
                      = Bits.zero.
    Proof. reflexivity. Qed.

    (* The three state-carrying outputs must SURVIVE every command unchanged --
       they are outputs only because non-secret state is modelled that way, and
       clearing them per command would wipe the measurement chain.  Pinned so
       [clear_results] can never quietly grow to cover them. *)
    Example pcr0_survives_regread :
        get (run act_regread 0 2 o_pcrs) out_pcr0
        = Bits.of_nat digest_sz 42.
    Proof. reflexivity. Qed.
    Example pcr1_survives_capabilityget :
        get (run act_capabilityget MARS_PT_PCR 0 o_pcrs) out_pcr1
        = Bits.of_nat digest_sz 99.
    Proof. reflexivity. Qed.

    (* An excluded command answers MARS_RC_COMMAND, not the previous out_rc. *)
    Example unsupported_rc : rc_of act_sequencehash 0 0 o_pcrs
                      = Bits.of_nat 16 MARS_RC_COMMAND.
    Proof. reflexivity. Qed.
    Example quote_not_yet : rc_of act_quote 0 0 o_pcrs
                      = Bits.of_nat 16 MARS_RC_COMMAND.
    Proof. reflexivity. Qed.

    (* Failure mode (spec section 5.3.1): everything except MARS_CapabilityGet
       answers MARS_RC_FAILURE, and the out_failure answer preempts
       MARS_RC_COMMAND. *)
    Definition o_failed := with_out o_pcrs out_failure Ob~1.

    Example failed_regread : rc_of act_regread 0 0 o_failed
                      = Bits.of_nat 16 MARS_RC_FAILURE.
    Proof. reflexivity. Qed.
    Example failed_unsupported : rc_of act_sequencehash 0 0 o_failed
                      = Bits.of_nat 16 MARS_RC_FAILURE.
    Proof. reflexivity. Qed.
    Example failed_capabilityget : rc_of act_capabilityget MARS_PT_PCR 0 o_failed
                      = Bits.of_nat 16 MARS_RC_SUCCESS.
    Proof. reflexivity. Qed.
    Example failed_capabilityget_cap : cap_of act_capabilityget MARS_PT_PCR 0 o_failed
                      = Bits.of_nat 16 2.
    Proof. reflexivity. Qed.

    (* [out_failure] itself survives too -- it is state, not a result. *)
    Example failure_survives_capabilityget :
        get (run act_capabilityget MARS_PT_PCR 0 o_failed) out_failure
        = Ob~1.
    Proof. reflexivity. Qed.

    (* ---------------------------------------------------------------------
       Stage 2: the crypto handshake.

       These are the cases REVIEW.md section 2.1 is about.  A mock IP is just a
       choice of (in_sha_res, in_sha_valid, in_sha_tag) on the input vector, so
       every attack below is expressible here, before any real crypto exists.
       --------------------------------------------------------------------- *)

    (* Step 1: host issues PcrExtend(in_idx, in_dig). *)
    Definition ext (idx dig: nat) out :=
        run_in act_pcrextend
          (arg_full 0 idx dig 0 false false 0 false false 0 false) out.

    (* Step 2: glue pulses Continue with whatever the SHA core is driving. *)
    Definition cont (res: nat) (valid tag: bool) out :=
        run_in act_continue
          (arg_full 0 0 0 res valid tag 0 false false 0 false) out.

    (* Any other command, for the interleaving tests. *)
    Definition other (act: fs_action) (pt idx: nat) out := run act pt idx out.

    Definition issued := ext 0 7 o_pcrs.

    (* --- the request ---------------------------------------------------- *)

    Example issue_rc        : get issued out_rc        = Bits.of_nat 16 MARS_RC_SUCCESS.
    Proof. reflexivity. Qed.
    Example issue_pend      : get issued out_pend      = Bits.of_nat pend_sz PEND_EXT0.
    Proof. reflexivity. Qed.
    Example issue_op        : get issued out_sha_active = Ob~1.
    Proof. reflexivity. Qed.
    Example issue_len       : get issued out_sha_len = Bits.of_nat 16 64.
    Proof. reflexivity. Qed.
    (* out_sha_req toggled 0 -> 1, so a matching tag is 1. *)
    Example issue_req       : get issued out_sha_req = Ob~1.
    Proof. reflexivity. Qed.
    (* in_sha_valid was low at issue, so the request is out_armed. *)
    Example issue_armed     : get issued out_armed     = Ob~1.
    Proof. reflexivity. Qed.

    (* The message is PCR[0] || in_dig, left-aligned: out_pcr0 in the top 256 bits,
       in_dig below it, zero padding in the low 512.  This pins the byte ORDER,
       which is where MARS correctness actually lives (MVP.md section 3.1). *)
    Example issue_msg_pcr : Bits.slice 768 digest_sz (get issued out_sha_msg)
                          = Bits.of_nat digest_sz 42.
    Proof. reflexivity. Qed.
    Example issue_msg_dig : Bits.slice 512 digest_sz (get issued out_sha_msg)
                          = Bits.of_nat digest_sz 7.
    Proof. reflexivity. Qed.
    Example issue_msg_pad : Bits.slice 0 512 (get issued out_sha_msg)
                          = Bits.zero.
    Proof. reflexivity. Qed.

    (* An out-of-range index issues NOTHING: no request, no pending step. *)
    Example ext_bad_idx_rc   : get (ext 2 7 o_pcrs) out_rc        = Bits.of_nat 16 MARS_RC_REG.
    Proof. reflexivity. Qed.
    Example ext_bad_idx_pend : get (ext 2 7 o_pcrs) out_pend      = Bits.of_nat pend_sz PEND_IDLE.
    Proof. reflexivity. Qed.
    Example ext_bad_idx_req  : get (ext 2 7 o_pcrs) out_sha_req = Ob~0.
    Proof. reflexivity. Qed.
    Example ext_bad_idx_op   : get (ext 2 7 o_pcrs) out_sha_active = Ob~0.
    Proof. reflexivity. Qed.

    (* --- the honest completion ------------------------------------------ *)

    Definition completed := cont 123 true true issued.

    Example done_pcr0  : get completed out_pcr0      = Bits.of_nat digest_sz 123.
    Proof. reflexivity. Qed.
    Example done_pcr1  : get completed out_pcr1      = Bits.of_nat digest_sz 99.
    Proof. reflexivity. Qed.
    Example done_rc    : get completed out_rc        = Bits.of_nat 16 MARS_RC_SUCCESS.
    Proof. reflexivity. Qed.
    Example done_pend  : get completed out_pend      = Bits.of_nat pend_sz PEND_IDLE.
    Proof. reflexivity. Qed.
    Example done_armed : get completed out_armed     = Ob~0.
    Proof. reflexivity. Qed.
    (* Zeroized, so nothing stays driven on the trusted port. *)
    Example done_op    : get completed out_sha_active = Ob~0.
    Proof. reflexivity. Qed.
    Example done_key   : get completed out_hmac_key = Bits.zero.
    Proof. reflexivity. Qed.
    Example done_msg   : get completed out_sha_msg = Bits.zero.
    Proof. reflexivity. Qed.

    (* --- ATTACK: Continue without in_sha_valid ---------------------------- *)
    (* The PCR must not move, and the request must stay pending. *)
    Example no_valid_pcr0  : get (cont 666 false true issued) out_pcr0 = Bits.of_nat digest_sz 42.
    Proof. reflexivity. Qed.
    Example no_valid_rc    : get (cont 666 false true issued) out_rc   = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example no_valid_pend  : get (cont 666 false true issued) out_pend = Bits.of_nat pend_sz PEND_EXT0.
    Proof. reflexivity. Qed.

    (* --- ATTACK: a stale tag -------------------------------------------- *)
    (* valid is high and the result looks fine, but it answers the PREVIOUS
       request.  This is the escalation path to AK disclosure at Stage 4.
       The PCR must not move -- and beyond refusing, this is an internal error
       (spec section 5.6), so the device enters out_failure mode rather than sitting
       there silently. *)
    Definition faulted := cont 666 true false issued.

    Example stale_tag_pcr0    : get faulted out_pcr0      = Bits.of_nat digest_sz 42.
    Proof. reflexivity. Qed.
    Example stale_tag_rc      : get faulted out_rc        = Bits.of_nat 16 MARS_RC_FAILURE.
    Proof. reflexivity. Qed.
    Example stale_tag_failure : get faulted out_failure   = Ob~1.
    Proof. reflexivity. Qed.
    (* One unambiguous stuck state, not two: failed, not also wedged. *)
    Example stale_tag_pend    : get faulted out_pend      = Bits.of_nat pend_sz PEND_IDLE.
    Proof. reflexivity. Qed.
    Example stale_tag_armed   : get faulted out_armed     = Ob~0.
    Proof. reflexivity. Qed.
    (* Nothing left driven on the trusted port. *)
    Example stale_tag_op      : get faulted out_sha_active = Ob~0.
    Proof. reflexivity. Qed.
    Example stale_tag_key     : get faulted out_hmac_key = Bits.zero.
    Proof. reflexivity. Qed.
    Example stale_tag_msg     : get faulted out_sha_msg = Bits.zero.
    Proof. reflexivity. Qed.

    (* And out_failure mode then behaves as spec section 5.3.1 requires: everything
       answers MARS_RC_FAILURE except MARS_CapabilityGet, which still works. *)
    Example faulted_regread : get (other act_regread 0 0 faulted) out_rc
                            = Bits.of_nat 16 MARS_RC_FAILURE.
    Proof. reflexivity. Qed.
    Example faulted_ext     : get (ext 0 7 faulted) out_rc
                            = Bits.of_nat 16 MARS_RC_FAILURE.
    Proof. reflexivity. Qed.
    Example faulted_ext_req : get (ext 0 7 faulted) out_sha_req = Ob~1.
    Proof. reflexivity. Qed.
    Example faulted_capget  : get (other act_capabilityget MARS_PT_PCR 0 faulted) out_cap
                            = Bits.of_nat 16 2.
    Proof. reflexivity. Qed.

    (* An EARLY Continue is not a violation -- valid is low, the glue simply
       pulsed too soon -- so it must NOT trip out_failure mode. *)
    Example no_valid_no_failure : get (cont 666 false true issued) out_failure = Ob~0.
    Proof. reflexivity. Qed.
    (* Nor is a spurious Continue with nothing outstanding. *)
    Example cont_idle_no_failure : get (cont 666 true false o_pcrs) out_failure = Ob~0.
    Proof. reflexivity. Qed.
    Example twice_no_failure     : get (cont 666 true false completed) out_failure = Ob~0.
    Proof. reflexivity. Qed.

    (* --- ATTACK: Continue twice ------------------------------------------ *)
    (* The second one finds out_pend = 0 and out_armed = 0 and does nothing. *)
    Example twice_pcr0 : get (cont 666 true true completed) out_pcr0 = Bits.of_nat digest_sz 123.
    Proof. reflexivity. Qed.
    Example twice_rc   : get (cont 666 true true completed) out_rc   = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.

    (* --- ATTACK: Continue with nothing pending --------------------------- *)
    Example cont_idle_rc   : get (cont 666 true true o_pcrs) out_rc   = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example cont_idle_pcr0 : get (cont 666 true true o_pcrs) out_pcr0 = Bits.of_nat digest_sz 42.
    Proof. reflexivity. Qed.

    (* --- ATTACK: the IP holds done high across requests ------------------- *)
    (* A real core (secworks/sha256, OpenTitan hmac) holds [done] until the next
       start.  Arming only while in_sha_valid is LOW means such a core leaves the
       module unarmed: it WEDGES rather than latching a result it cannot bind to
       its request.  Fail-stop is the intended outcome -- at Stage 4 the stale
       result would be published as the Attestation Key. *)
    Definition issued_stuck :=
        run_in act_pcrextend
          (arg_full 0 0 7 0 true false 0 false false 0 false) o_pcrs.

    Example stuck_pend    : get issued_stuck out_pend  = Bits.of_nat pend_sz PEND_EXT0.
    Proof. reflexivity. Qed.
    Example stuck_unarmed : get issued_stuck out_armed = Ob~0.
    Proof. reflexivity. Qed.
    (* ...and no later Continue, however well-formed, can complete it. *)
    Example stuck_wedged_pcr0 : get (cont 666 true true issued_stuck) out_pcr0
                              = Bits.of_nat digest_sz 42.
    Proof. reflexivity. Qed.
    Example stuck_wedged_rc   : get (cont 666 true true issued_stuck) out_rc
                              = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example stuck_wedged_pend : get (cont 666 true true issued_stuck) out_pend
                              = Bits.of_nat pend_sz PEND_EXT0.
    Proof. reflexivity. Qed.

    (* That vector gives the core the benefit of the doubt: it holds done AND
       echoes a matching tag, which we cannot distinguish from a real answer we
       failed to arm, so the module stays conservatively wedged.  A core that
       really is showing its PREVIOUS result echoes the PREVIOUS tag, and then
       [out_pend]-keyed detection catches it -- which is why the violation test is
       keyed on [out_pend] and not on [out_armed]. *)
    Example stuck_stale_tag_failure : get (cont 666 true false issued_stuck) out_failure = Ob~1.
    Proof. reflexivity. Qed.
    Example stuck_stale_tag_rc      : get (cont 666 true false issued_stuck) out_rc
                                    = Bits.of_nat 16 MARS_RC_FAILURE.
    Proof. reflexivity. Qed.
    Example stuck_stale_tag_pcr0    : get (cont 666 true false issued_stuck) out_pcr0
                                    = Bits.of_nat digest_sz 42.
    Proof. reflexivity. Qed.

    (* --- ATTACK: interleave a command into a pending sequence ------------- *)
    (* Refused, and -- the part that matters -- [out_pend] and the outstanding
       request are left untouched, so the sequence can still complete. *)
    Example busy_regread_rc  : get (other act_regread 0 0 issued) out_rc
                             = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example busy_capget_rc   : get (other act_capabilityget MARS_PT_PCR 0 issued) out_rc
                             = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example busy_ext_rc      : get (ext 1 9 issued) out_rc
                             = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example busy_ext_pend    : get (ext 1 9 issued) out_pend
                             = Bits.of_nat pend_sz PEND_EXT0.
    Proof. reflexivity. Qed.
    Example busy_ext_req     : get (ext 1 9 issued) out_sha_req = Ob~1.
    Proof. reflexivity. Qed.
    (* A refused command must not disturb the in-flight message either. *)
    Example busy_ext_msg_dig : Bits.slice 512 digest_sz (get (ext 1 9 issued) out_sha_msg)
                             = Bits.of_nat digest_sz 7.
    Proof. reflexivity. Qed.

    (* PCR1 works the same way, and lands in the other register. *)
    Definition issued1   := ext 1 7 o_pcrs.
    Definition completed1 := cont 55 true true issued1.
    Example ext1_pend  : get issued1 out_pend  = Bits.of_nat pend_sz PEND_EXT1.
    Proof. reflexivity. Qed.
    Example ext1_msg   : Bits.slice 768 digest_sz (get issued1 out_sha_msg)
                       = Bits.of_nat digest_sz 99.
    Proof. reflexivity. Qed.
    Example done1_pcr1 : get completed1 out_pcr1 = Bits.of_nat digest_sz 55.
    Proof. reflexivity. Qed.
    Example done1_pcr0 : get completed1 out_pcr0 = Bits.of_nat digest_sz 42.
    Proof. reflexivity. Qed.

    (* ---------------------------------------------------------------------
       _MARS_Init and the st gate.
       --------------------------------------------------------------------- *)

    Definition get_st (sys: sys_t) v := ContextEnv.(getenv) (fst sys) v.

    (* --- the request ---------------------------------------------------- *)

    Example init_takes_seed  : get_st sys_init st_ps = Bits.of_nat digest_sz 5.
    Proof. reflexivity. Qed.
    Example init_pend        : get sys_init out_pend = Bits.of_nat pend_sz PEND_DPINIT.
    Proof. reflexivity. Qed.
    Example init_hmac_active : get sys_init out_hmac_active = Ob~1.
    Proof. reflexivity. Qed.
    Example init_hmac_req    : get sys_init out_hmac_req = Ob~1.
    Proof. reflexivity. Qed.
    Example init_armed       : get sys_init out_armed = Ob~1.
    Proof. reflexivity. Qed.
    Example init_st_still_0  : get sys_init out_st = Ob~0.
    Proof. reflexivity. Qed.
    Example init_len         : get sys_init out_hmac_len = Bits.of_nat 16 13.
    Proof. reflexivity. Qed.

    (* The KDF key is the seed just latched -- the NEW one, since statement
       order is sequential. *)
    Example init_key_is_seed : get sys_init out_hmac_key = Bits.of_nat digest_sz 5.
    Proof. reflexivity. Qed.

    (* The framing, field by field:
         [1]_4 || 'D' || 0x00 || "prd" || [8192]_4,  13 bytes, left-aligned.
       Implemented from reference-emulator/c/hw_sha2.c, NOT from its comments --
       those say [i]_2 and [L]_2 while the code emits four bytes for each
       (REVIEW.md section 3.5).  These slices are what would catch that. *)
    Example kdf_counter : Bits.slice 480 32 (get sys_init out_hmac_msg)
                        = Bits.of_nat 32 1.
    Proof. reflexivity. Qed.
    Example kdf_label   : Bits.slice 472 8 (get sys_init out_hmac_msg)
                        = Bits.of_nat 8 68.    (* 'D' = MARS_LD *)
    Proof. reflexivity. Qed.
    Example kdf_sep     : Bits.slice 464 8 (get sys_init out_hmac_msg)
                        = Bits.zero.
    Proof. reflexivity. Qed.
    Example kdf_ctx_p   : Bits.slice 456 8 (get sys_init out_hmac_msg)
                        = Bits.of_nat 8 112.
    Proof. reflexivity. Qed.
    Example kdf_ctx_r   : Bits.slice 448 8 (get sys_init out_hmac_msg)
                        = Bits.of_nat 8 114.
    Proof. reflexivity. Qed.
    Example kdf_ctx_d   : Bits.slice 440 8 (get sys_init out_hmac_msg)
                        = Bits.of_nat 8 100.
    Proof. reflexivity. Qed.
    Example kdf_L       : Bits.slice 408 32 (get sys_init out_hmac_msg)
                        = Bits.of_nat 32 8192.
    Proof. reflexivity. Qed.
    Example kdf_pad     : Bits.slice 0 408 (get sys_init out_hmac_msg)
                        = Bits.zero.
    Proof. reflexivity. Qed.

    (* --- completion ----------------------------------------------------- *)

    Example ready_dp   : get_st sys_ready st_dp = Bits.of_nat digest_sz 77.
    Proof. reflexivity. Qed.
    Example ready_st   : get sys_ready out_st = Ob~1.
    Proof. reflexivity. Qed.
    Example ready_pend : get sys_ready out_pend = Bits.of_nat pend_sz PEND_IDLE.
    Proof. reflexivity. Qed.
    (* the seed must NOT be left driven on the HMAC key port *)
    Example ready_key_zeroized : get sys_ready out_hmac_key = Bits.zero.
    Proof. reflexivity. Qed.
    Example ready_msg_zeroized : get sys_ready out_hmac_msg = Bits.zero.
    Proof. reflexivity. Qed.

    (* --- the gate ------------------------------------------------------- *)
    (* Before Init, everything except MARS_CapabilityGet is refused. *)
    Example uninit_regread : rc_of act_regread 0 0 sys_zero
                           = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example uninit_pcrextend : get (ext 0 7 sys_zero) out_rc
                             = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example uninit_pcrextend_issues_nothing :
      get (ext 0 7 sys_zero) out_sha_active = Ob~0.
    Proof. reflexivity. Qed.
    (* ...and MARS_CapabilityGet still answers, as it does in failure mode. *)
    Example uninit_capget : cap_of act_capabilityget MARS_PT_PCR 0 sys_zero
                          = Bits.of_nat 16 2.
    Proof. reflexivity. Qed.

    (* --- Init is the recovery path -------------------------------------- *)
    (* Spec section 5.3.1: failure mode persists "until reinitialized", so Init
       is exempt from the failure guard and clears it. *)
    Example init_clears_failure :
      get (step act_init arg_boot o_failed) out_failure = Ob~0.
    Proof. reflexivity. Qed.
    Example init_reissues_from_failed :
      get (step act_init arg_boot o_failed) out_pend
      = Bits.of_nat pend_sz PEND_DPINIT.
    Proof. reflexivity. Qed.

    (* REVIEW.md section 2.8: Init is the only way out of a wedged crypto step,
       so it is exempt from the busy guard AND from the st gate -- gating it on
       st = 0 would make the wedge permanent. *)
    Example init_unwedges :
      get (step act_init arg_boot issued_stuck) out_pend
      = Bits.of_nat pend_sz PEND_DPINIT.
    Proof. reflexivity. Qed.
    Example init_clears_stale_sha :
      get (step act_init arg_boot issued_stuck) out_sha_active = Ob~0.
    Proof. reflexivity. Qed.
    (* and it re-zeroes the PCRs, as spec section 5.4 requires *)
    Example init_zeroes_pcr0 :
      get (step act_init arg_boot o_pcrs) out_pcr0 = Bits.zero.
    Proof. reflexivity. Qed.

    (* --- Init is not host-reachable ------------------------------------- *)
    (* Without the protected request line it does nothing at all. *)
    Definition arg_noreq := arg_full 0 0 0 0 false false 0 false false 5 false.
    Example init_needs_req_rc :
      get (step act_init arg_noreq sys_zero) out_rc = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example init_needs_req_st :
      get (step act_init arg_noreq sys_ready) out_st = Ob~1.
    Proof. reflexivity. Qed.
    Example init_needs_req_pend :
      get (step act_init arg_noreq sys_zero) out_pend = Bits.of_nat pend_sz PEND_IDLE.
    Proof. reflexivity. Qed.

End Vectors.

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
        tfs_spec_decls := []
    |}.

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
