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

Require Import Hammer.Plugin.Hammer.
Set Hammer GSMode 63.

(* MARS_SEQ: a minimal TCG MARS device, Profile [TF-MARS-S256-P2], over two
   PCRs, with each crypto round trip split across MARS_Continue.  Examples/Mars/Spec.v
   is the one-action form and is checked against this one.  Every MARS_CC code
   has an arm, so [out_rc] is always written (REVIEW.md 3.4).  Sources:
   spec/mars-library-v1r14.md 5.3.1, 8.1.2, 8.3.2; reference-emulator/c/mars.c. *)

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
    Definition PEND_SNAP   := 4.
    Definition PEND_KDF    := 5.
    Definition PEND_SIGN   := 6.

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
    | out_pend       (* which crypto step is in flight; 0 = idle *)
    | out_st         (* 0 = uninitialized, 1 = DP is valid       *)
    | out_snap       (* MARS_Quote: the device snapshot           *)
    (* MARS_Quote's context, latched at issue.  Inputs are re-sampled on every
       step (MVP.md section 5.3), so a multi-step command would otherwise be
       able to mix arguments from two different invocations.  [in_nonce] needs
       no latch -- it is consumed in the snapshot at step 1. *)
    | out_ctx
    | out_sha_req       (* toggles on each new SHA-256 request      *)
    | out_sha_active    (* a SHA-256 request is outstanding         *)
    | out_hmac_req
    | out_hmac_active
    (* Secret: the crypto ports, ONE GROUP PER ATTACHED IP.  The two cores differ
       (sha256_core takes raw blocks, hmac_core takes finalize/final_len and a
       key), so per-IP groups keep each one right-sized. *)
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
    | out_pend      => pend_sz
    | out_st        => 1
    | out_snap      => digest_sz
    | out_ctx       => digest_sz
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

    (* Confidentiality classification (Contract.v [port_class]).  [Secret] is
       "outside what the guarantee quantifies over, so it may carry a secret and
       stays off the memory map", which spec 5.8 requires of the crypto port
       since DP and AK cross it.  Over-classifying a port-group member costs
       nothing.  Class and wiring are independent. *)
    Definition fs_inputs_class (x: fs_inputs) : port_class :=
    match x with
    | in_pt | in_idx | in_dig => Public
    | in_sha_res  | in_sha_valid  | in_sha_tag  => Secret
    | in_hmac_res | in_hmac_valid | in_hmac_tag => Secret
    | in_ps | in_init_req                      => Secret
    (* Quote's arguments are the host's own; nothing secret about them. *)
    | in_regsel | in_nonce | in_ctx | in_nlen | in_ctxlen => Public
    end.

    Definition fs_outputs_class (x: fs_outputs) : port_class :=
    match x with
    (* handshake bits an observer could see on the bus edge anyway *)
    | out_rc | out_cap | out_dout | out_pcr0 | out_pcr1 | out_failure
    | out_pend | out_st | out_snap | out_ctx
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
    Definition guard_failure (body: @tf_ops fs_states fs_inputs fs_outputs Empty_set)
        : @tf_ops fs_states fs_inputs fs_outputs Empty_set :=
    {[
        if ($out_failure ==[1] #1)
        then let $out_rc := #MARS_RC_FAILURE
        else `body`
    ]}.

    (* Interleaving is REFUSED: a command issued with a crypto step in flight is
       rejected, leaving [out_pend] and the request untouched (MVP.md 5.3).
       MARS_Continue is the exception, being what advances [out_pend].  Section
       6.2 has no BUSY code, so the host reads busy from [out_pend]
       (REVIEW.md 3.2). *)
    Definition guard_busy (body: @tf_ops fs_states fs_inputs fs_outputs Empty_set)
        : @tf_ops fs_states fs_inputs fs_outputs Empty_set :=
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

    (* Per-group handshake: a response counts when the group has a request
       outstanding, the IP asserts valid, AND the tag echoes the request bit
       driven at issue ([tf_ovar] reads the pre-cycle value, so [_req] is the one
       sent).  The tag alone binds it: a core holding [done] from an earlier
       request echoes that request's tag and raises a protocol violation. *)
    Definition resp_ok (v_valid v_tag: fs_inputs) (o_req o_active: fs_outputs)
        : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 tf_and
          (tf_op2 tf_and (tf_ovar o_active) (tf_ivar v_valid))
          (tf_op2 (tf_cmp 1 tf_eq) (tf_ivar v_tag) (tf_ovar o_req)).

    (* A response for a request that is not the outstanding one: the group has
       something in flight, the IP says valid, and the tag names a DIFFERENT
       request.  Spec section 5.6 requires failure mode on "any other internal
       error", and answering a request that is not outstanding is one. *)
    Definition violation (v_valid v_tag: fs_inputs) (o_req o_active: fs_outputs)
        : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 tf_and
          (tf_op2 tf_and (tf_ovar o_active) (tf_ivar v_valid))
          (tf_op2 (tf_cmp 1 tf_neq) (tf_ivar v_tag) (tf_ovar o_req)).

    (* Issue a request: drive the port, flip the request bit, mark the group
       active, record the step.  Flipping [_req] binds the next response, since
       a leftover answer carries the earlier tag.  A misbehaving IP leaves it
       fail-stop: failure mode on a tag mismatch, or WEDGED with [out_pend]
       nonzero, recoverable only by _MARS_Init (REVIEW.md 2.8). *)
    Definition issue_sha (step: nat)
                     (msg: @tf_expr fs_states fs_inputs fs_outputs) (len: nat)
        : @tf_ops fs_states fs_inputs fs_outputs Empty_set :=
    {[
        let $out_sha_msg    := `msg`;
        let $out_sha_len    := #len;
        let $out_sha_active := #1;
        let $out_sha_req    := !$out_sha_req;
        let $out_pend       := #step;
        let $out_rc         := #MARS_RC_SUCCESS
    ]}.

    (* A response for a request that is not the outstanding one.
       the tag echoes the request bit that was driven at issue.  [tf_ovar] reads
       the pre-cycle value, so [out_sha_req] here is the one that was sent. *)

    (* A protocol violation: a step IS outstanding and the IP asserts valid for a
       DIFFERENT request, which spec 5.6 makes an internal error.  Keyed on
       [_active], true exactly while a request is outstanding on that group, so a
       mismatched tag is an error rather than noise. *)

    (* Enter out_failure mode.  Zeroizes like [finish], a faulting IP being exactly
       when the trusted port should carry nothing (REVIEW.md 2.7), and clears
       [out_pend] for ONE unambiguous stuck state.  Every command but
       MARS_CapabilityGet answers MARS_RC_FAILURE until _MARS_Init (spec 5.3.1). *)
    (* Zeroize every group, whichever one misbehaved: a faulting IP is exactly
       when nothing should be left driven on any trusted port. *)
    Definition zeroize : @tf_ops fs_states fs_inputs fs_outputs Empty_set :=
    {[
        let $out_sha_msg     := #0;
        let $out_sha_active  := #0;
        let $out_hmac_key    := #0;
        let $out_hmac_msg    := #0;
        let $out_hmac_active := #0
    ]}.

    Definition fault : @tf_ops fs_states fs_inputs fs_outputs Empty_set :=
    {[
        `zeroize`;
        let $out_pend    := #PEND_IDLE;
        let $out_failure := #1;
        let $out_rc      := #MARS_RC_FAILURE
    ]}.

    (* End of a sequence: zeroize the trusted ports and disarm.  The ports hold
       their value indefinitely otherwise, which is how AK would stay driven on
       256 wires after a Quote (REVIEW.md section 2.7). *)
    Definition finish : @tf_ops fs_states fs_inputs fs_outputs Empty_set :=
    {[
        `zeroize`;
        let $out_pend  := #PEND_IDLE;
        let $out_rc    := #MARS_RC_SUCCESS
    ]}.

    (* Commands are refused until _MARS_Init COMPLETES, which keeps MARS_Quote
       from deriving AK = KDF(0,'R',ctx) off a zero DP (REVIEW.md 2.2).
       [in_init_req] authorises STARTING an initialization; [out_st] records
       that one finished (MVP.md 2.2 deviation 3).  MARS_CapabilityGet is
       exempt: every value it returns is a Profile constant. *)
    Definition guard_init (body: @tf_ops fs_states fs_inputs fs_outputs Empty_set)
        : @tf_ops fs_states fs_inputs fs_outputs Empty_set :=
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
       The Profile pins the endianness (MVP.md 2).  Four shapes over two PCRs,
       three lengths -- 36 / 68 / 68 / 100 bytes, left-aligned in the 1024-bit
       SHA port.  The trailing field is the NONCE. *)
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
       32-byte context instead of the three-byte "prd".  42 bytes. *)
    Definition ak_kdf_msg : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 (tf_concat 336 176)
          (tf_op2 (tf_concat 32 304) (tf_const 1)
            (tf_op2 (tf_concat 8 296) (tf_const MARS_LR)
              (tf_op2 (tf_concat 8 288) (tf_const 0)
                (tf_op2 (tf_concat digest_sz 32) (tf_ovar out_ctx)
                  (tf_const 8192)))))
          (tf_const 0).

    (* CryptSign's message is the 32-byte snapshot, left-aligned. *)
    Definition sign_msg : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 (tf_concat digest_sz 256) (tf_ovar out_snap) (tf_const 0).

    (* Hand a completed group back to idle so its adapter drops valid (A7) and
       the next request can arm. *)
    Definition done_sha : @tf_ops fs_states fs_inputs fs_outputs Empty_set :=
    {[ let $out_sha_msg := #0; let $out_sha_active := #0 ]}.

    Definition done_hmac : @tf_ops fs_states fs_inputs fs_outputs Empty_set :=
    {[ let $out_hmac_key := #0; let $out_hmac_msg := #0;
       let $out_hmac_active := #0 ]}.

    Definition issue_hmac (step: nat)
                     (key msg: @tf_expr fs_states fs_inputs fs_outputs) (len: nat)
        : @tf_ops fs_states fs_inputs fs_outputs Empty_set :=
    {[
        let $out_hmac_key    := `key`;
        let $out_hmac_msg    := `msg`;
        let $out_hmac_len    := #len;
        let $out_hmac_active := #1;
        let $out_hmac_req    := !$out_hmac_req;
        let $out_pend        := #step;
        let $out_rc          := #MARS_RC_SUCCESS
    ]}.

    (* A command this Profile excludes (spec section 7).  Eight of the thirteen
       codes are excluded outright; PcrExtend and Quote are in the Profile but
       not yet built, and answer MARS_RC_COMMAND until they are. *)
    Definition unsupported : @tf_ops fs_states fs_inputs fs_outputs Empty_set :=
        guard_failure {[ let $out_rc := #MARS_RC_COMMAND ]}.

    (* An output HOLDS its value until an action writes it, so a Quote's signature
       would keep driving 256 wires until the next RegRead.  Every command clears
       the RESULT registers first.  The device-state outputs stay (MVP.md 6.1),
       and the crypt_* ports keep an in-flight request stable, zeroizing at
       sequence end and in every error arm instead (REVIEW.md 2.7). *)
    Definition clear_results (body: @tf_ops fs_states fs_inputs fs_outputs Empty_set)
        : @tf_ops fs_states fs_inputs fs_outputs Empty_set :=
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
        (@tf_ops fs_states fs_inputs fs_outputs Empty_set)
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

        (* MARS_RegRead -- spec section 8.3.2.  An out-of-range index gives
           MARS_RC_REG (7) and [out_dout] reads zero from [clear_results].  The
           host contract either way: check out_rc before using out_dout. *)
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
                    else if ($out_pend ==[pend_sz] #PEND_SNAP) then
                        (* step 2: snapshot taken, now derive the AK *)
                        let $out_snap := $in_sha_res;
                        `done_sha`;
                        `issue_hmac PEND_KDF (tf_svar st_dp) ak_kdf_msg 42`
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
                    else if ($out_pend ==[pend_sz] #PEND_KDF) then
                        (* step 3: AK derived.  It goes to a state variable and
                           straight back out as the signing key -- never to a
                           Public output. *)
                        let $st_ak := $in_hmac_res;
                        `issue_hmac PEND_SIGN (tf_svar st_ak) sign_msg 32`
                    else if ($out_pend ==[pend_sz] #PEND_SIGN) then
                        (* step 4: the signature is the result.  AK is zeroized
                           here rather than left in a register, per MVP.md
                           section 2.2 deviation 5. *)
                        let $out_dout := $in_hmac_res;
                        let $st_ak    := #0;
                        `finish`
                    else
                        let $out_rc := #MARS_RC_VALUE
                else
                    let $out_rc := #MARS_RC_VALUE
            ]}

        (* _MARS_Init -- spec section 5.4, a Profile command gated on [in_init_req],
           which the platform drives (section 5.8).  It runs unguarded because it
           is what clears failure mode (5.3.1) and the ONLY recovery from a wedged
           crypto step (REVIEW.md 2.8).  Protection comes from [in_init_req] being
           a Secret input, which is where spec 5.8 puts it. *)
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
        (* MARS_Quote -- spec 8.5.1.  Four strobes, three round trips: SNAP hashes
           regSelect || REGs || nonce, KDF derives AK, SIGN signs the snapshot,
           and the last Continue publishes dout and zeroizes AK.  Step 3 -> 4 is
           REVIEW.md 2.1: consecutive arms write [st_ak] then Public [out_dout],
           so tag binding is what keeps the AK off the wire. *)
        | act_quote =>
            guard_failure (guard_init (guard_busy {[
                if ($in_nlen !=[arg_sz] #32) then
                    let $out_rc := #MARS_RC_VALUE
                else if ($in_ctxlen !=[arg_sz] #32) then
                    let $out_rc := #MARS_RC_VALUE
                else
                    (* latch the context: step 2 needs it, and by then the
                       inputs may carry another command's arguments *)
                    let $out_ctx := $in_ctx;
                    if ($in_regsel ==[32] #0) then
                        `issue_sha PEND_SNAP snap_none 36`
                    else if ($in_regsel ==[32] #1) then
                        `issue_sha PEND_SNAP (snap_one out_pcr0) 68`
                    else if ($in_regsel ==[32] #2) then
                        `issue_sha PEND_SNAP (snap_one out_pcr1) 68`
                    else if ($in_regsel ==[32] #3) then
                        `issue_sha PEND_SNAP snap_both 100`
                    else
                        (* regSelect names a register this Profile does not
                           implement -- mars.c: regSelect >> PROFILE_COUNT_REG *)
                        let $out_rc := #MARS_RC_REG
            ]}))
        | act_sign             => unsupported
        | act_signatureverify  => unsupported
        end.

    Definition fs_transitions (act: fs_action)
        : (@tf_ops fs_states fs_inputs fs_outputs Empty_set) :=
        clear_results (fs_command act).

    Definition fs_step := tf_ops_run fs_states_size fs_inputs_size fs_outputs_size no_ips.

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
                        (rsel nonce ctx nlen ctxlen: nat)
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
        | in_regsel     => Bits.of_nat 32 rsel
        | in_nonce      => Bits.of_nat digest_sz nonce
        | in_ctx        => Bits.of_nat digest_sz ctx
        | in_nlen       => Bits.of_nat arg_sz nlen
        | in_ctxlen     => Bits.of_nat arg_sz ctxlen
        end.

    Definition arg (pt idx : nat) :=
        arg_full pt idx 0 0 false false 0 false false 0 false 0 0 0 32 32.

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
    Definition arg_boot := arg_full 0 0 0 0 false false 0 false false 5 true 0 0 0 32 32.
    Definition arg_hmac (r: nat) (v t: bool) :=
        arg_full 0 0 0 0 false false r v t 0 false 0 0 0 32 32.

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

    (* An invalid tag CLEARS [out_cap], so no command returns a previous command's
       result.  A documented divergence from the C emulator, whose sentinel lives
       in the caller's buffer (oracle/stage1.expected, in_pt = 0, 12, 13).  The
       host contract either way: check out_rc before using out_cap. *)
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

    (* Stage 2, the crypto handshake: the cases REVIEW.md 2.1 is about.  A mock IP
       is a choice of (in_sha_res, in_sha_valid, in_sha_tag) on the input vector,
       so every attack below is expressible against the module alone. *)

    (* Step 1: host issues PcrExtend(in_idx, in_dig). *)
    Definition ext (idx dig: nat) out :=
        run_in act_pcrextend
          (arg_full 0 idx dig 0 false false 0 false false 0 false 0 0 0 32 32) out.

    (* Step 2: glue pulses Continue with whatever the SHA core is driving. *)
    Definition cont (res: nat) (valid tag: bool) out :=
        run_in act_continue
          (arg_full 0 0 0 res valid tag 0 false false 0 false 0 0 0 32 32) out.

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
    Example issue_active    : get issued out_sha_active = Ob~1.
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
    Example done_inactive : get completed out_sha_active = Ob~0.
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
    Example stale_tag_inactive : get faulted out_sha_active = Ob~0.
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
    (* The second one finds the group inactive and does nothing. *)
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
       start, so it answers a NEW request while still showing the earlier tag.
       The tag turns that into failure mode with a reason. *)
    Definition issued_stuck :=
        run_in act_pcrextend
          (arg_full 0 0 7 0 true false 0 false false 0 false 0 0 0 32 32) o_pcrs.

    Example stuck_pend   : get issued_stuck out_pend = Bits.of_nat pend_sz PEND_EXT0.
    Proof. reflexivity. Qed.
    Example stuck_active : get issued_stuck out_sha_active = Ob~1.
    Proof. reflexivity. Qed.

    (* The core is still showing an earlier result, so its tag is that request's
       bit and the comparison fails. *)
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
    Example init_active      : get sys_init out_hmac_active = Ob~1.
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
    Definition arg_noreq := arg_full 0 0 0 0 false false 0 false false 5 false 0 0 0 32 32.
    Example init_needs_req_rc :
      get (step act_init arg_noreq sys_zero) out_rc = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example init_needs_req_st :
      get (step act_init arg_noreq sys_ready) out_st = Ob~1.
    Proof. reflexivity. Qed.
    Example init_needs_req_pend :
      get (step act_init arg_noreq sys_zero) out_pend = Bits.of_nat pend_sz PEND_IDLE.
    Proof. reflexivity. Qed.

    (* ---------------------------------------------------------------------
       MARS_Quote.  Four strobes, three round trips.
       --------------------------------------------------------------------- *)

    Definition arg_quote (rsel nonce ctx: nat) :=
        arg_full 0 0 0 0 false false 0 false false 0 false rsel nonce ctx 32 32.
    Definition arg_quote_len (rsel nl cl: nat) :=
        arg_full 0 0 0 0 false false 0 false false 0 false rsel 0 0 nl cl.
    Definition cont_h (r: nat) (v t: bool) sys := step act_continue (arg_hmac r v t) sys.

    (* regSelect = 3 selects both PCRs: the 100-byte shape. *)
    Definition q1 := step act_quote (arg_quote 3 9 11) o_pcrs.

    Example q1_pend   : get q1 out_pend = Bits.of_nat pend_sz PEND_SNAP.
    Proof. reflexivity. Qed.
    Example q1_active : get q1 out_sha_active = Ob~1.
    Proof. reflexivity. Qed.
    Example q1_len    : get q1 out_sha_len = Bits.of_nat 16 100.
    Proof. reflexivity. Qed.
    (* the context is latched at issue, because step 2 needs it and the inputs
       will have moved on by then *)
    Example q1_ctx_latched : get q1 out_ctx = Bits.of_nat digest_sz 11.
    Proof. reflexivity. Qed.

    (* The snapshot's field order, which is what MARS correctness rests on:
       regSelect big-endian first, then each selected register in index order,
       then the nonce.  100 bytes left-aligned in the 1024-bit port. *)
    Example snap3_regsel : Bits.slice 992 32 (get q1 out_sha_msg) = Bits.of_nat 32 3.
    Proof. reflexivity. Qed.
    Example snap3_pcr0   : Bits.slice 736 digest_sz (get q1 out_sha_msg)
                         = Bits.of_nat digest_sz 42.
    Proof. reflexivity. Qed.
    Example snap3_pcr1   : Bits.slice 480 digest_sz (get q1 out_sha_msg)
                         = Bits.of_nat digest_sz 99.
    Proof. reflexivity. Qed.
    Example snap3_nonce  : Bits.slice 224 digest_sz (get q1 out_sha_msg)
                         = Bits.of_nat digest_sz 9.
    Proof. reflexivity. Qed.
    Example snap3_pad    : Bits.slice 0 224 (get q1 out_sha_msg) = Bits.zero.
    Proof. reflexivity. Qed.

    (* The other three shapes, by length and by which register lands where. *)
    Definition q1_none := step act_quote (arg_quote 0 9 11) o_pcrs.
    Example snap0_len   : get q1_none out_sha_len = Bits.of_nat 16 36.
    Proof. reflexivity. Qed.
    Example snap0_nonce : Bits.slice 736 digest_sz (get q1_none out_sha_msg)
                        = Bits.of_nat digest_sz 9.
    Proof. reflexivity. Qed.

    Definition q1_pcr0 := step act_quote (arg_quote 1 9 11) o_pcrs.
    Example snap1_len  : get q1_pcr0 out_sha_len = Bits.of_nat 16 68.
    Proof. reflexivity. Qed.
    Example snap1_reg  : Bits.slice 736 digest_sz (get q1_pcr0 out_sha_msg)
                       = Bits.of_nat digest_sz 42.
    Proof. reflexivity. Qed.

    Definition q1_pcr1 := step act_quote (arg_quote 2 9 11) o_pcrs.
    Example snap2_len  : get q1_pcr1 out_sha_len = Bits.of_nat 16 68.
    Proof. reflexivity. Qed.
    (* regSelect = 2 selects PCR1 only, so PCR1 -- not PCR0 -- sits in the slot
       right after the selector.  Getting this wrong is the classic snapshot
       bug and it would still hash to something plausible. *)
    Example snap2_reg  : Bits.slice 736 digest_sz (get q1_pcr1 out_sha_msg)
                       = Bits.of_nat digest_sz 99.
    Proof. reflexivity. Qed.

    (* --- argument validation -------------------------------------------- *)
    Example quote_bad_regsel : get (step act_quote (arg_quote 4 9 11) o_pcrs) out_rc
                             = Bits.of_nat 16 MARS_RC_REG.
    Proof. reflexivity. Qed.
    Example quote_bad_regsel_issues_nothing :
      get (step act_quote (arg_quote 4 9 11) o_pcrs) out_sha_active = Ob~0.
    Proof. reflexivity. Qed.
    Example quote_bad_nlen : get (step act_quote (arg_quote_len 3 16 32) o_pcrs) out_rc
                           = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example quote_bad_ctxlen : get (step act_quote (arg_quote_len 3 32 16) o_pcrs) out_rc
                             = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example quote_before_init : get (step act_quote (arg_quote 3 9 11) sys_zero) out_rc
                              = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.

    (* --- the honest sequence -------------------------------------------- *)
    (* sha_req was 0, so the snapshot answer carries tag = 1.  hmac_req was 1
       after Init, so the KDF answer carries tag = 0 and the sign answer tag = 1;
       the alternation is exactly what binds each response to its request. *)
    Definition q2 := cont 1000 true true  q1.   (* snapshot back  *)
    Definition q3 := cont_h 2000 true false q2.  (* AK back        *)
    Definition q4 := cont_h 3000 true true  q3.  (* signature back *)

    Example q2_snap    : get q2 out_snap = Bits.of_nat digest_sz 1000.
    Proof. reflexivity. Qed.
    Example q2_pend    : get q2 out_pend = Bits.of_nat pend_sz PEND_KDF.
    Proof. reflexivity. Qed.
    (* the KDF is keyed with DP, and DP came from Init *)
    Example q2_key_is_dp : get q2 out_hmac_key = Bits.of_nat digest_sz 77.
    Proof. reflexivity. Qed.
    Example q2_len     : get q2 out_hmac_len = Bits.of_nat 16 42.
    Proof. reflexivity. Qed.
    (* the SHA group is handed back so its adapter drops valid (A7) *)
    Example q2_sha_idle : get q2 out_sha_active = Ob~0.
    Proof. reflexivity. Qed.

    (* The AK frame: [1]_4 || 'R' || 0x00 || ctx_32 || [8192]_4.  The label is
       the ONLY thing separating a restricted attestation key from an
       unrestricted signing key (spec section 5.5), which is why it is built
       here and not in the adapter. *)
    Example akkdf_counter : Bits.slice 480 32 (get q2 out_hmac_msg) = Bits.of_nat 32 1.
    Proof. reflexivity. Qed.
    Example akkdf_label   : Bits.slice 472 8 (get q2 out_hmac_msg)
                          = Bits.of_nat 8 MARS_LR.
    Proof. reflexivity. Qed.
    Example akkdf_sep     : Bits.slice 464 8 (get q2 out_hmac_msg) = Bits.zero.
    Proof. reflexivity. Qed.
    Example akkdf_ctx     : Bits.slice 208 digest_sz (get q2 out_hmac_msg)
                          = Bits.of_nat digest_sz 11.
    Proof. reflexivity. Qed.
    Example akkdf_L       : Bits.slice 176 32 (get q2 out_hmac_msg)
                          = Bits.of_nat 32 8192.
    Proof. reflexivity. Qed.

    Example q3_pend  : get q3 out_pend = Bits.of_nat pend_sz PEND_SIGN.
    Proof. reflexivity. Qed.
    Example q3_ak    : get_st q3 st_ak = Bits.of_nat digest_sz 2000.
    Proof. reflexivity. Qed.
    (* the AK becomes the signing key, and the message is the snapshot *)
    Example q3_key_is_ak : get q3 out_hmac_key = Bits.of_nat digest_sz 2000.
    Proof. reflexivity. Qed.
    Example q3_msg_is_snap : Bits.slice 256 digest_sz (get q3 out_hmac_msg)
                           = Bits.of_nat digest_sz 1000.
    Proof. reflexivity. Qed.
    Example q3_len   : get q3 out_hmac_len = Bits.of_nat 16 32.
    Proof. reflexivity. Qed.

    (* THE step that matters: at pend = KDF the AK is in flight, and [out_dout]
       is Public.  It must not have moved. *)
    Example q3_ak_not_published : get q3 out_dout = Bits.zero.
    Proof. reflexivity. Qed.

    Example q4_sig   : get q4 out_dout = Bits.of_nat digest_sz 3000.
    Proof. reflexivity. Qed.
    Example q4_pend  : get q4 out_pend = Bits.of_nat pend_sz PEND_IDLE.
    Proof. reflexivity. Qed.
    (* AK zeroized at sequence end rather than left in a register -- MVP.md
       section 2.2 deviation 5, mitigating the section 5.5 departure. *)
    Example q4_ak_zeroized  : get_st q4 st_ak = Bits.zero.
    Proof. reflexivity. Qed.
    Example q4_key_zeroized : get q4 out_hmac_key = Bits.zero.
    Proof. reflexivity. Qed.
    Example q4_msg_zeroized : get q4 out_hmac_msg = Bits.zero.
    Proof. reflexivity. Qed.
    Example q4_snap_visible : get q4 out_snap = Bits.of_nat digest_sz 1000.
    Proof. reflexivity. Qed.

    (* --- ATTACK: publish the AK at step 3 -> 4 --------------------------- *)
    (* REVIEW.md section 2.1's escalation.  At pend = SIGN the next result lands
       on [out_dout], which is Public.  A response the module cannot bind to its
       own request must never get there -- otherwise the value on [out_dout] is
       the Attestation Key in clear. *)
    Example sign_stale_tag_faults : get (cont_h 2000 true false q3) out_failure = Ob~1.
    Proof. reflexivity. Qed.
    Example sign_stale_tag_no_publish :
      get (cont_h 2000 true false q3) out_dout = Bits.zero.
    Proof. reflexivity. Qed.
    Example sign_no_valid_no_publish :
      get (cont_h 2000 false true q3) out_dout = Bits.zero.
    Proof. reflexivity. Qed.
    Example sign_no_valid_still_pending :
      get (cont_h 2000 false true q3) out_pend = Bits.of_nat pend_sz PEND_SIGN.
    Proof. reflexivity. Qed.
    (* and the SHA group answering while an HMAC step is outstanding does
       nothing either -- the groups are bound separately *)
    Example sign_wrong_group : get (cont 2000 true true q3) out_dout = Bits.zero.
    Proof. reflexivity. Qed.

    (* --- ATTACK: interleave into a Quote --------------------------------- *)
    Example quote_busy_refuses_regread :
      get (run act_regread 0 0 q1) out_rc = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example quote_busy_keeps_pend :
      get (run act_regread 0 0 q1) out_pend = Bits.of_nat pend_sz PEND_SNAP.
    Proof. reflexivity. Qed.

End Vectors.

Section Lowering.

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
        tfs_spec_ips := Empty_set;
        tfs_spec_ip := no_ips;
        tfs_spec_decls := []
    |}.

    Definition tf_schedule := tfs_schedule tfs_ctx 10.

    Definition tf_ctx : TFSynthContext := {|
        tf_sched_ctx := tf_schedule;

        tf_action_encoding := fs_action_encoding;
        tf_action_encoding_inj := fs_action_encoding_inj;
    |}.

  Definition package := Lowering.package tf_ctx "Example_MarsSeq".

End Lowering.

(* Extraction *)

Definition prog := Interop.Backends.register package.
Set Extraction Output Directory "build".
Extraction "Example_MarsSeq.ml" prog.
