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
    unrecognized code fires no rule, and [rc] would then retain the previous
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

    (* crypt_op -- what the attached IP is being asked for (MVP.md section 5.2). *)
    Definition CRYPT_IDLE   := 0.
    Definition CRYPT_SHA256 := 1.
    Definition CRYPT_HMAC   := 2.

    (* pend -- which step of which command is in flight; 0 is idle.  DPINIT,
       SNAP, KDF and SIGN arrive with Init and Quote at Stage 4. *)
    Definition PEND_IDLE   := 0.
    Definition PEND_EXT0   := 1.
    Definition PEND_EXT1   := 2.

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
    | fs_act_selftest           (* MARS_CC_SelfTest          0 *)
    | fs_act_capabilityget      (* MARS_CC_CapabilityGet     1 *)
    | fs_act_sequencehash       (* MARS_CC_SequenceHash      2 *)
    | fs_act_sequenceupdate     (* MARS_CC_SequenceUpdate    3 *)
    | fs_act_sequencecomplete   (* MARS_CC_SequenceComplete  4 *)
    | fs_act_pcrextend          (* MARS_CC_PcrExtend         5 *)
    | fs_act_regread            (* MARS_CC_RegRead           6 *)
    | fs_act_derive             (* MARS_CC_Derive            7 *)
    | fs_act_dpderive           (* MARS_CC_DpDerive          8 *)
    | fs_act_publicread         (* MARS_CC_PublicRead        9 *)
    | fs_act_quote              (* MARS_CC_Quote            10 *)
    | fs_act_sign               (* MARS_CC_Sign             11 *)
    | fs_act_signatureverify    (* MARS_CC_SignatureVerify  12 *)
    | fs_act_continue           (* Profile-specific         13 *)
    .

    (* MSB first, 16 bits. *)
    Definition fs_action_encoding (a: fs_action) : bits_t 16 :=
    match a with
    | fs_act_selftest         => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | fs_act_capabilityget    => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1
    | fs_act_sequencehash     => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0
    | fs_act_sequenceupdate   => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1
    | fs_act_sequencecomplete => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0
    | fs_act_pcrextend        => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~1
    | fs_act_regread          => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0
    | fs_act_derive           => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1
    | fs_act_dpderive         => Ob~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0
    | fs_act_publicread       => Ob~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~1
    | fs_act_quote            => Ob~0~0~0~0~0~0~0~0~0~0~0~0~1~0~1~0
    | fs_act_sign             => Ob~0~0~0~0~0~0~0~0~0~0~0~0~1~0~1~1
    | fs_act_signatureverify  => Ob~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0~0
    | fs_act_continue         => Ob~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0~1
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
    | fs_st_ps
    | fs_st_dp
    | fs_st_ak
    .

    Inductive fs_inputs :=
    | fs_in_pt            (* MARS_CapabilityGet: property tag        *)
    | fs_in_idx           (* MARS_RegRead / MARS_PcrExtend: index    *)
    | fs_in_dig           (* MARS_PcrExtend: the digest to extend    *)
    (* From the crypto IP.  Trusted, and NOT to be memory-mapped. *)
    | fs_in_crypt_res
    | fs_in_crypt_valid
    | fs_in_crypt_tag     (* echoes the crypt_req the result answers *)
    .

    (* PCRs are OUTPUT variables, not state variables: they are meant to be
       public (MARS_RegRead hands them out), and making them secret would taint
       the whole Quote datapath.  MVP.md section 6.1. *)
    Inductive fs_outputs :=
    (* Public: results *)
    | fs_out_rc
    | fs_out_cap
    | fs_out_dout
    (* Public: device state *)
    | fs_out_pcr0
    | fs_out_pcr1
    | fs_out_failure
    | fs_out_pend       (* which crypto step is in flight; 0 = idle *)
    | fs_out_armed      (* two-phase arming, REVIEW.md section 2.1  *)
    | fs_out_crypt_req  (* toggles on each new request              *)
    (* Trusted: the crypto port.  The netlist does not record this -- keeping
       these four off the MMIO map is the integrator's obligation (MVP.md
       section 9, A5), which spec section 5.8 imposes independently. *)
    | fs_out_crypt_op
    | fs_out_crypt_key
    | fs_out_crypt_msg
    | fs_out_crypt_len
    .

    Definition fs_states_size (x: fs_states) : nat :=
    match x with
    | fs_st_ps => digest_sz
    | fs_st_dp => digest_sz
    | fs_st_ak => digest_sz
    end.

    Definition fs_inputs_size (x: fs_inputs) : nat :=
    match x with
    | fs_in_pt          => arg_sz
    | fs_in_idx         => arg_sz
    | fs_in_dig         => digest_sz
    | fs_in_crypt_res   => digest_sz
    | fs_in_crypt_valid => 1
    | fs_in_crypt_tag   => 1
    end.

    Definition fs_outputs_size (x: fs_outputs) : nat :=
    match x with
    | fs_out_rc        => rc_sz
    | fs_out_cap       => 16
    | fs_out_dout      => digest_sz
    | fs_out_pcr0      => digest_sz
    | fs_out_pcr1      => digest_sz
    | fs_out_failure   => 1
    | fs_out_pend      => pend_sz
    | fs_out_armed     => 1
    | fs_out_crypt_req => 1
    | fs_out_crypt_op  => 4
    | fs_out_crypt_key => digest_sz
    | fs_out_crypt_msg => msg_sz
    | fs_out_crypt_len => 16
    end.

    Definition fs_states_t := tf_states_type fs_states_size.

    Definition fs_states_init (x: fs_states) : (fs_states_t x) :=
    match x with
    | fs_st_ps => Bits.zero
    | fs_st_dp => Bits.zero
    | fs_st_ak => Bits.zero
    end.

    (* The dispatcher's failure-mode rule (spec section 8, informative comment;
       normative in section 5.3.1): in failure mode every command except
       MARS_CapabilityGet returns MARS_RC_FAILURE, and it does so BEFORE the
       unsupported-command check. *)
    Definition guard_failure (body: @tf_ops fs_states fs_inputs fs_outputs)
        : @tf_ops fs_states fs_inputs fs_outputs :=
    {[
        if ($fs_out_failure ==[1] #1)
        then let $fs_out_rc := #MARS_RC_FAILURE
        else `body`
    ]}.

    (* Interleaving is refused, not merely discouraged: any command issued while
       a crypto step is in flight is rejected and leaves [pend] and the request
       untouched (MVP.md section 5.3).  MARS_Continue is the exception by
       construction -- it is the thing that advances [pend] -- and an excluded
       command answers MARS_RC_COMMAND regardless, since there is nothing to
       refuse.  Busy is never an rc of its own: section 6.2 has no BUSY code and
       3 is Reserved, so the host reads busy from [pend] (REVIEW.md 3.2). *)
    Definition guard_busy (body: @tf_ops fs_states fs_inputs fs_outputs)
        : @tf_ops fs_states fs_inputs fs_outputs :=
    {[
        if ($fs_out_pend !=[pend_sz] #PEND_IDLE)
        then let $fs_out_rc := #MARS_RC_VALUE
        else `body`
    ]}.

    (* PcrExtend hashes PCR[i] || dig -- 64 bytes -- left-aligned in the
       1024-bit port.  Two concatenations: the 512-bit message, then the
       zero padding out to the port width. *)
    Definition ext_msg (pcr: fs_outputs) : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 (tf_concat 512 512)
          (tf_op2 (tf_concat digest_sz digest_sz) (tf_ovar pcr) (tf_ivar fs_in_dig))
          (tf_const 0).

    (* Issue a request: drive the port, flip the request bit, record the step.

       [armed] is set ONLY while crypt_valid is low.  That is the whole
       two-phase arming fix (REVIEW.md section 2.1): a core that holds [done]
       high from its previous request cannot satisfy arm-and-fire, so the module
       WEDGES instead of latching a stale result.  Wedging is the intended
       failure -- at the KDF->SIGN step a stale result would publish the
       Attestation Key on [dout]. *)
    Definition issue (op: nat) (pend: nat)
                     (msg: @tf_expr fs_states fs_inputs fs_outputs) (len: nat)
        : @tf_ops fs_states fs_inputs fs_outputs :=
    {[
        let $fs_out_crypt_msg := `msg`;
        let $fs_out_crypt_len := #len;
        let $fs_out_crypt_op  := #op;
        let $fs_out_crypt_req := !$fs_out_crypt_req;
        let $fs_out_pend      := #pend;
        let $fs_out_armed     := ($fs_in_crypt_valid ==[1] #0);
        let $fs_out_rc        := #MARS_RC_SUCCESS
    ]}.

    (* A response counts only if the module armed it, the IP asserts valid, AND
       the tag echoes the request bit that was driven at issue.  [tf_ovar] reads
       the pre-cycle value, so [crypt_req] here is the one that was sent. *)
    Definition response_ok : @tf_expr fs_states fs_inputs fs_outputs :=
        tf_op2 tf_and
          (tf_op2 tf_and (tf_ovar fs_out_armed) (tf_ivar fs_in_crypt_valid))
          (tf_op2 (tf_cmp 1 tf_eq) (tf_ivar fs_in_crypt_tag) (tf_ovar fs_out_crypt_req)).

    (* End of a sequence: zeroize the trusted ports and disarm.  The ports hold
       their value indefinitely otherwise, which is how AK would stay driven on
       256 wires after a Quote (REVIEW.md section 2.7). *)
    Definition finish : @tf_ops fs_states fs_inputs fs_outputs :=
    {[
        let $fs_out_crypt_key := #0;
        let $fs_out_crypt_msg := #0;
        let $fs_out_crypt_op  := #CRYPT_IDLE;
        let $fs_out_pend      := #PEND_IDLE;
        let $fs_out_armed     := #0;
        let $fs_out_rc        := #MARS_RC_SUCCESS
    ]}.

    (* A command this Profile excludes (spec section 7).  Eight of the thirteen
       codes are excluded outright; PcrExtend and Quote are in the Profile but
       not yet built, and answer MARS_RC_COMMAND until they are. *)
    Definition unsupported : @tf_ops fs_states fs_inputs fs_outputs :=
        guard_failure {[ let $fs_out_rc := #MARS_RC_COMMAND ]}.

    (* An output variable HOLDS its value unless an action writes it, so a stale
       result survives every command that does not overwrite it -- after a Quote,
       [dout] would keep driving the signature on 256 wires until the next
       RegRead.  Every command therefore clears the RESULT registers first.

       Scope matters, and only these two (later [snap]) may be cleared:
         - [pcr0]/[pcr1]/[failure] -- and later [st]/[pend]/[armed] -- are
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
        let $fs_out_dout := #0;
        let $fs_out_cap  := #0;
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

        (* MARS_CapabilityGet -- spec section 8.1.2.  Note there is NO failure
           guard: section 5.3.1 excludes this command from failure mode.  All
           eleven Table 6 tags, then MARS_RC_VALUE. *)
        | fs_act_capabilityget =>
            guard_busy {[
                if ($fs_in_pt ==[arg_sz] #MARS_PT_PCR) then
                    let $fs_out_cap := #PROFILE_COUNT_PCR;
                    let $fs_out_rc  := #MARS_RC_SUCCESS
                else if ($fs_in_pt ==[arg_sz] #MARS_PT_TSR) then
                    let $fs_out_cap := #PROFILE_COUNT_TSR;
                    let $fs_out_rc  := #MARS_RC_SUCCESS
                else if ($fs_in_pt ==[arg_sz] #MARS_PT_LEN_DIGEST) then
                    let $fs_out_cap := #PROFILE_LEN_DIGEST;
                    let $fs_out_rc  := #MARS_RC_SUCCESS
                else if ($fs_in_pt ==[arg_sz] #MARS_PT_LEN_SIGN) then
                    let $fs_out_cap := #PROFILE_LEN_SIGN;
                    let $fs_out_rc  := #MARS_RC_SUCCESS
                else if ($fs_in_pt ==[arg_sz] #MARS_PT_LEN_KSYM) then
                    let $fs_out_cap := #PROFILE_LEN_KSYM;
                    let $fs_out_rc  := #MARS_RC_SUCCESS
                else if ($fs_in_pt ==[arg_sz] #MARS_PT_LEN_KPUB) then
                    let $fs_out_cap := #PROFILE_LEN_KPUB;
                    let $fs_out_rc  := #MARS_RC_SUCCESS
                else if ($fs_in_pt ==[arg_sz] #MARS_PT_LEN_KPRV) then
                    let $fs_out_cap := #PROFILE_LEN_KPRV;
                    let $fs_out_rc  := #MARS_RC_SUCCESS
                else if ($fs_in_pt ==[arg_sz] #MARS_PT_ALG_HASH) then
                    let $fs_out_cap := #PROFILE_ALG_HASH;
                    let $fs_out_rc  := #MARS_RC_SUCCESS
                else if ($fs_in_pt ==[arg_sz] #MARS_PT_ALG_SIGN) then
                    let $fs_out_cap := #PROFILE_ALG_SIGN;
                    let $fs_out_rc  := #MARS_RC_SUCCESS
                else if ($fs_in_pt ==[arg_sz] #MARS_PT_ALG_SKDF) then
                    let $fs_out_cap := #PROFILE_ALG_SKDF;
                    let $fs_out_rc  := #MARS_RC_SUCCESS
                else if ($fs_in_pt ==[arg_sz] #MARS_PT_ALG_AKDF) then
                    let $fs_out_cap := #PROFILE_ALG_AKDF;
                    let $fs_out_rc  := #MARS_RC_SUCCESS
                else
                    let $fs_out_rc := #MARS_RC_VALUE
            ]}

        (* MARS_RegRead -- spec section 8.3.2.  An out-of-range index is
           MARS_RC_REG (7), not MARS_RC_VALUE, and [dout] reads zero because
           [clear_results] already cleared it.  The C emulator instead leaves
           the CALLER's buffer untouched, which has no analogue on an MMIO
           result register; either way the host contract is the same, "check rc
           before using dout". *)
        | fs_act_regread =>
            guard_failure (guard_busy {[
                if ($fs_in_idx ==[arg_sz] #0) then
                    let $fs_out_dout := $fs_out_pcr0;
                    let $fs_out_rc   := #MARS_RC_SUCCESS
                else if ($fs_in_idx ==[arg_sz] #1) then
                    let $fs_out_dout := $fs_out_pcr1;
                    let $fs_out_rc   := #MARS_RC_SUCCESS
                else
                    let $fs_out_rc := #MARS_RC_REG
            ]})

        (* MARS_PcrExtend -- spec section 8.3.1.  Step 1 of 2: validate, build
           PCR[i] || dig, and issue.  Step 2 is MARS_Continue.  [pend] carries
           which PCR, so the index needs no separate latch -- which matters,
           because an input is re-sampled on every step. *)
        | fs_act_pcrextend =>
            guard_failure (guard_busy {[
                if ($fs_in_idx ==[arg_sz] #0) then
                    `issue CRYPT_SHA256 PEND_EXT0 (ext_msg fs_out_pcr0) 64`
                else if ($fs_in_idx ==[arg_sz] #1) then
                    `issue CRYPT_SHA256 PEND_EXT1 (ext_msg fs_out_pcr1) 64`
                else
                    let $fs_out_rc := #MARS_RC_REG
            ]})

        (* MARS_Continue -- Profile-specific, not a TCG command.  Advances
           whatever [pend] names, and does NOTHING otherwise: glue that pulses
           Continue spuriously, repeatedly or never cannot make the module do
           anything it did not itself start.  A second Continue after a
           completed step finds pend = 0 and is refused. *)
        | fs_act_continue =>
            guard_failure {[
                if `response_ok` then
                    if ($fs_out_pend ==[pend_sz] #PEND_EXT0) then
                        let $fs_out_pcr0 := $fs_in_crypt_res;
                        `finish`
                    else if ($fs_out_pend ==[pend_sz] #PEND_EXT1) then
                        let $fs_out_pcr1 := $fs_in_crypt_res;
                        `finish`
                    else
                        let $fs_out_rc := #MARS_RC_VALUE
                else
                    let $fs_out_rc := #MARS_RC_VALUE
            ]}

        | fs_act_selftest         => unsupported
        | fs_act_sequencehash     => unsupported
        | fs_act_sequenceupdate   => unsupported
        | fs_act_sequencecomplete => unsupported
        | fs_act_derive           => unsupported
        | fs_act_dpderive         => unsupported
        | fs_act_publicread       => unsupported
        | fs_act_quote            => unsupported
        | fs_act_sign             => unsupported
        | fs_act_signatureverify  => unsupported
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

    Definition o_zero : ContextEnv.(env_t) (tf_outputs_type fs_outputs_size) :=
        ContextEnv.(create) (fun _ => Bits.zero).

    Definition s_zero : ContextEnv.(env_t) (tf_states_type fs_states_size) :=
        ContextEnv.(create) fs_states_init.

    (* Full input vector.  [arg] keeps the two-argument form the Stage 1
       vectors use; [arg_crypt] adds what the IP drives back. *)
    Definition arg_full (pt idx dig res: nat) (valid tag: bool)
        (x : fs_inputs) : bits_t (fs_inputs_size x) :=
        match x with
        | fs_in_pt          => Bits.of_nat arg_sz pt
        | fs_in_idx         => Bits.of_nat arg_sz idx
        | fs_in_dig         => Bits.of_nat digest_sz dig
        | fs_in_crypt_res   => Bits.of_nat digest_sz res
        | fs_in_crypt_valid => if valid then Ob~1 else Ob~0
        | fs_in_crypt_tag   => if tag then Ob~1 else Ob~0
        end.

    Definition arg (pt idx : nat) := arg_full pt idx 0 0 false false.

    Definition run_in (act: fs_action) (input: forall x, bits_t (fs_inputs_size x))
        (out: ContextEnv.(env_t) (tf_outputs_type fs_outputs_size)) :=
        snd (fs_step (fs_transitions act) (s_zero, out) input).

    Definition run (act: fs_action) (pt idx : nat)
        (out: ContextEnv.(env_t) (tf_outputs_type fs_outputs_size)) :=
        run_in act (arg pt idx) out.

    Definition rc_of (act: fs_action) (pt idx : nat) out :=
        ContextEnv.(getenv) (run act pt idx out) fs_out_rc.
    Definition cap_of (act: fs_action) (pt idx : nat) out :=
        ContextEnv.(getenv) (run act pt idx out) fs_out_cap.
    Definition dout_of (act: fs_action) (pt idx : nat) out :=
        ContextEnv.(getenv) (run act pt idx out) fs_out_dout.

    (* MARS_CapabilityGet: all eleven Table 6 tags. *)
    Example cap_pcr : cap_of fs_act_capabilityget MARS_PT_PCR 0 o_zero
                      = Bits.of_nat 16 2.
    Proof. reflexivity. Qed.
    Example cap_tsr : cap_of fs_act_capabilityget MARS_PT_TSR 0 o_zero
                      = Bits.of_nat 16 0.
    Proof. reflexivity. Qed.
    Example cap_len_digest : cap_of fs_act_capabilityget MARS_PT_LEN_DIGEST 0 o_zero
                      = Bits.of_nat 16 32.
    Proof. reflexivity. Qed.
    Example cap_len_sign : cap_of fs_act_capabilityget MARS_PT_LEN_SIGN 0 o_zero
                      = Bits.of_nat 16 32.
    Proof. reflexivity. Qed.
    Example cap_len_ksym : cap_of fs_act_capabilityget MARS_PT_LEN_KSYM 0 o_zero
                      = Bits.of_nat 16 32.
    Proof. reflexivity. Qed.
    Example cap_len_kpub : cap_of fs_act_capabilityget MARS_PT_LEN_KPUB 0 o_zero
                      = Bits.of_nat 16 0.
    Proof. reflexivity. Qed.
    Example cap_len_kprv : cap_of fs_act_capabilityget MARS_PT_LEN_KPRV 0 o_zero
                      = Bits.of_nat 16 0.
    Proof. reflexivity. Qed.
    Example cap_alg_hash : cap_of fs_act_capabilityget MARS_PT_ALG_HASH 0 o_zero
                      = Bits.of_nat 16 11.
    Proof. reflexivity. Qed.
    Example cap_alg_sign : cap_of fs_act_capabilityget MARS_PT_ALG_SIGN 0 o_zero
                      = Bits.of_nat 16 5.
    Proof. reflexivity. Qed.
    Example cap_alg_skdf : cap_of fs_act_capabilityget MARS_PT_ALG_SKDF 0 o_zero
                      = Bits.of_nat 16 34.
    Proof. reflexivity. Qed.
    Example cap_alg_akdf : cap_of fs_act_capabilityget MARS_PT_ALG_AKDF 0 o_zero
                      = Bits.of_nat 16 0.
    Proof. reflexivity. Qed.

    Example cap_rc_success : rc_of fs_act_capabilityget MARS_PT_ALG_AKDF 0 o_zero
                      = Bits.of_nat 16 MARS_RC_SUCCESS.
    Proof. reflexivity. Qed.

    (* pt = 0 and pt = 12 bracket Table 6: both MARS_RC_VALUE. *)
    Example cap_rc_value_low : rc_of fs_act_capabilityget 0 0 o_zero
                      = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example cap_rc_value_high : rc_of fs_act_capabilityget 12 0 o_zero
                      = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.

    Example cap_rc_value_13 : rc_of fs_act_capabilityget 13 0 o_zero
                      = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.

    (* An invalid tag clears [cap] rather than leaving it stale: no command may
       return a previous command's result.  This is where the module and the C
       emulator DIVERGE by design -- oracle/stage1.expected shows the 0x0fff
       sentinel surviving pt = 0, 12 and 13, because there the sentinel lives in
       the CALLER's buffer, which an MMIO result register has no analogue for.
       Either way the host contract is the same: check rc before using cap. *)
    Definition o_cap_sentinel :=
        ContextEnv.(putenv) o_zero fs_out_cap (Bits.of_nat 16 4095).
    Example cap_cleared_on_invalid : cap_of fs_act_capabilityget 0 0 o_cap_sentinel
                      = Bits.zero.
    Proof. reflexivity. Qed.

    (* And a stale result never survives a command that does not produce one:
       RegRead clears [cap], CapabilityGet clears [dout]. *)
    Example regread_clears_cap : cap_of fs_act_regread 0 0 o_cap_sentinel
                      = Bits.zero.
    Proof. reflexivity. Qed.
    Example unsupported_clears_cap : cap_of fs_act_sequencehash 0 0 o_cap_sentinel
                      = Bits.zero.
    Proof. reflexivity. Qed.

    (* MARS_RegRead over two distinguishable PCRs. *)
    Definition o_pcrs :=
        ContextEnv.(putenv)
          (ContextEnv.(putenv) o_zero fs_out_pcr0 (Bits.of_nat digest_sz 42))
          fs_out_pcr1 (Bits.of_nat digest_sz 99).

    Example reg_read_0 : dout_of fs_act_regread 0 0 o_pcrs
                      = Bits.of_nat digest_sz 42.
    Proof. reflexivity. Qed.
    Example reg_read_1 : dout_of fs_act_regread 0 1 o_pcrs
                      = Bits.of_nat digest_sz 99.
    Proof. reflexivity. Qed.
    Example reg_read_0_rc : rc_of fs_act_regread 0 0 o_pcrs
                      = Bits.of_nat 16 MARS_RC_SUCCESS.
    Proof. reflexivity. Qed.

    (* regIndex = 2 is out of range for PROFILE_COUNT_REG = 2: MARS_RC_REG,
       and [dout] must not change. *)
    Example reg_read_2_rc : rc_of fs_act_regread 0 2 o_pcrs
                      = Bits.of_nat 16 MARS_RC_REG.
    Proof. reflexivity. Qed.
    Example reg_read_2_dout : dout_of fs_act_regread 0 2 o_pcrs
                      = Bits.zero.
    Proof. reflexivity. Qed.

    (* The three state-carrying outputs must SURVIVE every command unchanged --
       they are outputs only because non-secret state is modelled that way, and
       clearing them per command would wipe the measurement chain.  Pinned so
       [clear_results] can never quietly grow to cover them. *)
    Example pcr0_survives_regread :
        ContextEnv.(getenv) (run fs_act_regread 0 2 o_pcrs) fs_out_pcr0
        = Bits.of_nat digest_sz 42.
    Proof. reflexivity. Qed.
    Example pcr1_survives_capabilityget :
        ContextEnv.(getenv) (run fs_act_capabilityget MARS_PT_PCR 0 o_pcrs) fs_out_pcr1
        = Bits.of_nat digest_sz 99.
    Proof. reflexivity. Qed.

    (* An excluded command answers MARS_RC_COMMAND, not the previous rc. *)
    Example unsupported_rc : rc_of fs_act_sequencehash 0 0 o_pcrs
                      = Bits.of_nat 16 MARS_RC_COMMAND.
    Proof. reflexivity. Qed.
    Example quote_not_yet : rc_of fs_act_quote 0 0 o_pcrs
                      = Bits.of_nat 16 MARS_RC_COMMAND.
    Proof. reflexivity. Qed.

    (* Failure mode (spec section 5.3.1): everything except MARS_CapabilityGet
       answers MARS_RC_FAILURE, and the failure answer preempts
       MARS_RC_COMMAND. *)
    Definition o_failed := ContextEnv.(putenv) o_pcrs fs_out_failure Ob~1.

    Example failed_regread : rc_of fs_act_regread 0 0 o_failed
                      = Bits.of_nat 16 MARS_RC_FAILURE.
    Proof. reflexivity. Qed.
    Example failed_unsupported : rc_of fs_act_sequencehash 0 0 o_failed
                      = Bits.of_nat 16 MARS_RC_FAILURE.
    Proof. reflexivity. Qed.
    Example failed_capabilityget : rc_of fs_act_capabilityget MARS_PT_PCR 0 o_failed
                      = Bits.of_nat 16 MARS_RC_SUCCESS.
    Proof. reflexivity. Qed.
    Example failed_capabilityget_cap : cap_of fs_act_capabilityget MARS_PT_PCR 0 o_failed
                      = Bits.of_nat 16 2.
    Proof. reflexivity. Qed.

    (* [failure] itself survives too -- it is state, not a result. *)
    Example failure_survives_capabilityget :
        ContextEnv.(getenv) (run fs_act_capabilityget MARS_PT_PCR 0 o_failed) fs_out_failure
        = Ob~1.
    Proof. reflexivity. Qed.

    (* ---------------------------------------------------------------------
       Stage 2: the crypto handshake.

       These are the cases REVIEW.md section 2.1 is about.  A mock IP is just a
       choice of (crypt_res, crypt_valid, crypt_tag) on the input vector, so
       every attack below is expressible here, before any real crypto exists.
       --------------------------------------------------------------------- *)

    Definition get (o: ContextEnv.(env_t) (tf_outputs_type fs_outputs_size)) v :=
        ContextEnv.(getenv) o v.

    (* Step 1: host issues PcrExtend(idx, dig). *)
    Definition ext (idx dig: nat) out :=
        run_in fs_act_pcrextend (arg_full 0 idx dig 0 false false) out.

    (* Step 2: glue pulses Continue with whatever the IP is driving. *)
    Definition cont (res: nat) (valid tag: bool) out :=
        run_in fs_act_continue (arg_full 0 0 0 res valid tag) out.

    (* Any other command, for the interleaving tests. *)
    Definition other (act: fs_action) (pt idx: nat) out := run act pt idx out.

    Definition issued := ext 0 7 o_pcrs.

    (* --- the request ---------------------------------------------------- *)

    Example issue_rc        : get issued fs_out_rc        = Bits.of_nat 16 MARS_RC_SUCCESS.
    Proof. reflexivity. Qed.
    Example issue_pend      : get issued fs_out_pend      = Bits.of_nat pend_sz PEND_EXT0.
    Proof. reflexivity. Qed.
    Example issue_op        : get issued fs_out_crypt_op  = Bits.of_nat 4 CRYPT_SHA256.
    Proof. reflexivity. Qed.
    Example issue_len       : get issued fs_out_crypt_len = Bits.of_nat 16 64.
    Proof. reflexivity. Qed.
    (* crypt_req toggled 0 -> 1, so a matching tag is 1. *)
    Example issue_req       : get issued fs_out_crypt_req = Ob~1.
    Proof. reflexivity. Qed.
    (* crypt_valid was low at issue, so the request is armed. *)
    Example issue_armed     : get issued fs_out_armed     = Ob~1.
    Proof. reflexivity. Qed.

    (* The message is PCR[0] || dig, left-aligned: pcr0 in the top 256 bits,
       dig below it, zero padding in the low 512.  This pins the byte ORDER,
       which is where MARS correctness actually lives (MVP.md section 3.1). *)
    Example issue_msg_pcr : Bits.slice 768 digest_sz (get issued fs_out_crypt_msg)
                          = Bits.of_nat digest_sz 42.
    Proof. reflexivity. Qed.
    Example issue_msg_dig : Bits.slice 512 digest_sz (get issued fs_out_crypt_msg)
                          = Bits.of_nat digest_sz 7.
    Proof. reflexivity. Qed.
    Example issue_msg_pad : Bits.slice 0 512 (get issued fs_out_crypt_msg)
                          = Bits.zero.
    Proof. reflexivity. Qed.

    (* An out-of-range index issues NOTHING: no request, no pending step. *)
    Example ext_bad_idx_rc   : get (ext 2 7 o_pcrs) fs_out_rc        = Bits.of_nat 16 MARS_RC_REG.
    Proof. reflexivity. Qed.
    Example ext_bad_idx_pend : get (ext 2 7 o_pcrs) fs_out_pend      = Bits.of_nat pend_sz PEND_IDLE.
    Proof. reflexivity. Qed.
    Example ext_bad_idx_req  : get (ext 2 7 o_pcrs) fs_out_crypt_req = Ob~0.
    Proof. reflexivity. Qed.
    Example ext_bad_idx_op   : get (ext 2 7 o_pcrs) fs_out_crypt_op  = Bits.of_nat 4 CRYPT_IDLE.
    Proof. reflexivity. Qed.

    (* --- the honest completion ------------------------------------------ *)

    Definition completed := cont 123 true true issued.

    Example done_pcr0  : get completed fs_out_pcr0      = Bits.of_nat digest_sz 123.
    Proof. reflexivity. Qed.
    Example done_pcr1  : get completed fs_out_pcr1      = Bits.of_nat digest_sz 99.
    Proof. reflexivity. Qed.
    Example done_rc    : get completed fs_out_rc        = Bits.of_nat 16 MARS_RC_SUCCESS.
    Proof. reflexivity. Qed.
    Example done_pend  : get completed fs_out_pend      = Bits.of_nat pend_sz PEND_IDLE.
    Proof. reflexivity. Qed.
    Example done_armed : get completed fs_out_armed     = Ob~0.
    Proof. reflexivity. Qed.
    (* Zeroized, so nothing stays driven on the trusted port. *)
    Example done_op    : get completed fs_out_crypt_op  = Bits.of_nat 4 CRYPT_IDLE.
    Proof. reflexivity. Qed.
    Example done_key   : get completed fs_out_crypt_key = Bits.zero.
    Proof. reflexivity. Qed.
    Example done_msg   : get completed fs_out_crypt_msg = Bits.zero.
    Proof. reflexivity. Qed.

    (* --- ATTACK: Continue without crypt_valid ---------------------------- *)
    (* The PCR must not move, and the request must stay pending. *)
    Example no_valid_pcr0  : get (cont 666 false true issued) fs_out_pcr0 = Bits.of_nat digest_sz 42.
    Proof. reflexivity. Qed.
    Example no_valid_rc    : get (cont 666 false true issued) fs_out_rc   = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example no_valid_pend  : get (cont 666 false true issued) fs_out_pend = Bits.of_nat pend_sz PEND_EXT0.
    Proof. reflexivity. Qed.

    (* --- ATTACK: a stale tag -------------------------------------------- *)
    (* valid is high and the result looks fine, but it answers the PREVIOUS
       request.  This is the escalation path to AK disclosure at Stage 4. *)
    Example stale_tag_pcr0 : get (cont 666 true false issued) fs_out_pcr0 = Bits.of_nat digest_sz 42.
    Proof. reflexivity. Qed.
    Example stale_tag_rc   : get (cont 666 true false issued) fs_out_rc   = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example stale_tag_pend : get (cont 666 true false issued) fs_out_pend = Bits.of_nat pend_sz PEND_EXT0.
    Proof. reflexivity. Qed.

    (* --- ATTACK: Continue twice ------------------------------------------ *)
    (* The second one finds pend = 0 and armed = 0 and does nothing. *)
    Example twice_pcr0 : get (cont 666 true true completed) fs_out_pcr0 = Bits.of_nat digest_sz 123.
    Proof. reflexivity. Qed.
    Example twice_rc   : get (cont 666 true true completed) fs_out_rc   = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.

    (* --- ATTACK: Continue with nothing pending --------------------------- *)
    Example cont_idle_rc   : get (cont 666 true true o_pcrs) fs_out_rc   = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example cont_idle_pcr0 : get (cont 666 true true o_pcrs) fs_out_pcr0 = Bits.of_nat digest_sz 42.
    Proof. reflexivity. Qed.

    (* --- ATTACK: the IP holds done high across requests ------------------- *)
    (* A real core (secworks/sha256, OpenTitan hmac) holds [done] until the next
       start.  Arming only while crypt_valid is LOW means such a core leaves the
       module unarmed: it WEDGES rather than latching a result it cannot bind to
       its request.  Fail-stop is the intended outcome -- at Stage 4 the stale
       result would be published as the Attestation Key. *)
    Definition issued_stuck :=
        run_in fs_act_pcrextend (arg_full 0 0 7 0 true false) o_pcrs.

    Example stuck_pend    : get issued_stuck fs_out_pend  = Bits.of_nat pend_sz PEND_EXT0.
    Proof. reflexivity. Qed.
    Example stuck_unarmed : get issued_stuck fs_out_armed = Ob~0.
    Proof. reflexivity. Qed.
    (* ...and no later Continue, however well-formed, can complete it. *)
    Example stuck_wedged_pcr0 : get (cont 666 true true issued_stuck) fs_out_pcr0
                              = Bits.of_nat digest_sz 42.
    Proof. reflexivity. Qed.
    Example stuck_wedged_rc   : get (cont 666 true true issued_stuck) fs_out_rc
                              = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example stuck_wedged_pend : get (cont 666 true true issued_stuck) fs_out_pend
                              = Bits.of_nat pend_sz PEND_EXT0.
    Proof. reflexivity. Qed.

    (* --- ATTACK: interleave a command into a pending sequence ------------- *)
    (* Refused, and -- the part that matters -- [pend] and the outstanding
       request are left untouched, so the sequence can still complete. *)
    Example busy_regread_rc  : get (other fs_act_regread 0 0 issued) fs_out_rc
                             = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example busy_capget_rc   : get (other fs_act_capabilityget MARS_PT_PCR 0 issued) fs_out_rc
                             = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example busy_ext_rc      : get (ext 1 9 issued) fs_out_rc
                             = Bits.of_nat 16 MARS_RC_VALUE.
    Proof. reflexivity. Qed.
    Example busy_ext_pend    : get (ext 1 9 issued) fs_out_pend
                             = Bits.of_nat pend_sz PEND_EXT0.
    Proof. reflexivity. Qed.
    Example busy_ext_req     : get (ext 1 9 issued) fs_out_crypt_req = Ob~1.
    Proof. reflexivity. Qed.
    (* A refused command must not disturb the in-flight message either. *)
    Example busy_ext_msg_dig : Bits.slice 512 digest_sz (get (ext 1 9 issued) fs_out_crypt_msg)
                             = Bits.of_nat digest_sz 7.
    Proof. reflexivity. Qed.

    (* PCR1 works the same way, and lands in the other register. *)
    Definition issued1   := ext 1 7 o_pcrs.
    Definition completed1 := cont 55 true true issued1.
    Example ext1_pend  : get issued1 fs_out_pend  = Bits.of_nat pend_sz PEND_EXT1.
    Proof. reflexivity. Qed.
    Example ext1_msg   : Bits.slice 768 digest_sz (get issued1 fs_out_crypt_msg)
                       = Bits.of_nat digest_sz 99.
    Proof. reflexivity. Qed.
    Example done1_pcr1 : get completed1 fs_out_pcr1 = Bits.of_nat digest_sz 55.
    Proof. reflexivity. Qed.
    Example done1_pcr0 : get completed1 fs_out_pcr0 = Bits.of_nat digest_sz 42.
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

        tfs_spec_outputs := fs_outputs;
        tfs_spec_outputs_fin := _;
        tfs_spec_outputs_size := fs_outputs_size;

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
