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
    | fs_in_pt      (* MARS_CapabilityGet: property tag *)
    | fs_in_idx     (* MARS_RegRead: regIndex           *)
    .

    (* PCRs are OUTPUT variables, not state variables: they are meant to be
       public (MARS_RegRead hands them out), and making them secret would taint
       the whole Quote datapath.  MVP.md section 6.1. *)
    Inductive fs_outputs :=
    | fs_out_rc
    | fs_out_cap
    | fs_out_dout
    | fs_out_pcr0
    | fs_out_pcr1
    | fs_out_failure
    .

    Definition fs_states_size (x: fs_states) : nat :=
    match x with
    | fs_st_ps => digest_sz
    | fs_st_dp => digest_sz
    | fs_st_ak => digest_sz
    end.

    Definition fs_inputs_size (x: fs_inputs) : nat :=
    match x with
    | fs_in_pt  => arg_sz
    | fs_in_idx => arg_sz
    end.

    Definition fs_outputs_size (x: fs_outputs) : nat :=
    match x with
    | fs_out_rc      => rc_sz
    | fs_out_cap     => 16
    | fs_out_dout    => digest_sz
    | fs_out_pcr0    => digest_sz
    | fs_out_pcr1    => digest_sz
    | fs_out_failure => 1
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
            {[
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
            guard_failure {[
                if ($fs_in_idx ==[arg_sz] #0) then
                    let $fs_out_dout := $fs_out_pcr0;
                    let $fs_out_rc   := #MARS_RC_SUCCESS
                else if ($fs_in_idx ==[arg_sz] #1) then
                    let $fs_out_dout := $fs_out_pcr1;
                    let $fs_out_rc   := #MARS_RC_SUCCESS
                else
                    let $fs_out_rc := #MARS_RC_REG
            ]}

        | fs_act_selftest         => unsupported
        | fs_act_sequencehash     => unsupported
        | fs_act_sequenceupdate   => unsupported
        | fs_act_sequencecomplete => unsupported
        | fs_act_pcrextend        => unsupported
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

    Definition arg (pt idx : nat) (x : fs_inputs) : bits_t (fs_inputs_size x) :=
        match x with
        | fs_in_pt  => Bits.of_nat arg_sz pt
        | fs_in_idx => Bits.of_nat arg_sz idx
        end.

    Definition run (act: fs_action) (pt idx : nat)
        (out: ContextEnv.(env_t) (tf_outputs_type fs_outputs_size)) :=
        snd (fs_step (fs_transitions act) (s_zero, out) (arg pt idx)).

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
