//======================================================================
// mars_sha256_glue.v
//
// The adapter between the verified MARS module's Trusted crypto port and
// secworks/sha256_core.  MVP.md section 5.3 / section 9 A6: this is TCB --
// DP and AK cross it from Stage 4 -- so it is deliberately small and does
// nothing but sequence blocks.
//
// Two facts about the core drive this design, both read out of
// sha256_core.v rather than assumed:
//
//   1. The core does NOT pad.  It takes 512-bit blocks with init (first) /
//      next (subsequent).  For MARS_PcrExtend the message is a fixed 64
//      bytes, so the second block is the CONSTANT below.
//
//   2. digest_valid is set in CTRL_DONE and cleared only when the next
//      init/next starts (sha256_core.v L505/L516/L541), so it STAYS HIGH
//      between requests.  That is precisely the "real cores hold done until
//      the next start" behaviour REVIEW.md section 2.1 is about.
//
// (2) forces an interface obligation that MVP.md section 6.3 does not state:
// the module arms a request only while crypt_valid is LOW, so the glue MUST
// deassert crypt_valid once the module has consumed the result -- otherwise
// the SECOND command never arms.  The module announces consumption by
// driving crypt_op back to IDLE in its completion arm, so that is the signal
// used here.  Without this the second PcrExtend wedges, and with the Stage 3
// fault detector it faults.
//======================================================================

module mars_sha256_glue (
    input  wire           CLK,
    input  wire           RST_N,

    // From the MARS module (Trusted outputs).
    input  wire [3:0]     crypt_op,
    input  wire [1023:0]  crypt_msg,
    input  wire [15:0]    crypt_len,
    input  wire           crypt_req,

    // To the MARS module (Trusted inputs).
    output reg  [255:0]   crypt_res,
    output reg            crypt_valid,
    output reg            crypt_tag
);

  localparam OP_IDLE   = 4'd0;
  localparam OP_SHA256 = 4'd1;

  localparam S_IDLE = 2'd0;
  localparam S_BLK1 = 2'd1;
  localparam S_BLK2 = 2'd2;

  // SHA-256 padding for a 512-bit message: 0x80, zeros, then the length in
  // bits as a 64-bit big-endian integer.  8 + 440 + 64 = 512.
  localparam [511:0] PAD_512 = {8'h80, 440'd0, 64'd512};

  reg  [1:0]   state;
  reg          last_req;
  reg  [511:0] block;
  reg          core_init;
  reg          core_next;

  wire         core_ready;
  wire         core_dv;
  wire [255:0] core_digest;

  sha256_core core (
      .clk(CLK), .reset_n(RST_N),
      .init(core_init), .next(core_next),
      .mode(1'b1),                       // 1 = SHA-256, 0 = SHA-224
      .block(block),
      .ready(core_ready), .digest(core_digest), .digest_valid(core_dv)
  );

  wire new_request = (crypt_op == OP_SHA256) && (crypt_req != last_req);

  always @(posedge CLK) begin
    if (!RST_N) begin
      state       <= S_IDLE;
      last_req    <= 1'b0;
      core_init   <= 1'b0;
      core_next   <= 1'b0;
      crypt_res   <= 256'd0;
      crypt_valid <= 1'b0;
      crypt_tag   <= 1'b0;
      block       <= 512'd0;
    end else begin
      core_init <= 1'b0;
      core_next <= 1'b0;

      // The module has taken the result and gone idle: drop valid so the
      // next request can arm.  See the header.
      //
      // Defining GLUE_OMIT_DEASSERT removes exactly this, turning the glue
      // into the misbehaving TCB the two-phase arming and the fault detector
      // exist for.  oracle/run-stage3.sh builds both ways: the module must
      // produce the emulator's digests with it, and must enter failure mode
      // without it.
`ifndef GLUE_OMIT_DEASSERT
      if (crypt_op == OP_IDLE)
        crypt_valid <= 1'b0;
`endif

      case (state)
        S_IDLE:
          if (new_request && core_ready) begin
            last_req    <= crypt_req;
            crypt_valid <= 1'b0;
            block       <= crypt_msg[1023:512];   // message, left-aligned
            core_init   <= 1'b1;
            state       <= S_BLK1;
          end

        S_BLK1:
          // ready falls on init and rises again when the block is absorbed.
          if (core_ready && !core_init) begin
            block     <= PAD_512;
            core_next <= 1'b1;
            state     <= S_BLK2;
          end

        S_BLK2:
          if (core_ready && !core_next) begin
            crypt_res   <= core_digest;
            crypt_tag   <= last_req;   // echo the request we served
            crypt_valid <= 1'b1;
            state       <= S_IDLE;
          end
      endcase
    end
  end

endmodule
