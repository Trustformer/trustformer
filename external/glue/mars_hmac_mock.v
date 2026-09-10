//======================================================================
// mars_hmac_mock.v
//
// A STAND-IN for the HMAC core, not an HMAC.  It answers every request with
// a fixed value after a fixed delay, using the same handshake the real
// adapter will.
//
// Why this exists: from Stage 4a the module refuses every command except
// MARS_CapabilityGet until _MARS_Init completes, and Init is a KDF -- an
// HMAC.  Without something on the HMAC port the device never initializes and
// the Stage 3 differential, which is about SHA-256, could not run at all.
//
// What it therefore does and does not buy: PcrExtend's PCR values stay
// byte-exact against the reference emulator, because they come from the real
// sha256_core.  DP is wrong, which matters only from MARS_Quote onward.  A
// real HMAC lands at Stage 4c and this file is deleted then.
//
// It is deliberately written to the same contract as the real adapter,
// including MVP.md section 9 A7: deassert valid once the module drops
// hmac_active, or the SECOND HMAC request never arms.
//======================================================================

module mars_hmac_mock #(
    parameter [255:0] FIXED_RESULT = 256'h4d4f434b5f484d41435f5245535f5630_00000000000000000000000000000000,
    parameter integer LATENCY      = 7
) (
    input  wire           CLK,
    input  wire           RST_N,

    input  wire           hmac_active,
    input  wire [255:0]   hmac_key,
    input  wire [511:0]   hmac_msg,
    input  wire [15:0]    hmac_len,
    input  wire           hmac_req,

    output reg  [255:0]   hmac_res,
    output reg            hmac_valid,
    output reg            hmac_tag
);

  reg          last_req;
  reg [7:0]    count;
  reg          running;

  wire new_request = hmac_active && (hmac_req != last_req);

  always @(posedge CLK) begin
    if (!RST_N) begin
      last_req   <= 1'b0;
      count      <= 8'd0;
      running    <= 1'b0;
      hmac_res   <= 256'd0;
      hmac_valid <= 1'b0;
      hmac_tag   <= 1'b0;
    end else begin
      // A7: the module has taken the result and gone idle.
      if (!hmac_active)
        hmac_valid <= 1'b0;

      if (!running && new_request) begin
        last_req   <= hmac_req;
        hmac_valid <= 1'b0;
        count      <= LATENCY[7:0];
        running    <= 1'b1;
      end else if (running) begin
        if (count == 8'd0) begin
          hmac_res   <= FIXED_RESULT;
          hmac_tag   <= last_req;
          hmac_valid <= 1'b1;
          running    <= 1'b0;
        end else begin
          count <= count - 8'd1;
        end
      end
    end
  end

endmodule
