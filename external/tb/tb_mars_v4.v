//======================================================================
// tb_mars_v4.v
//
// Stage 3 for the ONE-ACTION MARS: the generated module + secworks/sha256_core,
// joined by mars_sha256_glue / mars_hmac_glue through the two IP adapters.
//
// The difference from tb_mars_pcrextend.v, which drives the sequential design,
// is the whole point of the V4 campaign: there is no MARS_Continue.  A command
// is one action, so the host issues it and waits for [ready] -- the round trips
// happen inside.
//
// It prints one line per observation in the format of oracle/stage3_vectors.c,
// which run-stage3-v4.sh diffs against the TCG C reference emulator.
//======================================================================
`timescale 1ns/1ps

// CORE_DIV = core cycles per MODULE cycle.  1 is the ordinary case, one clock
// for everything.  A larger value puts the crypto core in a faster domain,
// which is how a small declared ip_lat can cover a many-cycle IP.
`ifndef CORE_DIV
 `define CORE_DIV 1
`endif
`ifndef IP_LAT_SHA
 `define IP_LAT_SHA 140
`endif
`ifndef IP_LAT_HMAC
 `define IP_LAT_HMAC 275
`endif

module tb_mars_v4;

  localparam CC_CAPABILITYGET = 16'd1;
  localparam CC_PCREXTEND     = 16'd5;
  localparam CC_REGREAD       = 16'd6;
  localparam CC_QUOTE         = 16'd10;
  localparam CC_INIT          = 16'hFFFF;

  // "Here are thirty two secret bytes" -- the seed reference-emulator/c/mars.c
  // is compiled with.  Both sides must start from the same PS or every
  // DP-derived value differs.
  localparam [255:0] PS =
      256'h4865726520617265207468697274792074776f20736563726574206279746573;

  reg CLK = 1'b0;                       // the core and adapter clock
  reg RST_N = 1'b0;
  reg CLK_slow = 1'b0;
  integer dcnt = 0;
  wire CLK_M = (`CORE_DIV == 1) ? CLK : CLK_slow;   // the MODULE clock
  always #5 CLK = ~CLK;
  always @(posedge CLK)
    if (dcnt == (`CORE_DIV / 2) - 1) begin dcnt <= 0; CLK_slow <= ~CLK_slow; end
    else dcnt <= dcnt + 1;

  reg [16:0]  in_cmd;
  reg [15:0]  a_pt, a_idx;
  reg [255:0] a_dig;
  reg [31:0]  a_regsel;
  reg [255:0] a_nonce, a_ctx;
  reg         init_req;

  wire         ready;
  wire [15:0]  rc, cap;
  wire [255:0] dout, pcr0, pcr1, snap;
  wire         failure, st;

  wire [1040:0] sha_req;
  wire [784:0]  hmac_req;
  wire [255:0]  sha_resp, hmac_resp;

  Example_Mars dut (
      .CLK(CLK_M), .RST_N(RST_N),
      .in_cmd_out(in_cmd), .in_cmd_arg(ready),

      .in_param_pub_in_pt_out(a_pt),   .in_param_pub_in_pt_arg(),
      .in_param_pub_in_idx_out(a_idx), .in_param_pub_in_idx_arg(),
      .in_param_pub_in_dig_out(a_dig), .in_param_pub_in_dig_arg(),

      // platform side: the Primary Seed and the protected init request
      .in_param_sec_in_ps_out(PS),             .in_param_sec_in_ps_arg(),
      .in_param_sec_in_init_req_out(init_req), .in_param_sec_in_init_req_arg(),

      .in_param_pub_in_regsel_out(a_regsel), .in_param_pub_in_regsel_arg(),
      .in_param_pub_in_nonce_out(a_nonce),   .in_param_pub_in_nonce_arg(),
      .in_param_pub_in_ctx_out(a_ctx),       .in_param_pub_in_ctx_arg(),
      .in_param_pub_in_nlen_out(16'd32),     .in_param_pub_in_nlen_arg(),
      .in_param_pub_in_ctxlen_out(16'd32),   .in_param_pub_in_ctxlen_arg(),

      .out_param_pub_out_rc_arg(rc),           .out_param_pub_out_rc_out(1'b1),
      .out_param_pub_out_cap_arg(cap),         .out_param_pub_out_cap_out(1'b1),
      .out_param_pub_out_dout_arg(dout),       .out_param_pub_out_dout_out(1'b1),
      .out_param_pub_out_pcr0_arg(pcr0),       .out_param_pub_out_pcr0_out(1'b1),
      .out_param_pub_out_pcr1_arg(pcr1),       .out_param_pub_out_pcr1_out(1'b1),
      .out_param_pub_out_failure_arg(failure), .out_param_pub_out_failure_out(1'b1),
      .out_param_pub_out_st_arg(st),           .out_param_pub_out_st_out(1'b1),
      .out_param_pub_out_snap_arg(snap),       .out_param_pub_out_snap_out(1'b1),

      .ip_req_sec_ip_sha_arg(sha_req),      .ip_req_sec_ip_sha_out(1'b1),
      .ip_resp_sec_ip_sha_out(sha_resp),    .ip_resp_sec_ip_sha_arg(),
      .ip_req_sec_ip_hmac_arg(hmac_req),    .ip_req_sec_ip_hmac_out(1'b1),
      .ip_resp_sec_ip_hmac_out(hmac_resp),  .ip_resp_sec_ip_hmac_arg()
  );

  mars_ip_sha_adapter  #(.DECLARED_LAT(`IP_LAT_SHA * `CORE_DIV)) sha_ip (
      .CLK(CLK), .RST_N(RST_N), .ip_req(sha_req),  .ip_resp(sha_resp));

  mars_ip_hmac_adapter #(.DECLARED_LAT(`IP_LAT_HMAC * `CORE_DIV)) hmac_ip (
      .CLK(CLK), .RST_N(RST_N), .ip_req(hmac_req), .ip_resp(hmac_resp));

  // ---- host helpers --------------------------------------------------

  // Stimulus is driven on the NEGEDGE and sampled there: driving it in the
  // same time step as the clock edge races the module's own evaluation.
  task automatic issue(input [15:0] code);
    begin
      @(negedge CLK_M);
      while (ready !== 1'b1) @(negedge CLK_M);
      in_cmd = {1'b1, code};
      @(posedge CLK_M);                       // the accepting edge
      @(negedge CLK_M);
      in_cmd = 17'b0;
      while (ready !== 1'b1) @(negedge CLK_M);  // the action retires
    end
  endtask

  task automatic pcr_extend(input [15:0] idx, input [255:0] dig);
    begin
      a_idx = idx;
      a_dig = dig;
      issue(CC_PCREXTEND);
    end
  endtask

  task automatic reg_read(input [15:0] idx);
    begin
      a_idx = idx;
      issue(CC_REGREAD);
    end
  endtask

  task automatic quote(input [31:0] rsel, input [255:0] nonce, input [255:0] ctx);
    begin
      a_regsel = rsel; a_nonce = nonce; a_ctx = ctx;
      issue(CC_QUOTE);
    end
  endtask

  // ---- the run -------------------------------------------------------

  integer i;
  initial begin
    in_cmd = 17'b0; a_pt = 16'b0; a_idx = 16'b0; a_dig = 256'b0; init_req = 1'b0;
    a_regsel = 32'b0; a_nonce = 256'b0; a_ctx = 256'b0;
    repeat (4) @(posedge CLK_M);
    RST_N = 1'b1;
    repeat (2) @(posedge CLK_M);

    // _MARS_Init: ONE action, the DP derivation included.
    init_req = 1'b1;
    issue(CC_INIT);
    init_req = 1'b0;
    $display("Init               rc=%0d st=%0d", rc, st);

    // A fresh device: both PCRs zero, as after _MARS_Init.
    reg_read(16'd0);
    $display("RegRead      i =0  rc=%0d dig=%064x", rc, dout);
    reg_read(16'd1);
    $display("RegRead      i =1  rc=%0d dig=%064x", rc, dout);

    for (i = 1; i <= 3; i = i + 1) begin
      pcr_extend(16'd0, {248'd0, i[7:0]});
      $display("PcrExtend    i =0  rc=%0d", rc);
      reg_read(16'd0);
      $display("RegRead      i =0  rc=%0d dig=%064x", rc, dout);
    end

    // PCR1 is independent and must still be zero until its own extend.
    pcr_extend(16'd1, {248'd0, 8'hAA});
    reg_read(16'd1);
    $display("RegRead      i =1  rc=%0d dig=%064x", rc, dout);
    reg_read(16'd0);
    $display("RegRead      i =0  rc=%0d dig=%064x", rc, dout);

    // MARS_Quote over both PCRs.  The signature is HMAC(AK, snapshot) with AK
    // derived from DP, so one value exercises the whole key hierarchy: the KDF
    // framing, the snapshot field order, and both HMAC passes.
    quote(32'd3,
          256'h0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20,
          256'h2122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40);
    $display("Quote        rsel=3 rc=%0d sig=%064x", rc, dout);
    $display("Snapshot           snap=%064x", snap);

    $display("FINAL        failure=%0d st=%0d", failure, st);
    $finish;
  end

  initial begin
    repeat (200000) @(posedge CLK_M);
    $display("TIMEOUT: the module never became ready again");
    $finish;
  end

endmodule
