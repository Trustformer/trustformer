//======================================================================
// tb_mars_pcrextend.sv
//
// Stage 3 test bench: the generated MARS module + secworks/sha256_core,
// joined by mars_sha256_glue, driven through the MMIO handshake of
// MVP.md section 6.3.
//
// It prints one line per observation; oracle/run-stage3.sh diffs those
// against the C reference emulator.
//======================================================================
`timescale 1ns/1ps

module tb_mars_pcrextend;

  localparam CC_CAPABILITYGET = 16'd1;
  localparam CC_PCREXTEND     = 16'd5;
  localparam CC_REGREAD       = 16'd6;
  localparam CC_CONTINUE      = 16'd13;
  localparam CC_INIT          = 16'hFFFF;
  localparam CC_QUOTE         = 16'd10;

  // "Here are thirty two secret bytes" -- the seed reference-emulator/c/mars.c
  // is compiled with.  Both sides must start from the same PS or every
  // DP-derived value differs.
  localparam [255:0] PS =
      256'h4865726520617265207468697274792074776f20736563726574206279746573;

  reg CLK = 1'b0;
  reg RST_N = 1'b0;
  always #5 CLK = ~CLK;

  reg [16:0]  in_cmd;
  reg [15:0]  a_pt, a_idx;
  reg [255:0] a_dig;
  reg [31:0]  a_regsel;
  reg [255:0] a_nonce, a_ctx;

  wire        ready;
  wire [15:0] rc, cap;
  wire [255:0] dout, pcr0, pcr1;
  wire [7:0]  pend;
  wire        failure, st;
  wire [255:0] snap;

  // SHA-256 group
  wire          sha_req, sha_active;
  wire [1023:0] sha_msg;
  wire [15:0]   sha_len;
  wire [255:0]  sha_res;
  wire          sha_valid, sha_tag;

  // HMAC group -- driven by the real HMAC-SHA256 adapter, so DP and the AK are
  // the values the reference emulator computes and MARS_Quote's signature is
  // comparable byte for byte.
  wire          hmac_req, hmac_active;
  wire [255:0]  hmac_key;
  wire [511:0]  hmac_msg;
  wire [15:0]   hmac_len;
  wire [255:0]  hmac_res;
  wire          hmac_valid, hmac_tag;
  reg           init_req;

  Example_MarsSeq dut (
      .CLK(CLK), .RST_N(RST_N),
      .in_cmd_out(in_cmd), .in_cmd_arg(ready),

      .in_param_pub_in_pt_out(a_pt),   .in_param_pub_in_pt_arg(),
      .in_param_pub_in_idx_out(a_idx), .in_param_pub_in_idx_arg(),
      .in_param_pub_in_dig_out(a_dig), .in_param_pub_in_dig_arg(),

      .in_param_sec_in_sha_res_out(sha_res),     .in_param_sec_in_sha_res_arg(),
      .in_param_sec_in_sha_valid_out(sha_valid), .in_param_sec_in_sha_valid_arg(),
      .in_param_sec_in_sha_tag_out(sha_tag),     .in_param_sec_in_sha_tag_arg(),

      .in_param_sec_in_hmac_res_out(hmac_res),     .in_param_sec_in_hmac_res_arg(),
      .in_param_sec_in_hmac_valid_out(hmac_valid), .in_param_sec_in_hmac_valid_arg(),
      .in_param_sec_in_hmac_tag_out(hmac_tag),     .in_param_sec_in_hmac_tag_arg(),

      // platform side: the Primary Seed and the protected init request
      .in_param_sec_in_ps_out(PS),         .in_param_sec_in_ps_arg(),
      .in_param_sec_in_init_req_out(init_req), .in_param_sec_in_init_req_arg(),

      .out_param_pub_out_rc_arg(rc),                 .out_param_pub_out_rc_out(1'b0),
      .out_param_pub_out_cap_arg(cap),               .out_param_pub_out_cap_out(1'b0),
      .out_param_pub_out_dout_arg(dout),             .out_param_pub_out_dout_out(1'b0),
      .out_param_pub_out_pcr0_arg(pcr0),             .out_param_pub_out_pcr0_out(1'b0),
      .out_param_pub_out_pcr1_arg(pcr1),             .out_param_pub_out_pcr1_out(1'b0),
      .out_param_pub_out_failure_arg(failure),       .out_param_pub_out_failure_out(1'b0),
      .out_param_pub_out_pend_arg(pend),             .out_param_pub_out_pend_out(1'b0),
      .out_param_pub_out_st_arg(st),                 .out_param_pub_out_st_out(1'b0),
      .out_param_pub_out_snap_arg(snap),             .out_param_pub_out_snap_out(1'b0),
      .out_param_pub_out_ctx_arg(),                  .out_param_pub_out_ctx_out(1'b0),

      // MARS_Quote arguments -- tied to a legal-but-unused vector; Quote itself
      // is exercised in Coq and, byte-exactly, at Stage 4c against a real HMAC.
      .in_param_pub_in_regsel_out(a_regsel), .in_param_pub_in_regsel_arg(),
      .in_param_pub_in_nonce_out(a_nonce),   .in_param_pub_in_nonce_arg(),
      .in_param_pub_in_ctx_out(a_ctx),       .in_param_pub_in_ctx_arg(),
      .in_param_pub_in_nlen_out(16'd32),     .in_param_pub_in_nlen_arg(),
      .in_param_pub_in_ctxlen_out(16'd32),   .in_param_pub_in_ctxlen_arg(),

      .out_param_pub_out_sha_req_arg(sha_req),       .out_param_pub_out_sha_req_out(1'b0),
      .out_param_pub_out_sha_active_arg(sha_active), .out_param_pub_out_sha_active_out(1'b0),
      .out_param_sec_out_sha_msg_arg(sha_msg),       .out_param_sec_out_sha_msg_out(1'b0),
      .out_param_sec_out_sha_len_arg(sha_len),       .out_param_sec_out_sha_len_out(1'b0),

      .out_param_pub_out_hmac_req_arg(hmac_req),       .out_param_pub_out_hmac_req_out(1'b0),
      .out_param_pub_out_hmac_active_arg(hmac_active), .out_param_pub_out_hmac_active_out(1'b0),
      .out_param_sec_out_hmac_key_arg(hmac_key),       .out_param_sec_out_hmac_key_out(1'b0),
      .out_param_sec_out_hmac_msg_arg(hmac_msg),       .out_param_sec_out_hmac_msg_out(1'b0),
      .out_param_sec_out_hmac_len_arg(hmac_len),       .out_param_sec_out_hmac_len_out(1'b0)
  );

  mars_hmac_glue hmac (
      .CLK(CLK), .RST_N(RST_N),
      .hmac_active(hmac_active), .hmac_key(hmac_key),
      .hmac_msg(hmac_msg), .hmac_len(hmac_len), .hmac_req(hmac_req),
      .hmac_res(hmac_res), .hmac_valid(hmac_valid), .hmac_tag(hmac_tag)
  );

  mars_sha256_glue glue (
      .CLK(CLK), .RST_N(RST_N),
      .sha_active(sha_active), .sha_msg(sha_msg),
      .sha_len(sha_len), .sha_req(sha_req),
      .sha_res(sha_res), .sha_valid(sha_valid), .sha_tag(sha_tag)
  );

  // ---- host helpers --------------------------------------------------

  task automatic wait_ready;
    begin
      while (ready !== 1'b1) @(posedge CLK);
    end
  endtask

  // Drive one command on the cycle the module accepts it.  Arguments must be
  // stable on that cycle: inputs are latched on the accept cycle only
  // (SPIKE.md section 4).
  task automatic issue(input [15:0] code);
    begin
      wait_ready;
      in_cmd = {1'b1, code};
      @(posedge CLK);
      in_cmd = 17'b0;
      @(posedge CLK);
    end
  endtask

  task automatic pcr_extend(input [15:0] idx, input [255:0] dig);
    begin
      a_idx = idx;
      a_dig = dig;
      issue(CC_PCREXTEND);
    end
  endtask

  // The glue raises sha_valid when the core finishes; the host then
  // advances the command.  A real integration lets the glue pulse Continue
  // itself (MVP.md section 6.3 step 5); doing it here keeps the bench free of
  // an arbiter on the command port.
  task automatic finish_crypto;
    integer guard;
    begin
      guard = 0;
      while (sha_valid !== 1'b1 && guard < 2000) begin
        @(posedge CLK);
        guard = guard + 1;
      end
      if (guard >= 2000) $display("TIMEOUT waiting for sha_valid");
      issue(CC_CONTINUE);
    end
  endtask

  // The reset sequence of MVP.md section 6.3: the platform asserts init_req,
  // the wrapper strobes Init, and the glue advances it when the KDF answers.
  task automatic boot;
    integer guard;
    begin
      init_req = 1'b1;
      issue(CC_INIT);
      guard = 0;
      while (hmac_valid !== 1'b1 && guard < 2000) begin
        @(posedge CLK);
        guard = guard + 1;
      end
      if (guard >= 2000) $display("TIMEOUT waiting for hmac_valid");
      issue(CC_CONTINUE);
      init_req = 1'b0;
      $display("Init               rc=%0d st=%0d pend=%0d", rc, st, pend);
    end
  endtask

  // MARS_Quote: one strobe, then three Continues.  Steps 1 and 2 wait on the
  // SHA core, steps 3 and 4 on the HMAC adapter.
  task automatic quote(input [31:0] rsel, input [255:0] nonce, input [255:0] ctx);
    integer g;
    begin
      a_regsel = rsel; a_nonce = nonce; a_ctx = ctx;
      issue(CC_QUOTE);
      finish_crypto;                     // snapshot -> KDF
      g = 0;
      while (hmac_valid !== 1'b1 && g < 4000) begin @(posedge CLK); g = g + 1; end
      issue(CC_CONTINUE);                // AK -> SIGN
      g = 0;
      while (hmac_valid !== 1'b1 && g < 4000) begin @(posedge CLK); g = g + 1; end
      issue(CC_CONTINUE);                // signature
    end
  endtask

  task automatic reg_read(input [15:0] idx);
    begin
      a_idx = idx;
      issue(CC_REGREAD);
    end
  endtask

  // ---- expected values ------------------------------------------------
  // The TCG C reference emulator's output.  The one-action design is checked
  // against the same numbers in tb_mars_v4.sv.
  // Regenerate with scripts/regen-golden.py.
  localparam logic [255:0] E_ZERO = 256'h0;
  localparam logic [255:0] E_EXT1 = 256'h90f4b39548df55ad6187a1d20d731ecee78c545b94afd16f42ef7592d99cd365;
  localparam logic [255:0] E_EXT2 = 256'h9dea5804aca8b476cf8f1efb4fe41abae758ccb238d6656dbc4ca5d40803dc74;
  localparam logic [255:0] E_EXT3 = 256'h05937d0339976abf003ab9e1247e5e6e3e06c07b11dceb9c6e333c7569ed0f33;
  localparam logic [255:0] E_PCR1 = 256'h17eaf835d8496ed16d40454b53344de18ffac7e5fbbb87860889922e51f47d70;
  localparam logic [255:0] E_SIG  = 256'h335d2b4259e5011ff8fc5584037939b3a751ce2c842432029f3c00174062ab4f;

  int checks = 0, fails = 0;

  task automatic chk(input string what, input logic [255:0] got,
                     input logic [255:0] want);
    checks++;
    if (got !== want) begin
      fails++;
      $display("  FAIL  %s", what);
      $display("        got  %064x", got);
      $display("        want %064x", want);
    end
  endtask

  task automatic chk_rc(input string what, input logic [15:0] got);
    checks++;
    if (got !== 16'd0) begin
      fails++;
      $display("  FAIL  %s: rc=%0d", what, got);
    end
  endtask

  // ---- the run -------------------------------------------------------

  integer i;
  initial begin
    in_cmd = 17'b0; a_pt = 16'b0; a_idx = 16'b0; a_dig = 256'b0; init_req = 1'b0;
    a_regsel = 32'b0; a_nonce = 256'b0; a_ctx = 256'b0;
    repeat (4) @(posedge CLK);
    RST_N = 1'b1;
    repeat (2) @(posedge CLK);

    boot;

    // A fresh device: both PCRs zero, as after _MARS_Init.
    reg_read(16'd0);
    $display("RegRead      i =0  rc=%0d dig=%064x", rc, dout);
    chk_rc("fresh PCR0 read", rc);
    chk("fresh PCR0 is zero", dout, E_ZERO);
    reg_read(16'd1);
    $display("RegRead      i =1  rc=%0d dig=%064x", rc, dout);
    chk_rc("fresh PCR1 read", rc);
    chk("fresh PCR1 is zero", dout, E_ZERO);

    // Extend PCR0 three times with distinct digests, reading back each time.
    // Three, not one, because the second is what catches a glue that leaves
    // sha_valid asserted.
    for (i = 1; i <= 3; i = i + 1) begin
      pcr_extend(16'd0, {248'd0, i[7:0]});
      $display("PcrExtend    i =0  dig=%064x rc=%0d", {248'd0, i[7:0]}, rc);
      finish_crypto;
      $display("Continue           rc=%0d failure=%0d pend=%0d", rc, failure, pend);
      reg_read(16'd0);
      $display("RegRead      i =0  rc=%0d dig=%064x", rc, dout);
      chk_rc("PCR0 read after extend", rc);
      chk($sformatf("PCR0 after extend %0d", i), dout,
          i == 1 ? E_EXT1 : i == 2 ? E_EXT2 : E_EXT3);
    end

    // PCR1 is independent and must still be zero.
    pcr_extend(16'd1, {248'd0, 8'hAA});
    finish_crypto;
    reg_read(16'd1);
    $display("RegRead      i =1  rc=%0d dig=%064x", rc, dout);
    chk("PCR1 after its own extend", dout, E_PCR1);
    reg_read(16'd0);
    $display("RegRead      i =0  rc=%0d dig=%064x", rc, dout);
    chk("PCR0 unchanged by the PCR1 extend", dout, E_EXT3);

    // MARS_Quote over both PCRs, with a nonce and a context the C driver uses
    // verbatim.  The signature is HMAC(AK, snapshot) with AK derived from DP,
    // so it exercises the whole key hierarchy in one value.
    quote(32'd3,
          256'h0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20,
          256'h2122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40);
    $display("Quote        rsel=3 rc=%0d sig=%064x", rc, dout);
    chk_rc("Quote", rc);
    chk("Quote signature", dout, E_SIG);
    $display("Snapshot           snap=%064x", snap);

    $display("FINAL        failure=%0d pend=%0d st=%0d sha_active=%0d", failure, pend, st, sha_active);

    $display("");
    if (fails == 0) $display("PASS  (%0d checks)", checks);
    else begin
      $display("FAIL  (%0d of %0d checks failed)", fails, checks);
      $fatal(1);
    end
    $finish;
  end

endmodule
