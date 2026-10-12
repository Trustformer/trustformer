//======================================================================
// tb_mars_v2.sv
//
// Example_MarsV2 with the real secworks/sha256_core behind external/glue/:
// every implemented command on its success path, crypto values from the TCG
// reference emulator, each kind of error, failure mode through the secret
// in_fault, and the exact cycle count of every command path.  The E_* lines
// follow the format of sim/golden/mars_v2_vectors.c, so the two diff.
//======================================================================
`timescale 1ns/1ps

module tb_mars_v2;

  localparam CC_SELFTEST         = 16'd0;
  localparam CC_CAPABILITYGET    = 16'd1;
  localparam CC_SEQUENCEHASH     = 16'd2;
  localparam CC_SEQUENCEUPDATE   = 16'd3;
  localparam CC_SEQUENCECOMPLETE = 16'd4;
  localparam CC_PCREXTEND        = 16'd5;
  localparam CC_REGREAD          = 16'd6;
  localparam CC_DERIVE           = 16'd7;
  localparam CC_DPDERIVE         = 16'd8;
  localparam CC_PUBLICREAD       = 16'd9;
  localparam CC_QUOTE            = 16'd10;
  localparam CC_SIGN             = 16'd11;
  localparam CC_SIGNATUREVERIFY  = 16'd12;
  localparam CC_INIT             = 16'hFFFF;

  localparam RC_SUCCESS = 16'd0;
  localparam RC_FAILURE = 16'd2;
  localparam RC_BUFFER  = 16'd4;
  localparam RC_COMMAND = 16'd5;
  localparam RC_VALUE   = 16'd6;
  localparam RC_REG     = 16'd7;

  // "Here are thirty two secret bytes", the seed the reference emulator carries.
  localparam [255:0] PS =
      256'h4865726520617265207468697274792074776f20736563726574206279746573;

  // Host arguments, first byte most significant: bytes 0x01.., 0x21.., 0x41.., 0x61..
  localparam [255:0] NONCE = 256'h0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20;
  localparam [255:0] CTX   = 256'h2122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40;
  localparam [255:0] DIG   = 256'h4142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f60;
  localparam [255:0] CTX2  = 256'h6162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f80;

  reg CLK = 1'b0;
  reg RST_N = 1'b0;
  always #5 CLK = ~CLK;

  reg [16:0]  in_cmd;
  reg [15:0]  a_pt, a_idx, a_nlen, a_ctxlen;
  reg [255:0] a_dig, a_nonce, a_ctx, a_sig;
  reg [31:0]  a_regsel;
  reg         a_restricted;
  reg         init_req, fault;              // platform side, Secret
  reg [1:0]   kat_flip;                     // corrupts the SHA [0] / HMAC [1] answer

  wire         ready;
  wire [15:0]  rc, cap;
  wire [255:0] dout, pcr0, pcr1, snap;
  wire         failure, st, result;

  wire [1040:0] sha_req;
  wire [784:0]  hmac_req;
  wire [255:0]  sha_resp, hmac_resp;

  Example_MarsV2 dut (
      .CLK(CLK), .RST_N(RST_N),
      .in_cmd_out(in_cmd), .in_cmd_arg(ready),

      .in_param_pub_in_pt_out(a_pt),   .in_param_pub_in_pt_arg(),
      .in_param_pub_in_idx_out(a_idx), .in_param_pub_in_idx_arg(),
      .in_param_pub_in_dig_out(a_dig), .in_param_pub_in_dig_arg(),

      // platform side: the Primary Seed, the init request and the fault line
      .in_param_sec_in_ps_out(PS),             .in_param_sec_in_ps_arg(),
      .in_param_sec_in_init_req_out(init_req), .in_param_sec_in_init_req_arg(),
      .in_param_sec_in_fault_out(fault),       .in_param_sec_in_fault_arg(),

      .in_param_pub_in_regsel_out(a_regsel),         .in_param_pub_in_regsel_arg(),
      .in_param_pub_in_nonce_out(a_nonce),           .in_param_pub_in_nonce_arg(),
      .in_param_pub_in_ctx_out(a_ctx),               .in_param_pub_in_ctx_arg(),
      .in_param_pub_in_nlen_out(a_nlen),             .in_param_pub_in_nlen_arg(),
      .in_param_pub_in_ctxlen_out(a_ctxlen),         .in_param_pub_in_ctxlen_arg(),
      .in_param_pub_in_sig_out(a_sig),               .in_param_pub_in_sig_arg(),
      .in_param_pub_in_restricted_out(a_restricted), .in_param_pub_in_restricted_arg(),

      .out_param_pub_out_rc_arg(rc),           .out_param_pub_out_rc_out(1'b1),
      .out_param_pub_out_cap_arg(cap),         .out_param_pub_out_cap_out(1'b1),
      .out_param_pub_out_dout_arg(dout),       .out_param_pub_out_dout_out(1'b1),
      .out_param_pub_out_result_arg(result),   .out_param_pub_out_result_out(1'b1),
      .out_param_pub_out_pcr0_arg(pcr0),       .out_param_pub_out_pcr0_out(1'b1),
      .out_param_pub_out_pcr1_arg(pcr1),       .out_param_pub_out_pcr1_out(1'b1),
      .out_param_pub_out_failure_arg(failure), .out_param_pub_out_failure_out(1'b1),
      .out_param_pub_out_st_arg(st),           .out_param_pub_out_st_out(1'b1),
      .out_param_pub_out_snap_arg(snap),       .out_param_pub_out_snap_out(1'b1),

      .ip_req_sec_ip_sha_arg(sha_req),      .ip_req_sec_ip_sha_out(1'b1),
      .ip_resp_sec_ip_sha_out(sha_resp ^ {255'b0, kat_flip[0]}), .ip_resp_sec_ip_sha_arg(),
      .ip_req_sec_ip_hmac_arg(hmac_req),    .ip_req_sec_ip_hmac_out(1'b1),
      .ip_resp_sec_ip_hmac_out(hmac_resp ^ {255'b0, kat_flip[1]}), .ip_resp_sec_ip_hmac_arg()
  );

  mars_ip_sha_adapter  #(.DECLARED_LAT(140)) sha_ip (
      .CLK(CLK), .RST_N(RST_N), .ip_req(sha_req),  .ip_resp(sha_resp));

  mars_ip_hmac_adapter #(.DECLARED_LAT(275)) hmac_ip (
      .CLK(CLK), .RST_N(RST_N), .ip_req(hmac_req), .ip_resp(hmac_resp));

  // Every Public output, to show that a command left them all as they were.
  wire [1058:0] pub = {rc, cap, result, dout, pcr0, pcr1, snap, failure, st};

  // ---- host helpers --------------------------------------------------

  // Module cycles from the accepting edge to the earliest edge that can
  // accept the next command: 1 = ready stays high.
  integer lat;

  // Stimulus is driven on the NEGEDGE and sampled there: driving it in the
  // same time step as the clock edge races the module's own evaluation.
  task automatic issue(input [15:0] code);
    begin
      @(negedge CLK);
      while (ready !== 1'b1) @(negedge CLK);
      in_cmd = {1'b1, code};
      @(posedge CLK);                         // the accepting edge
      @(negedge CLK);
      in_cmd = 17'b0;
      fault = 1'b0;                           // the platform holds these until the accept
      init_req = 1'b0;
      lat = 1;
      while (ready !== 1'b1) begin
        @(negedge CLK);
        lat = lat + 1;
      end
    end
  endtask

  task automatic init(input logic req);
    begin
      init_req = req;
      issue(CC_INIT);
    end
  endtask

  task automatic cap_get(input [15:0] pt);
    begin
      a_pt = pt;
      issue(CC_CAPABILITYGET);
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

  task automatic derive(input [31:0] rsel, input [15:0] ctxlen);
    begin
      a_regsel = rsel; a_ctx = CTX; a_ctxlen = ctxlen;
      issue(CC_DERIVE);
    end
  endtask

  task automatic dp_derive(input [31:0] rsel, input [15:0] ctxlen);
    begin
      a_regsel = rsel; a_ctx = CTX2; a_ctxlen = ctxlen;
      issue(CC_DPDERIVE);
    end
  endtask

  task automatic quote(input [31:0] rsel, input [15:0] nlen);
    begin
      a_regsel = rsel; a_nonce = NONCE; a_nlen = nlen; a_ctx = CTX; a_ctxlen = 16'd32;
      issue(CC_QUOTE);
    end
  endtask

  task automatic sign(input [15:0] ctxlen);
    begin
      a_ctx = CTX; a_ctxlen = ctxlen; a_dig = DIG;
      issue(CC_SIGN);
    end
  endtask

  task automatic verify(input logic restricted, input [255:0] dig,
                        input [255:0] sig, input [15:0] ctxlen);
    begin
      a_restricted = restricted; a_ctx = CTX; a_ctxlen = ctxlen;
      a_dig = dig; a_sig = sig;
      issue(CC_SIGNATUREVERIFY);
    end
  endtask

  // ---- expected values ------------------------------------------------
  // The TCG reference emulator's output for this exact stimulus.
  // Regenerate with scripts/regen-golden.py --design mars_v2.
  localparam logic [255:0] E_EXT1      = 256'h90f4b39548df55ad6187a1d20d731ecee78c545b94afd16f42ef7592d99cd365;
  localparam logic [255:0] E_PCR1      = 256'h17eaf835d8496ed16d40454b53344de18ffac7e5fbbb87860889922e51f47d70;
  localparam logic [255:0] E_QUOTE0    = 256'heb01e0c80afbe12c08171cbc79833ce41e6f80a6ac5791b9e8c6a9e1c7522107;
  localparam logic [255:0] E_SNAP0     = 256'h387b856e561089f473389b31b9faf54ea4fcea5129a46fd6c3a0626f1a56c6ef;
  localparam logic [255:0] E_QUOTE1    = 256'h1c8be2509eb6f357c7ed5e0e47e2b8d142060f878cc74f6c97c3d2cf22675ac1;
  localparam logic [255:0] E_SNAP1     = 256'hab9167a2c6d6cd5e5b65e556f246e5188ecb75eeb93448671aa4db4fb090af0d;
  localparam logic [255:0] E_QUOTE2    = 256'h17ba17b2bac9579a0a9bfaacfe4899f601194d027778ca7757a4228e0e023bb5;
  localparam logic [255:0] E_SNAP2     = 256'h955fcd52ef0e7e868878f6a279e72623ea7f4e59f819669588066ebac8ddbb1f;
  localparam logic [255:0] E_QUOTE3    = 256'hc3ecb2842c5e21f91cbb5d01380eedc1cee81e61eb929b9fed9bf03098811b3f;
  localparam logic [255:0] E_SNAP3     = 256'hbd0e0d246b4898fb2bc653ee68b679bf7711939e180d618082583fd9c4ad4a9b;
  localparam logic [255:0] E_DERIVE    = 256'h7807f9a3a05ad9967c8574954e504fcdda94b28f2cf4a83375998fed4a1e6c70;
  localparam logic [255:0] E_SIGN      = 256'h25a5cd60c50ee23c6a28a5e100ba5b80097d5530a4c8722435bd0ce143c14df2;
  localparam bit           E_VFY_U_OK  = 1'b1;
  localparam bit           E_VFY_U_BAD = 1'b0;
  localparam bit           E_VFY_R_BAD = 1'b0;
  localparam bit           E_VFY_R_OK  = 1'b1;
  localparam logic [255:0] E_QUOTE_DP  = 256'h884abc5e8978da18ebc13e060ef12bfa3a7b0b458c620edc12200ccded451965;

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

  // One command's answer: its response code and its exact cycle count.  Every
  // command first clears out_dout, out_cap and out_result, so an error answer
  // leaves all three zero.
  task automatic chk_cmd(input string what, input logic [15:0] want_rc,
                         input integer want_lat);
    $display("%-38s rc=%0d lat=%0d", what, rc, lat);
    checks += 2;
    if (rc !== want_rc) begin
      fails++;
      $display("  FAIL  %s: rc=%0d, want %0d", what, rc, want_rc);
    end
    if (lat != want_lat) begin
      fails++;
      $display("  FAIL  %s: %0d cycles, want %0d", what, lat, want_lat);
    end
    if (want_rc !== RC_SUCCESS) begin
      checks++;
      if ({dout, cap, result} !== '0) begin
        fails++;
        $display("  FAIL  %s: out_dout, out_cap or out_result set", what);
      end
    end
  endtask

  // An E_* observation, printed as the golden driver prints it.
  task automatic chk_golden(input string tag, input string field,
                            input logic [255:0] got, input logic [255:0] want);
    $display("%-12s rc=%0d %s=%064x", tag, rc, field, got);
    chk(tag, got, want);
  endtask

  // SignatureVerify's verdict, the one bit of it that leaves the module.
  task automatic chk_verdict(input string tag, input bit want);
    $display("%-12s rc=%0d result=%0d", tag, rc, result);
    chk(tag, {255'b0, result}, {255'b0, want});
    chk({tag, ": out_dout stays zero"}, dout, 0);
  endtask

  // Two runs apart only in a secret: the same cycle count.
  task automatic chk_same(input string what, input integer a, input integer b);
    $display("%-38s %0d / %0d cycles", what, a, b);
    checks++;
    if (a != b) begin
      fails++;
      $display("  FAIL  %s: %0d vs %0d cycles", what, a, b);
    end
  endtask

  task automatic quote_ok(input [31:0] rsel, input string sig_tag,
                          input logic [255:0] esig, input logic [255:0] esnap);
    quote(rsel, 16'd32);
    chk_cmd($sformatf("Quote regsel=%0d", rsel), RC_SUCCESS, 554);
    chk_golden(sig_tag, "sig", dout, esig);
    chk_golden($sformatf("E_SNAP%0d", rsel), "snap", snap, esnap);
  endtask

  // A code outside the action encodings, offered for 8 cycles: ready stays
  // high and every Public output holds.
  task automatic offer(input [15:0] code);
    integer k, drops;
    logic [1058:0] was;
    begin
      @(negedge CLK);
      while (ready !== 1'b1) @(negedge CLK);
      was = pub;
      drops = 0;
      in_cmd = {1'b1, code};
      for (k = 0; k < 8; k++) begin
        @(negedge CLK);
        if (ready !== 1'b1) drops++;
      end
      in_cmd = 17'b0;
      $display("%-38s ready low for %0d of 8 cycles", $sformatf("code %0d offered", code), drops);
      checks += 2;
      if (drops != 0) begin
        fails++;
        $display("  FAIL  code %0d: ready dropped", code);
      end
      if (pub !== was) begin
        fails++;
        $display("  FAIL  code %0d: a Public output moved", code);
      end
    end
  endtask

  // ---- the run -------------------------------------------------------

  integer i, l_ir0, l_selftest, l_sign, l_vfy;
  initial begin
    in_cmd = 17'b0; a_pt = 16'b0; a_idx = 16'b0; a_dig = 256'b0; a_sig = 256'b0;
    a_regsel = 32'b0; a_nonce = 256'b0; a_ctx = 256'b0; a_nlen = 16'd32;
    a_ctxlen = 16'd32; a_restricted = 1'b0;
    init_req = 1'b0; fault = 1'b0; kat_flip = 2'b00;
    repeat (4) @(posedge CLK);
    RST_N = 1'b1;
    repeat (2) @(posedge CLK);

    // Before _MARS_Init every guarded command answers VALUE.
    issue(CC_SELFTEST);
    chk_cmd("SelfTest before Init", RC_VALUE, 2);
    sign(16'd32);
    chk_cmd("Sign before Init", RC_VALUE, 2);
    reg_read(16'd0);
    chk_cmd("RegRead before Init", RC_VALUE, 1);
    chk("st before Init", st, 0);

    // _MARS_Init: init_req=0 refuses, init_req=1 initialises, in equal cycles.
    init(1'b0);
    chk_cmd("Init, init_req=0", RC_VALUE, 278);
    chk("st after a refused Init", st, 0);
    l_ir0 = lat;
    init(1'b1);
    chk_cmd("Init, init_req=1", RC_SUCCESS, 278);
    chk("st after Init", st, 1);
    chk_same("Init: init_req 0 vs 1", l_ir0, lat);

    // Management.
    issue(CC_SELFTEST);
    chk_cmd("SelfTest", RC_SUCCESS, 278);
    chk("SelfTest passes", failure, 0);
    l_selftest = lat;
    cap_get(16'd1);
    chk_cmd("CapabilityGet PT_PCR", RC_SUCCESS, 1);
    chk("PT_PCR is 2", cap, 2);
    cap_get(16'd9);
    chk_cmd("CapabilityGet PT_ALG_SIGN", RC_SUCCESS, 2);
    chk("PT_ALG_SIGN is TPM_ALG_HMAC", cap, 5);
    cap_get(16'd12);
    chk_cmd("CapabilityGet tag 12", RC_VALUE, 2);
    issue(CC_SEQUENCEHASH);
    chk_cmd("SequenceHash", RC_COMMAND, 1);
    issue(CC_SEQUENCEUPDATE);
    chk_cmd("SequenceUpdate", RC_COMMAND, 1);
    issue(CC_SEQUENCECOMPLETE);
    chk_cmd("SequenceComplete", RC_COMMAND, 1);
    issue(CC_PUBLICREAD);
    chk_cmd("PublicRead", RC_COMMAND, 1);

    // Integrity collection.
    reg_read(16'd0);
    chk_cmd("RegRead 0", RC_SUCCESS, 1);
    chk("fresh PCR0 reads zero", dout, 0);
    reg_read(16'd2);
    chk_cmd("RegRead 2", RC_REG, 1);
    pcr_extend(16'd0, 256'h01);
    chk_cmd("PcrExtend 0", RC_SUCCESS, 143);
    chk("out_pcr0 after the extend", pcr0, E_EXT1);
    reg_read(16'd0);
    chk_cmd("RegRead 0", RC_SUCCESS, 1);
    chk_golden("E_EXT1", "dig", dout, E_EXT1);
    pcr_extend(16'd1, 256'hAA);
    chk_cmd("PcrExtend 1", RC_SUCCESS, 143);
    reg_read(16'd1);
    chk_cmd("RegRead 1", RC_SUCCESS, 1);
    chk_golden("E_PCR1", "dig", dout, E_PCR1);
    chk("PCR0 unchanged by the PCR1 extend", pcr0, E_EXT1);
    pcr_extend(16'd2, 256'h01);
    chk_cmd("PcrExtend 2", RC_REG, 2);

    // Quote over each of the four regSelect shapes (36, 68, 68, 100 bytes).
    quote_ok(0, "E_QUOTE0", E_QUOTE0, E_SNAP0);
    quote_ok(1, "E_QUOTE1", E_QUOTE1, E_SNAP1);
    quote_ok(2, "E_QUOTE2", E_QUOTE2, E_SNAP2);
    quote_ok(3, "E_QUOTE3", E_QUOTE3, E_SNAP3);
    quote(3, 16'd31);
    chk_cmd("Quote nlen=31", RC_BUFFER, 2);

    // Key management and signing.
    derive(3, 16'd32);
    chk_cmd("Derive regsel=3", RC_SUCCESS, 419);
    chk_golden("E_DERIVE", "out", dout, E_DERIVE);
    derive(4, 16'd32);
    chk_cmd("Derive regsel=4", RC_REG, 2);
    sign(16'd32);
    chk_cmd("Sign", RC_SUCCESS, 554);
    chk_golden("E_SIGN", "sig", dout, E_SIGN);
    l_sign = lat;

    // SignatureVerify answers SUCCESS either way; the verdict is out_result.
    // An error answer after each match shows the next command clears it.
    verify(1'b0, DIG, E_SIGN, 16'd32);
    chk_cmd("SignatureVerify U, Sign's MAC", RC_SUCCESS, 554);
    chk_verdict("E_VFY_U_OK", E_VFY_U_OK);
    l_vfy = lat;
    sign(16'd0);
    chk_cmd("Sign ctxlen=0", RC_BUFFER, 2);
    verify(1'b0, DIG, E_SIGN ^ 256'd1, 16'd32);
    chk_cmd("SignatureVerify U, one bit flipped", RC_SUCCESS, 554);
    chk_verdict("E_VFY_U_BAD", E_VFY_U_BAD);
    chk_same("SignatureVerify U: match vs mismatch", l_vfy, lat);
    verify(1'b1, DIG, E_SIGN, 16'd32);
    chk_cmd("SignatureVerify R, Sign's MAC", RC_SUCCESS, 554);
    chk_verdict("E_VFY_R_BAD", E_VFY_R_BAD);
    l_vfy = lat;
    verify(1'b1, E_SNAP3, E_QUOTE3, 16'd32);
    chk_cmd("SignatureVerify R, Quote's signature", RC_SUCCESS, 554);
    chk_verdict("E_VFY_R_OK", E_VFY_R_OK);
    chk_same("SignatureVerify R: match vs mismatch", l_vfy, lat);
    init(1'b0);
    chk_cmd("Init, init_req=0, after Init", RC_VALUE, 278);
    chk("a refused Init keeps st", st, 1);
    verify(1'b0, DIG, E_SIGN, 16'd31);
    chk_cmd("SignatureVerify ctxlen=31", RC_BUFFER, 2);

    // DpDerive moves DP, so the same Quote signs anew; REG comes first even
    // for a NULL ctx and keeps DP; a NULL ctx resets it to Init's.
    dp_derive(3, 16'd32);
    chk_cmd("DpDerive regsel=3", RC_SUCCESS, 419);
    quote_ok(3, "E_QUOTE_DP", E_QUOTE_DP, E_SNAP3);
    dp_derive(4, 16'd0);
    chk_cmd("DpDerive regsel=4 ctxlen=0", RC_REG, 2);
    quote_ok(3, "E_QUOTE_DP", E_QUOTE_DP, E_SNAP3);
    dp_derive(3, 16'd0);
    chk_cmd("DpDerive ctxlen=0 (DP reset)", RC_SUCCESS, 278);
    quote_ok(3, "E_QUOTE3", E_QUOTE3, E_SNAP3);

    // Failure mode: in_fault at accept, in the cycles of the public path.
    fault = 1'b1;
    sign(16'd32);
    chk_cmd("Sign with in_fault", RC_FAILURE, 554);
    chk("in_fault enters failure mode", failure, 1);
    chk_same("Sign: in_fault 0 vs 1", l_sign, lat);
    reg_read(16'd0);
    chk_cmd("RegRead in failure mode", RC_FAILURE, 1);
    quote(3, 16'd32);
    chk_cmd("Quote in failure mode", RC_FAILURE, 2);
    issue(CC_SEQUENCEHASH);
    chk_cmd("SequenceHash in failure mode", RC_FAILURE, 1);
    cap_get(16'd1);
    chk_cmd("CapabilityGet in failure mode", RC_SUCCESS, 1);
    chk("CapabilityGet still answers", cap, 2);
    init(1'b0);
    chk_cmd("Init, init_req=0, in failure mode", RC_VALUE, 278);
    chk("a refused Init keeps failure mode", failure, 1);
    init(1'b1);
    chk_cmd("Init, init_req=1, in failure mode", RC_SUCCESS, 278);
    chk("Init clears failure mode", failure, 0);
    chk("Init zeroes PCR0", pcr0, 0);
    chk("Init zeroes PCR1", pcr1, 0);
    sign(16'd32);
    chk_cmd("Sign after the recovery", RC_SUCCESS, 554);
    chk_golden("E_SIGN", "sig", dout, E_SIGN);
    fault = 1'b1;
    quote(3, 16'd32);
    chk_cmd("Quote with in_fault", RC_FAILURE, 554);
    chk("in_fault enters failure mode", failure, 1);
    init(1'b1);
    chk_cmd("Init, init_req=1, in failure mode", RC_SUCCESS, 278);
    chk("Init clears failure mode", failure, 0);

    // SelfTest fails on a corrupted SHA or HMAC answer, in the cycles of a pass.
    for (i = 0; i < 2; i++) begin
      kat_flip = 2'b01 << i;
      issue(CC_SELFTEST);
      kat_flip = 2'b00;
      if (i == 0) chk_cmd("SelfTest, SHA answer corrupted", RC_FAILURE, 278);
      else        chk_cmd("SelfTest, HMAC answer corrupted", RC_FAILURE, 278);
      chk("a failed SelfTest enters failure mode", failure, 1);
      chk_same("SelfTest: pass vs fail", l_selftest, lat);
      init(1'b1);
      chk_cmd("Init, init_req=1, after SelfTest", RC_SUCCESS, 278);
      chk("Init clears failure mode", failure, 0);
    end

    // Codes 13..0xFFFE stay unaccepted.
    offer(16'd13);

    $display("FINAL        failure=%0d st=%0d", failure, st);

    $display("");
    if (fails == 0) $display("PASS  (%0d checks)", checks);
    else begin
      $display("FAIL  (%0d of %0d checks failed)", fails, checks);
      $fatal(1);
    end
    $finish;
  end

  initial begin
    repeat (100000) @(posedge CLK);
    $display("TIMEOUT: the module never became ready again");
    $fatal(1);
  end

endmodule
