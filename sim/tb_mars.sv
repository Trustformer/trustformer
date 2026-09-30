// Behavioural testbench for Example_Mars, the one-action MARS.  Both IPs are
// modelled as functions of the whole request word, and every expected value is
// that function applied to a payload built independently from Mars.v -- so a
// wrong length, field order or key fails though the digest itself is arbitrary.
// Each IP answers for exactly ONE cycle, drives garbage otherwise, and rejects
// a request while one is in flight.
module tb;
  localparam int LSHA  = 140;        // must match fs_ip ip_sha  ip_lat
  localparam int LHMAC = 275;        // must match fs_ip ip_hmac ip_lat

  localparam [255:0] GARB = 256'hdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef;

  // MARS_CC codes (fs_action_encoding)
  localparam [15:0] CC_SELFTEST = 16'h0000, CC_CAPGET = 16'h0001, CC_PCREXT = 16'h0005,
                    CC_REGREAD  = 16'h0006, CC_QUOTE  = 16'h000a, CC_INIT   = 16'hffff;
  // Table 4 response codes
  localparam [15:0] RC_SUCCESS = 16'd0, RC_FAILURE = 16'd2, RC_COMMAND = 16'd5,
                    RC_VALUE   = 16'd6, RC_REG     = 16'd7;

  // ---------------- the modelled IPs ----------------
  function automatic [255:0] sha_model(input [15:0] len, input [1023:0] msg);
    logic [255:0] h;
    begin
      h = 256'h0123456789abcdeffedcba98765432100f1e2d3c4b5a69788796a5b4c3d2e1f0 ^ {240'b0, len};
      for (int i = 0; i < 4; i++)
        h = {h[0], h[255:1]} ^ msg[i*256 +: 256] ^ {h[127:0], h[255:128]};
      sha_model = h;
    end
  endfunction

  function automatic [255:0] hmac_model(input [15:0] len, input [255:0] key, input [511:0] msg);
    logic [255:0] h;
    begin
      h = 256'hc3d2e1f08796a5b40f1e2d3c4b5a6978fedcba98765432100123456789abcdef ^ {240'b0, len};
      h = {h[1:0], h[255:2]} ^ key;
      for (int i = 0; i < 2; i++)
        h = {h[0], h[255:1]} ^ msg[i*256 +: 256] ^ {h[127:0], h[255:128]};
      hmac_model = h;
    end
  endfunction

  // ---------------- request framing, rebuilt from coq/Examples/Mars/Spec.v ----------------
  // call_sha  : {len[15:0], msg[1023:0]}                   (tf_concat hi lo, hi = high bits)
  // call_hmac : {len[15:0], key[255:0], msg[511:0]}
  function automatic [1039:0] sha_req_of(input [15:0] len, input [1023:0] msg);
    sha_req_of = {len, msg};
  endfunction
  function automatic [783:0] hmac_req_of(input [15:0] len, input [255:0] key, input [511:0] msg);
    hmac_req_of = {len, key, msg};
  endfunction

  // ext_msg pcr  = (pcr || in_dig) || 0     -- 64 bytes left-aligned in 1024
  function automatic [1023:0] ext_msg(input [255:0] pcr, input [255:0] dig);
    ext_msg = {pcr, dig, 512'b0};
  endfunction
  // dpinit_msg = [1]_4 || 'D' || 0x00 || "prd" || [8192]_4, left-aligned in 512
  function automatic [511:0] dpinit_msg();
    dpinit_msg = {32'd1, 8'd68, 8'd0, 8'd112, 8'd114, 8'd100, 32'd8192, 408'b0};
  endfunction
  // ak_kdf_msg = [1]_4 || 'R' || 0x00 || ctx || [8192]_4, left-aligned in 512
  function automatic [511:0] ak_kdf_msg(input [255:0] ctx);
    ak_kdf_msg = {32'd1, 8'd82, 8'd0, ctx, 32'd8192, 176'b0};
  endfunction
  function automatic [511:0] sign_msg(input [255:0] snap);
    sign_msg = {snap, 256'b0};
  endfunction
  function automatic [1023:0] snap_none(input [31:0] regsel, input [255:0] nonce);
    snap_none = {regsel, nonce, 736'b0};
  endfunction
  function automatic [1023:0] snap_one(input [31:0] regsel, input [255:0] pcr, input [255:0] nonce);
    snap_one = {regsel, pcr, nonce, 480'b0};
  endfunction
  function automatic [1023:0] snap_both(input [31:0] regsel, input [255:0] p0, input [255:0] p1,
                                        input [255:0] nonce);
    snap_both = {regsel, p0, p1, nonce, 224'b0};
  endfunction

  // ---------------- DUT plumbing ----------------
  logic clk = 0, rst_n = 0;
  logic [16:0] in_cmd_out = 17'b0;
  logic [15:0] in_pt = 0, in_idx = 0, in_nlen = 0, in_ctxlen = 0;
  logic [31:0] in_regsel = 0;
  logic [255:0] in_dig = 0, in_ps = 0, in_nonce = 0, in_ctx = 0;
  logic in_init_req = 0;

  wire ready;
  wire [1040:0] sha_req;            // {strobe, len, msg}
  wire [784:0]  hmac_req;           // {strobe, len, key, msg}
  wire [255:0]  sha_resp, hmac_resp;
  wire [255:0]  o_pcr0, o_pcr1, o_dout, o_snap;
  wire [15:0]   o_rc, o_cap;
  wire          o_st, o_failure;
  wire          ack_pt, ack_idx, ack_dig, ack_ps, ack_init_req, ack_regsel,
                ack_nonce, ack_ctx, ack_nlen, ack_ctxlen, ack_sha, ack_hmac;

  Example_Mars dut(
    .CLK(clk), .RST_N(rst_n),
    // command channel
    .in_cmd_out(in_cmd_out), .in_cmd_arg(ready),
    // inputs: the design drives <x>_arg as a read strobe and reads <x>_out
    .in_param_pub_in_pt_out(in_pt),           .in_param_pub_in_pt_arg(ack_pt),
    .in_param_pub_in_idx_out(in_idx),         .in_param_pub_in_idx_arg(ack_idx),
    .in_param_pub_in_dig_out(in_dig),         .in_param_pub_in_dig_arg(ack_dig),
    .in_param_sec_in_ps_out(in_ps),           .in_param_sec_in_ps_arg(ack_ps),
    .in_param_sec_in_init_req_out(in_init_req), .in_param_sec_in_init_req_arg(ack_init_req),
    .in_param_pub_in_regsel_out(in_regsel),   .in_param_pub_in_regsel_arg(ack_regsel),
    .in_param_pub_in_nonce_out(in_nonce),     .in_param_pub_in_nonce_arg(ack_nonce),
    .in_param_pub_in_ctx_out(in_ctx),         .in_param_pub_in_ctx_arg(ack_ctx),
    .in_param_pub_in_nlen_out(in_nlen),       .in_param_pub_in_nlen_arg(ack_nlen),
    .in_param_pub_in_ctxlen_out(in_ctxlen),   .in_param_pub_in_ctxlen_arg(ack_ctxlen),
    // outputs: the design drives <y>_arg with the value and reads <y>_out as an ack
    .out_param_pub_out_rc_arg(o_rc),           .out_param_pub_out_rc_out(1'b1),
    .out_param_pub_out_cap_arg(o_cap),         .out_param_pub_out_cap_out(1'b1),
    .out_param_pub_out_dout_arg(o_dout),       .out_param_pub_out_dout_out(1'b1),
    .out_param_pub_out_pcr0_arg(o_pcr0),       .out_param_pub_out_pcr0_out(1'b1),
    .out_param_pub_out_pcr1_arg(o_pcr1),       .out_param_pub_out_pcr1_out(1'b1),
    .out_param_pub_out_failure_arg(o_failure), .out_param_pub_out_failure_out(1'b1),
    .out_param_pub_out_st_arg(o_st),           .out_param_pub_out_st_out(1'b1),
    .out_param_pub_out_snap_arg(o_snap),       .out_param_pub_out_snap_out(1'b1),
    // IP links
    .ip_req_sec_ip_sha_arg(sha_req),    .ip_req_sec_ip_sha_out(1'b1),
    .ip_resp_sec_ip_sha_out(sha_resp),  .ip_resp_sec_ip_sha_arg(ack_sha),
    .ip_req_sec_ip_hmac_arg(hmac_req),  .ip_req_sec_ip_hmac_out(1'b1),
    .ip_resp_sec_ip_hmac_out(hmac_resp),.ip_resp_sec_ip_hmac_arg(ack_hmac));

  int cyc = 0;
  always #5 clk = ~clk;
  always @(posedge clk) cyc <= cyc + 1;

  // ---------------- the SHA IP ----------------
  logic [255:0] sha_cap;
  logic [LSHA-1:0] sha_pipe;
  logic sha_busy = 0;
  int sha_reqs = 0, sha_strobe_cycles = 0;
  logic [1039:0] sha_log [0:15];

  always @(posedge clk) begin
    if (!rst_n) begin sha_pipe <= '0; sha_busy <= 0; end
    else begin
      sha_pipe <= {sha_pipe[LSHA-2:0], sha_req[1040]};
      if (sha_req[1040]) begin
        sha_strobe_cycles = sha_strobe_cycles + 1;
        if (sha_busy) begin
          $display("FAIL(cyc %0d): SHA request while one is in flight -- a held strobe, not a pulse", cyc);
          $fatal(1);
        end
        if (sha_reqs < 16) sha_log[sha_reqs] = sha_req[1039:0];
        sha_reqs = sha_reqs + 1;
        sha_cap <= sha_model(sha_req[1039:1024], sha_req[1023:0]);
        sha_busy <= 1;
      end
      if (sha_pipe[LSHA-1]) sha_busy <= 0;
    end
  end
  assign sha_resp = sha_pipe[LSHA-1] ? sha_cap : GARB;

  // ---------------- the HMAC IP ----------------
  logic [255:0] hmac_cap;
  logic [LHMAC-1:0] hmac_pipe;
  logic hmac_busy = 0;
  int hmac_reqs = 0, hmac_strobe_cycles = 0;
  logic [783:0] hmac_log [0:15];

  always @(posedge clk) begin
    if (!rst_n) begin hmac_pipe <= '0; hmac_busy <= 0; end
    else begin
      hmac_pipe <= {hmac_pipe[LHMAC-2:0], hmac_req[784]};
      if (hmac_req[784]) begin
        hmac_strobe_cycles = hmac_strobe_cycles + 1;
        if (hmac_busy) begin
          $display("FAIL(cyc %0d): HMAC request while one is in flight -- a held strobe, not a pulse", cyc);
          $fatal(1);
        end
        if (hmac_reqs < 16) hmac_log[hmac_reqs] = hmac_req[783:0];
        hmac_reqs = hmac_reqs + 1;
        hmac_cap <= hmac_model(hmac_req[783:768], hmac_req[767:512], hmac_req[511:0]);
        hmac_busy <= 1;
      end
      if (hmac_pipe[LHMAC-1]) hmac_busy <= 0;
    end
  end
  assign hmac_resp = hmac_pipe[LHMAC-1] ? hmac_cap : GARB;

  // ---------------- command driver ----------------
  int fails = 0, checks = 0;
  int sha_base, hmac_base, accept_cyc, done_cyc, lat;
  string phase = "";

  // Stimulus is driven on the NEGEDGE and sampled on the NEGEDGE: driving it in
  // the same time step as the clock edge races the DUT's own evaluation, and
  // whether the command is seen at all then depends on scheduling order.
  task automatic run_cmd(input [15:0] code);
    begin
      sha_base = sha_reqs; hmac_base = hmac_reqs;
      @(negedge clk);
      while (ready !== 1'b1) @(negedge clk);          // the next posedge will accept
      in_cmd_out = {1'b1, code};
      @(posedge clk);                                // the accepting edge
      accept_cyc = cyc;
      @(negedge clk);
      in_cmd_out = 17'b0;                            // valid was high for exactly one edge
      while (ready !== 1'b1) @(negedge clk);         // ready again: the action retired
      done_cyc = cyc;
      lat = done_cyc - accept_cyc;
    end
  endtask

  task automatic chk(input string what, input logic cond);
    begin
      checks++;
      if (!cond) begin fails++; $display("  FAIL  [%s] %s", phase, what); end
    end
  endtask

  task automatic chk_eq256(input string what, input [255:0] got, input [255:0] exp);
    begin
      checks++;
      if (got !== exp) begin
        fails++;
        $display("  FAIL  [%s] %s", phase, what);
        $display("        got %h", got);
        $display("        exp %h", exp);
        if (got === GARB) $display("        (it is the GARBAGE value -> sampled on the wrong cycle)");
      end
    end
  endtask

  task automatic chk_req_sha(input string what, input int n, input [1039:0] exp);
    begin
      checks++;
      if (sha_log[n] !== exp) begin
        fails++;
        $display("  FAIL  [%s] %s", phase, what);
        $display("        got len=%0d msg=%h", sha_log[n][1039:1024], sha_log[n][1023:0]);
        $display("        exp len=%0d msg=%h", exp[1039:1024], exp[1023:0]);
      end
    end
  endtask

  task automatic chk_req_hmac(input string what, input int n, input [783:0] exp);
    begin
      checks++;
      if (hmac_log[n] !== exp) begin
        fails++;
        $display("  FAIL  [%s] %s", phase, what);
        $display("        got len=%0d key=%h msg=%h", hmac_log[n][783:768], hmac_log[n][767:512], hmac_log[n][511:0]);
        $display("        exp len=%0d key=%h msg=%h", exp[783:768], exp[767:512], exp[511:0]);
      end
    end
  endtask

  // ---------------- expectations, tracked independently of the DUT ----------------
  logic [255:0] exp_pcr0 = 256'b0, exp_pcr1 = 256'b0;
  logic [255:0] exp_dp, exp_ak, exp_snap, exp_sig;
  int lat_regsel0, lat_regsel3, lat_ext0, lat_ext1, lat_init_no;

  localparam [255:0] PS    = 256'h00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff;
  localparam [255:0] DIG_A = 256'haaaaaaaabbbbbbbbccccccccddddddddeeeeeeeeffffffff00000000_11111111;
  localparam [255:0] DIG_B = 256'h0f0f0f0f1e1e1e1e2d2d2d2d3c3c3c3c4b4b4b4b5a5a5a5a6969696978787878;
  localparam [255:0] NONCE = 256'h1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef;
  localparam [255:0] CTX   = 256'hfeedfacefeedfacefeedfacefeedfacefeedfacefeedfacefeedfacefeedface;

  initial begin
    repeat (4) @(posedge clk);
    rst_n = 1;
    @(posedge clk);

    // ---- 1. CapabilityGet needs no init and is exempt from the guards ----
    phase = "capget";
    in_pt = 16'd3;                                   // MARS_PT_LEN_DIGEST
    run_cmd(CC_CAPGET);
    chk("rc = SUCCESS", o_rc === RC_SUCCESS);
    chk("cap = PROFILE_LEN_DIGEST (32)", o_cap === 16'd32);
    chk("no SHA request",  sha_reqs  == sha_base);
    chk("no HMAC request", hmac_reqs == hmac_base);
    $display("  capget(LEN_DIGEST) rc=%0d cap=%0d  latency=%0d cycles", o_rc, o_cap, lat);

    in_pt = 16'd1;                                   // MARS_PT_PCR
    run_cmd(CC_CAPGET);
    chk("cap = PROFILE_COUNT_PCR (2)", o_cap === 16'd2 && o_rc === RC_SUCCESS);
    in_pt = 16'd9;                                   // MARS_PT_ALG_SIGN
    run_cmd(CC_CAPGET);
    chk("cap = PROFILE_ALG_SIGN (5)", o_cap === 16'd5 && o_rc === RC_SUCCESS);
    in_pt = 16'd99;                                  // not a Table 6 tag
    run_cmd(CC_CAPGET);
    chk("unknown tag -> RC_VALUE", o_rc === RC_VALUE);

    // ---- 2. every other command is refused until Init has COMPLETED ----
    phase = "pre-init";
    in_idx = 16'd0;
    run_cmd(CC_REGREAD);
    chk("RegRead before init -> RC_VALUE", o_rc === RC_VALUE);
    in_dig = DIG_A;
    run_cmd(CC_PCREXT);
    chk("PcrExtend before init -> RC_VALUE", o_rc === RC_VALUE);
    chk("PcrExtend before init drives NO SHA request", sha_reqs == sha_base);
    in_nlen = 16'd32; in_ctxlen = 16'd32; in_regsel = 32'd0; in_nonce = NONCE; in_ctx = CTX;
    run_cmd(CC_QUOTE);
    chk("Quote before init -> RC_VALUE", o_rc === RC_VALUE);
    chk("Quote before init drives no requests", sha_reqs == sha_base && hmac_reqs == hmac_base);

    // ---- 3. _MARS_Init: gated on the platform request, one HMAC round trip ----
    phase = "init-refused";
    in_ps = PS; in_init_req = 1'b0;
    run_cmd(CC_INIT);
    chk("Init without in_init_req -> RC_VALUE", o_rc === RC_VALUE);
    lat_init_no = lat;
    chk("Init without in_init_req drives no HMAC", hmac_reqs == hmac_base);
    chk("out_st still 0", o_st === 1'b0);

    phase = "init";
    in_init_req = 1'b1;
    run_cmd(CC_INIT);
    exp_dp = hmac_model(16'd13, PS, dpinit_msg());
    chk("exactly one HMAC request", hmac_reqs == hmac_base + 1);
    chk("no SHA request", sha_reqs == sha_base);
    chk_req_hmac("Init HMAC request = (13, PS, [1]||'D'||0||\"prd\"||[8192])",
                 hmac_base, hmac_req_of(16'd13, PS, dpinit_msg()));
    chk_eq256("st_ps latched from in_ps", dut.st_s_st_ps, PS);
    chk_eq256("st_dp = HMAC(PS, dpinit frame)", dut.st_s_st_dp, exp_dp);
    chk("rc = SUCCESS", o_rc === RC_SUCCESS);
    chk("out_st = 1", o_st === 1'b1);
    chk("out_failure = 0", o_failure === 1'b0);
    chk("out_pcr0 cleared", o_pcr0 === 256'b0);
    chk("out_pcr1 cleared", o_pcr1 === 256'b0);
    chk_eq256("st_ak cleared", dut.st_s_st_ak, 256'b0);
    $display("  init  latency=%0d cycles, hmac requests=%0d", lat, hmac_reqs - hmac_base);
    
    // [in_init_req] is a SECRET input, so the refused arm -- which does no
    // crypto at all -- must still take as long as the arm that does.
    $display("  init  in_init_req=0: %0d cycles   in_init_req=1: %0d cycles", lat_init_no, lat);
    chk("Init takes the same time whether or not the secret request is set",
        lat_init_no == lat);
    in_init_req = 1'b0;

    // ---- 4. RegRead after init ----
    phase = "regread";
    in_idx = 16'd0; run_cmd(CC_REGREAD);
    chk("RegRead 0 -> SUCCESS", o_rc === RC_SUCCESS);
    chk_eq256("dout = PCR0 (zero)", o_dout, exp_pcr0);
    in_idx = 16'd2; run_cmd(CC_REGREAD);
    chk("RegRead 2 -> RC_REG", o_rc === RC_REG);
    chk_eq256("dout cleared by clear_results", o_dout, 256'b0);

    // ---- 5. PcrExtend: one SHA round trip, the answer lands in the right PCR ----
    phase = "pcrextend-0";
    in_idx = 16'd0; in_dig = DIG_A;
    run_cmd(CC_PCREXT);
    exp_pcr0 = sha_model(16'd64, ext_msg(256'b0, DIG_A));
    lat_ext0 = lat;
    chk("exactly one SHA request", sha_reqs == sha_base + 1);
    chk("no HMAC request", hmac_reqs == hmac_base);
    chk_req_sha("SHA request = (64, PCR0 || in_dig || 0)", sha_base,
                sha_req_of(16'd64, ext_msg(256'b0, DIG_A)));
    chk_eq256("out_pcr0 = SHA(PCR0 || dig)", o_pcr0, exp_pcr0);
    chk_eq256("out_pcr1 untouched", o_pcr1, exp_pcr1);
    chk("rc = SUCCESS", o_rc === RC_SUCCESS);
    $display("  pcrextend(0) latency=%0d cycles", lat);

    phase = "pcrextend-1";
    in_idx = 16'd1; in_dig = DIG_B;
    run_cmd(CC_PCREXT);
    exp_pcr1 = sha_model(16'd64, ext_msg(256'b0, DIG_B));
    lat_ext1 = lat;
    chk_req_sha("SHA request = (64, PCR1 || in_dig || 0)", sha_base,
                sha_req_of(16'd64, ext_msg(256'b0, DIG_B)));
    chk_eq256("out_pcr1 = SHA(PCR1 || dig)", o_pcr1, exp_pcr1);
    chk_eq256("out_pcr0 untouched", o_pcr0, exp_pcr0);

    phase = "pcrextend-chain";
    in_idx = 16'd0; in_dig = DIG_B;
    run_cmd(CC_PCREXT);
    chk_req_sha("second extend hashes the UPDATED PCR0", sha_base,
                sha_req_of(16'd64, ext_msg(exp_pcr0, DIG_B)));
    exp_pcr0 = sha_model(16'd64, ext_msg(exp_pcr0, DIG_B));
    chk_eq256("out_pcr0 = SHA(PCR0' || dig)", o_pcr0, exp_pcr0);

    phase = "pcrextend-range";
    in_idx = 16'd5;
    run_cmd(CC_PCREXT);
    chk("index out of range -> RC_REG", o_rc === RC_REG);
    chk("out-of-range extend drives NO SHA request", sha_reqs == sha_base);

    phase = "regread-after";
    in_idx = 16'd0; run_cmd(CC_REGREAD);
    chk_eq256("RegRead 0 returns the extended PCR0", o_dout, exp_pcr0);
    in_idx = 16'd1; run_cmd(CC_REGREAD);
    chk_eq256("RegRead 1 returns the extended PCR1", o_dout, exp_pcr1);

    // ---- 6. Quote: 1 SHA + 2 HMAC in ONE action, the sequenced and chained case ----
    phase = "quote-regsel0";
    in_nlen = 16'd32; in_ctxlen = 16'd32; in_nonce = NONCE; in_ctx = CTX; in_regsel = 32'd0;
    run_cmd(CC_QUOTE);
    exp_snap = sha_model(16'd36, snap_none(32'd0, NONCE));
    exp_ak   = hmac_model(16'd42, exp_dp, ak_kdf_msg(CTX));
    exp_sig  = hmac_model(16'd32, exp_ak, sign_msg(exp_snap));
    lat_regsel0 = lat;
    chk("exactly ONE SHA request", sha_reqs == sha_base + 1);
    chk("exactly TWO HMAC requests", hmac_reqs == hmac_base + 2);
    chk_req_sha("SHA request = (36, regSelect || nonce || 0)", sha_base,
                sha_req_of(16'd36, snap_none(32'd0, NONCE)));
    chk_req_hmac("HMAC #1 = (42, DP, [1]||'R'||0||ctx||[8192])", hmac_base,
                 hmac_req_of(16'd42, exp_dp, ak_kdf_msg(CTX)));
    chk_req_hmac("HMAC #2 = (32, AK, snapshot || 0)", hmac_base + 1,
                 hmac_req_of(16'd32, exp_ak, sign_msg(exp_snap)));
    chk_eq256("st_snap", dut.st_s_st_snap, exp_snap);
    chk_eq256("st_ak",   dut.st_s_st_ak,   exp_ak);
    chk_eq256("st_sig",  dut.st_s_st_sig,  exp_sig);
    chk_eq256("out_snap = snapshot", o_snap, exp_snap);
    chk_eq256("out_dout = signature", o_dout, exp_sig);
    chk("rc = SUCCESS", o_rc === RC_SUCCESS);
    $display("  quote(regsel=0) latency=%0d cycles, sha=%0d hmac=%0d",
             lat, sha_reqs - sha_base, hmac_reqs - hmac_base);

    phase = "quote-regsel3";
    in_regsel = 32'd3;
    run_cmd(CC_QUOTE);
    exp_snap = sha_model(16'd100, snap_both(32'd3, exp_pcr0, exp_pcr1, NONCE));
    exp_ak   = hmac_model(16'd42, exp_dp, ak_kdf_msg(CTX));
    exp_sig  = hmac_model(16'd32, exp_ak, sign_msg(exp_snap));
    lat_regsel3 = lat;
    chk("exactly ONE SHA request", sha_reqs == sha_base + 1);
    chk("exactly TWO HMAC requests", hmac_reqs == hmac_base + 2);
    chk_req_sha("SHA request = (100, regSelect || PCR0 || PCR1 || nonce || 0)", sha_base,
                sha_req_of(16'd100, snap_both(32'd3, exp_pcr0, exp_pcr1, NONCE)));
    chk_req_hmac("HMAC #2 = (32, AK, snapshot || 0)", hmac_base + 1,
                 hmac_req_of(16'd32, exp_ak, sign_msg(exp_snap)));
    chk_eq256("out_dout = signature", o_dout, exp_sig);
    chk_eq256("out_snap = snapshot", o_snap, exp_snap);
    $display("  quote(regsel=3) latency=%0d cycles, sha=%0d hmac=%0d",
             lat, sha_reqs - sha_base, hmac_reqs - hmac_base);

    phase = "quote-regsel1";
    in_regsel = 32'd1;
    run_cmd(CC_QUOTE);
    exp_snap = sha_model(16'd68, snap_one(32'd1, exp_pcr0, NONCE));
    exp_sig  = hmac_model(16'd32, exp_ak, sign_msg(exp_snap));
    chk_req_sha("SHA request = (68, regSelect || PCR0 || nonce || 0)", sha_base,
                sha_req_of(16'd68, snap_one(32'd1, exp_pcr0, NONCE)));
    chk_eq256("out_dout = signature", o_dout, exp_sig);

    phase = "quote-rejects";
    in_nlen = 16'd16;
    run_cmd(CC_QUOTE);
    chk("nlen != 32 -> RC_VALUE", o_rc === RC_VALUE);
    chk("and no requests are driven", sha_reqs == sha_base && hmac_reqs == hmac_base);
    in_nlen = 16'd32; in_ctxlen = 16'd8;
    run_cmd(CC_QUOTE);
    chk("ctxlen != 32 -> RC_VALUE", o_rc === RC_VALUE);
    in_ctxlen = 16'd32; in_regsel = 32'd7;
    run_cmd(CC_QUOTE);
    chk("regSelect out of range -> RC_REG", o_rc === RC_REG);
    chk("and no requests are driven", sha_reqs == sha_base && hmac_reqs == hmac_base);

    // ---- 7. the live input must not be used: change it after acceptance ----
    phase = "latched-input";
    in_idx = 16'd1; in_dig = DIG_A;
    begin
      sha_base = sha_reqs;
      @(negedge clk);
      while (ready !== 1'b1) @(negedge clk);
      in_cmd_out = {1'b1, CC_PCREXT};
      @(posedge clk);
      @(negedge clk);
      in_cmd_out = 17'b0;
      in_dig = ~DIG_A;                                // changed AFTER acceptance
      while (ready !== 1'b1) @(negedge clk);
    end
    chk_req_sha("the request carries the LATCHED in_dig, not the live one", sha_base,
                sha_req_of(16'd64, ext_msg(exp_pcr1, DIG_A)));
    exp_pcr1 = sha_model(16'd64, ext_msg(exp_pcr1, DIG_A));
    chk_eq256("out_pcr1 = SHA(PCR1 || latched dig)", o_pcr1, exp_pcr1);
    in_dig = DIG_A;

    // ---- 8. an unsupported command code ----
    phase = "unsupported";
    run_cmd(CC_SELFTEST);
    chk("SelfTest -> RC_COMMAND", o_rc === RC_COMMAND);

    // ---- 9. latency: does the taken arm change the cycle count? ----
    $display("");
    $display("  latency  pcrextend idx=0: %0d   idx=1: %0d", lat_ext0, lat_ext1);
    $display("  latency  quote regsel=0: %0d   regsel=3: %0d", lat_regsel0, lat_regsel3);
    chk("PcrExtend: both arms take the same number of cycles", lat_ext0 == lat_ext1);
    chk("Quote: all snapshot arms take the same number of cycles", lat_regsel0 == lat_regsel3);

    $display("");
    $display("  SHA  requests=%0d strobe-cycles=%0d", sha_reqs, sha_strobe_cycles);
    $display("  HMAC requests=%0d strobe-cycles=%0d", hmac_reqs, hmac_strobe_cycles);
    chk("every SHA strobe was a one-cycle pulse", sha_strobe_cycles == sha_reqs);
    chk("every HMAC strobe was a one-cycle pulse", hmac_strobe_cycles == hmac_reqs);

    $display("");
    if (fails == 0) $display("PASS  (%0d checks)", checks);
    else begin $display("FAIL  (%0d of %0d checks failed)", fails, checks); $fatal(1); end
    $finish;
  end

  initial begin
    repeat (60000) @(posedge clk);
    $display("FAIL: timeout in phase [%s] (the module never became ready again)", phase);
    $fatal(1);
  end
endmodule
