module tb_knox_otp;
  import sha1_ref::*;

  localparam [1:0] SET_SECRET = 2'd0, OTP = 2'd1, AUDIT = 2'd2, UNUSED = 2'd3;
  localparam [159:0] RFCK = 160'h3132333435363738393031323334353637383930;
  localparam [63:0] ONES64 = 64'hFFFF_FFFF_FFFF_FFFF;

  logic clk = 0, rst_n = 0;
  logic [2:0]   in_cmd_out = 3'b0;
  logic [159:0] secret_in = '0;
  logic [63:0]  ctr_in = '0;
  wire          ready, secret_ack, ctr_ack, resp_ack;
  wire [1024:0] ip_req;
  wire [159:0]  ip_resp;
  wire [0:0]    set_ok;
  wire [31:0]   code;
  wire [63:0]   max_ctr;

  Knox_Otp dut(
    .CLK(clk), .RST_N(rst_n),
    .in_cmd_out(in_cmd_out), .in_cmd_arg(ready),
    .in_param_pub_in_secret_out(secret_in), .in_param_pub_in_secret_arg(secret_ack),
    .in_param_pub_in_ctr_out(ctr_in), .in_param_pub_in_ctr_arg(ctr_ack),
    .out_param_pub_out_set_ok_arg(set_ok), .out_param_pub_out_set_ok_out(1'b1),
    .out_param_pub_out_code_arg(code), .out_param_pub_out_code_out(1'b1),
    .out_param_pub_out_max_ctr_arg(max_ctr), .out_param_pub_out_max_ctr_out(1'b1),
    .ip_req_sec_ip_sha1_arg(ip_req), .ip_req_sec_ip_sha1_out(1'b1),
    .ip_resp_sec_ip_sha1_out(ip_resp), .ip_resp_sec_ip_sha1_arg(resp_ack));

  sha1_2blk_model #(.DECLARED_LAT(180)) ip(.CLK(clk), .RST_N(rst_n), .ip_req(ip_req), .ip_resp(ip_resp));

  always #5 clk = ~clk;

  int checks = 0, fails = 0;

  function automatic logic [1023:0] pad2(input logic [1023:0] m, input int len);
    logic [1023:0] p;
    p = m;
    p[1023 - len] = 1'b1;
    p[63:0] = 64'(len);
    return p;
  endfunction
  function automatic logic [159:0] sha1_2(input logic [1023:0] padded);
    return compress(compress(IV, padded[1023:512]), padded[511:0]);
  endfunction

  function automatic logic [159:0] hmac(input logic [159:0] key, input logic [63:0] msg,
                                        output logic [1023:0] req_in, output logic [1023:0] req_out);
    logic [511:0] k0;
    logic [1023:0] m;
    logic [159:0] inner;
    k0 = {key, 352'b0};
    m = '0; m[1023 -: 576] = {k0 ^ {64{8'h36}}, msg};
    req_in = pad2(m, 576);
    inner = sha1_2(req_in);
    m = '0; m[1023 -: 672] = {k0 ^ {64{8'h5c}}, inner};
    req_out = pad2(m, 672);
    return sha1_2(req_out);
  endfunction

  function automatic logic [31:0] trunc_mod(input logic [159:0] hs);
    int off;
    logic [31:0] p;
    off = int'(hs[3:0]);
    p = hs[159 - 8*off -: 32];
    return (p & 32'h7fff_ffff) % 32'd1000000;
  endfunction

  function automatic logic [31:0] hotp(input logic [159:0] key, input logic [63:0] c);
    logic [1023:0] ri, ro;
    return trunc_mod(hmac(key, c, ri, ro));
  endfunction

  logic [159:0] m_secret = '0;
  logic [63:0]  m_bound = '0;

  task automatic expect_eq(input string what, input logic [159:0] got, input logic [159:0] want);
    checks++;
    if (got !== want) begin
      $display("FAIL: %s = %h, expected %h", what, got, want);
      fails++;
    end
  endtask

  task automatic expect_req(input string what, input logic [1023:0] got, input logic [1023:0] want);
    checks++;
    if (got !== want) begin
      $display("FAIL: %s\n  got      %h\n  expected %h", what, got, want);
      fails++;
    end
  endtask

  task automatic expect_ports(input string what, input logic s, input logic [31:0] c, input logic [63:0] m);
    expect_eq({what, ": out_set_ok"}, 160'(set_ok), 160'(s));
    expect_eq({what, ": out_code"}, 160'(code), 160'(c));
    expect_eq({what, ": out_max_ctr"}, 160'(max_ctr), 160'(m));
  endtask

  task automatic expect_state(input string what);
    expect_eq({what, ": secret"}, dut.st_s_st_secret, m_secret);
    expect_eq({what, ": max-ctr"}, 160'(dut.st_s_st_maxctr), 160'(m_bound));
    expect_eq({what, ": scratch hs"}, dut.st_s_st_hs, '0);
    expect_eq({what, ": scratch tmp"}, 160'(dut.st_s_st_tmp), '0);
  endtask

  localparam int NOUT = 4;
  int lat_seen[NOUT] = '{-1, -1, -1, -1};
  int lat_count[NOUT] = '{0, 0, 0, 0};
  string lat_name[NOUT] = '{"set-secret", "otp/accept", "otp/reject", "audit"};

  task automatic record_latency(input int outcome, input int lat);
    checks++;
    lat_count[outcome]++;
    if (lat_seen[outcome] < 0) lat_seen[outcome] = lat;
    else if (lat_seen[outcome] != lat) begin
      $display("FAIL: %s latency %0d, earlier %0d", lat_name[outcome], lat, lat_seen[outcome]);
      fails++;
    end
  endtask

  task automatic scramble();
    secret_in = {$urandom, $urandom, $urandom, $urandom, $urandom};
    ctr_in = {$urandom, $urandom};
  endtask

  task automatic call(input [1:0] c, input [159:0] s, input [63:0] t, output int lat);
    @(negedge clk);
    while (ready !== 1'b1) begin scramble(); @(negedge clk); end
    in_cmd_out = {1'b1, c}; secret_in = s; ctr_in = t;
    @(posedge clk);
    lat = 1;
    @(negedge clk);
    in_cmd_out = 3'b0; scramble();
    #1;
    while (ready !== 1'b1) begin @(negedge clk); #1; lat++; end
  endtask

  task automatic set_secret(input [159:0] k);
    int lat;
    call(SET_SECRET, k, {$urandom, $urandom}, lat);
    record_latency(0, lat);
    m_secret = k;
    expect_ports($sformatf("set-secret(%h)", k), 1'b1, 0, 0);
    expect_state("set-secret");
  endtask

  task automatic audit();
    int lat;
    call(AUDIT, {$urandom, $urandom, $urandom, $urandom, $urandom}, {$urandom, $urandom}, lat);
    record_latency(3, lat);
    expect_ports("audit", 1'b0, 0, m_bound);
    expect_state("audit");
  endtask

  task automatic otp(input [63:0] c, input bit has_lit = 0, input [31:0] lit = 0);
    int lat, r0;
    bit accept = !(c < m_bound);
    logic [1023:0] ri, ro;
    logic [159:0] hs;
    logic [31:0] want;
    string what = $sformatf("otp(%0d)", c);
    hs = hmac(m_secret, c, ri, ro);
    if (ip.override_en) hs = ip.override_digest;
    want = accept ? trunc_mod(hs) : 32'd0;
    r0 = ip.requests;
    call(OTP, {$urandom, $urandom, $urandom, $urandom, $urandom}, c, lat);
    record_latency(accept ? 1 : 2, lat);
    expect_eq({what, ": IP requests"}, 160'(ip.requests - r0), accept ? 2 : 0);
    if (accept && !ip.override_en) begin
      expect_req({what, ": inner request"}, ip.req_log[r0 % 2], ri);
      expect_req({what, ": outer request"}, ip.req_log[(r0 + 1) % 2], ro);
    end
    if (has_lit) expect_eq({what, ": reference = literal"}, 160'(want), 160'(lit));
    if (accept) m_bound = c;
    expect_ports(what, 1'b0, want, 0);
    expect_state(what);
  endtask

  task automatic reset_device();
    @(negedge clk); rst_n = 0;
    repeat (3) @(negedge clk); rst_n = 1;
    m_secret = '0; m_bound = '0;
    #1;
    expect_ports("after reset", 1'b0, 0, 0);
    expect_state("after reset");
  endtask

  logic [31:0] rfc4226 [10] = '{755224, 287082, 359152, 969429, 338314,
                                254676, 287922, 162583, 399871, 520489};
  logic [63:0] rfc6238_t [6] = '{64'h1, 64'h23523EC, 64'h23523ED, 64'h273EF07,
                                 64'h3F940AA, 64'h27BC86AA};
  logic [31:0] rfc6238_c [6] = '{287082, 81804, 50471, 5924, 279037, 353130};

  initial begin
    logic [1023:0] ri, ro;
    logic [63:0] c;
    int lat;

    begin
      logic [511:0] blk;
      blk = '0;
      blk[511 -: 24] = 24'h616263;
      blk[487] = 1'b1;
      blk[63:0] = 64'd24;
      expect_eq("ref SHA-1(abc)", compress(IV, blk),
                160'ha9993e364706816aba3e25717850c26c9cd0d89d);
    end
    expect_eq("ref RFC 2202 tc1", hmac({20{8'h0b}}, 64'h4869205468657265, ri, ro),
              160'hb617318655057264e28bc0b6fb378c8ef146be00);
    expect_eq("ref RFC 4226 HMAC(0)", hmac(RFCK, 0, ri, ro),
              160'hcc93cf18508d94934c64b65d8ba7667fb7cde4b0);

    repeat (3) @(posedge clk);
    rst_n = 1;
    #1;
    expect_ports("power-on", 1'b0, 0, 0);
    expect_state("power-on");

    audit();
    otp(0, 1, 328482);

    set_secret(RFCK);
    for (int i = 0; i < 10; i++) otp(i, 1, rfc4226[i]);
    audit();
    otp(3, 1, 0);
    audit();

    set_secret(160'h1337);
    otp(1234, 1, 451349);
    otp(1, 1, 0);
    audit();
    otp(1234, 1, 451349);
    otp(9999, 1, 910689);
    audit();
    set_secret(160'hcafe);
    otp(1, 1, 0);
    audit();

    begin
      int r0 = ip.requests;
      call(UNUSED, {$urandom, $urandom, $urandom, $urandom, $urandom}, 0, lat);
      expect_eq("code 3: latency", 160'(lat), 1);
      expect_eq("code 3: IP requests", 160'(ip.requests - r0), 0);
      expect_ports("code 3", 1'b0, 0, 9999);
      expect_state("code 3");
    end

    reset_device();
    set_secret(RFCK);
    for (int i = 0; i < 6; i++) otp(rfc6238_t[i], 1, rfc6238_c[i]);

    set_secret({160{1'b1}});
    otp(64'h1_0000_0000);
    otp(64'h0_FFFF_FFFF, 1, 0);
    otp(ONES64, 1, 995544);
    otp(ONES64 - 1, 1, 0);
    audit();

    reset_device();
    c = 0;
    for (int i = 0; i < 100; i++) begin
      if (i % 25 == 0) set_secret({$urandom, $urandom, $urandom, $urandom, $urandom});
      case ($urandom % 4)
        0: otp(c);
        1: if (c > 0) otp(c - 1 - ($urandom % c));
        default: begin c = c + 1 + 64'($urandom); otp(c); end
      endcase
      if (i % 50 == 0) audit();
      if (i % 100 == 99) c = c + ({$urandom, $urandom} >> 2);
    end

    reset_device();
    set_secret(RFCK);
    for (int i = 0; i < 4; i++) begin
      ip.answer_at = (i == 0) ? 1 : (i == 1) ? 60 : (i == 2) ? 120 : 179;
      otp(i, 1, rfc4226[i]);
      expect_eq("IP answer delay", 160'(ip.last_lat), 160'(ip.answer_at));
    end
    ip.answer_at = 179;

    begin
      logic [31:0] vals [$];
      logic [159:0] hs;
      int n;
      for (int i = 0; i < 12; i++) begin
        vals.push_back(32'd1000000 << i); vals.push_back((32'd1000000 << i) - 1);
      end
      vals.push_back(0); vals.push_back(1); vals.push_back(999999);
      vals.push_back(32'h7FFF_FFFF); vals.push_back(2147000000); vals.push_back(2146999999);
      vals.push_back(123456789);
      n = vals.size();
      for (int k = 0; k < n; k++) vals.push_back(vals[k] | 32'h8000_0000);
      ip.override_en = 1;
      c = m_bound;
      for (int o = 0; o < 16; o++)
        foreach (vals[k]) begin
          hs = {160{1'b1}};
          hs[159 - 8*o -: 32] = vals[k];
          hs[3:0] = 4'(o);
          ip.override_digest = hs;
          c = c + 1;
          otp(c, 1, (vals[k] & 32'h7FFF_FFFF) % 1000000);
        end
      for (int k = 0; k < 64; k++) begin
        ip.override_digest = {$urandom, $urandom, $urandom, $urandom, $urandom};
        c = c + 1;
        otp(c);
      end
      ip.override_en = 0;
    end

    for (int o = 0; o < NOUT; o++)
      $display("latency %s: %0d cycle(s) (%0d calls)", lat_name[o], lat_seen[o], lat_count[o]);
    checks++;
    if (lat_seen[1] != lat_seen[2]) begin
      $display("FAIL: otp latency depends on accept / reject"); fails++;
    end
    $display("IP: %0d requests, model failures %0d", ip.requests, ip.fails);
    fails += ip.fails;

    if (fails != 0) begin $display("FAIL: %0d of %0d checks", fails, checks); $fatal(1); end
    $display("PASS (%0d checks)", checks);
    $finish;
  end

  initial begin repeat (2000000) @(posedge clk); $display("FAIL: timeout"); $fatal(1); end
endmodule
