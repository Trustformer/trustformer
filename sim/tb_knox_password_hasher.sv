module tb_knox_password_hasher;
  localparam [1:0] SET = 2'd0, GET = 2'd1;

  logic clk = 0, rst_n = 0;
  logic [2:0]   in_cmd_out = 3'b0;
  logic [159:0] sec_in = '0;
  logic [255:0] msg_in = '0;
  wire          ready, sec_ack, msg_ack, resp_ack;
  wire [512:0]  ip_req;
  wire [255:0]  ip_resp;
  wire          out_ok;
  wire [255:0]  out_digest;

  Knox_PwHasher dut(
    .CLK(clk), .RST_N(rst_n),
    .in_cmd_out(in_cmd_out), .in_cmd_arg(ready),
    .in_param_pub_in_secret_out(sec_in), .in_param_pub_in_secret_arg(sec_ack),
    .in_param_pub_in_msg_out(msg_in), .in_param_pub_in_msg_arg(msg_ack),
    .out_param_pub_out_ok_arg(out_ok), .out_param_pub_out_ok_out(1'b1),
    .out_param_pub_out_digest_arg(out_digest), .out_param_pub_out_digest_out(1'b1),
    .ip_req_sec_ip_sha_blk_arg(ip_req), .ip_req_sec_ip_sha_blk_out(1'b1),
    .ip_resp_sec_ip_sha_blk_out(ip_resp), .ip_resp_sec_ip_sha_blk_arg(resp_ack));

  pwhash_sha256_adapter #(.DECLARED_LAT(72)) ip(
    .CLK(clk), .RST_N(rst_n), .ip_req(ip_req), .ip_resp(ip_resp));

  always #5 clk = ~clk;

  int strobes = 0;
  logic strobe_d = 1'b0;
  always @(posedge clk) begin
    strobe_d <= rst_n ? ip_req[512] : 1'b0;
    if (rst_n && ip_req[512] && !strobe_d) strobes <= strobes + 1;
  end

  typedef logic [7:0] bytes_t [$];

  logic [31:0] KK [64] = '{
    32'h428a2f98, 32'h71374491, 32'hb5c0fbcf, 32'he9b5dba5, 32'h3956c25b, 32'h59f111f1, 32'h923f82a4, 32'hab1c5ed5,
    32'hd807aa98, 32'h12835b01, 32'h243185be, 32'h550c7dc3, 32'h72be5d74, 32'h80deb1fe, 32'h9bdc06a7, 32'hc19bf174,
    32'he49b69c1, 32'hefbe4786, 32'h0fc19dc6, 32'h240ca1cc, 32'h2de92c6f, 32'h4a7484aa, 32'h5cb0a9dc, 32'h76f988da,
    32'h983e5152, 32'ha831c66d, 32'hb00327c8, 32'hbf597fc7, 32'hc6e00bf3, 32'hd5a79147, 32'h06ca6351, 32'h14292967,
    32'h27b70a85, 32'h2e1b2138, 32'h4d2c6dfc, 32'h53380d13, 32'h650a7354, 32'h766a0abb, 32'h81c2c92e, 32'h92722c85,
    32'ha2bfe8a1, 32'ha81a664b, 32'hc24b8b70, 32'hc76c51a3, 32'hd192e819, 32'hd6990624, 32'hf40e3585, 32'h106aa070,
    32'h19a4c116, 32'h1e376c08, 32'h2748774c, 32'h34b0bcb5, 32'h391c0cb3, 32'h4ed8aa4a, 32'h5b9cca4f, 32'h682e6ff3,
    32'h748f82ee, 32'h78a5636f, 32'h84c87814, 32'h8cc70208, 32'h90befffa, 32'ha4506ceb, 32'hbef9a3f7, 32'hc67178f2};

  function automatic logic [31:0] rotr(input logic [31:0] x, input int n);
    return (x >> n) | (x << (32 - n));
  endfunction

  function automatic logic [255:0] ref_sha256(input bytes_t m);
    bytes_t p;
    logic [63:0] bitlen;
    logic [31:0] H [8];
    logic [31:0] W [64];
    logic [31:0] a, b, c, d, e, f, g, h, t1, t2, s0, s1;
    int nblk;
    H = '{32'h6a09e667, 32'hbb67ae85, 32'h3c6ef372, 32'ha54ff53a,
          32'h510e527f, 32'h9b05688c, 32'h1f83d9ab, 32'h5be0cd19};
    bitlen = 64'(m.size()) * 64'd8;
    p = m;
    p.push_back(8'h80);
    while (p.size() % 64 != 56) p.push_back(8'h00);
    for (int i = 7; i >= 0; i--) p.push_back(bitlen[8*i +: 8]);
    nblk = p.size() / 64;
    for (int blk = 0; blk < nblk; blk++) begin
      for (int t = 0; t < 16; t++)
        W[t] = {p[64*blk + 4*t], p[64*blk + 4*t + 1], p[64*blk + 4*t + 2], p[64*blk + 4*t + 3]};
      for (int t = 16; t < 64; t++) begin
        s0 = rotr(W[t-15], 7) ^ rotr(W[t-15], 18) ^ (W[t-15] >> 3);
        s1 = rotr(W[t-2], 17) ^ rotr(W[t-2], 19) ^ (W[t-2] >> 10);
        W[t] = s1 + W[t-7] + s0 + W[t-16];
      end
      a = H[0]; b = H[1]; c = H[2]; d = H[3]; e = H[4]; f = H[5]; g = H[6]; h = H[7];
      for (int t = 0; t < 64; t++) begin
        t1 = h + (rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)) + ((e & f) ^ (~e & g)) + KK[t] + W[t];
        t2 = (rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)) + ((a & b) ^ (a & c) ^ (b & c));
        h = g; g = f; f = e; e = d + t1; d = c; c = b; b = a; a = t1 + t2;
      end
      H[0] += a; H[1] += b; H[2] += c; H[3] += d; H[4] += e; H[5] += f; H[6] += g; H[7] += h;
    end
    return {H[0], H[1], H[2], H[3], H[4], H[5], H[6], H[7]};
  endfunction

  function automatic bytes_t str_bytes(input string s);
    bytes_t q;
    for (int i = 0; i < s.len(); i++) q.push_back(s[i]);
    return q;
  endfunction

  function automatic bytes_t be_bytes(input logic [255:0] v, input int nbytes);
    bytes_t q;
    for (int i = nbytes - 1; i >= 0; i--) q.push_back(v[8*i +: 8]);
    return q;
  endfunction

  function automatic logic [255:0] ref_get_hash(input logic [159:0] s, input logic [255:0] m);
    return ref_sha256({be_bytes(256'(s), 20), be_bytes(m, 32)});
  endfunction

  function automatic logic [255:0] ref_paper_order(input logic [159:0] s, input logic [255:0] m);
    return ref_sha256({be_bytes(m, 32), be_bytes(256'(s), 20)});
  endfunction

  logic [159:0] m_secret = '0;
  logic         m_ok = 1'b0;
  logic [255:0] m_digest = '0;

  function automatic void m_reset();
    m_secret = '0; m_ok = 1'b0; m_digest = '0;
  endfunction
  function automatic void m_set_secret(input logic [159:0] s);
    m_secret = s; m_ok = 1'b1; m_digest = '0;
  endfunction
  function automatic void m_get_hash(input logic [255:0] m);
    m_ok = 1'b0; m_digest = ref_get_hash(m_secret, m);
  endfunction

  int checks = 0, fails = 0;

  task automatic expect_eq(input string what, input logic [255:0] got, input logic [255:0] want);
    checks++;
    if (got !== want) begin
      $display("FAIL: %s = %h, expected %h", what, got, want);
      fails++;
    end
  endtask

  task automatic expect_ret(input string what, input logic ok, input logic [255:0] dig);
    expect_eq({what, ": out_ok"}, 256'(out_ok), 256'(ok));
    expect_eq({what, ": out_digest"}, out_digest, dig);
  endtask

  task automatic expect_model(input string what);
    expect_ret(what, m_ok, m_digest);
    expect_eq({what, ": secret register"}, 256'(dut.st_s_st_secret), 256'(m_secret));
    expect_eq({what, ": scratch register"}, dut.st_s_st_dig, 256'd0);
  endtask

  int lat_seen[2] = '{-1, -1};
  int lat_count[2] = '{0, 0};
  int sw_seen[2] = '{-1, -1};
  int sw_count[2] = '{0, 0};
  string lat_name[2] = '{"set-secret", "get-hash"};

  task automatic record(input int meth, input int lat, input int sw);
    checks++;
    lat_count[meth]++;
    if (lat_seen[meth] < 0) lat_seen[meth] = lat;
    else if (lat_seen[meth] != lat) begin
      $display("FAIL: %s latency %0d, earlier %0d", lat_name[meth], lat, lat_seen[meth]);
      fails++;
    end
    if (sw >= 0) begin
      checks++;
      sw_count[meth]++;
      if (sw_seen[meth] < 0) sw_seen[meth] = sw;
      else if (sw_seen[meth] != sw) begin
        $display("FAIL: %s ports switched at +%0d, earlier +%0d", lat_name[meth], sw, sw_seen[meth]);
        fails++;
      end
    end
  endtask

  task automatic scramble();
    sec_in = {$urandom, $urandom, $urandom, $urandom, $urandom};
    msg_in = {$urandom, $urandom, $urandom, $urandom, $urandom, $urandom, $urandom, $urandom};
  endtask

  task automatic call(input logic [1:0] c, input logic [159:0] s, input logic [255:0] m,
                      input logic post_ok, input logic [255:0] post_dig, input bit hostile,
                      output int lat, output int sw);
    logic pre_ok;
    logic [255:0] pre_dig;
    bit switched;
    @(negedge clk);
    while (ready !== 1'b1) begin scramble(); @(negedge clk); end
    pre_ok = out_ok; pre_dig = out_digest;
    in_cmd_out = {1'b1, c}; sec_in = s; msg_in = m;
    @(posedge clk);
    lat = 1; sw = -1; switched = 0;
    @(negedge clk);
    in_cmd_out = 3'b0; scramble();
    #1;
    while (ready !== 1'b1) begin
      checks++;
      if (!switched && out_ok === pre_ok && out_digest === pre_dig) ;
      else if (out_ok === post_ok && out_digest === post_dig) begin
        if (!switched) begin switched = 1; sw = lat; end
      end else begin
        $display("FAIL: busy cycle +%0d of %s shows (%b, %h), neither the previous nor the new return",
                 lat, lat_name[c[0]], out_ok, out_digest);
        fails++;
      end
      if (hostile) begin
        in_cmd_out = {1'b1, 2'($urandom)};
        scramble();
      end
      @(negedge clk);
      if (hostile && ready === 1'b1) in_cmd_out = 3'b0;
      #1;
      lat++;
    end
    if (pre_ok === post_ok && pre_dig === post_dig) sw = -1;
    else if (!switched) sw = lat;
  endtask

  task automatic set_secret(input logic [159:0] s, input bit hostile = 0);
    int lat, sw;
    m_set_secret(s);
    call(SET, s, {$urandom, $urandom, $urandom, $urandom, $urandom, $urandom, $urandom, $urandom},
         m_ok, m_digest, hostile, lat, sw);
    record(0, lat, sw);
  endtask

  task automatic get_hash(input logic [255:0] m, input bit hostile = 0);
    int lat, sw;
    int s0;
    s0 = strobes;
    m_get_hash(m);
    call(GET, {$urandom, $urandom, $urandom, $urandom, $urandom}, m, m_ok, m_digest, hostile, lat, sw);
    record(1, lat, sw);
    expect_eq("get-hash: exactly one SHA request", 256'(strobes - s0), 256'd1);
  endtask

  task automatic idle(input int n);
    repeat (n) begin @(negedge clk); in_cmd_out = {1'b0, 2'($urandom)}; scramble(); end
    @(negedge clk); in_cmd_out = 3'b0; #1;
  endtask

  task automatic do_reset();
    @(negedge clk); rst_n = 0; @(negedge clk); rst_n = 1; #1;
    m_reset();
  endtask

  localparam logic [255:0] KMSG = 256'h0123456789abcdef;
  localparam logic [159:0] SW = 160'h0102030405060708090a0b0c0d0e0f1011121314;
  localparam logic [255:0] MW = 256'h2122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40;
  localparam logic [255:0] H_KNOX = 256'hc4162593dac170ed49fe1a7aca6837761be71e95d470407696a1666790d967ab;

  initial begin
    expect_eq("ref: sha256(\"abc\")", ref_sha256(str_bytes("abc")),
              256'hba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad);
    expect_eq("ref: sha256(\"\")", ref_sha256(str_bytes("")),
              256'he3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855);
    expect_eq("ref: sha256(56-byte FIPS message)",
              ref_sha256(str_bytes("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")),
              256'h248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1);
    expect_eq("ref: Knox spec.rkt:41-46 vector", ref_get_hash(160'd1337, KMSG), H_KNOX);
    expect_eq("ref: paper order msg||secret", ref_paper_order(160'd1337, KMSG),
              256'h57d35d26c9b263c00c9b0ef045be94e6677e5ad05103d0b86317b0d937ffddb8);

    repeat (3) @(posedge clk); rst_n = 1;

    @(negedge clk); #1;
    expect_model("power-on");

    get_hash(KMSG);  expect_model("fresh get-hash");
    expect_eq("fresh vector (hashlib)", out_digest,
              256'hc98d239b456aacb44548032f0455c46828573d9fc14a7d0983e3582f2648e883);
    get_hash(0);     expect_model("fresh get-hash(0)");
    expect_eq("52 zero bytes (hashlib)", out_digest,
              256'h7955cb2de90dd9efc6df9fdbf5f5d10c114f4135a9a6b52db1003be749e32f7a);
    get_hash(1);     expect_model("fresh get-hash(1)");
    expect_eq("message LSB is the last bit hashed (hashlib)", out_digest,
              256'haeadacea552de15142e357824da1048a52e0441789294224808010e7a7a6a16c);

    set_secret(1337); expect_model("set-secret(1337)"); expect_ret("set-secret returns #t", 1, 0);
    get_hash(KMSG);   expect_model("Knox vector");      expect_ret("Knox vector", 0, H_KNOX);
    checks++;
    if (out_digest === ref_paper_order(160'd1337, KMSG)) begin
      $display("FAIL: digest is in the paper's msg||secret order"); fails++;
    end
    get_hash(MW);     expect_model("second get-hash");
    expect_eq("two gets (hashlib)", out_digest,
              256'h1979af1ec0e1d683797013adb301df16c92b40123073686665fcf7940b0b5706);
    get_hash(MW);     expect_model("repeated get-hash");

    set_secret(160'h1 << 159); get_hash(0); expect_model("secret MSB");
    expect_eq("secret MSB is the first bit hashed (hashlib)", out_digest,
              256'h2871774b49f3973020fa3e9090d7091c60b7589284463d132f338df722f665e3);
    set_secret(SW);   get_hash(MW); expect_model("full width");
    expect_eq("full width (hashlib)", out_digest,
              256'h8912b86c5a100e7e585d035fae01084c71ca937b7bf8b0104fba06e5cc00021c);
    set_secret('1);   get_hash('1); expect_model("all ones");
    expect_eq("all ones (hashlib)", out_digest,
              256'h01028783afa8d55efe67c3967e5405a39640fede4405133b3f1f86a8edcd07dd);

    set_secret(SW); set_secret(1337); get_hash(KMSG); expect_ret("set replaces", 0, H_KNOX);

    get_hash(MW);     idle(5); expect_model("digest after 5 idle cycles");
    set_secret(SW);   expect_model("set-secret after get-hash: (1, 0)");
    get_hash(KMSG);   expect_model("get-hash after set-secret: (0, digest)");
    idle(5);          expect_model("after 5 more idle cycles");

    set_secret(SW);   expect_model("host wipe");
    expect_eq("host wipe: secret register unchanged", 256'(dut.st_s_st_secret), 256'(SW));
    idle(5);          expect_ret("host wipe, after 5 idle cycles", 1, 0);
    get_hash(MW);     expect_model("after host wipe");

    begin
      int s0;
      s0 = strobes;
      for (int c = 2; c < 4; c++) begin
        @(negedge clk); in_cmd_out = {1'b1, 2'(c)}; scramble();
        @(posedge clk); @(negedge clk); in_cmd_out = 3'b0; scramble(); #1;
        expect_eq("unused code: ready", 256'(ready), 256'd1);
        expect_model("unused code: nothing changes");
      end
      expect_eq("unused codes: no SHA request", 256'(strobes - s0), 256'd0);
    end

    set_secret(SW, 1);  expect_model("set-secret, hostile host");
    get_hash(KMSG, 1);  expect_model("get-hash, hostile host while busy");
    get_hash(MW, 1);    expect_model("get-hash, hostile host while busy (2)");

    begin
      int offs [10] = '{1, 2, 30, 66, 67, 68, 70, 71, 72, 73};
      foreach (offs[j]) begin
        set_secret(SW);
        @(negedge clk);
        in_cmd_out = {1'b1, GET}; msg_in = MW;
        @(posedge clk); @(negedge clk);
        in_cmd_out = 3'b0; scramble();
        repeat (offs[j] - 1) @(negedge clk);
        rst_n = 0; @(negedge clk); rst_n = 1; #1;
        m_reset();
        expect_eq($sformatf("reset at +%0d: ready", offs[j]), 256'(ready), 256'd1);
        expect_model($sformatf("reset at +%0d", offs[j]));
        get_hash(KMSG);   expect_model($sformatf("reset at +%0d, then fresh get-hash", offs[j]));
        set_secret(1337); get_hash(KMSG);
        expect_ret($sformatf("reset at +%0d, then Knox vector", offs[j]), 0, H_KNOX);
      end
    end

    begin
      logic [255:0] last_m = KMSG;
      logic [255:0] mm;
      int r;
      bit hostile;
      for (int k = 0; k < 600; k++) begin
        r = $urandom_range(0, 99);
        hostile = ($urandom_range(0, 7) == 0);
        if (r < 20) set_secret({$urandom, $urandom, $urandom, $urandom, $urandom}, hostile);
        else if (r < 25) set_secret(m_secret, hostile);
        else begin
          mm = (r < 32) ? last_m : {$urandom, $urandom, $urandom, $urandom, $urandom, $urandom, $urandom, $urandom};
          get_hash(mm, hostile);
          last_m = mm;
        end
        if ($urandom_range(0, 9) == 0) idle($urandom_range(1, 3));
        expect_model("random");
      end
    end

    do_reset();
    expect_model("after reset");
    get_hash(KMSG);   expect_model("after reset: fresh get-hash");

    expect_eq("adapter: no broken obligation", 256'(ip.errors), 256'd0);
    $display("IP: %0d requests, %0d answers, slowest answer %0d edges after the strobe (budget %0d, ip_lat 72)",
             ip.requests, ip.answers, ip.lat_max, 71);

    for (int o = 0; o < 2; o++) begin
      checks++;
      if (lat_count[o] == 0) begin $display("FAIL: %s never called", lat_name[o]); fails++; end
      else $display("latency %s: %0d cycle(s) (%0d calls); ports switch at busy cycle %0d (%0d calls with a new return)",
                    lat_name[o], lat_seen[o], lat_count[o], sw_seen[o], sw_count[o]);
    end

    if (fails != 0) begin $display("FAIL: %0d of %0d checks", fails, checks); $fatal(1); end
    $display("PASS (%0d checks)", checks);
    $finish;
  end

  initial begin repeat (400000) @(posedge clk); $display("FAIL: timeout"); $fatal(1); end
endmodule
