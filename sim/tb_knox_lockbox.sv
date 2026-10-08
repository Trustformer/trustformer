module tb_knox_lockbox;
  localparam [1:0] STORE = 2'd0, GET = 2'd1;

  logic clk = 0, rst_n = 0;
  logic [2:0]   in_cmd_out = 3'b0;
  logic [127:0] sec_in = 128'b0, pw_in = 128'b0;
  wire ready, sec_ack, pw_ack;
  wire          ok;
  wire [127:0]  ret;

  Knox_Lockbox dut(
    .CLK(clk), .RST_N(rst_n),
    .in_cmd_out(in_cmd_out), .in_cmd_arg(ready),
    .in_param_pub_in_secret_out(sec_in), .in_param_pub_in_secret_arg(sec_ack),
    .in_param_pub_in_password_out(pw_in), .in_param_pub_in_password_arg(pw_ack),
    .out_param_pub_out_ok_arg(ok), .out_param_pub_out_ok_out(1'b1),
    .out_param_pub_out_ret_arg(ret), .out_param_pub_out_ret_out(1'b1));

  always #5 clk = ~clk;

  logic [127:0] m_secret = 0, m_password = 0;
  logic         m_ok = 0;
  logic [127:0] m_ret = 0;
  logic         m_match = 0;

  function automatic void m_reset();
    m_secret = 0; m_password = 0; m_ok = 0; m_ret = 0;
  endfunction

  function automatic void m_store(input [127:0] secret, input [127:0] password);
    m_secret = secret; m_password = password;
    m_ok = 1; m_ret = 0;
  endfunction

  function automatic void m_get(input [127:0] guess);
    m_match = (guess == m_password);
    m_ok = 0; m_ret = m_match ? m_secret : 128'b0;
    m_secret = 0; m_password = 0;
  endfunction

  int checks = 0, fails = 0;

  task automatic expect_eq(input string what, input [127:0] got, input [127:0] want);
    checks++;
    if (got !== want) begin
      $display("FAIL: %s = %h, expected %h", what, got, want);
      fails++;
    end
  endtask

  task automatic expect_ports(input string what, input logic o, input [127:0] r);
    expect_eq({what, ": out_ok"}, 128'(ok), 128'(o));
    expect_eq({what, ": out_ret"}, ret, r);
  endtask

  task automatic expect_state(input string what, input [127:0] s, input [127:0] p);
    expect_eq({what, ": secret register"}, dut.st_s_st_secret, s);
    expect_eq({what, ": password register"}, dut.st_s_st_password, p);
  endtask

  task automatic expect_model(input string what);
    expect_ports(what, m_ok, m_ret);
    expect_state(what, m_secret, m_password);
  endtask

  int lat_seen[3] = '{-1, -1, -1};
  int lat_count[3] = '{0, 0, 0};
  string lat_name[3] = '{"store", "get/match", "get/miss"};

  task automatic record_latency(input int outcome, input int lat);
    checks++;
    lat_count[outcome]++;
    if (lat_seen[outcome] < 0) lat_seen[outcome] = lat;
    else if (lat_seen[outcome] != lat) begin
      $display("FAIL: %s latency %0d, earlier %0d", lat_name[outcome], lat, lat_seen[outcome]);
      fails++;
    end
  endtask

  function automatic [127:0] r128();
    r128 = {$urandom, $urandom, $urandom, $urandom};
  endfunction

  task automatic scramble();
    sec_in = r128(); pw_in = r128();
  endtask

  task automatic call(input [1:0] c, input [127:0] s, input [127:0] p, output int lat);
    @(negedge clk);
    while (ready !== 1'b1) begin scramble(); @(negedge clk); end
    in_cmd_out = {1'b1, c}; sec_in = s; pw_in = p;
    @(posedge clk);
    lat = 1;
    @(negedge clk);
    in_cmd_out = 3'b0; scramble();
    #1;
    while (ready !== 1'b1) begin @(negedge clk); #1; lat++; end
  endtask

  task automatic store(input [127:0] secret, input [127:0] password);
    int lat;
    call(STORE, secret, password, lat);
    m_store(secret, password);
    record_latency(0, lat);
  endtask

  task automatic get(input [127:0] guess);
    int lat;
    call(GET, r128(), guess, lat);
    m_get(guess);
    record_latency(m_match ? 1 : 2, lat);
  endtask

  task automatic idle(input int n);
    repeat (n) begin @(negedge clk); in_cmd_out = {1'b0, 2'($urandom)}; scramble(); end
    @(negedge clk); in_cmd_out = 3'b0; #1;
  endtask

  task automatic do_reset();
    @(negedge clk); rst_n = 0; repeat (2) @(posedge clk); @(negedge clk); rst_n = 1; #1;
    m_reset();
  endtask

  localparam [127:0] ALL = '1;
  localparam [127:0] HI  = 128'h1 << 127;
  localparam [127:0] S1  = 128'h0123456789abcdef_fedcba9876543210;
  localparam [127:0] P1  = 128'ha5a5a5a5c3c3c3c3_0f0f0f0f99999999;
  localparam [127:0] S2  = 128'hdeadbeefcafebabe_0000000000000001;
  localparam [127:0] P2  = 128'h00000000ffffffff;

  initial begin
    repeat (3) @(posedge clk); rst_n = 1;

    @(negedge clk); #1;
    expect_ports("power-on", 0, 0);      expect_state("power-on", 0, 0);

    get(0);                  expect_ports("fresh get(0)", 0, 0);       expect_state("fresh get(0)", 0, 0);

    store(S1, P1);           expect_ports("store", 1, 0);              expect_state("store", S1, P1);
    get(P1);                 expect_ports("right guess", 0, S1);       expect_state("right guess", 0, 0);
    idle(5);                 expect_ports("right guess, 5 idle cycles later", 0, S1);
    get(P1);                 expect_ports("right guess again", 0, 0);  expect_state("right guess again", 0, 0);

    store(S1, P1);
    get(P1 ^ HI);            expect_ports("wrong in bit 127", 0, 0);   expect_state("wrong in bit 127", 0, 0);
    get(P1);                 expect_ports("right after wrong", 0, 0);
    store(S1, P1);
    get(P1 ^ 128'h1);        expect_ports("wrong in bit 0", 0, 0);     expect_state("wrong in bit 0", 0, 0);
    get(P1);                 expect_ports("right after wrong", 0, 0);
    store(S1, P1);
    get(~P1);                expect_ports("all bits wrong", 0, 0);
    store(S1, P1);
    get(0);                  expect_ports("guess 0", 0, 0);            expect_state("guess 0", 0, 0);

    store(S1, P1); store(S2, P2);
    expect_ports("overwrite", 1, 0);     expect_state("overwrite", S2, P2);
    get(P1);                 expect_ports("old password", 0, 0);
    store(S1, P1); store(S2, P2);
    get(P2);                 expect_ports("new password", 0, S2);
    get(P2);                 expect_ports("new password again", 0, 0);

    store(ALL, ALL);
    get(ALL);                expect_ports("all ones", 0, ALL);
    get(ALL);                expect_ports("all ones again", 0, 0);

    store(0, P1);
    get(P1);                 expect_ports("secret 0, right guess", 0, 0);
    store(S1, 0);
    get(0);                  expect_ports("password 0", 0, S1);
    get(0);                  expect_ports("password 0 again", 0, 0);

    store(S1, P1); get(P1);  expect_ports("release", 0, S1);
    store(S2, P2);           expect_ports("store after release", 1, 0);
    get(0);                  expect_ports("miss after store", 0, 0);
    store(0, 0);             expect_ports("store(0,0)", 1, 0);          expect_state("store(0,0)", 0, 0);
    get(0);                  expect_ports("get(0) on (0,0)", 0, 0);

    store(S1, P1);
    get(P1);                 expect_ports("host: release", 0, S1);
    get(0);                  expect_ports("host: get(0)", 0, 0);        expect_state("host: get(0)", 0, 0);
    idle(5);                 expect_ports("host: 5 idle cycles later", 0, 0);

    store(S1, P1);
    begin
      int lat;
      call(GET, ALL, P1, lat); m_get(P1); record_latency(1, lat);
      expect_ports("get with in_secret = all ones", 0, S1); expect_state("get with in_secret = all ones", 0, 0);
    end

    store(S2, P2);
    for (int c = 2; c < 4; c++) begin
      @(negedge clk); in_cmd_out = {1'b1, 2'(c)}; sec_in = S1; pw_in = P2;
      @(posedge clk); @(negedge clk); in_cmd_out = 3'b0; scramble(); #1;
      expect_eq("unused code: ready", 128'(ready), 1);
      expect_ports("unused code: ports unchanged", 1, 0);
      expect_state("unused code: state unchanged", S2, P2);
    end
    get(P2);                 expect_ports("after unused codes", 0, S2);

    store(S1, P1);
    do_reset();
    expect_ports("after reset", 0, 0);   expect_state("after reset", 0, 0);
    get(P1);                 expect_ports("after reset: get(P1)", 0, 0);

    begin
      int r, sel, k;
      logic [127:0] g;
      for (int i = 0; i < 4000; i++) begin
        r = $urandom_range(0, 99);
        sel = $urandom_range(0, 3);
        k = $urandom_range(0, 127);
        if (r < 2) do_reset();
        else if (r < 40) begin
          case (sel)
            0: store(r128(), r128());
            1: store(r128(), 0);
            2: store(0, r128());
            default: store({96'b0, $urandom}, {126'b0, 2'($urandom)});
          endcase
        end else begin
          case (sel)
            0, 1: g = m_password;
            2: g = m_password ^ (128'h1 << k);
            default: g = ($urandom_range(0, 1) == 0) ? 128'b0 : r128();
          endcase
          get(g);
        end
        if ($urandom_range(0, 9) == 0) idle($urandom_range(1, 3));
        expect_model("random");
      end
    end

    for (int o = 0; o < 3; o++) begin
      checks++;
      if (lat_count[o] == 0) begin $display("FAIL: outcome %s never seen", lat_name[o]); fails++; end
      else $display("latency %s: %0d cycle(s) (%0d calls)", lat_name[o], lat_seen[o], lat_count[o]);
    end
    checks++;
    if (lat_seen[1] != lat_seen[2]) begin
      $display("FAIL: get latency depends on the outcome"); fails++;
    end

    if (fails != 0) begin $display("FAIL: %0d of %0d checks", fails, checks); $fatal(1); end
    $display("PASS (%0d checks)", checks);
    $finish;
  end

  initial begin repeat (200000) @(posedge clk); $display("FAIL: timeout"); $fatal(1); end
endmodule
