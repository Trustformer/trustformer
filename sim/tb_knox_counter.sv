module tb_knox_counter;
  localparam [1:0] ADD = 2'd0, GET = 2'd1;
  localparam [31:0] MAX = 32'hFFFF_FFFF, HALF = 32'h8000_0000;

  logic clk = 0, rst_n = 0;
  logic [2:0]  in_cmd_out = 3'b0;
  logic [31:0] x_in = 32'b0;
  wire ready, x_ack;
  wire [31:0] val;

  Knox_Counter dut(
    .CLK(clk), .RST_N(rst_n),
    .in_cmd_out(in_cmd_out), .in_cmd_arg(ready),
    .in_param_pub_in_x_out(x_in), .in_param_pub_in_x_arg(x_ack),
    .out_param_pub_out_val_arg(val), .out_param_pub_out_val_out(1'b1));

  always #5 clk = ~clk;

  logic [31:0] m_s = 0;
  logic [31:0] m_port = 0;

  function automatic [31:0] spec_add(input [31:0] x, input [31:0] s);
    logic [32:0] sum33;
    sum33 = {1'b0, x} + {1'b0, s};
    return (sum33 <= 33'h0_FFFF_FFFF) ? x + s : 32'hFFFF_FFFF;
  endfunction

  function automatic [31:0] impl_add(input [31:0] x, input [31:0] s);
    return (s + x < s) ? 32'hFFFF_FFFF : s + x;
  endfunction

  int checks = 0, fails = 0;

  task automatic expect_eq(input string what, input [31:0] got, input [31:0] want);
    checks++;
    if (got !== want) begin
      $display("FAIL: %s = %h, expected %h", what, got, want);
      fails++;
    end
  endtask

  task automatic expect_port(input string what, input [31:0] v);
    expect_eq({what, ": out_val"}, val, v);
  endtask

  task automatic expect_count(input string what, input [31:0] v);
    expect_eq({what, ": counter register"}, dut.st_s_st_s, v);
  endtask

  task automatic expect_model(input string what);
    expect_port(what, m_port);
    expect_count(what, m_s);
  endtask

  int lat_seen[4] = '{-1, -1, -1, -1};
  int lat_count[4] = '{0, 0, 0, 0};
  string lat_name[4] = '{"add/below 0xffffffff", "add/exactly 0xffffffff",
                         "add/saturating", "get"};

  task automatic record_latency(input int outcome, input int lat);
    checks++;
    lat_count[outcome]++;
    if (lat_seen[outcome] < 0) lat_seen[outcome] = lat;
    else if (lat_seen[outcome] != lat) begin
      $display("FAIL: %s latency %0d, earlier %0d", lat_name[outcome], lat, lat_seen[outcome]);
      fails++;
    end
  endtask

  task automatic call(input [1:0] c, input [31:0] x, output int lat);
    @(negedge clk);
    while (ready !== 1'b1) begin x_in = $urandom; @(negedge clk); end
    in_cmd_out = {1'b1, c}; x_in = x;
    @(posedge clk);
    lat = 1;
    @(negedge clk);
    in_cmd_out = 3'b0; x_in = $urandom;
    #1;
    while (ready !== 1'b1) begin @(negedge clk); #1; lat++; end
  endtask

  task automatic add(input [31:0] x);
    int lat, outcome;
    logic [32:0] sum33;
    sum33 = {1'b0, x} + {1'b0, m_s};
    outcome = (sum33 < 33'h0_FFFF_FFFF) ? 0 : (sum33 == 33'h0_FFFF_FFFF) ? 1 : 2;
    call(ADD, x, lat);
    checks++;
    if (spec_add(x, m_s) !== impl_add(x, m_s)) begin
      $display("FAIL: spec.rkt and counter.v disagree on x=%h s=%h", x, m_s); fails++;
    end
    m_s = spec_add(x, m_s); m_port = 0;
    record_latency(outcome, lat);
  endtask

  task automatic get();
    int lat;
    call(GET, $urandom, lat);
    m_port = m_s;
    record_latency(3, lat);
  endtask

  task automatic idle(input int n);
    repeat (n) begin @(negedge clk); in_cmd_out = {1'b0, 2'($urandom)}; x_in = $urandom; end
    @(negedge clk); in_cmd_out = 3'b0; #1;
  endtask

  task automatic do_reset();
    @(negedge clk); rst_n = 0; repeat (2) @(posedge clk); @(negedge clk); rst_n = 1; #1;
    m_s = 0; m_port = 0;
  endtask

  initial begin
    repeat (3) @(posedge clk); rst_n = 1;

    @(negedge clk); #1;
    expect_port("power-on", 0); expect_count("power-on", 0);
    get();                         expect_port("fresh get", 0);

    add(32'd3000000000);           expect_port("add 3e9", 0);        expect_count("add 3e9", 32'd3000000000);
    get();                         expect_port("get", 32'd3000000000);
    add(32'd1294967295);           expect_port("add to exactly MAX", 0); expect_count("exactly MAX", MAX);
    get();                         expect_port("get MAX", MAX);
    add(32'd2000000000);           expect_port("add past MAX", 0);   expect_count("saturates", MAX);
    get();                         expect_port("get sticky", MAX);
    add(32'd0);                    expect_port("add 0", 0);          expect_count("add 0 at MAX", MAX);
    get();                         expect_port("get after add 0", MAX);

    add(32'd1);  expect_count("MAX + 1", MAX);
    add(HALF);   expect_count("MAX + HALF", MAX);
    add(MAX);    expect_count("MAX + MAX", MAX);

    do_reset();
    add(HALF); add(HALF);          expect_count("HALF + HALF", MAX);
    do_reset();
    add(MAX - 1); add(32'd1);      expect_count("MAX-1 + 1", MAX);
    do_reset();
    add(MAX - 1); add(32'd2);      expect_count("MAX-1 + 2", MAX);
    do_reset();
    add(32'd1); add(MAX);          expect_count("1 + MAX", MAX);

    begin
      logic [31:0] cs [19] = '{32'd0, 32'd0, 32'd7, MAX - 1, MAX - 1, MAX, MAX, MAX,
                               HALF, HALF - 1, HALF, 32'd1, 32'd0,
                               MAX - 1000, MAX - 1000, MAX - 1000,
                               32'd123456789, 32'd3000000000, 32'd3000000000};
      logic [31:0] cx [19] = '{32'd0, 32'd5, 32'd9, 32'd1, 32'd2, 32'd0, 32'd1, MAX,
                               HALF, HALF, HALF - 1, MAX, MAX,
                               32'd999, 32'd1000, 32'd1001,
                               32'd987654321, 32'd1294967295, 32'd1294967296};
      logic [31:0] ce [19] = '{32'd0, 32'd5, 32'd16, MAX, MAX, MAX, MAX, MAX,
                               MAX, MAX, MAX, MAX, MAX,
                               MAX - 1, MAX, MAX,
                               32'd1111111110, MAX, MAX};
      foreach (cs[k]) begin
        do_reset();
        add(cs[k]);                expect_count("boundary: reach s", cs[k]);
        add(cx[k]);                expect_port("boundary: add", 0); expect_count("boundary: add", ce[k]);
        get();                     expect_port("boundary: get", ce[k]); expect_count("boundary: get", ce[k]);
      end
    end

    do_reset();
    add(32'd42);
    for (int i = 0; i < 20; i++) begin get(); expect_port("get, random in_x", 42); expect_count("get", 42); end

    get();                         expect_port("get 42", 42);
    add(32'd1);                    expect_port("add after get", 0);
    get();                         expect_port("get 43", 43);
    get();                         expect_port("get after get", 43);

    get(); idle(5);                expect_port("get, after 5 idle cycles", 43); expect_count("idle", 43);
    add(32'd7); idle(5);           expect_port("add, after 5 idle cycles", 0);  expect_count("idle", 50);

    get();                         expect_port("host: get", 50);
    add(32'd0);                    expect_port("host wipe: port", 0); expect_count("host wipe: counter", 50);
    idle(5);                       expect_port("host wipe, after 5 idle cycles", 0);
    get();                         expect_port("host wipe: get again", 50);

    get();
    for (int c = 2; c < 4; c++) begin
      @(negedge clk); in_cmd_out = {1'b1, 2'(c)}; x_in = 32'd1000;
      @(posedge clk); @(negedge clk); in_cmd_out = 3'b0; x_in = $urandom; #1;
      expect_eq("unused code: ready", 32'(ready), 1);
      expect_port("unused code: port unchanged", 50);
      expect_count("unused code: counter unchanged", 50);
    end

    begin
      int r, k;
      logic [31:0] x, u;
      for (int i = 0; i < 4000; i++) begin
        r = $urandom_range(0, 99);
        k = $urandom_range(0, 4);
        u = $urandom;
        if (r < 5) do_reset();
        else if (r < 35) get();
        else begin
          case (k)
            0: x = u;
            1: x = $urandom_range(0, 1000);
            2: x = MAX - m_s + 32'(u[2:0]) - 32'd3;
            3: x = MAX - 32'(u[1:0]);
            default: x = {u[1:0], 30'b0};
          endcase
          add(x);
        end
        if ($urandom_range(0, 9) == 0) idle($urandom_range(1, 3));
        expect_model("random");
      end
    end

    add(32'd5);
    do_reset();
    expect_model("after reset");
    get();                         expect_port("after reset: get", 0);

    $display("calls: %0d adds below 0xffffffff, %0d exactly 0xffffffff, %0d saturating; %0d gets",
             lat_count[0], lat_count[1], lat_count[2], lat_count[3]);
    for (int o = 0; o < 4; o++) begin
      checks++;
      if (lat_count[o] == 0) begin $display("FAIL: outcome %s never seen", lat_name[o]); fails++; end
      else $display("latency %s: %0d cycle(s) (%0d calls)", lat_name[o], lat_seen[o], lat_count[o]);
    end
    checks++;
    if (lat_seen[0] != lat_seen[1] || lat_seen[0] != lat_seen[2]) begin
      $display("FAIL: add latency depends on the outcome"); fails++;
    end

    if (fails != 0) begin $display("FAIL: %0d of %0d checks", fails, checks); $fatal(1); end
    $display("PASS (%0d checks)", checks);
    $finish;
  end

  initial begin repeat (200000) @(posedge clk); $display("FAIL: timeout"); $fatal(1); end
endmodule
