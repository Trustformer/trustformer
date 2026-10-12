module tb_knox_adder;
  localparam [0:0] ADD = 1'd0;
  localparam [31:0] MAX = 32'hFFFF_FFFF, HALF = 32'h8000_0000;

  logic clk = 0, rst_n = 0;
  logic [1:0]  in_cmd_out = 2'b0;
  logic [31:0] x_in = 32'b0, y_in = 32'b0;
  wire ready, x_ack, y_ack;
  wire [31:0] sum;

  Knox_Adder dut(
    .CLK(clk), .RST_N(rst_n),
    .in_cmd_out(in_cmd_out), .in_cmd_arg(ready),
    .in_param_pub_in_x_out(x_in), .in_param_pub_in_x_arg(x_ack),
    .in_param_pub_in_y_out(y_in), .in_param_pub_in_y_arg(y_ack),
    .out_param_pub_out_sum_arg(sum), .out_param_pub_out_sum_out(1'b1));

  always #5 clk = ~clk;

  logic [31:0] m_port = 0;

  function automatic [31:0] spec_add(input [31:0] x, input [31:0] y);
    logic [32:0] s33;
    s33 = {1'b0, x} + {1'b0, y};
    return s33[31:0];
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
    expect_eq({what, ": out_sum"}, sum, v);
  endtask

  int lat_seen = -1, lat_count = 0;

  task automatic record_latency(input int lat);
    checks++;
    lat_count++;
    if (lat_seen < 0) lat_seen = lat;
    else if (lat_seen != lat) begin
      $display("FAIL: add latency %0d, earlier %0d", lat, lat_seen);
      fails++;
    end
  endtask

  task automatic scramble();
    x_in = $urandom; y_in = $urandom;
  endtask

  task automatic add(input [31:0] x, input [31:0] y);
    int lat;
    @(negedge clk);
    while (ready !== 1'b1) begin scramble(); @(negedge clk); end
    in_cmd_out = {1'b1, ADD}; x_in = x; y_in = y;
    @(posedge clk);
    lat = 1;
    @(negedge clk);
    in_cmd_out = 2'b0; scramble();
    #1;
    while (ready !== 1'b1) begin @(negedge clk); #1; lat++; end
    m_port = spec_add(x, y);
    record_latency(lat);
  endtask

  int idle_cycles = 0;

  task automatic idle(input int n);
    int pick;
    repeat (n) begin
      @(negedge clk);
      scramble();
      pick = $urandom_range(0, 2);
      case (pick)
        0: in_cmd_out = {1'b0, ADD};
        1: in_cmd_out = 2'b11;
        default: in_cmd_out = {1'b0, 1'($urandom)};
      endcase
      @(posedge clk); #1;
      idle_cycles++;
      expect_port("idle", m_port);
      expect_eq("idle: ready", 32'(ready), 1);
    end
    @(negedge clk); in_cmd_out = 2'b0; #1;
  endtask

  initial begin
    repeat (3) @(posedge clk); rst_n = 1;

    @(negedge clk); #1;
    expect_port("power-on", 0); expect_eq("power-on: ready", 32'(ready), 1);

    begin
      logic [31:0] vx [11] = '{32'd0, 32'd7, MAX, 32'd1, MAX, HALF, HALF - 1,
                               32'd3000000000, 32'd3000000000, 32'hDEADBEEF, 32'd123456789};
      logic [31:0] vy [11] = '{32'd0, 32'd9, 32'd1, MAX, MAX, HALF, HALF,
                               32'd1294967295, 32'd1294967296, 32'hCAFEBABE, 32'd987654321};
      logic [31:0] ve [11] = '{32'd0, 32'd16, 32'd0, 32'd0, MAX - 1, 32'd0, MAX,
                               MAX, 32'd0, 32'd2846652845, 32'd1111111110};
      foreach (vx[k]) begin
        add(vx[k], vy[k]);         expect_port("vector", ve[k]); expect_port("vector: model", m_port);
        add(vy[k], vx[k]);         expect_port("vector reversed", ve[k]);
      end
    end

    add(HALF, 32'd3); add(MAX, MAX); add(32'd5, 32'd6);
    expect_port("chain", 32'd11);

    add(32'd40, 32'd2); idle(5);   expect_port("after 5 idle cycles", 32'd42);

    add(32'd0, 32'd0);             expect_port("host: add(0, 0)", 0);
    idle(5);                       expect_port("host: add(0, 0), after 5 idle cycles", 0);

    add(32'd1000, 32'd337);
    for (int i = 0; i < 4; i++) begin
      @(negedge clk); in_cmd_out = 2'b11; scramble();
      @(posedge clk); @(negedge clk); in_cmd_out = 2'b0; scramble(); #1;
      expect_eq("unused code: ready", 32'(ready), 1);
      expect_port("unused code: port unchanged", 32'd1337);
    end

    for (int k = 0; k < 5000; k++) begin
      logic [31:0] x, y;
      int pick;
      x = $urandom; y = $urandom;
      pick = $urandom_range(0, 3);
      case (pick)
        0: y = MAX - x + 32'($urandom_range(0, 2)) - 32'd1;
        1: x = {1'b1, 31'($urandom)};
        default: ;
      endcase
      idle($urandom_range(0, 6));
      add(x, y);
      expect_port("random", m_port);
      expect_eq("random: independent", m_port, 32'((64'(x) + 64'(y)) % 64'h1_0000_0000));
    end

    add(32'd123, 32'd456);
    @(negedge clk); rst_n = 0; repeat (2) @(posedge clk); @(negedge clk); rst_n = 1; #1;
    m_port = 0;
    expect_port("after reset", 0);
    add(MAX, 32'd2);               expect_port("after reset: add", 32'd1);

    checks++;
    if (lat_count == 0) begin $display("FAIL: no add seen"); fails++; end
    $display("calls: %0d adds, %0d idle cycles with garbage inputs", lat_count, idle_cycles);
    $display("latency add: %0d cycle(s) (%0d calls)", lat_seen, lat_count);

    if (fails != 0) begin $display("FAIL: %0d of %0d checks", fails, checks); $fatal(1); end
    $display("PASS (%0d checks)", checks);
    $finish;
  end

  initial begin repeat (400000) @(posedge clk); $display("FAIL: timeout"); $fatal(1); end
endmodule
