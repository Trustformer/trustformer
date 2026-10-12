module tb_knox_fifo;
  localparam [2:0] FULL = 3'd0, EMPTY = 3'd1, PUSH = 3'd2, PEEK = 3'd3, POP = 3'd4;
  localparam int CAPACITY = 3;
  localparam [31:0] MAX = 32'hFFFF_FFFF, HALF = 32'h8000_0000, DEAD = 32'hDEAD_BEEF;
  localparam [31:0] A = 32'hABCD_EF01, B = 32'h1234_5678;

  logic clk = 0, rst_n = 0;
  logic [3:0]  in_cmd_out = 4'b0;
  logic [31:0] v_in = 32'b0;
  wire ready, v_ack;
  wire        o_full, o_empty, o_pv;
  wire [31:0] o_pd;

  Knox_Fifo dut(
    .CLK(clk), .RST_N(rst_n),
    .in_cmd_out(in_cmd_out), .in_cmd_arg(ready),
    .in_param_pub_in_v_out(v_in), .in_param_pub_in_v_arg(v_ack),
    .out_param_pub_out_full_arg(o_full), .out_param_pub_out_full_out(1'b1),
    .out_param_pub_out_empty_arg(o_empty), .out_param_pub_out_empty_out(1'b1),
    .out_param_pub_out_peek_valid_arg(o_pv), .out_param_pub_out_peek_valid_out(1'b1),
    .out_param_pub_out_peek_data_arg(o_pd), .out_param_pub_out_peek_data_out(1'b1));

  always #5 clk = ~clk;

  logic [31:0] m_q[$];
  logic        m_f = 0, m_e = 0, m_pv = 0;
  logic [31:0] m_pd = 0;

  function automatic void m_ports(input logic f, input logic e, input logic pv, input [31:0] pd);
    m_f = f; m_e = e; m_pv = pv; m_pd = pd;
  endfunction

  function automatic void m_reset();
    m_q.delete(); m_ports(0, 0, 0, 0);
  endfunction

  function automatic void m_full();  m_ports(m_q.size() == CAPACITY, 0, 0, 0); endfunction
  function automatic void m_empty(); m_ports(0, m_q.size() == 0, 0, 0);        endfunction
  function automatic void m_push(input [31:0] v);
    if (m_q.size() != CAPACITY) m_q.push_back(v);
    m_ports(0, 0, 0, 0);
  endfunction
  function automatic void m_peek();
    if (m_q.size() == 0) m_ports(0, 0, 0, 0); else m_ports(0, 0, 1, m_q[0]);
  endfunction
  function automatic void m_pop();
    if (m_q.size() != 0) void'(m_q.pop_front());
    m_ports(0, 0, 0, 0);
  endfunction

  int checks = 0, fails = 0;

  task automatic expect_eq(input string what, input [31:0] got, input [31:0] want);
    checks++;
    if (got !== want) begin
      $display("FAIL: %s = %h, expected %h", what, got, want);
      fails++;
    end
  endtask

  task automatic expect_ports(input string what, input logic f, input logic e,
                              input logic pv, input [31:0] pd);
    expect_eq({what, ": out_full"}, 32'(o_full), 32'(f));
    expect_eq({what, ": out_empty"}, 32'(o_empty), 32'(e));
    expect_eq({what, ": out_peek_valid"}, 32'(o_pv), 32'(pv));
    expect_eq({what, ": out_peek_data"}, o_pd, pd);
  endtask

  function automatic [31:0] slot_reg(input int k);
    case (k)
      0: return dut.st_s_st_slot_S0;
      1: return dut.st_s_st_slot_S1;
      default: return dut.st_s_st_slot_S2;
    endcase
  endfunction

  task automatic expect_list(input string what, input logic [31:0] q[$]);
    expect_eq({what, ": count register"}, 32'(dut.st_s_st_cnt), q.size());
    for (int k = 0; k < CAPACITY; k++)
      expect_eq($sformatf("%s: slot %0d", what, k), slot_reg(k), (k < q.size()) ? q[k] : 32'b0);
  endtask

  task automatic expect_model(input string what);
    expect_ports(what, m_f, m_e, m_pv, m_pd);
    expect_list(what, m_q);
  endtask

  localparam int NOUT = 10;
  int lat_seen[NOUT] = '{default: -1};
  int lat_count[NOUT] = '{default: 0};
  string lat_name[NOUT] = '{"full/#t", "full/#f", "empty/#t", "empty/#f",
                            "push/appended", "push/dropped", "peek/value", "peek/#f",
                            "pop/removed", "pop/no-op"};

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
    v_in = $urandom;
  endtask

  task automatic call(input [2:0] c, input [31:0] x, output int lat);
    @(negedge clk);
    while (ready !== 1'b1) begin scramble(); @(negedge clk); end
    in_cmd_out = {1'b1, c}; v_in = x;
    @(posedge clk);
    lat = 1;
    @(negedge clk);
    in_cmd_out = 4'b0; scramble();
    #1;
    while (ready !== 1'b1) begin @(negedge clk); #1; lat++; end
  endtask

  task automatic full_x(input [31:0] x);
    int lat, n;
    n = m_q.size();
    call(FULL, x, lat); m_full(); record_latency(n == CAPACITY ? 0 : 1, lat);
  endtask
  task automatic empty_x(input [31:0] x);
    int lat, n;
    n = m_q.size();
    call(EMPTY, x, lat); m_empty(); record_latency(n == 0 ? 2 : 3, lat);
  endtask
  task automatic push(input [31:0] v);
    int lat, n;
    n = m_q.size();
    call(PUSH, v, lat); m_push(v); record_latency(n == CAPACITY ? 5 : 4, lat);
  endtask
  task automatic peek_x(input [31:0] x);
    int lat, n;
    n = m_q.size();
    call(PEEK, x, lat); m_peek(); record_latency(n == 0 ? 7 : 6, lat);
  endtask
  task automatic pop_x(input [31:0] x);
    int lat, n;
    n = m_q.size();
    call(POP, x, lat); m_pop(); record_latency(n == 0 ? 9 : 8, lat);
  endtask
  task automatic full();  full_x($urandom);  endtask
  task automatic empty(); empty_x($urandom); endtask
  task automatic peek();  peek_x($urandom);  endtask
  task automatic pop();   pop_x($urandom);   endtask

  task automatic idle(input int n);
    repeat (n) begin @(negedge clk); in_cmd_out = {1'b0, 3'($urandom)}; scramble(); end
    @(negedge clk); in_cmd_out = 4'b0; #1;
  endtask

  task automatic do_reset();
    @(negedge clk); rst_n = 0; repeat (2) @(posedge clk); @(negedge clk); rst_n = 1; #1;
    m_reset();
  endtask

  initial begin
    repeat (3) @(posedge clk); rst_n = 1;

    @(negedge clk); #1;
    expect_ports("power-on", 0, 0, 0, 0);  expect_list("power-on", '{});

    empty();  expect_ports("s0: empty", 0, 1, 0, 0);
    full();   expect_ports("s0: full", 0, 0, 0, 0);
    peek();   expect_ports("s0: peek -> #f", 0, 0, 0, 0);
    pop();    expect_ports("s0: pop (no-op)", 0, 0, 0, 0);  expect_list("s0: pop", '{});

    push(0);  peek();  expect_ports("push 0; peek", 0, 0, 1, 0);
    empty();  expect_ports("push 0; empty", 0, 0, 0, 0);
    pop();    expect_list("push 0; pop", '{});

    push(1); push(2); push(3);       expect_list("push 1, 2, 3", '{1, 2, 3});
    full();   expect_ports("fill: full", 1, 0, 0, 0);
    push(4);  expect_ports("fill: push 4 (dropped)", 0, 0, 0, 0);  expect_list("fill: push 4", '{1, 2, 3});
    peek();   expect_ports("fill: peek", 0, 0, 1, 1);
    pop();    expect_ports("fill: pop", 0, 0, 0, 0);  expect_list("fill: pop", '{2, 3});
    peek();   expect_ports("fill: peek", 0, 0, 1, 2);
    pop(); pop();                    expect_list("fill: drained", '{});
    peek();   expect_ports("fill: peek on empty", 0, 0, 0, 0);
    pop();    expect_ports("fill: pop on empty", 0, 0, 0, 0);  expect_list("fill: pop on empty", '{});
    empty();  expect_ports("fill: empty", 0, 1, 0, 0);

    push(A); push(B); push(MAX); pop(); push(HALF);
    expect_list("refill", '{B, MAX, HALF});
    peek();   expect_ports("refill: peek", 0, 0, 1, B);
    full();   expect_ports("refill: full", 1, 0, 0, 0);
    pop(); pop(); peek();  expect_ports("refill: peek after 2 pops", 0, 0, 1, HALF);
    pop();

    push(A); push(B); push(MAX); push(HALF); pop(); pop();
    expect_list("dropped push", '{MAX});
    peek();   expect_ports("dropped push: peek", 0, 0, 1, MAX);
    pop();

    push(DEAD); peek();  expect_ports("peek DEAD", 0, 0, 1, DEAD);
    pop();    expect_ports("pop after peek", 0, 0, 0, 0);

    push(DEAD); peek(); idle(5);
    expect_ports("peek, 5 idle cycles later", 0, 0, 1, DEAD);

    empty();  expect_ports("host: empty after peek", 0, 0, 0, 0);  expect_list("host: empty", '{DEAD});
    idle(5);  expect_ports("host: 5 idle cycles later", 0, 0, 0, 0);
    peek(); full();  expect_ports("host: full after peek", 0, 0, 0, 0);
    pop();

    begin
      logic [31:0] vs [5] = '{32'd0, 32'd1, HALF, DEAD, MAX};
      foreach (vs[i]) foreach (vs[j]) foreach (vs[k]) begin
        push(vs[i]); push(vs[j]); push(vs[k]); push(~vs[k]);
        full();  expect_ports("boundary: full", 1, 0, 0, 0);
        peek();  expect_ports("boundary: peek 1", 0, 0, 1, vs[i]);  pop();
        peek();  expect_ports("boundary: peek 2", 0, 0, 1, vs[j]);  pop();
        peek();  expect_ports("boundary: peek 3", 0, 0, 1, vs[k]);  pop();
        empty(); expect_ports("boundary: empty", 0, 1, 0, 0);
      end
    end

    for (int n = 0; n <= CAPACITY; n++) begin
      if (n > 0) push(32'h100 + n);
      full_x(MAX);   expect_model("full, in_v = MAX");
      empty_x(0);    expect_model("empty, in_v = 0");
      peek_x(DEAD);  expect_model("peek, in_v = DEAD");
    end
    pop_x(MAX); pop_x(0); pop_x(DEAD); pop_x(HALF);  expect_model("pops with in_v set");

    push(A); push(B); peek();
    for (int c = 5; c < 8; c++) begin
      @(negedge clk); in_cmd_out = {1'b1, 3'(c)}; v_in = MAX;
      @(posedge clk); @(negedge clk); in_cmd_out = 4'b0; scramble(); #1;
      expect_eq("unused code: ready", 32'(ready), 1);
      expect_ports("unused code: ports unchanged", 0, 0, 1, A);
      expect_list("unused code: state unchanged", '{A, B});
    end

    do_reset();
    expect_ports("after reset", 0, 0, 0, 0);  expect_list("after reset", '{});
    peek();   expect_ports("after reset: peek", 0, 0, 0, 0);

    for (int i = 0; i < 6000; i++) begin
      int r, sel, hi;
      logic [31:0] v;
      r = $urandom_range(0, 99);
      sel = $urandom_range(0, 3);
      hi = $urandom_range(0, 1);
      case (sel)
        0: v = 0;
        1: v = (hi == 0) ? MAX : HALF;
        default: v = $urandom;
      endcase
      if (r < 2) do_reset();
      else if (r < 14) full();
      else if (r < 26) empty();
      else if (r < 58) push(v);
      else if (r < 74) peek();
      else pop();
      if ($urandom_range(0, 9) == 0) idle($urandom_range(1, 3));
      expect_model("random");
    end

    for (int o = 0; o < NOUT; o++) begin
      checks++;
      if (lat_count[o] == 0) begin $display("FAIL: outcome %s never seen", lat_name[o]); fails++; end
      else $display("latency %s: %0d cycle(s) (%0d calls)", lat_name[o], lat_seen[o], lat_count[o]);
    end
    for (int m = 0; m < NOUT; m += 2) begin
      checks++;
      if (lat_seen[m] != lat_seen[m + 1]) begin
        $display("FAIL: %s and %s latencies differ", lat_name[m], lat_name[m + 1]); fails++;
      end
    end

    if (fails != 0) begin $display("FAIL: %0d of %0d checks", fails, checks); $fatal(1); end
    $display("PASS (%0d checks)", checks);
    $finish;
  end

  initial begin repeat (400000) @(posedge clk); $display("FAIL: timeout"); $fatal(1); end
endmodule
