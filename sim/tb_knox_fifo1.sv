module tb_knox_fifo1;
  localparam [2:0] FULL = 3'd0, EMPTY = 3'd1, PUSH = 3'd2, POP = 3'd3;
  localparam [31:0] MAX = 32'hFFFF_FFFF, HALF = 32'h8000_0000, DEAD = 32'hDEAD_BEEF;

  logic clk = 0, rst_n = 0;
  logic [3:0]  in_cmd_out = 4'b0;
  logic [31:0] v_in = 32'b0;
  wire ready, v_ack;
  wire        o_full, o_empty, o_pv;
  wire [31:0] o_pd;

  Knox_Fifo1 dut(
    .CLK(clk), .RST_N(rst_n),
    .in_cmd_out(in_cmd_out), .in_cmd_arg(ready),
    .in_param_pub_in_v_out(v_in), .in_param_pub_in_v_arg(v_ack),
    .out_param_pub_out_full_arg(o_full), .out_param_pub_out_full_out(1'b1),
    .out_param_pub_out_empty_arg(o_empty), .out_param_pub_out_empty_out(1'b1),
    .out_param_pub_out_pop_valid_arg(o_pv), .out_param_pub_out_pop_valid_out(1'b1),
    .out_param_pub_out_pop_data_arg(o_pd), .out_param_pub_out_pop_data_out(1'b1));

  always #5 clk = ~clk;

  logic        m_has = 0;
  logic [31:0] m_val = 0;
  logic        m_f = 0, m_e = 0, m_pv = 0;
  logic [31:0] m_pd = 0;

  function automatic void m_ports(input logic f, input logic e, input logic pv, input [31:0] pd);
    m_f = f; m_e = e; m_pv = pv; m_pd = pd;
  endfunction

  function automatic void m_reset();
    m_has = 0; m_val = 0; m_ports(0, 0, 0, 0);
  endfunction

  function automatic void m_full();  m_ports(m_has, 0, 0, 0);  endfunction
  function automatic void m_empty(); m_ports(0, !m_has, 0, 0); endfunction
  function automatic void m_push(input [31:0] v);
    if (!m_has) begin m_has = 1; m_val = v; end
    m_ports(0, 0, 0, 0);
  endfunction
  function automatic void m_pop();
    if (m_has) m_ports(0, 0, 1, m_val); else m_ports(0, 0, 0, 0);
    m_has = 0;
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
    expect_eq({what, ": out_pop_valid"}, 32'(o_pv), 32'(pv));
    expect_eq({what, ": out_pop_data"}, o_pd, pd);
  endtask

  task automatic expect_state(input string what, input logic has, input [31:0] val);
    expect_eq({what, ": valid register"}, 32'(dut.st_s_st_valid), 32'(has));
    if (has) expect_eq({what, ": data register"}, dut.st_s_st_data, val);
  endtask

  task automatic expect_model(input string what);
    expect_ports(what, m_f, m_e, m_pv, m_pd);
    expect_state(what, m_has, m_val);
  endtask

  localparam int NOUT = 8;
  int lat_seen[NOUT] = '{default: -1};
  int lat_count[NOUT] = '{default: 0};
  string lat_name[NOUT] = '{"full/#t", "full/#f", "empty/#t", "empty/#f",
                            "push/stored", "push/dropped", "pop/value", "pop/#f"};

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

  task automatic full();
    int lat; logic was;
    was = m_has;
    call(FULL, $urandom, lat); m_full(); record_latency(was ? 0 : 1, lat);
  endtask
  task automatic empty();
    int lat; logic was;
    was = m_has;
    call(EMPTY, $urandom, lat); m_empty(); record_latency(was ? 3 : 2, lat);
  endtask
  task automatic push(input [31:0] v);
    int lat; logic was;
    was = m_has;
    call(PUSH, v, lat); m_push(v); record_latency(was ? 5 : 4, lat);
  endtask
  task automatic pop();
    int lat; logic was;
    was = m_has;
    call(POP, $urandom, lat); m_pop(); record_latency(was ? 6 : 7, lat);
  endtask

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
    expect_ports("power-on", 0, 0, 0, 0);  expect_state("power-on", 0, 0);

    empty();          expect_ports("demo: empty", 0, 1, 0, 0);
    push(0);          expect_ports("demo: push 0", 0, 0, 0, 0);   expect_state("demo: push 0", 1, 0);
    full();           expect_ports("demo: full (0 counts as stored)", 1, 0, 0, 0);
    push(7);          expect_ports("demo: push 7 (dropped)", 0, 0, 0, 0); expect_state("demo: push 7", 1, 0);
    pop();            expect_ports("demo: pop -> 0", 0, 0, 1, 0); expect_state("demo: pop", 0, 0);
    pop();            expect_ports("demo: pop on empty -> #f", 0, 0, 0, 0);
    full();           expect_ports("demo: full", 0, 0, 0, 0);
    push(MAX);        expect_ports("demo: push MAX", 0, 0, 0, 0);
    pop();            expect_ports("demo: pop -> MAX", 0, 0, 1, MAX);
    empty();          expect_ports("demo: empty", 0, 1, 0, 0);

    push(5); push(9); expect_state("push 5; push 9", 1, 5);
    pop();            expect_ports("push 5; push 9; pop", 0, 0, 1, 5);

    push(42); pop();  expect_ports("push 42; pop", 0, 0, 1, 42);
    pop();            expect_ports("push 42; pop; pop", 0, 0, 0, 0);
    expect_eq("stale data register", dut.st_s_st_data, 42);
    full();           expect_ports("full on stale register", 0, 0, 0, 0);
    empty();          expect_ports("empty on stale register", 0, 1, 0, 0);

    push(DEAD); pop(); idle(5);
    expect_ports("pop, 5 idle cycles later", 0, 0, 1, DEAD);

    empty();          expect_ports("host: empty after pop", 0, 1, 0, 0);
    idle(5);          expect_ports("host: 5 idle cycles later", 0, 1, 0, 0);
    push(32'hC0FFEE42); pop(); full();
    expect_ports("host: full after pop", 0, 0, 0, 0);

    begin
      logic [31:0] vs [5] = '{32'd0, 32'd1, HALF, DEAD, MAX};
      foreach (vs[i]) foreach (vs[j]) begin
        push(vs[i]); push(vs[j]);
        full();  expect_ports("boundary: full", 1, 0, 0, 0);
        pop();   expect_ports("boundary: pop", 0, 0, 1, vs[i]);
        empty(); expect_ports("boundary: empty", 0, 1, 0, 0);
      end
    end

    for (int k = 0; k < 2; k++) begin
      int lat;
      if (k == 1) push(HALF);
      call(FULL, MAX, lat);  m_full();  record_latency(m_has ? 0 : 1, lat); expect_model("full, in_v = MAX");
      call(EMPTY, 0, lat);   m_empty(); record_latency(m_has ? 3 : 2, lat); expect_model("empty, in_v = 0");
      call(POP, DEAD, lat);  record_latency(m_has ? 6 : 7, lat); m_pop(); expect_model("pop, in_v = DEAD");
    end

    push(32'h1234_5678); pop(); push(32'h0BAD_F00D);
    for (int c = 4; c < 8; c++) begin
      @(negedge clk); in_cmd_out = {1'b1, 3'(c)}; v_in = MAX;
      @(posedge clk); @(negedge clk); in_cmd_out = 4'b0; scramble(); #1;
      expect_eq("unused code: ready", 32'(ready), 1);
      expect_ports("unused code: ports unchanged", 0, 0, 0, 0);
      expect_state("unused code: state unchanged", 1, 32'h0BAD_F00D);
    end
    pop();            expect_ports("after unused codes", 0, 0, 1, 32'h0BAD_F00D);

    push(32'h5555_AAAA);
    do_reset();
    expect_ports("after reset", 0, 0, 0, 0);   expect_state("after reset", 0, 0);
    pop();            expect_ports("after reset: pop", 0, 0, 0, 0);

    for (int i = 0; i < 4000; i++) begin
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
      else if (r < 20) full();
      else if (r < 38) empty();
      else if (r < 70) push(v);
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

  initial begin repeat (200000) @(posedge clk); $display("FAIL: timeout"); $fatal(1); end
endmodule
