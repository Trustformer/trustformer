module tb_knox_multi_lockbox;
  localparam [1:0] STORE = 2'd0, GET = 2'd1;

  logic clk = 0, rst_n = 0;
  logic [2:0]   in_cmd_out = 3'b0;
  logic [15:0]  tag_in = 16'b0;
  logic [127:0] sec_in = 128'b0, pw_in = 128'b0;
  wire ready, tag_ack, sec_ack, pw_ack;
  wire          ok;
  wire [127:0]  ret;

  Knox_MultiLockbox dut(
    .CLK(clk), .RST_N(rst_n),
    .in_cmd_out(in_cmd_out), .in_cmd_arg(ready),
    .in_param_pub_in_tag_out(tag_in), .in_param_pub_in_tag_arg(tag_ack),
    .in_param_pub_in_secret_out(sec_in), .in_param_pub_in_secret_arg(sec_ack),
    .in_param_pub_in_password_out(pw_in), .in_param_pub_in_password_arg(pw_ack),
    .out_param_pub_out_ok_arg(ok), .out_param_pub_out_ok_out(1'b1),
    .out_param_pub_out_ret_arg(ret), .out_param_pub_out_ret_out(1'b1));

  always #5 clk = ~clk;

  logic         mv [2];
  logic [15:0]  mt [2];
  logic [127:0] ms [2], mp [2];
  logic         m_ok = 0;
  logic [127:0] m_ret = 0;
  int           m_outcome = 0;

  function automatic void m_reset();
    for (int r = 0; r < 2; r++) begin mv[r] = 0; mt[r] = 0; ms[r] = 0; mp[r] = 0; end
    m_ok = 0; m_ret = 0;
  endfunction

  function automatic void m_store(input [15:0] t, input [127:0] s, input [127:0] p);
    int r = -1;
    for (int k = 1; k >= 0; k--) if (mv[k] && mt[k] == t) r = k;
    if (r >= 0) m_outcome = r;
    else begin
      for (int k = 1; k >= 0; k--) if (!mv[k]) r = k;
      m_outcome = (r >= 0) ? 2 + r : 4;
    end
    if (r >= 0) begin mv[r] = 1; mt[r] = t; ms[r] = s; mp[r] = p; end
    m_ok = (r >= 0); m_ret = 0;
  endfunction

  function automatic void m_get(input [15:0] t, input [127:0] g);
    int r = -1;
    for (int k = 1; k >= 0; k--) if (mv[k] && mt[k] == t) r = k;
    m_ok = 0;
    if (r >= 0) begin
      m_ret = (mp[r] == g) ? ms[r] : 128'b0;
      m_outcome = 5 + 2 * r + ((mp[r] == g) ? 0 : 1);
      mv[r] = 0; mt[r] = 0; ms[r] = 0; mp[r] = 0;
    end else begin
      m_ret = 0;
      m_outcome = 9;
    end
  endfunction

  function automatic string m_leak();
    return $sformatf("(%0d, %h, %0d, %h)", mv[0], mv[0] ? mt[0] : 16'h0, mv[1], mv[1] ? mt[1] : 16'h0);
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

  task automatic expect_state(input string what);
    expect_eq({what, ": valid0"},    128'(dut.st_s_st_valid_r0), 128'(mv[0]));
    expect_eq({what, ": tag0"},      128'(dut.st_s_st_tag_r0), 128'(mt[0]));
    expect_eq({what, ": secret0"},   dut.st_s_st_secret_r0, ms[0]);
    expect_eq({what, ": password0"}, dut.st_s_st_password_r0, mp[0]);
    expect_eq({what, ": valid1"},    128'(dut.st_s_st_valid_r1), 128'(mv[1]));
    expect_eq({what, ": tag1"},      128'(dut.st_s_st_tag_r1), 128'(mt[1]));
    expect_eq({what, ": secret1"},   dut.st_s_st_secret_r1, ms[1]);
    expect_eq({what, ": password1"}, dut.st_s_st_password_r1, mp[1]);
  endtask

  task automatic expect_model(input string what);
    expect_ports(what, m_ok, m_ret);
    expect_state(what);
  endtask

  task automatic expect_row(input string what, input int r, input logic v, input [15:0] t,
                            input [127:0] s, input [127:0] p);
    expect_eq({what, ": model valid"},    128'(mv[r]), 128'(v));
    expect_eq({what, ": model tag"},      128'(mt[r]), 128'(t));
    expect_eq({what, ": model secret"},   ms[r], s);
    expect_eq({what, ": model password"}, mp[r], p);
  endtask

  int lat_seen[10] = '{default: -1};
  int lat_count[10] = '{default: 0};
  string lat_name[10] = '{"match0", "match1", "free0", "free1", "full",
                          "row0-right", "row0-wrong", "row1-right", "row1-wrong", "absent"};

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
    tag_in = 16'($urandom); sec_in = r128(); pw_in = r128();
  endtask

  task automatic call(input [1:0] c, input [15:0] t, input [127:0] s, input [127:0] p,
                      output int lat);
    @(negedge clk);
    while (ready !== 1'b1) begin scramble(); @(negedge clk); end
    in_cmd_out = {1'b1, c}; tag_in = t; sec_in = s; pw_in = p;
    @(posedge clk);
    lat = 1;
    @(negedge clk);
    in_cmd_out = 3'b0; scramble();
    #1;
    while (ready !== 1'b1) begin @(negedge clk); #1; lat++; end
  endtask

  int last_lat;

  task automatic store(input [15:0] t, input [127:0] secret, input [127:0] password);
    call(STORE, t, secret, password, last_lat);
    m_store(t, secret, password);
    record_latency(m_outcome, last_lat);
  endtask

  task automatic get(input [15:0] t, input [127:0] guess);
    call(GET, t, r128(), guess, last_lat);
    m_get(t, guess);
    record_latency(m_outcome, last_lat);
  endtask

  task automatic idle(input int n);
    repeat (n) begin @(negedge clk); in_cmd_out = {1'b0, 2'($urandom)}; scramble(); end
    @(negedge clk); in_cmd_out = 3'b0; #1;
  endtask

  task automatic do_reset();
    @(negedge clk); rst_n = 0; repeat (2) @(posedge clk); @(negedge clk); rst_n = 1; #1;
    m_reset();
  endtask

  task automatic deposit(input logic v0, input [15:0] t0, input [127:0] s0, input [127:0] p0,
                         input logic v1, input [15:0] t1, input [127:0] s1, input [127:0] p1);
    @(negedge clk);
    dut.st_s_st_valid_r0 = v0; dut.st_s_st_tag_r0 = t0;
    dut.st_s_st_secret_r0 = s0; dut.st_s_st_password_r0 = p0;
    dut.st_s_st_valid_r1 = v1; dut.st_s_st_tag_r1 = t1;
    dut.st_s_st_secret_r1 = s1; dut.st_s_st_password_r1 = p1;
    mv[0] = v0; mt[0] = t0; ms[0] = s0; mp[0] = p0;
    mv[1] = v1; mt[1] = t1; ms[1] = s1; mp[1] = p1;
    #1;
  endtask

  localparam [127:0] ALL = '1;
  localparam [127:0] HI  = 128'h1 << 127;
  localparam [127:0] S1  = 128'h0123456789abcdef_fedcba9876543210;
  localparam [127:0] P1  = 128'ha5a5a5a5c3c3c3c3_0f0f0f0f99999999;
  localparam [127:0] S2  = 128'hdeadbeefcafebabe_0000000000000001;
  localparam [127:0] P2  = 128'h00000000ffffffff;
  localparam [127:0] S3  = 128'h77777777777777777777777777777777;
  localparam [127:0] P3  = 128'h8000000000000000000000000000beef;
  localparam [15:0]  TALL = 16'hffff;

  typedef struct { logic [1:0] op; logic [15:0] t; logic [127:0] s, p; } kcall_t;
  kcall_t fu [5][4];
  int     fu_len [5] = '{2, 4, 2, 3, 3};

  task automatic run_followups(input string layout, output logic [128:0] outs [5][4],
                               output int lats [5][4]);
    for (int i = 0; i < 5; i++) begin
      do_reset();
      if (layout == "LA") begin store(1, S1, P1); store(2, S2, P2); get(1, 0); end
      else store(2, S2, P2);
      if (i == 0) $display("leak layout %s: Knox leak = %s", layout, m_leak());
      for (int k = 0; k < fu_len[i]; k++) begin
        if (fu[i][k].op == STORE) store(fu[i][k].t, fu[i][k].s, fu[i][k].p);
        else get(fu[i][k].t, fu[i][k].p);
        expect_model({"leak layout ", layout});
        outs[i][k] = {ok, ret};
        lats[i][k] = last_lat;
      end
    end
  endtask

  initial begin
    m_reset();
    repeat (3) @(posedge clk); rst_n = 1;

    @(negedge clk); #1;
    expect_ports("power-on", 0, 0);           expect_state("power-on");

    get(0, 0);               expect_ports("fresh get(0,0)", 0, 0);           expect_model("fresh get(0,0)");
    expect_row("fresh get(0,0)", 0, 0, 0, 0, 0);
    store(0, 0, 0);          expect_ports("store(0,0,0)", 1, 0);             expect_model("store(0,0,0)");
    expect_row("store(0,0,0)", 0, 1, 0, 0, 0);
    get(0, 0);               expect_ports("get(0,0)", 0, 0);                 expect_model("get(0,0)");
    expect_row("get(0,0) wipes", 0, 0, 0, 0, 0);

    do_reset();
    store(34, 1337, 1234);   expect_ports("basic: store", 1, 0);             expect_model("basic: store");
    get(34, 0);              expect_ports("basic: wrong guess", 0, 0);       expect_model("basic: wrong guess");
    get(34, 1234);           expect_ports("basic: right guess after wipe", 0, 0);
    store(34, 1337, 1234);
    get(34, 1234);           expect_ports("basic: right guess", 0, 1337);    expect_model("basic: right guess");
    get(34, 1234);           expect_ports("basic: one-shot", 0, 0);

    do_reset();
    store(1, S1, P1);        expect_ports("full: store 1", 1, 0);
    store(2, S2, P2);        expect_ports("full: store 2", 1, 0);
    expect_row("full: row0", 0, 1, 1, S1, P1); expect_row("full: row1", 1, 1, 2, S2, P2);
    store(3, S3, P3);        expect_ports("full: store 3 refused", 0, 0);    expect_model("full: store 3 refused");
    expect_row("full: row0 kept", 0, 1, 1, S1, P1); expect_row("full: row1 kept", 1, 1, 2, S2, P2);
    get(3, P3);              expect_ports("full: get 3", 0, 0);
    get(2, P2);              expect_ports("full: get 2", 0, S2);             expect_model("full: get 2");
    get(1, P1);              expect_ports("full: get 1", 0, S1);             expect_model("full: get 1");

    do_reset();
    store(1, S1, P1); store(2, S2, P2);
    get(1, 0);               expect_ports("priority: wrong guess frees row0", 0, 0);
    store(2, S3, P3);        expect_ports("priority: re-key tag 2", 1, 0);   expect_model("priority: re-key tag 2");
    expect_row("priority: row0 still free", 0, 0, 0, 0, 0); expect_row("priority: row1 re-keyed", 1, 1, 2, S3, P3);
    get(2, P2);              expect_ports("priority: old password", 0, 0);   expect_model("priority: old password");
    store(1, S1, P1);        expect_ports("priority: tag 1 again", 1, 0);
    get(1, P1);              expect_ports("priority: tag 1 right", 0, S1);
    do_reset();
    store(1, S1, P1); store(2, S2, P2); get(1, 0);
    store(2, S3, P3);
    store(9, S1, P1);        expect_ports("priority: tag 9 into free row0", 1, 0);
    expect_row("priority: row0 holds tag 9", 0, 1, 9, S1, P1);
    get(2, P3);              expect_ports("priority: tag 2 new password", 0, S3);
    get(9, P1);              expect_ports("priority: tag 9", 0, S1);         expect_model("priority: tag 9");

    do_reset();
    store(TALL, S1, P1);
    get(TALL, P1 ^ HI);      expect_ports("wrong in bit 127", 0, 0);         expect_model("wrong in bit 127");
    get(TALL, P1);           expect_ports("right after wrong", 0, 0);
    store(TALL, S2, P2);
    get(TALL, P2 ^ 128'h1);  expect_ports("wrong in bit 0", 0, 0);           expect_model("wrong in bit 0");
    get(TALL, P2);           expect_ports("right after wrong", 0, 0);

    do_reset();
    store(0, ALL, ALL);      expect_ports("all ones: store", 1, 0);
    get(5, ALL);             expect_ports("absent tag", 0, 0);               expect_model("absent tag");
    expect_row("absent tag wipes nothing", 0, 1, 0, ALL, ALL);
    get(0, ALL);             expect_ports("all ones: get", 0, ALL);
    get(0, ALL);             expect_ports("all ones: again", 0, 0);

    do_reset();
    store(7, S1, P1); store(7, S2, P2);
    expect_row("re-store", 0, 1, 7, S2, P2); expect_row("re-store: row1 untouched", 1, 0, 0, 0, 0);
    get(7, P1);              expect_ports("re-store: old password", 0, 0);
    store(7, S1, P1); store(7, S2, P2);
    get(7, P2);              expect_ports("re-store: new password", 0, S2);

    do_reset();
    store(16'h8001, S1, P1);
    get(16'h0001, P1);       expect_ports("tag differs in bit 15", 0, 0);
    get(16'h8000, P1);       expect_ports("tag differs in bit 0", 0, 0);
    get(16'h8001, P1);       expect_ports("tag 8001", 0, S1);

    do_reset();
    store(7, S1, P1);
    get(7, P1);              expect_ports("release", 0, S1);
    store(8, S2, P2);        expect_ports("store after release", 1, 0);
    get(8, 0);               expect_ports("wrong guess after store", 0, 0);
    store(7, 0, 0);          expect_ports("store(7,0,0)", 1, 0);
    get(7, 0);               expect_ports("get(7,0) on secret 0", 0, 0);
    store(1, S1, P1); store(2, S2, P2);
    get(1, P1);              expect_ports("release row0", 0, S1);
    store(3, S3, P3);        expect_ports("store after release", 1, 0);
    store(4, S3, P3);        expect_ports("refused store after store", 0, 0);

    do_reset();
    store(5, S1, P1);
    call(GET, 5, ALL, P1, last_lat); m_get(5, P1); record_latency(m_outcome, last_lat);
    expect_ports("get with in_secret = all ones", 0, S1); expect_model("get with in_secret = all ones");

    deposit(1, 1, S2, P2, 1, 1, S3, P3);
    get(1, P3);              expect_ports("duplicate tag: get opens row0", 0, 0); expect_model("duplicate tag: get");
    get(1, P3);              expect_ports("duplicate tag: then row1", 0, S3);     expect_model("duplicate tag: then row1");
    deposit(1, 1, S2, P2, 1, 1, S3, P3);
    store(1, S1, P1);        expect_ports("duplicate tag: store re-keys row0", 1, 0);
    expect_row("duplicate tag: row0", 0, 1, 1, S1, P1); expect_row("duplicate tag: row1", 1, 1, 1, S3, P3);
    expect_model("duplicate tag: store");
    deposit(0, 34, S3, 1234, 0, 1, S2, P2);
    get(34, 1234);           expect_ports("invalid row with data: get", 0, 0);   expect_model("invalid row with data: get");
    store(5, S1, P1);        expect_ports("invalid row with data: store", 1, 0); expect_model("invalid row with data: store");
    expect_row("invalid row with data: row0", 0, 1, 5, S1, P1);
    expect_row("invalid row with data: row1 kept", 1, 0, 1, S2, P2);

    do_reset();
    store(7, S1, P1); store(8, S2, P2);
    get(7, P1);              expect_ports("host: release", 0, S1);
    idle(5);                 expect_ports("host: 5 idle cycles later", 0, S1);
    get(7, 0);               expect_ports("host: get(7,0)", 0, 0);           expect_model("host: get(7,0)");
    expect_row("host: row1 kept", 1, 1, 8, S2, P2);
    idle(5);                 expect_ports("host: 5 idle cycles later", 0, 0);

    fu[0][0] = '{STORE, 2, S3, P3}; fu[0][1] = '{GET, 2, 0, P3};
    fu[1][0] = '{STORE, 5, S1, P1}; fu[1][1] = '{STORE, 6, S3, P3}; fu[1][2] = '{GET, 5, 0, P1}; fu[1][3] = '{GET, 6, 0, 0};
    fu[2][0] = '{GET, 2, 0, P2};    fu[2][1] = '{GET, 2, 0, P2};
    fu[3][0] = '{GET, 2, 0, 0};     fu[3][1] = '{STORE, 2, S1, P1}; fu[3][2] = '{GET, 2, 0, P1};
    fu[4][0] = '{GET, 9, 0, P2};    fu[4][1] = '{STORE, 9, S1, P1}; fu[4][2] = '{STORE, 8, S3, P3};
    begin
      logic [128:0] oa [5][4], ob [5][4];
      int la [5][4], lb [5][4];
      bit same = 1;
      run_followups("LA", oa, la);
      run_followups("LB", ob, lb);
      for (int i = 0; i < 5; i++)
        for (int k = 0; k < fu_len[i]; k++) begin
          checks++;
          if (oa[i][k] !== ob[i][k] || la[i][k] != lb[i][k]) begin
            same = 0; fails++;
            $display("FAIL: leak layouts differ at session %0d call %0d", i, k);
          end
        end
      expect_eq("leak layouts: store(2) re-keys, ret", oa[0][0][127:0], 0);
      expect_eq("leak layouts: store(2) re-keys, ok", 128'(oa[0][0][128]), 1);
      expect_eq("leak layouts: get(2, P3)", oa[0][1][127:0], S3);
      expect_eq("leak layouts: store(5) ok", 128'(oa[1][0][128]), 1);
      expect_eq("leak layouts: store(6) refused", 128'(oa[1][1][128]), 0);
      expect_eq("leak layouts: get(5, P1)", oa[1][2][127:0], S1);
      expect_eq("leak layouts: get(2, P2)", oa[2][0][127:0], S2);
      expect_eq("leak layouts: store(8) refused", 128'(oa[4][2][128]), 0);
      if (same) $display("leak layouts LA/LB: same ports and latency on all 5 follow-up sessions");
    end

    do_reset();
    store(1, S1, P1); store(2, S2, P2);
    for (int c = 2; c < 4; c++) begin
      @(negedge clk); in_cmd_out = {1'b1, 2'(c)}; tag_in = 1; sec_in = S3; pw_in = P1;
      @(posedge clk); @(negedge clk); in_cmd_out = 3'b0; scramble(); #1;
      expect_eq("unused code: ready", 128'(ready), 1);
      expect_ports("unused code: ports unchanged", 1, 0);
      expect_state("unused code: state unchanged");
    end
    get(1, P1);              expect_ports("after unused codes", 0, S1);

    store(9, S3, P3);
    do_reset();
    expect_ports("after reset", 0, 0);   expect_state("after reset");
    get(9, P3);              expect_ports("after reset: get(9,P3)", 0, 0);

    begin
      logic [15:0] pool [6] = '{16'd0, 16'd1, 16'd2, 16'hffff, 16'h1234, 16'h8001};
      int r, sel, k, row, i0, i1, i2;
      logic [15:0] t;
      logic [127:0] g;
      for (int i = 0; i < 6000; i++) begin
        r = $urandom_range(0, 99);
        sel = $urandom_range(0, 3);
        k = $urandom_range(0, 127);
        i0 = $urandom_range(0, 1); i1 = $urandom_range(0, 5); i2 = $urandom_range(0, 5);
        t = ($urandom_range(0, 2) == 0) ? mt[i0] : pool[i1];
        if (r < 1) do_reset();
        else if (r < 3)
          deposit(1'($urandom_range(0, 1)), pool[i1], r128(), r128(),
                  1'($urandom_range(0, 1)), pool[i2], r128(), r128());
        else if (r < 45) begin
          case (sel)
            0: store(t, r128(), r128());
            1: store(t, r128(), 0);
            2: store(t, 0, r128());
            default: store(t, {96'b0, $urandom}, {126'b0, 2'($urandom)});
          endcase
        end else begin
          row = (mv[0] && mt[0] == t) ? 0 : 1;
          case (sel)
            0, 1: g = mp[row];
            2: g = mp[row] ^ (128'h1 << k);
            default: g = ($urandom_range(0, 1) == 0) ? 128'b0 : r128();
          endcase
          get(t, g);
        end
        if ($urandom_range(0, 9) == 0) idle($urandom_range(1, 3));
        expect_model("random");
      end
    end

    begin
      int base [2] = '{-1, -1};
      for (int o = 0; o < 10; o++) begin
        int m = (o < 5) ? 0 : 1;
        checks++;
        if (lat_count[o] == 0) begin $display("FAIL: outcome %s never seen", lat_name[o]); fails++; end
        else begin
          $display("latency %s %s: %0d cycle(s) (%0d calls)", m == 0 ? "store" : "get", lat_name[o],
                   lat_seen[o], lat_count[o]);
          if (base[m] < 0) base[m] = lat_seen[o];
          else if (base[m] != lat_seen[o]) begin
            $display("FAIL: %s latency depends on the outcome", m == 0 ? "store" : "get"); fails++;
          end
        end
      end
      $display("latency store: %0d cycle(s), get: %0d cycle(s), the same for every outcome", base[0], base[1]);
    end

    if (fails != 0) begin $display("FAIL: %0d of %0d checks", fails, checks); $fatal(1); end
    $display("PASS (%0d checks)", checks);
    $finish;
  end

  initial begin repeat (400000) @(posedge clk); $display("FAIL: timeout"); $fatal(1); end
endmodule
