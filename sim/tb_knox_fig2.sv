module tb_knox_fig2;
  localparam [1:0] STORE = 2'd0, RETRIEVE = 2'd1;
  localparam [7:0] ST_NONE = 8'd0, ST_OK = 8'd1, ST_BAD_PIN = 8'd2, ST_NO_GUESSES = 8'd3;

  logic clk = 0, rst_n = 0;
  logic [2:0]   in_cmd_out = 3'b0;
  logic [31:0]  pin_in = 32'b0;
  logic [127:0] sec_in = 128'b0;
  wire ready, pin_ack, sec_ack;
  wire [7:0]   status;
  wire [127:0] data;

  Knox_Fig2Backup dut(
    .CLK(clk), .RST_N(rst_n),
    .in_cmd_out(in_cmd_out), .in_cmd_arg(ready),
    .in_param_pub_in_pin_out(pin_in), .in_param_pub_in_pin_arg(pin_ack),
    .in_param_pub_in_secret_out(sec_in), .in_param_pub_in_secret_arg(sec_ack),
    .out_param_pub_out_status_arg(status), .out_param_pub_out_status_out(1'b1),
    .out_param_pub_out_data_arg(data), .out_param_pub_out_data_out(1'b1));

  always #5 clk = ~clk;

  logic [31:0]  m_pin = 0;
  logic [127:0] m_secret = 0;
  int           m_bad = 0;
  logic [7:0]   m_status = 0;
  logic [127:0] m_data = 0;

  function automatic void m_reset();
    m_pin = 0; m_secret = 0; m_bad = 0; m_status = 0; m_data = 0;
  endfunction

  function automatic void m_store(input [127:0] new_secret, input [31:0] new_pin);
    m_secret = new_secret; m_pin = new_pin; m_bad = 0;
    m_status = ST_NONE; m_data = 0;
  endfunction

  function automatic void m_retrieve(input [31:0] guess);
    if (m_bad >= 10) begin m_status = ST_NO_GUESSES; m_data = 0; end
    else if (guess == m_pin) begin m_bad = 0; m_status = ST_OK; m_data = m_secret; end
    else begin m_bad = m_bad + 1; m_status = ST_BAD_PIN; m_data = 0; end
  endfunction

  int checks = 0, fails = 0;

  task automatic expect_eq(input string what, input [127:0] got, input [127:0] want);
    checks++;
    if (got !== want) begin
      $display("FAIL: %s = %h, expected %h", what, got, want);
      fails++;
    end
  endtask

  task automatic expect_ret(input string what, input [7:0] st, input [127:0] d);
    expect_eq({what, ": status"}, 128'(status), 128'(st));
    expect_eq({what, ": data"}, data, d);
  endtask

  task automatic expect_bad(input string what, input int b);
    expect_eq({what, ": bad_guesses"}, 128'(dut.st_s_st_bad_guesses), 128'(b));
  endtask

  task automatic expect_state(input string what);
    expect_eq({what, ": pin register"}, 128'(dut.st_s_st_pin), 128'(m_pin));
    expect_eq({what, ": secret register"}, dut.st_s_st_secret, m_secret);
    expect_bad(what, m_bad);
  endtask

  task automatic expect_model(input string what);
    expect_ret(what, m_status, m_data);
    expect_state(what);
  endtask

  int lat_seen[4] = '{-1, -1, -1, -1};
  int lat_count[4] = '{0, 0, 0, 0};
  string lat_name[4] = '{"store", "retrieve/secret", "retrieve/Incorrect PIN",
                         "retrieve/No more guesses"};

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
    pin_in = $urandom;
    sec_in = {$urandom, $urandom, $urandom, $urandom};
  endtask

  task automatic call(input [1:0] c, input [31:0] p, input [127:0] s, output int lat);
    @(negedge clk);
    while (ready !== 1'b1) begin scramble(); @(negedge clk); end
    in_cmd_out = {1'b1, c}; pin_in = p; sec_in = s;
    @(posedge clk);
    lat = 1;
    @(negedge clk);
    in_cmd_out = 3'b0; scramble();
    #1;
    while (ready !== 1'b1) begin @(negedge clk); #1; lat++; end
  endtask

  task automatic store(input [127:0] new_secret, input [31:0] new_pin);
    int lat;
    call(STORE, new_pin, new_secret, lat);
    m_store(new_secret, new_pin);
    record_latency(0, lat);
  endtask

  task automatic retrieve(input [31:0] guess);
    int lat;
    call(RETRIEVE, guess, {$urandom, $urandom, $urandom, $urandom}, lat);
    m_retrieve(guess);
    record_latency(int'(m_status), lat);
  endtask

  task automatic idle(input int n);
    repeat (n) begin @(negedge clk); in_cmd_out = {1'b0, 2'($urandom)}; scramble(); end
    @(negedge clk); in_cmd_out = 3'b0; #1;
  endtask

  localparam [127:0] SECRET_MAX = '1;
  localparam [127:0] SECRET_MIX = 128'hC0FFEE00_11223344_55667788_99AABBCC;

  initial begin
    repeat (3) @(posedge clk); rst_n = 1;

    @(negedge clk);
    expect_ret("power-on ports", ST_NONE, 0);
    retrieve(0);              expect_ret("fresh retrieve(0)", ST_OK, 0);       expect_bad("fresh retrieve(0)", 0);
    retrieve(5);              expect_ret("fresh retrieve(5)", ST_BAD_PIN, 0);  expect_bad("fresh retrieve(5)", 1);

    store(1337, 1234);        expect_ret("store", ST_NONE, 0);                  expect_bad("store", 0);
    retrieve(1234);           expect_ret("correct guess", ST_OK, 1337);
    retrieve(1111);           expect_ret("bad guess", ST_BAD_PIN, 0);           expect_bad("bad guess", 1);
    retrieve(1234);           expect_ret("one bad guess is okay", ST_OK, 1337); expect_bad("one bad guess is okay", 0);

    for (int i = 0; i < 9; i++) retrieve(1111);
    expect_ret("9th wrong", ST_BAD_PIN, 0);  expect_bad("9th wrong", 9);
    retrieve(1234);           expect_ret("correct at 9", ST_OK, 1337);          expect_bad("correct at 9", 0);
    for (int i = 0; i < 9; i++) retrieve(1111);
    retrieve(1111);           expect_ret("10th wrong is still 'Incorrect PIN'", ST_BAD_PIN, 0);
    expect_bad("10th wrong", 10);
    retrieve(1234);           expect_ret("locked: correct pin", ST_NO_GUESSES, 0); expect_bad("locked", 10);
    for (int i = 0; i < 300; i++) retrieve($urandom);
    expect_ret("300 more while locked", ST_NO_GUESSES, 0); expect_bad("saturates", 10);
    expect_state("locked: pin and secret unchanged");

    store(7, 55);             expect_ret("store while locked", ST_NONE, 0);     expect_bad("store while locked", 0);
    retrieve(1234);           expect_ret("old pin dead", ST_BAD_PIN, 0);        expect_bad("old pin dead", 1);
    retrieve(55);             expect_ret("new pin", ST_OK, 7);                  expect_bad("new pin", 0);

    retrieve(55);             expect_ret("release", ST_OK, 7);
    retrieve(1111);           expect_ret("fail after release", ST_BAD_PIN, 0);
    retrieve(55);             expect_ret("release again", ST_OK, 7);
    store(1337, 1234);        expect_ret("store after release", ST_NONE, 0);

    retrieve(1234);  idle(5); expect_ret("release, after 5 idle cycles", ST_OK, 1337);

    store(1337, 1234);        expect_ret("host wipe: ports", ST_NONE, 0);
    expect_eq("host wipe: pin register", 128'(dut.st_s_st_pin), 1234);
    expect_eq("host wipe: secret register", dut.st_s_st_secret, 1337);
    expect_bad("host wipe", 0);
    idle(5);                  expect_ret("host wipe, after 5 idle cycles", ST_NONE, 0);
    retrieve(1234);           expect_ret("after host wipe", ST_OK, 1337);

    store(42, 32'h8000_04D2);
    retrieve(1234);           expect_ret("2^31+1234 vs 1234", ST_BAD_PIN, 0);
    retrieve(32'h8000_04D2);  expect_ret("2^31+1234 exact", ST_OK, 42);
    store(1, 32'hFFFF_FFFF);
    retrieve(32'h7FFF_FFFF);  expect_ret("top bit differs", ST_BAD_PIN, 0);
    retrieve(32'hFFFF_FFFE);  expect_ret("bottom bit differs", ST_BAD_PIN, 0);
    retrieve(0);              expect_ret("all bits differ", ST_BAD_PIN, 0);
    retrieve(32'hFFFF_FFFF);  expect_ret("all-ones pin", ST_OK, 1);

    store(SECRET_MAX, 9);  retrieve(9);  expect_ret("secret 2^128-1", ST_OK, SECRET_MAX);
    store(SECRET_MIX, 9);  retrieve(9);  expect_ret("secret mix", ST_OK, SECRET_MIX);

    for (int i = 0; i < 10; i++) retrieve(1);
    store(0, 0);              expect_ret("store(0,0)", ST_NONE, 0); expect_state("store(0,0): power-on state");
    retrieve(0);              expect_ret("store(0,0) then retrieve(0)", ST_OK, 0);

    store(SECRET_MIX, 77);
    retrieve(76);
    for (int c = 2; c < 4; c++) begin
      @(negedge clk); in_cmd_out = {1'b1, 2'(c)}; pin_in = 77; sec_in = '0;
      @(posedge clk); @(negedge clk); in_cmd_out = 3'b0; scramble(); #1;
      expect_eq("unused code: ready", 128'(ready), 1);
      expect_ret("unused code: ports unchanged", ST_BAD_PIN, 0);
      expect_bad("unused code: counter unchanged", 1);
    end
    retrieve(77);             expect_ret("after unused codes", ST_OK, SECRET_MIX);

    begin
      logic [31:0] pool [4] = '{32'd0, 32'd1234, 32'hFFFF_FFFF, 32'h8000_04D2};
      int r, idx;
      logic [31:0] p;
      for (int k = 0; k < 4000; k++) begin
        r = $urandom_range(0, 99);
        idx = $urandom_range(0, 3);
        p = pool[idx];
        if ($urandom_range(0, 3) == 0) p = $urandom;
        if (r < 8) store({$urandom, $urandom, $urandom, $urandom}, p);
        else if (r < 40) retrieve(m_pin);
        else retrieve(p);
        if ($urandom_range(0, 9) == 0) idle($urandom_range(1, 3));
        expect_model("random");
      end
    end

    @(negedge clk); rst_n = 0; repeat (2) @(posedge clk); @(negedge clk); rst_n = 1; #1;
    m_reset();
    expect_ret("after reset: ports", ST_NONE, 0); expect_state("after reset");
    retrieve(0);              expect_ret("after reset: retrieve(0)", ST_OK, 0);

    for (int o = 0; o < 4; o++) begin
      checks++;
      if (lat_count[o] == 0) begin $display("FAIL: outcome %s never seen", lat_name[o]); fails++; end
      else $display("latency %s: %0d cycle(s) (%0d calls)", lat_name[o], lat_seen[o], lat_count[o]);
    end
    checks++;
    if (lat_seen[1] != lat_seen[2] || lat_seen[1] != lat_seen[3]) begin
      $display("FAIL: retrieve latency depends on the outcome"); fails++;
    end

    if (fails != 0) begin $display("FAIL: %0d of %0d checks", fails, checks); $fatal(1); end
    $display("PASS (%0d checks)", checks);
    $finish;
  end

  initial begin repeat (200000) @(posedge clk); $display("FAIL: timeout"); $fatal(1); end
endmodule
