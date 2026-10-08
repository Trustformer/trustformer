module tb_knox_pin_backup;
  localparam [2:0] STATUS = 3'd0, DELETE = 3'd1, STORE = 3'd2, RETRIEVE = 3'd3;
  localparam int NSLOT = 4, LIMIT = 10;

  logic clk = 0, rst_n = 0;
  logic [3:0]   in_cmd = 4'b0;
  logic [7:0]   slot = 8'd0;
  logic [31:0]  pin  = 32'd0;
  logic [127:0] data = 128'd0;
  wire ready, slot_ack, pin_ack, data_ack;
  wire         ok;
  wire [127:0] odata;

  Knox_PinBackup dut(
    .CLK(clk), .RST_N(rst_n),
    .in_cmd_out(in_cmd), .in_cmd_arg(ready),
    .in_param_pub_in_slot_out(slot), .in_param_pub_in_slot_arg(slot_ack),
    .in_param_pub_in_pin_out(pin),   .in_param_pub_in_pin_arg(pin_ack),
    .in_param_pub_in_data_out(data), .in_param_pub_in_data_arg(data_ack),
    .out_param_pub_out_ok_arg(ok),      .out_param_pub_out_ok_out(1'b1),
    .out_param_pub_out_data_arg(odata), .out_param_pub_out_data_out(1'b1));

  always #5 clk = ~clk;

  int checks = 0, fails = 0;

  task automatic expect_eq(input string what, input [127:0] got, input [127:0] want);
    checks++;
    if (got !== want) begin
      $display("FAIL: %s = %0h, expected %0h", what, got, want);
      fails++;
    end
  endtask

  logic         m_valid [NSLOT];
  logic [7:0]   m_bad   [NSLOT];
  logic [31:0]  m_pin   [NSLOT];
  logic [127:0] m_data  [NSLOT];
  logic         e_ok;
  logic [127:0] e_data;

  localparam int O_STATUS_VALID = 0, O_STATUS_EMPTY = 1, O_STATUS_OOB = 2;
  localparam int O_DELETE_VALID = 0, O_DELETE_EMPTY = 1, O_DELETE_OOB = 2;
  localparam int O_STORE_OK = 0, O_STORE_OCCUPIED = 1, O_STORE_OOB = 2;
  localparam int O_RET_RIGHT = 0, O_RET_WRONG = 1, O_RET_LOCKED = 2, O_RET_EMPTY = 3,
                 O_RET_OOB = 4;
  localparam int NOUT [4] = '{3, 3, 3, 5};
  string mname [4] = '{"status", "delete", "store", "retrieve"};

  function automatic int model(input [2:0] c, input [7:0] s, input [31:0] p,
                               input [127:0] d);
    int o;
    e_ok = 1'b0; e_data = '0;
    if (s >= NSLOT)
      case (c) STATUS: return O_STATUS_OOB; DELETE: return O_DELETE_OOB;
               STORE: return O_STORE_OOB; default: return O_RET_OOB; endcase
    case (c)
      STATUS: begin
        e_ok = m_valid[s];
        o = m_valid[s] ? O_STATUS_VALID : O_STATUS_EMPTY;
      end
      DELETE: begin
        e_ok = m_valid[s];
        o = m_valid[s] ? O_DELETE_VALID : O_DELETE_EMPTY;
        m_valid[s] = 1'b0; m_bad[s] = '0; m_pin[s] = '0; m_data[s] = '0;
      end
      STORE: begin
        if (m_valid[s]) o = O_STORE_OCCUPIED;
        else begin
          m_valid[s] = 1'b1; m_bad[s] = '0; m_pin[s] = p; m_data[s] = d;
          e_ok = 1'b1; o = O_STORE_OK;
        end
      end
      default: begin
        if (!m_valid[s]) o = O_RET_EMPTY;
        else if (m_bad[s] >= LIMIT) o = O_RET_LOCKED;
        else if (m_pin[s] == p) begin
          e_ok = 1'b1; e_data = m_data[s]; m_bad[s] = '0; o = O_RET_RIGHT;
        end else begin
          m_bad[s] = m_bad[s] + 8'd1; o = O_RET_WRONG;
        end
      end
    endcase
    return o;
  endfunction

  function automatic logic [168:0] dut_slot(input int k);
    case (k)
      0: return {dut.st_s_st_valid_S0, dut.st_s_st_bad_S0, dut.st_s_st_pin_S0, dut.st_s_st_data_S0};
      1: return {dut.st_s_st_valid_S1, dut.st_s_st_bad_S1, dut.st_s_st_pin_S1, dut.st_s_st_data_S1};
      2: return {dut.st_s_st_valid_S2, dut.st_s_st_bad_S2, dut.st_s_st_pin_S2, dut.st_s_st_data_S2};
      default: return {dut.st_s_st_valid_S3, dut.st_s_st_bad_S3, dut.st_s_st_pin_S3, dut.st_s_st_data_S3};
    endcase
  endfunction

  task automatic check_state(input string what);
    for (int k = 0; k < NSLOT; k++) begin
      logic [168:0] got = dut_slot(k);
      checks++;
      if (got !== {m_valid[k], m_bad[k], m_pin[k], m_data[k]}) begin
        $display("FAIL: %s: slot %0d = (%0d, %0d, %0h, %0h), expected (%0d, %0d, %0h, %0h)",
                 what, k, got[168], got[167:160], got[159:128], got[127:0],
                 m_valid[k], m_bad[k], m_pin[k], m_data[k]);
        fails++;
      end
    end
  endtask

  int lat [4][5];
  int last_lat;

  task automatic issue(input [2:0] c, input [7:0] s, input [31:0] p, input [127:0] d,
                       output int o);
    @(negedge clk);
    while (ready !== 1'b1) @(negedge clk);
    in_cmd = {1'b1, c}; slot = s; pin = p; data = d;
    @(posedge clk);
    @(negedge clk);
    in_cmd = 4'b0; slot = ~s; pin = $urandom; data = {$urandom, $urandom, $urandom, $urandom};
    #1;
    last_lat = 1;
    while (ready !== 1'b1) begin @(negedge clk); #1; last_lat++; end
    o = model(c, s, p, d);
    if (lat[c][o] == 0) lat[c][o] = last_lat;
    else if (lat[c][o] != last_lat) begin
      $display("FAIL: %s outcome %0d took %0d cycles, earlier %0d", mname[c], o, last_lat, lat[c][o]);
      fails++;
    end
  endtask

  task automatic op(input string what, input [2:0] c, input [7:0] s, input [31:0] p,
                    input [127:0] d);
    int o;
    issue(c, s, p, d, o);
    expect_eq({what, " ok"}, ok, e_ok);
    expect_eq({what, " data"}, odata, e_data);
    check_state(what);
  endtask

  task automatic status(input [7:0] s);
    op($sformatf("status(%0d)", s), STATUS, s, $urandom, {4{$urandom}});
  endtask
  task automatic delete(input [7:0] s);
    op($sformatf("delete(%0d)", s), DELETE, s, $urandom, {4{$urandom}});
  endtask
  task automatic store(input [7:0] s, input [31:0] p, input [127:0] d);
    op($sformatf("store(%0d, %0d)", s, p), STORE, s, p, d);
  endtask
  task automatic retrieve(input [7:0] s, input [31:0] p);
    op($sformatf("retrieve(%0d, %0d)", s, p), RETRIEVE, s, p, {4{$urandom}});
  endtask

  initial begin
    for (int k = 0; k < NSLOT; k++) begin
      m_valid[k] = 0; m_bad[k] = 0; m_pin[k] = 0; m_data[k] = 0;
    end
    foreach (lat[i, j]) lat[i][j] = 0;
    repeat (3) @(posedge clk); rst_n = 1;

    @(negedge clk);
    expect_eq("reset ok", ok, 0); expect_eq("reset data", odata, 0);
    check_state("reset");

    status(0);
    store(3, 1234, 1337);
    status(3);
    retrieve(3, 1234);
    expect_eq("k_correct", odata, 1337);
    retrieve(3, 1111);
    retrieve(3, 1234);
    expect_eq("k_one_bad_ok", ok, 1);
    delete(3);
    expect_eq("del_was_valid", ok, 1);
    retrieve(3, 1234);
    store(3, 1234, 1337);
    for (int i = 0; i < LIMIT; i++) retrieve(3, 1111);
    expect_eq("ten_exact", dut.st_s_st_bad_S3, 10);
    retrieve(3, 1234);
    expect_eq("k_limit", ok, 0);

    status(3);
    for (int i = 0; i < 10; i++) retrieve(3, 1111);
    expect_eq("locked_sat", dut.st_s_st_bad_S3, 10);
    delete(3); store(3, 4321, 9); retrieve(3, 4321);
    expect_eq("relock_by_delete", odata, 9);

    for (int i = 0; i < 3; i++) retrieve(3, 1);
    expect_eq("cnt_three", dut.st_s_st_bad_S3, 3);
    retrieve(3, 4321);
    expect_eq("cnt_reset", dut.st_s_st_bad_S3, 0);
    for (int i = 0; i < 9; i++) retrieve(3, 1);
    retrieve(3, 4321);
    expect_eq("nine_then_ok", ok, 1);

    store(3, 55, 66);
    delete(2);
    retrieve(1, 0);

    for (int k = 0; k < NSLOT; k++) begin
      if (k != 3) store(k[7:0], 100 + k, k + 7);
    end
    for (int k = 0; k < NSLOT; k++) retrieve(k[7:0], 100 + k);
    for (int i = 0; i < 4; i++) retrieve(0, 5);
    for (int k = 0; k < NSLOT; k++) status(k[7:0]);

    status(4); status(255);
    delete(255); delete(131);
    store(4, 1, 2); store(131, 1, 2); store(7, 1, 2);
    retrieve(200, 1234); retrieve(131, 4321); retrieve(7, 4321);

    for (int v = 200; v <= 255; v += 55) begin
      @(negedge clk);
      dut.st_s_st_bad_S3 = v[7:0]; m_bad[3] = v[7:0];
      retrieve(3, 4321); retrieve(3, 1);
      expect_eq("sym_locked", dut.st_s_st_bad_S3, v);
    end
    delete(3);

    store(3, 1234, 1337);
    retrieve(3, 32'h8000_04D2);
    expect_eq("pin_bit31", ok, 0);
    delete(0);
    store(0, 32'hFFFF_FFFF, {128{1'b1}});
    retrieve(0, 32'hFFFF_FFFF);
    expect_eq("wide_data", odata, {128{1'b1}});

    retrieve(3, 1234);
    repeat (5) @(negedge clk);
    expect_eq("held until next command", odata, 1337);
    status(3);    expect_eq("host wipe: status", odata, 0);
    retrieve(3, 1234); retrieve(3, 1111);
    retrieve(3, 1234); retrieve(9, 1234);
    retrieve(3, 1234); store(1, 1, 1);
    retrieve(3, 1234); delete(2);
    retrieve(3, 1234); status(200);

    retrieve(3, 1234);
    for (int c = 4; c < 8; c++) begin
      @(negedge clk);
      in_cmd = {1'b1, 3'(c)}; slot = 3; pin = 1234; data = '1;
      @(posedge clk);
      @(negedge clk);
      in_cmd = 4'b0; slot = 8'hEE; pin = $urandom; #1;
      expect_eq($sformatf("code %0d: ready", c), ready, 1);
      expect_eq($sformatf("code %0d: ok", c), ok, 1);
      expect_eq($sformatf("code %0d: data", c), odata, 1337);
      check_state($sformatf("code %0d", c));
    end
    status(3);

    for (int i = 0; i < 4000; i++) begin
      logic [2:0] c = 3'($urandom_range(0, 3));
      logic [7:0] s = ($urandom_range(0, 7) == 0) ? 8'($urandom) : 8'($urandom_range(0, 3));
      logic [31:0] p = ($urandom_range(0, 3) == 0) ? $urandom : 32'($urandom_range(0, 2));
      if ($urandom_range(0, 1) == 0) c = RETRIEVE;
      op($sformatf("random #%0d", i), c, s, p, {$urandom, $urandom, $urandom, $urandom});
    end

    for (int c = 0; c < 4; c++) begin
      string line = $sformatf("LATENCY %-8s", mname[c]);
      int l0 = lat[c][0];
      for (int o = 0; o < NOUT[c]; o++) begin
        line = {line, $sformatf(" o%0d=%0d", o, lat[c][o])};
        checks++;
        if (lat[c][o] == 0) begin
          $display("FAIL: %s outcome %0d never exercised", mname[c], o); fails++;
        end else if (lat[c][o] != l0) begin
          $display("FAIL: %s latency depends on the outcome", mname[c]); fails++;
        end
      end
      $display("%s -> %0d cycle(s), same for every outcome", line, l0);
    end

    if (fails != 0) begin $display("FAIL: %0d of %0d checks", fails, checks); $fatal(1); end
    $display("PASS (%0d checks)", checks);
    $finish;
  end

  initial begin repeat (200000) @(posedge clk); $display("FAIL: timeout"); $fatal(1); end
endmodule
