module tb_macrolib;
  localparam [4:0] WRITE = 0, READ = 1, CLEAR = 2, MOD = 3, MOD8 = 4,
                   BITS = 5, CONST = 6, CONST2 = 7, LOOP = 8, CONCAT = 9, SELECT = 10,
                   FIND = 11, SHIFT = 12, CASE = 13, SEXT = 14, PSET = 15, PGET = 16,
                   PSET_WIDE = 17, PGET_WIDE = 18, WHILE = 19;

  logic clk = 0, rst_n = 0;
  logic [5:0]  in_cmd_out = 6'b0;
  logic [1:0]  idx = 2'b0;
  logic [31:0] val = 32'b0;
  wire ready, idx_ack, val_ack;
  wire [31:0]  out_val;
  wire         out_ok;
  wire [127:0] out_wide;

  Regression_MacroLib dut(
    .CLK(clk), .RST_N(rst_n),
    .in_cmd_out(in_cmd_out), .in_cmd_arg(ready),
    .in_param_pub_in_idx_out(idx), .in_param_pub_in_idx_arg(idx_ack),
    .in_param_pub_in_val_out(val), .in_param_pub_in_val_arg(val_ack),
    .out_param_pub_out_val_arg(out_val), .out_param_pub_out_val_out(1'b1),
    .out_param_pub_out_ok_arg(out_ok), .out_param_pub_out_ok_out(1'b1),
    .out_param_pub_out_wide_arg(out_wide), .out_param_pub_out_wide_out(1'b1));

  always #5 clk = ~clk;

  int checks = 0, fails = 0;

  task automatic cmd(input [4:0] c, input [1:0] i, input [31:0] v);
    @(negedge clk);
    while (ready !== 1'b1) @(negedge clk);
    in_cmd_out = {1'b1, c}; idx = i; val = v;
    @(posedge clk);
    @(negedge clk);
    in_cmd_out = 6'b0; idx = ~i; val = 32'hdeadbeef;
    #1;
    while (ready !== 1'b1) @(negedge clk);
  endtask

  task automatic expect_eq(input string what, input [127:0] got, input [127:0] want);
    checks++;
    if (got !== want) begin
      $display("FAIL: %s = %h, expected %h", what, got, want);
      fails++;
    end
  endtask

  initial begin
    repeat (3) @(posedge clk); rst_n = 1;

    cmd(WRITE, 1, 32'h1AB);  expect_eq("write ok", out_ok, 1); expect_eq("write val", out_val, 0);
    cmd(WRITE, 0, 32'h17);
    cmd(WRITE, 2, 32'h42);
    cmd(WRITE, 3, 32'hFF);   expect_eq("write idx 3 ok", out_ok, 0);
    cmd(READ, 0, 0);         expect_eq("read 0", out_val, 32'h17); expect_eq("read 0 ok", out_ok, 1);
    cmd(READ, 1, 0);         expect_eq("read 1", out_val, 32'hAB);
    cmd(READ, 2, 0);         expect_eq("read 2", out_val, 32'h42);
    cmd(READ, 3, 0);         expect_eq("read 3", out_val, 0); expect_eq("read 3 ok", out_ok, 0);
    cmd(CLEAR, 0, 0);        expect_eq("clear val", out_val, 0);
    for (int i = 0; i < 3; i++) begin
      cmd(READ, i[1:0], 0);  expect_eq("read after clear", out_val, 0);
    end

    begin
      logic [31:0] vs [6] = '{32'd0, 32'd999999, 32'd1000000, 32'd1000001, 32'd123456789, 32'hFFFFFFFF};
      foreach (vs[k]) begin cmd(MOD, 0, vs[k]); expect_eq("mod 1e6", out_val, vs[k] % 1000000); end
    end
    for (int k = 0; k < 200; k++) begin
      logic [31:0] v = $urandom;
      cmd(MOD, 0, v); expect_eq("mod 1e6 (random)", out_val, v % 1000000);
    end

    for (int v = 0; v < 256; v++) begin
      cmd(MOD8, 0, v); expect_eq("mod 10", out_val, v % 10);
    end

    cmd(BITS, 0, 32'hAABBCCDD); expect_eq("slice", out_val, 32'hBBCC); expect_eq("bit 31", out_ok, 1);
    cmd(BITS, 0, 32'h7FFFFFFF); expect_eq("bit 31 clear", out_ok, 0);

    cmd(CONST, 0, 0);
    expect_eq("hex ^ N", out_val, 32'hDFAFBDEB);
    expect_eq("128-bit hex", out_wide, 128'h0123456789ABCDEF_FEDCBA9876543210);
    cmd(CONST2, 0, 0);
    expect_eq("rep ++ odd hex", out_val, 32'h5C5C0ABC);
    expect_eq("N with top chunk", out_wide, 128'hABCDE);

    for (int k = 0; k < 200; k++) begin
      logic [31:0] v = $urandom;
      cmd(LOOP, 0, v);   expect_eq("popcount", out_val, $countones(v[7:0])); expect_eq("parity", out_ok, ^v);
      cmd(CONCAT, 0, v); expect_eq("concat", out_val, {v[7:0], v[15:8], 16'h0});
      cmd(SEXT, 0, v);   expect_eq("sext", out_val, {{24{v[7]}}, v[7:0]});
      if (v != 5 && v != 32'hDEADBEEF) begin cmd(CASE, 0, v); expect_eq("case default", out_val, 7); end
    end
    cmd(CASE, 0, 5);            expect_eq("case 5", out_val, 50);
    cmd(CASE, 0, 32'hDEADBEEF); expect_eq("case wide", out_val, 1);
    for (int i = 0; i < 4; i++) begin
      cmd(SELECT, i[1:0], 0);   expect_eq("select", out_val, (i == 0) ? 10 : (i == 1) ? 20 : (i == 2) ? 30 : 99);
    end

    cmd(CLEAR, 0, 0);
    cmd(FIND, 0, 32'h111); expect_eq("find 1 full", out_ok, 0);
    cmd(FIND, 0, 32'h122); expect_eq("find 2 full", out_ok, 0);
    cmd(FIND, 0, 32'h133); expect_eq("find 3 full", out_ok, 1);
    cmd(FIND, 0, 32'h144); expect_eq("find 4 full", out_ok, 1);
    cmd(READ, 0, 0); expect_eq("find c0", out_val, 32'h11);
    cmd(READ, 1, 0); expect_eq("find c1", out_val, 32'h22);
    cmd(READ, 2, 0); expect_eq("find c2", out_val, 32'h33);
    cmd(SHIFT, 0, 32'h155);
    cmd(READ, 0, 0); expect_eq("shift c0", out_val, 32'h22);
    cmd(READ, 1, 0); expect_eq("shift c1", out_val, 32'h33);
    cmd(READ, 2, 0); expect_eq("shift c2", out_val, 32'h55);

    begin
      logic [31:0] pk = 0;
      for (int k = 0; k < 300; k++) begin
        logic [1:0] i = $urandom;
        logic [31:0] v = $urandom;
        if (k % 2 == 0) begin
          pk[i * 8 +: 8] = v[7:0];
          cmd(PSET, i, v); expect_eq("packed set", out_val, pk);
        end else begin
          cmd(PGET, i, v); expect_eq("packed get", out_val, {24'h0, pk[i * 8 +: 8]});
        end
      end
      for (int k = 0; k < 300; k++) begin
        logic [31:0] v = $urandom;
        logic [2:0] i = v[2:0];
        if (k % 2 == 0) begin
          if (i < 4) pk[i * 8 +: 8] = v[15:8];
          cmd(PSET_WIDE, 0, v); expect_eq("packed set (wide index)", out_val, pk);
        end else begin
          cmd(PGET_WIDE, 0, v); expect_eq("packed get (wide index)", out_val, (i < 4) ? {24'h0, pk[i * 8 +: 8]} : 32'h0);
        end
      end
    end

    begin
      longint t0, quick, full;
      for (int k = 0; k < 300; k++) begin
        logic [31:0] v;
        int n;
        v = $urandom >> ($urandom % 33);
        n = 0;
        while (n < 8 && (v >> n) != 0) n++;
        cmd(WHILE, 0, v); expect_eq("while bit length", out_val, n); expect_eq("while done", out_ok, (v >> n) == 0);
      end
      t0 = $time; cmd(WHILE, 0, 0); quick = $time - t0;
      t0 = $time; cmd(WHILE, 0, 32'hFFFFFFFF); full = $time - t0;
      expect_eq("while exits early on a public condition", quick < full, 1);
    end

    if (fails != 0) begin $display("FAIL: %0d of %0d checks", fails, checks); $fatal(1); end
    $display("PASS (%0d checks)", checks);
    $finish;
  end

  initial begin repeat (200000) @(posedge clk); $display("FAIL: timeout"); $fatal(1); end
endmodule
