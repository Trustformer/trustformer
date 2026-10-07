// Regression_MacroLib: the Examples of coq/Regressions/MacroLib.v, replayed on
// the generated Verilog.
//
// The macros of coq/Macros.v run inside the EXTRACTED program, where nat and N
// are OCaml ints.  A constant or a widening can come out wrong in the Verilog
// while every vm_compute Example still holds, so each action is driven here and
// its ports are compared with the values the Examples prove.  Inputs are
// scrambled once a command is accepted, so a design reading the live wire
// instead of the latch fails.
//
// Command codes are the derived encoding (mk_synth_ctx): the action's position
// in its declaration, in 4 bits.
module tb_macrolib;
  localparam [3:0] WRITE = 0, READ = 1, CLEAR = 2, MOD = 3, MOD8 = 4,
                   BITS = 5, CONST = 6, CONST2 = 7;

  logic clk = 0, rst_n = 0;
  logic [4:0]  in_cmd_out = 5'b0;
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

  // valid across exactly one accepting edge, then wait until ready again
  task automatic cmd(input [3:0] c, input [1:0] i, input [31:0] v);
    @(negedge clk);
    while (ready !== 1'b1) @(negedge clk);
    in_cmd_out = {1'b1, c}; idx = i; val = v;
    @(posedge clk);
    @(negedge clk);
    in_cmd_out = 5'b0; idx = ~i; val = 32'hdeadbeef;
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

    // Arrays: a write lands in the indexed cell only, truncated to 8 bits;
    // index 3 names no cell.  Every action clears the outputs first.
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

    // Modulo by 10^6 at 32 bits: boundaries, then random values
    begin
      logic [31:0] vs [6] = '{32'd0, 32'd999999, 32'd1000000, 32'd1000001, 32'd123456789, 32'hFFFFFFFF};
      foreach (vs[k]) begin cmd(MOD, 0, vs[k]); expect_eq("mod 1e6", out_val, vs[k] % 1000000); end
    end
    for (int k = 0; k < 200; k++) begin
      logic [31:0] v = $urandom;
      cmd(MOD, 0, v); expect_eq("mod 1e6 (random)", out_val, v % 1000000);
    end

    // Modulo by 10 at 8 bits, every value
    for (int v = 0; v < 256; v++) begin
      cmd(MOD8, 0, v); expect_eq("mod 10", out_val, v % 10);
    end

    // Bits 23..8, and bit 31
    cmd(BITS, 0, 32'hAABBCCDD); expect_eq("slice", out_val, 32'hBBCC); expect_eq("bit 31", out_ok, 1);
    cmd(BITS, 0, 32'h7FFFFFFF); expect_eq("bit 31 clear", out_ok, 0);

    // Constants, including a 128-bit one
    cmd(CONST, 0, 0);
    expect_eq("hex ^ N", out_val, 32'hDFAFBDEB);
    expect_eq("128-bit hex", out_wide, 128'h0123456789ABCDEF_FEDCBA9876543210);
    cmd(CONST2, 0, 0);
    expect_eq("rep ++ odd hex", out_val, 32'h5C5C0ABC);
    expect_eq("N with top chunk", out_wide, 128'hABCDE);

    if (fails != 0) begin $display("FAIL: %0d of %0d checks", fails, checks); $fatal(1); end
    $display("PASS (%0d checks)", checks);
    $finish;
  end

  initial begin repeat (200000) @(posedge clk); $display("FAIL: timeout"); $fatal(1); end
endmodule
