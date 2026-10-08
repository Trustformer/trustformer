module tb_operators;
  localparam [2:0] LSR = 0, LSL = 1, ASR = 2, SLT = 3, SLICE = 4, SLICE_OUT = 5, ISLICE = 6;

  logic clk = 0, rst_n = 0;
  logic [3:0]  in_cmd_out = 4'b0;
  logic [31:0] a = 32'b0, b = 32'b0;
  wire ready, a_ack, b_ack;
  wire [31:0] out_r;
  wire        out_f;

  Regression_Operators dut(
    .CLK(clk), .RST_N(rst_n),
    .in_cmd_out(in_cmd_out), .in_cmd_arg(ready),
    .in_param_pub_in_a_out(a), .in_param_pub_in_a_arg(a_ack),
    .in_param_pub_in_b_out(b), .in_param_pub_in_b_arg(b_ack),
    .out_param_pub_out_r_arg(out_r), .out_param_pub_out_r_out(1'b1),
    .out_param_pub_out_f_arg(out_f), .out_param_pub_out_f_out(1'b1));

  always #5 clk = ~clk;

  int checks = 0, fails = 0;

  task automatic cmd(input [2:0] c, input [31:0] x, input [31:0] y);
    @(negedge clk);
    while (ready !== 1'b1) @(negedge clk);
    in_cmd_out = {1'b1, c}; a = x; b = y;
    @(posedge clk);
    @(negedge clk);
    in_cmd_out = 4'b0; a = ~x; b = ~y;
    #1;
    while (ready !== 1'b1) @(negedge clk);
  endtask

  function automatic [31:0] expected(input [2:0] c, input [31:0] x, input [31:0] y);
    case (c)
      LSR:       return x >> y;
      LSL:       return x << y;
      ASR:       return $signed(x) >>> y;
      SLT:       return {31'b0, $signed(x) < $signed(y)};
      SLICE:     return (x >> 4) & 32'hFF;
      SLICE_OUT: return (x >> 28) & 32'hFF;
      default:   return (x >> y[4:0]) & 32'hFF;
    endcase
  endfunction

  task automatic check(input [2:0] c, input [31:0] x, input [31:0] y);
    logic [31:0] got, want;
    cmd(c, x, y);
    got = (c == SLT) ? {31'b0, out_f} : out_r;
    want = expected(c, x, y);
    checks++;
    if (got !== want) begin
      $display("FAIL: op %0d a=%h b=%h: got %h, expected %h", c, x, y, got, want);
      fails++;
    end
  endtask

  initial begin
    logic [31:0] edges [8] = '{32'h0, 32'h1, 32'h7FFFFFFF, 32'h80000000, 32'hFFFFFFFF,
                               32'h12345678, 32'hF0000000, 32'h40000000};
    logic [31:0] amounts [10] = '{0, 1, 4, 8, 28, 31, 32, 33, 40, 32'hFFFFFFFF};
    repeat (3) @(posedge clk); rst_n = 1;

    for (int op = 0; op <= 6; op++)
      foreach (edges[i])
        foreach (amounts[j])
          check(op[2:0], edges[i], (op == SLT) ? edges[j % 8] : amounts[j]);

    for (int op = 0; op <= 6; op++)
      for (int k = 0; k < 300; k++)
        check(op[2:0], $urandom, (k % 2 == 0) ? $urandom % 48 : $urandom);

    if (fails != 0) begin $display("FAIL: %0d of %0d checks", fails, checks); $fatal(1); end
    $display("PASS (%0d checks)", checks);
    $finish;
  end

  initial begin repeat (100000) @(posedge clk); $display("FAIL: timeout"); $fatal(1); end
endmodule
