// Testbench for Example_CallSpike: one IP call, declared latency 3.
//
// The IP model presents its answer for EXACTLY ONE CYCLE, 3 cycles after the
// request strobe, and drives GARBAGE on the response wire at every other
// cycle.  A design that samples on the wrong cycle therefore latches garbage
// and fails, rather than accidentally passing.
module tb_call;
  localparam LAT = 3;
  localparam [255:0] MSG     = 256'h00112233445566778899aabbccddeeff_0f1e2d3c4b5a69788796a5b4c3d2e1f0;
  localparam [255:0] GARBAGE = 256'hdeadbeefdeadbeefdeadbeefdeadbeef_deadbeefdeadbeefdeadbeefdeadbeef;
  localparam [255:0] LATER   = 256'hffffffffffffffffffffffffffffffff_ffffffffffffffffffffffffffffffff;

  logic clk = 0, rst_n = 0;
  logic [16:0]  in_cmd_out = 17'b0;
  logic [255:0] msg = MSG;

  wire [256:0] ip_arg;      // {strobe, payload}
  wire         ready;
  wire         resp_ack, msg_ack;
  logic [255:0] resp_wire;

  Example_CallSpike dut(
    .CLK(clk), .RST_N(rst_n),
    .ip_resp_sec_cs_crypto_out(resp_wire),
    .in_param_pub_in_msg_out(msg),
    .in_cmd_arg(ready),
    .ip_req_sec_cs_crypto_out(1'b1),
    .in_cmd_out(in_cmd_out),
    .ip_req_sec_cs_crypto_arg(ip_arg),
    .ip_resp_sec_cs_crypto_arg(resp_ack),
    .in_param_pub_in_msg_arg(msg_ack));

  // ---- the attached IP: identity, latency LAT, answer valid for one cycle ----
  logic [255:0] cap;
  logic [LAT-1:0] pipe;
  int strobe_count = 0;
  always @(posedge clk) begin
    if (!rst_n) begin pipe <= '0; end
    else begin
      pipe <= {pipe[LAT-2:0], ip_arg[256]};
      if (ip_arg[256]) begin cap <= ip_arg[255:0]; strobe_count <= strobe_count + 1; end
    end
  end
  assign resp_wire = pipe[LAT-1] ? cap : GARBAGE;

  int cyc = 0;
  int accept_cyc = -1, done_cyc = -1;
  always #5 clk = ~clk;

  initial begin
    repeat (4) @(posedge clk);
    rst_n = 1;
    @(posedge clk);
    // present the command until it is accepted
    in_cmd_out = {1'b1, 16'h0001};
    wait (ready === 1'b1);
    @(posedge clk);
    accept_cyc = cyc;
    in_cmd_out = 17'b0;
    // change the live input AFTER acceptance: the design must use the latched value
    msg = LATER;
    // run to completion
    wait (ready === 1'b1);
    @(posedge clk);
    done_cyc = cyc;

    $display("strobes=%0d  latency=%0d cycles", strobe_count, done_cyc - accept_cyc);
    $display("captured_by_ip = %h", cap);
    $display("st_s_st_res    = %h", dut.st_s_st_res);
    $display("expected       = %h", MSG);
    if (dut.st_s_st_res !== MSG) begin
      $display("FAIL: result is wrong");
      if (dut.st_s_st_res === GARBAGE) $display("      (it is the GARBAGE value -> sampled on the wrong cycle)");
      if (dut.st_s_st_res === LATER)   $display("      (it is the LATER value -> used the live input, not the latch)");
      $fatal(1);
    end
    if (cap !== MSG) begin $display("FAIL: IP received the wrong request payload"); $fatal(1); end
    if (strobe_count !== 1) begin $display("FAIL: expected exactly one strobe"); $fatal(1); end
    $display("PASS");
    $finish;
  end

  always @(posedge clk) cyc <= cyc + 1;
  initial begin repeat (400) @(posedge clk); $display("FAIL: timeout (module never became ready again)"); $fatal(1); end
endmodule
