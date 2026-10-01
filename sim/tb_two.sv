// Two calls to ONE IP in one action.  ops:
//   st_a := ip(in_msg)        st_b := ip(~in_msg)
// The IP is identity, latency 3, and NOT pipelined -- so a second request
// arriving while one is in flight is a design error and is reported as such.
module tb_two;
  localparam LAT = 3;
  localparam [255:0] MSG     = 256'h00112233445566778899aabbccddeeff_0f1e2d3c4b5a69788796a5b4c3d2e1f0;
  localparam [255:0] GARBAGE = 256'hdeadbeefdeadbeefdeadbeefdeadbeef_deadbeefdeadbeefdeadbeefdeadbeef;

  logic clk = 0, rst_n = 0;
  logic [16:0]  in_cmd_out = 17'b0;
  logic [255:0] msg = MSG;

  wire [256:0] ip_arg;
  wire         ready, resp_ack, msg_ack;
  logic [255:0] resp_wire;

  Regression_TwoCall dut(
    .CLK(clk), .RST_N(rst_n),
    .ip_resp_sec_cs_crypto_out(resp_wire),
    .in_param_pub_in_msg_out(msg),
    .in_cmd_arg(ready),
    .ip_req_sec_cs_crypto_out(1'b1),
    .in_cmd_out(in_cmd_out),
    .ip_req_sec_cs_crypto_arg(ip_arg),
    .ip_resp_sec_cs_crypto_arg(resp_ack),
    .in_param_pub_in_msg_arg(msg_ack));

  // ---- non-pipelined IP: one request in flight at a time ----
  logic [255:0] cap;
  logic [LAT-1:0] pipe;
  logic busy = 0;
  int  strobe_cycles = 0, requests = 0;
  logic [255:0] req_log [0:7];
  int cyc = 0;

  always @(posedge clk) begin
    if (!rst_n) begin pipe <= '0; busy <= 0; end
    else begin
      pipe <= {pipe[LAT-2:0], ip_arg[256]};
      if (ip_arg[256]) begin
        strobe_cycles <= strobe_cycles + 1;
        if (busy) begin
          $display("FAIL: request at cycle %0d while one is still in flight", cyc);
          $display("      (a held strobe, not a pulse -- the IP sees %0d back-to-back requests)", strobe_cycles+1);
          $fatal(1);
        end
        if (requests < 8) req_log[requests] <= ip_arg[255:0];
        requests <= requests + 1;
        cap <= ip_arg[255:0];
        busy <= 1;
      end
      if (pipe[LAT-1]) busy <= 0;
    end
  end
  assign resp_wire = pipe[LAT-1] ? cap : GARBAGE;

  always #5 clk = ~clk;
  always @(posedge clk) cyc <= cyc + 1;

  initial begin
    repeat (4) @(posedge clk);
    rst_n = 1;
    @(posedge clk);
    in_cmd_out = {1'b1, 16'h0001};
    wait (ready === 1'b1);
    @(posedge clk);
    in_cmd_out = 17'b0;
    wait (ready === 1'b1);
    @(posedge clk);

    $display("requests seen by IP = %0d (strobe high for %0d cycles)", requests, strobe_cycles);
    for (int i = 0; i < requests && i < 8; i++) $display("  req[%0d] = %h", i, req_log[i]);
    $display("st_a = %h", dut.st_s_st_a);
    $display("  exp  %h   (ip(msg))", MSG);
    $display("st_b = %h", dut.st_s_st_b);
    $display("  exp  %h   (ip(~msg))", ~MSG);
    if (dut.st_s_st_a !== MSG)  begin $display("FAIL: st_a wrong"); $fatal(1); end
    if (dut.st_s_st_b !== ~MSG) begin $display("FAIL: st_b wrong"); $fatal(1); end
    $display("PASS");
    $finish;
  end

  initial begin repeat (400) @(posedge clk); $display("FAIL: timeout"); $fatal(1); end
endmodule
