// Example_GuardCallSpike: an [if] whose condition is a CALL RESULT.
//
//   st_a := ip(in_msg);
//   if st_a = 0 then st_b := ip(7) else st_b := ip(9)
//
// The IP is identity, latency 3, not pipelined, and -- as in every spike here
// -- it presents its answer for EXACTLY ONE cycle and drives garbage otherwise.
// A guard that reads the response wire instead of the sample's latch therefore
// sees garbage at the cycle the second drive fires, and picks the wrong arm.
module tb;
  localparam LAT = 3;
  localparam [255:0] GARBAGE = 256'hdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef;
  localparam [255:0] NONZERO = 256'h00000000000000000000000000000000000000000000000000000000000000f5;

  logic clk = 0, rst_n = 0;
  logic [16:0] in_cmd_out = 17'b0;
  logic [255:0] msg = 256'b0;

  wire [256:0] ip_arg;
  wire         ready, resp_ack, msg_ack;
  wire [255:0] resp_wire;

  Example_GuardCallSpike dut(
    .CLK(clk), .RST_N(rst_n),
    .ip_resp_sec_cs_crypto_out(resp_wire),
    .in_param_pub_in_msg_out(msg),
    .in_cmd_arg(ready),
    .ip_req_sec_cs_crypto_out(1'b1),
    .in_cmd_out(in_cmd_out),
    .ip_req_sec_cs_crypto_arg(ip_arg),
    .ip_resp_sec_cs_crypto_arg(resp_ack),
    .in_param_pub_in_msg_arg(msg_ack));

  logic [255:0] cap;
  logic [LAT-1:0] pipe;
  logic busy = 0;
  int  requests = 0, strobe_cycles = 0;
  logic [255:0] req_log [0:7];
  int cyc = 0;

  always @(posedge clk) begin
    if (!rst_n) begin pipe <= '0; busy <= 0; end
    else begin
      pipe <= {pipe[LAT-2:0], ip_arg[256]};
      if (ip_arg[256]) begin
        strobe_cycles = strobe_cycles + 1;
        if (busy) begin
          $display("FAIL(cyc %0d): request while one is in flight", cyc);
          $fatal(1);
        end
        if (requests < 8) req_log[requests] = ip_arg[255:0];
        requests = requests + 1;
        cap <= ip_arg[255:0];                       // identity
        busy <= 1;
      end
      if (pipe[LAT-1]) busy <= 0;
    end
  end
  assign resp_wire = pipe[LAT-1] ? cap : GARBAGE;

  always #5 clk = ~clk;
  always @(posedge clk) cyc <= cyc + 1;

  int fails = 0, base;

  task automatic run_cmd();
    begin
      base = requests;
      @(negedge clk);
      while (ready !== 1'b1) @(negedge clk);
      in_cmd_out = {1'b1, 16'h0001};
      @(posedge clk);
      @(negedge clk);
      in_cmd_out = 17'b0;
      while (ready !== 1'b1) @(negedge clk);
    end
  endtask

  task automatic expect_arm(input string what, input [255:0] second_arg);
    begin
      $display("  %s: requests=%0d  req0=%h  req1=%h  st_b=%h",
               what, requests - base, req_log[base], req_log[base+1], dut.st_s_st_b);
      if (requests - base !== 2) begin
        $display("  FAIL [%s] expected two requests, saw %0d", what, requests - base);
        fails++;
      end else if (req_log[base+1] !== second_arg) begin
        $display("  FAIL [%s] the second call took the WRONG ARM", what);
        $display("        got %h", req_log[base+1]);
        $display("        exp %h", second_arg);
        fails++;
      end
      if (dut.st_s_st_b !== second_arg) begin
        $display("  FAIL [%s] st_b is wrong: got %h exp %h", what, dut.st_s_st_b, second_arg);
        fails++;
      end
    end
  endtask

  initial begin
    repeat (4) @(posedge clk);
    rst_n = 1;

    // st_a = 0  ->  the THEN arm  ->  second call asks for 7
    msg = 256'b0;
    run_cmd();
    expect_arm("st_a = 0   (then arm)", 256'd7);

    // st_a != 0 ->  the ELSE arm  ->  second call asks for 9
    msg = NONZERO;
    run_cmd();
    expect_arm("st_a != 0  (else arm)", 256'd9);

    $display("  strobe-cycles=%0d over %0d requests", strobe_cycles, requests);
    if (strobe_cycles !== requests) begin
      $display("  FAIL: a strobe was held rather than pulsed");
      fails++;
    end

    if (fails == 0) $display("PASS");
    else begin $display("FAIL (%0d checks)", fails); $fatal(1); end
    $finish;
  end

  initial begin repeat (400) @(posedge clk); $display("FAIL: timeout"); $fatal(1); end
endmodule
