// Example_XPortGuardSpike: a branch on a call result, where the branch's own
// calls are on a DIFFERENT port from the call the condition reads.
//
//   st_c := cond(in_msg);
//   if st_c = 0 then st_r := arm(7) else st_r := arm(9)
//
// tb_guard.sv is the same program with every call on ONE port, and it passes:
// [last_sample] finds the first call's sample there, so both arms' drives are
// sequenced behind it.  Across two ports there is no such join, so this asks
// whether the arm's drive still waits for the condition to settle.
//
// Both IPs are identity, latency 3, not pipelined, and present their answer
// for exactly one cycle (garbage otherwise).
module tb_xport;
  localparam LAT = 3;
  localparam [255:0] GARBAGE = 256'hdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef;
  localparam [255:0] NONZERO = 256'h00000000000000000000000000000000000000000000000000000000000000f5;

  logic clk = 0, rst_n = 0;
  logic [16:0] in_cmd_out = 17'b0;
  logic [255:0] msg = 256'b0;

  wire [256:0] cond_arg, arm_arg;
  wire         ready, cond_ack, arm_ack, msg_ack;
  wire [255:0] cond_wire, arm_wire;

  Example_XPortGuardSpike dut(
    .CLK(clk), .RST_N(rst_n),
    .ip_resp_sec_xp_cond_out(cond_wire),
    .ip_resp_sec_xp_arm_out(arm_wire),
    .in_param_pub_in_msg_out(msg),
    .in_cmd_arg(ready),
    .ip_req_sec_xp_cond_out(1'b1),
    .ip_req_sec_xp_arm_out(1'b1),
    .in_cmd_out(in_cmd_out),
    .ip_req_sec_xp_cond_arg(cond_arg),
    .ip_req_sec_xp_arm_arg(arm_arg),
    .ip_resp_sec_xp_cond_arg(cond_ack),
    .ip_resp_sec_xp_arm_arg(arm_ack),
    .in_param_pub_in_msg_arg(msg_ack));

  // ---- two identical IP models ----
  logic [255:0] cond_cap, arm_cap;
  logic [LAT-1:0] cond_pipe, arm_pipe;
  logic cond_busy = 0, arm_busy = 0;
  int cond_reqs = 0, arm_reqs = 0;
  logic [255:0] arm_log [0:7];
  int cyc = 0;

  always @(posedge clk) begin
    if (!rst_n) begin
      cond_pipe <= '0; arm_pipe <= '0; cond_busy <= 0; arm_busy <= 0;
    end else begin
      cond_pipe <= {cond_pipe[LAT-2:0], cond_arg[256]};
      if (cond_arg[256]) begin
        if (cond_busy) begin
          $display("FAIL(cyc %0d): cond request while one is in flight", cyc);
          $fatal(1);
        end
        cond_reqs = cond_reqs + 1;
        cond_cap <= cond_arg[255:0];
        cond_busy <= 1;
      end
      if (cond_pipe[LAT-1]) cond_busy <= 0;

      arm_pipe <= {arm_pipe[LAT-2:0], arm_arg[256]};
      if (arm_arg[256]) begin
        if (arm_busy) begin
          $display("FAIL(cyc %0d): arm request while one is in flight", cyc);
          $fatal(1);
        end
        if (arm_reqs < 8) arm_log[arm_reqs] = arm_arg[255:0];
        arm_reqs = arm_reqs + 1;
        arm_cap <= arm_arg[255:0];
        arm_busy <= 1;
      end
      if (arm_pipe[LAT-1]) arm_busy <= 0;
    end
  end
  assign cond_wire = cond_pipe[LAT-1] ? cond_cap : GARBAGE;
  assign arm_wire  = arm_pipe[LAT-1]  ? arm_cap  : GARBAGE;

  always #5 clk = ~clk;
  always @(posedge clk) cyc <= cyc + 1;

  int fails = 0, base;

  task automatic run_cmd();
    begin
      base = arm_reqs;
      @(negedge clk);
      while (ready !== 1'b1) @(negedge clk);
      in_cmd_out = {1'b1, 16'h0001};
      @(posedge clk);
      @(negedge clk);
      in_cmd_out = 17'b0;
      while (ready !== 1'b1) @(negedge clk);
    end
  endtask

  task automatic expect_arm(input string what, input [255:0] want);
    begin
      $display("  %s: arm requests=%0d  arg=%h  st_c=%h  st_r=%h",
               what, arm_reqs - base,
               (arm_reqs - base > 0) ? arm_log[base] : 256'bx,
               dut.st_s_st_c, dut.st_s_st_r);
      if (arm_reqs - base !== 1) begin
        $display("  FAIL [%s] expected ONE request on the arm port, saw %0d",
                 what, arm_reqs - base);
        fails++;
      end else if (arm_log[base] !== want) begin
        $display("  FAIL [%s] the arm call took the WRONG ARM", what);
        $display("        got %h", arm_log[base]);
        $display("        exp %h", want);
        fails++;
      end
      if (dut.st_s_st_r !== want) begin
        $display("  FAIL [%s] st_r is wrong: got %h exp %h",
                 what, dut.st_s_st_r, want);
        fails++;
      end
    end
  endtask

  initial begin
    repeat (4) @(posedge clk);
    rst_n = 1;

    // st_c = 0  ->  the THEN arm  ->  the arm call asks for 7
    msg = 256'b0;
    run_cmd();
    expect_arm("st_c = 0   (then arm)", 256'd7);

    // st_c != 0 ->  the ELSE arm  ->  the arm call asks for 9
    msg = NONZERO;
    run_cmd();
    expect_arm("st_c != 0  (else arm)", 256'd9);

    if (fails == 0) $display("PASS");
    else begin $display("FAIL (%0d checks)", fails); $fatal(1); end
    $finish;
  end

  initial begin repeat (400) @(posedge clk); $display("FAIL: timeout"); $fatal(1); end
endmodule
