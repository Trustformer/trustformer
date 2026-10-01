// Regression_ArmsSeq: a call AFTER an [if] whose arms both call the same IP.
//
//   if sel = 0 then st_t := ip(x*x*x*x) else st_e := ip(y);
//   st_z := ip(1)
//
// The third call must wait for whichever arm ran.  An untaken arm's stall
// counts out regardless of its guard, so if the third call waits only on the
// most recently emitted arm, the untaken one waves it through and its request
// lands on the port while the taken arm is still waiting for its answer.
// The taken arm then latches the third call's answer.
//
// The taken arm here is the DEEP one, so it is several cycles behind the arm
// that is not taken -- which is what removes the one-cycle margin that hides
// this in a symmetric branch.
module tb_arms;
  localparam LAT = 3;
  localparam [31:0] GARBAGE = 32'hdeadbeef;
  localparam [31:0] XV = 32'd3;              // x
  localparam [31:0] DEEP = 32'd81;           // x*x*x*x
  localparam [31:0] YV = 32'd7;

  logic clk = 0, rst_n = 0;
  logic [16:0] in_cmd_out = 17'b0;
  logic [31:0] sel = 32'b0, xv = XV, yv = YV;

  wire [32:0] ip_arg;
  wire        ready, resp_ack, sel_ack, x_ack, y_ack;
  wire [31:0] resp_wire;

  Regression_ArmsSeq dut(
    .CLK(clk), .RST_N(rst_n),
    .ip_resp_sec_as_ip_out(resp_wire),
    .in_param_pub_in_sel_out(sel),
    .in_param_pub_in_x_out(xv),
    .in_param_pub_in_y_out(yv),
    .in_cmd_arg(ready),
    .ip_req_sec_as_ip_out(1'b1),
    .in_cmd_out(in_cmd_out),
    .ip_req_sec_as_ip_arg(ip_arg),
    .ip_resp_sec_as_ip_arg(resp_ack),
    .in_param_pub_in_sel_arg(sel_ack),
    .in_param_pub_in_x_arg(x_ack),
    .in_param_pub_in_y_arg(y_ack));

  logic [31:0] cap;
  logic [LAT-1:0] pipe;
  logic busy = 0;
  int  requests = 0;
  logic [31:0] req_log [0:7];
  int cyc = 0;

  always @(posedge clk) begin
    if (!rst_n) begin pipe <= '0; busy <= 0; end
    else begin
      pipe <= {pipe[LAT-2:0], ip_arg[32]};
      if (ip_arg[32]) begin
        if (busy) begin
          $display("FAIL(cyc %0d): request while one is in flight", cyc);
          $fatal(1);
        end
        if (requests < 8) req_log[requests] = ip_arg[31:0];
        requests = requests + 1;
        cap <= ip_arg[31:0];
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

  initial begin
    repeat (4) @(posedge clk);
    rst_n = 1;

    // sel = 0 -> the DEEP arm runs.  Two requests: x*x*x*x then 1,
    // in that order, and st_t must hold the answer to the DEEP one.
    sel = 32'd0;
    run_cmd();
    $display("  deep arm: requests=%0d  req0=%0d req1=%0d  st_t=%0d st_z=%0d",
             requests - base, req_log[base], req_log[base+1],
             dut.st_s_st_t, dut.st_s_st_z);
    if (requests - base !== 2) begin
      $display("  FAIL expected two requests, saw %0d", requests - base);
      fails++;
    end else begin
      if (req_log[base] !== DEEP) begin
        $display("  FAIL first request was %0d, expected %0d", req_log[base], DEEP);
        fails++;
      end
      if (req_log[base+1] !== 32'd1) begin
        $display("  FAIL second request was %0d, expected 1", req_log[base+1]);
        fails++;
      end
    end
    if (dut.st_s_st_t !== DEEP) begin
      $display("  FAIL st_t = %0d, expected %0d -- the taken arm latched the",
               dut.st_s_st_t, DEEP);
      $display("       answer to a later call", );
      fails++;
    end
    if (dut.st_s_st_z !== 32'd1) begin
      $display("  FAIL st_z = %0d, expected 1", dut.st_s_st_z);
      fails++;
    end

    if (fails == 0) $display("PASS");
    else begin $display("FAIL (%0d checks)", fails); $fatal(1); end
    $finish;
  end

  initial begin repeat (600) @(posedge clk); $display("FAIL: timeout"); $fatal(1); end
endmodule
