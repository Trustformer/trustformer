// Example_ArmsSeqSpike: what an UNTAKEN arm's call does while it is skipped.
//
//   if sel = 0 then st_t := ip(x*x*x*x) else st_e := ip(y);
//   st_z := ip(1)
//
// The skipped arm sends NO request -- its strobe is gated by the guard -- yet
// its stall counts anyway, because a drive's compiled validity is its
// payload's and its guard nodes' VALIDITY, not their truth.  That padding is
// what makes both arms cost the same, so it is kept, and this checks it: the
// skipped arm's sample still validates, on the same cycle either way.
//
// What it must NOT do is capture.  Its window opens while the shared response
// channel is carrying another call's cycle, and the datasheet promises nothing
// there.  So its buffer keeps its reset value, which is the guard in the latch
// enable.  Before that guard was added both arms captured 0xdeadbeef here.
//
// In the generated Verilog the then arm is buffer 7 behind stall 3, the else
// arm is buffer 8 behind stall 2, and the third call is buffer 9.  The third
// call's guard is empty, so its enable is unchanged.
//
// Both arms are run as the skipped one.  The buffers are zeroed when the
// action retires, so everything is sampled DURING the action.
module tb;
  localparam LAT = 3;
  localparam [31:0] GARBAGE = 32'hdeadbeef;
  localparam [31:0] XV = 32'd3;
  localparam [31:0] DEEP = 32'd81;
  localparam [31:0] YV = 32'd7;

  logic clk = 0, rst_n = 0;
  logic [16:0] in_cmd_out = 17'b0;
  logic [31:0] sel = 32'd1, xv = XV, yv = YV;

  wire [32:0] ip_arg;
  wire        ready, resp_ack, sel_ack, x_ack, y_ack;
  wire [31:0] resp_wire;

  Example_ArmsSeqSpike dut(
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

  // ---- the IP: one in flight, answer presented for exactly one cycle ----
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

  // ---- watch each sample's valid flag rise; record what it captured ----
  int run_idx = 0;
  logic seen_t [0:1]; logic [31:0] buf_t [0:1]; int cyc_t [0:1];
  logic seen_e [0:1]; logic [31:0] buf_e [0:1]; int cyc_e [0:1];
  logic seen_z [0:1]; logic [31:0] buf_z [0:1]; int cyc_z [0:1];

  always @(posedge clk) begin
    if (rst_n) begin
      if (dut.st_v_0_7 && !seen_t[run_idx]) begin
        seen_t[run_idx] <= 1; buf_t[run_idx] <= dut.st_b_0_7; cyc_t[run_idx] <= cyc;
      end
      if (dut.st_v_0_8 && !seen_e[run_idx]) begin
        seen_e[run_idx] <= 1; buf_e[run_idx] <= dut.st_b_0_8; cyc_e[run_idx] <= cyc;
      end
      if (dut.st_v_0_9 && !seen_z[run_idx]) begin
        seen_z[run_idx] <= 1; buf_z[run_idx] <= dut.st_b_0_9; cyc_z[run_idx] <= cyc;
      end
    end
  end

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

  task automatic expect_two(input [31:0] r0, input [31:0] r1);
    begin
      if (requests - base !== 2) begin
        $display("  FAIL expected 2 requests, saw %0d", requests - base); fails++;
      end else begin
        if (req_log[base] !== r0) begin
          $display("  FAIL req0 = %0d, expected %0d", req_log[base], r0); fails++;
        end
        if (req_log[base+1] !== r1) begin
          $display("  FAIL req1 = %0d, expected %0d", req_log[base+1], r1); fails++;
        end
      end
    end
  endtask

  initial begin
    for (int i = 0; i < 2; i++) begin
      seen_t[i] = 0; seen_e[i] = 0; seen_z[i] = 0;
      cyc_t[i] = -1; cyc_e[i] = -1; cyc_z[i] = -1;
      buf_t[i] = 0;  buf_e[i] = 0;  buf_z[i] = 0;
    end

    repeat (4) @(posedge clk);
    rst_n = 1;

    // ---------- run 0: sel != 0, the THEN arm is skipped ----------
    run_idx = 0; sel = 32'd1;
    run_cmd();
    $display("run 0 -- then arm SKIPPED (sel=1)");
    $display("  requests: %0d  req0=%0d req1=%0d", requests - base,
             req_log[base], req_log[base+1]);
    $display("  skipped then arm: valid=%0b at cyc %0d, captured 0x%08x",
             seen_t[0], cyc_t[0], buf_t[0]);
    $display("  taken   else arm: valid=%0b at cyc %0d, captured 0x%08x",
             seen_e[0], cyc_e[0], buf_e[0]);
    $display("  state: st_t=%0d st_e=%0d st_z=%0d",
             dut.st_s_st_t, dut.st_s_st_e, dut.st_s_st_z);
    expect_two(YV, 32'd1);
    if (!seen_t[0]) begin
      $display("  FAIL the skipped arm's sample never validated"); fails++;
    end
    if (buf_t[0] !== 32'd0) begin
      $display("  FAIL the skipped arm captured 0x%08x off the channel,",
               buf_t[0]);
      $display("       expected it to keep its reset value"); fails++;
    end
    if (dut.st_s_st_t !== 32'd0) begin
      $display("  FAIL st_t = %0d, expected 0", dut.st_s_st_t); fails++;
    end
    if (dut.st_s_st_e !== YV) begin
      $display("  FAIL st_e = %0d, expected %0d", dut.st_s_st_e, YV); fails++;
    end

    // ---------- run 1: sel = 0, the ELSE arm is skipped ----------
    run_idx = 1; sel = 32'd0;
    run_cmd();
    $display("run 1 -- else arm SKIPPED (sel=0)");
    $display("  requests: %0d  req0=%0d req1=%0d", requests - base,
             req_log[base], req_log[base+1]);
    $display("  skipped else arm: valid=%0b at cyc %0d, captured 0x%08x",
             seen_e[1], cyc_e[1], buf_e[1]);
    $display("  taken   then arm: valid=%0b at cyc %0d, captured 0x%08x",
             seen_t[1], cyc_t[1], buf_t[1]);
    $display("  state: st_t=%0d st_e=%0d st_z=%0d",
             dut.st_s_st_t, dut.st_s_st_e, dut.st_s_st_z);
    expect_two(DEEP, 32'd1);
    if (!seen_e[1]) begin
      $display("  FAIL the skipped arm's sample never validated"); fails++;
    end
    if (buf_e[1] !== 32'd0) begin
      $display("  FAIL the skipped arm captured 0x%08x off the channel,",
               buf_e[1]);
      $display("       expected it to keep its reset value"); fails++;
    end
    if (dut.st_s_st_t !== DEEP) begin
      $display("  FAIL st_t = %0d, expected %0d", dut.st_s_st_t, DEEP); fails++;
    end
    if (dut.st_s_st_e !== YV) begin
      $display("  FAIL st_e = %0d, expected %0d (unchanged)", dut.st_s_st_e, YV);
      fails++;
    end

    if (fails == 0) $display("PASS");
    else begin $display("FAIL (%0d checks)", fails); $fatal(1); end
    $finish;
  end

  initial begin repeat (600) @(posedge clk); $display("FAIL: timeout"); $fatal(1); end
endmodule
