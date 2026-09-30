// A call inside BOTH arms of an if.  sel=1 selects ~a.
// The lowering sequences the two drives rather than making them exclusive, so
// the IP sees TWO requests and a phi picks the answer.  This checks that the
// phi picks the RIGHT one, and reports what the IP was actually asked.
module tb_branch;
  localparam LAT = 3;
  localparam [255:0] A       = 256'h00112233445566778899aabbccddeeff_0f1e2d3c4b5a69788796a5b4c3d2e1f0;
  localparam [255:0] GARBAGE = 256'hdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef;
  localparam [15:0]  SEL     = 16'd1;          // take the ~a branch

  logic clk = 0, rst_n = 0;
  logic [16:0]  in_cmd_out = 17'b0;
  logic [15:0]  sel = SEL;
  logic [255:0] a = A;

  wire [256:0] ip_arg;
  wire         ready, resp_ack, sel_ack, a_ack;
  logic [255:0] resp_wire;

  Example_BranchCallSpike dut(
    .CLK(clk), .RST_N(rst_n),
    .ip_resp_sec_cs_crypto_out(resp_wire),
    .ip_resp_sec_cs_crypto_arg(resp_ack),
    .in_param_pub_in_sel_out(sel), .in_param_pub_in_sel_arg(sel_ack),
    .in_param_pub_in_a_out(a),     .in_param_pub_in_a_arg(a_ack),
    .in_cmd_arg(ready),
    .ip_req_sec_cs_crypto_out(1'b1),
    .in_cmd_out(in_cmd_out),
    .ip_req_sec_cs_crypto_arg(ip_arg));

  // identity IP, latency LAT, one request in flight at a time
  logic [255:0] cap;
  logic [LAT-1:0] pipe;
  logic busy = 0;
  int requests = 0;
  logic [255:0] req_log [0:7];
  int cyc = 0;

  always @(posedge clk) begin
    if (!rst_n) begin pipe <= '0; busy <= 0; end
    else begin
      pipe <= {pipe[LAT-2:0], ip_arg[256]};
      if (ip_arg[256]) begin
        if (busy) begin $display("FAIL: overlapping requests at cycle %0d", cyc); $fatal(1); end
        if (requests < 8) req_log[requests] <= ip_arg[255:0];
        requests <= requests + 1; cap <= ip_arg[255:0]; busy <= 1;
      end
      if (pipe[LAT-1]) busy <= 0;
    end
  end
  assign resp_wire = pipe[LAT-1] ? cap : GARBAGE;

  always #5 clk = ~clk;
  always @(posedge clk) cyc <= cyc + 1;

  initial begin
    repeat (4) @(posedge clk); rst_n = 1; @(posedge clk);
    in_cmd_out = {1'b1, 16'h0001};
    wait (ready === 1'b1); @(posedge clk); in_cmd_out = 17'b0;
    wait (ready === 1'b1); @(posedge clk);
    $display("requests seen by IP = %0d", requests);
    for (int i = 0; i < requests && i < 8; i++) $display("  req[%0d] = %h", i, req_log[i]);
    $display("st_out = %h", dut.st_s_st_out);
    $display("  exp    %h   (sel=1 -> ip(~a))", ~A);
    if (dut.st_s_st_out !== ~A) begin $display("FAIL: wrong branch result"); $fatal(1); end
    $display("PASS");
    $finish;
  end
  initial begin repeat (400) @(posedge clk); $display("FAIL: timeout"); $fatal(1); end
endmodule
