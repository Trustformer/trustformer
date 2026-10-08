// Differential fuzz bench for Example_MarsV2 with the real SHA/HMAC adapters,
// driven by scripts/fuzz-mars.py.  It replays gen_mars_v2's command file through a
// model of the wrapper's handshake, writes the full public state and the busy
// cycles after each command, and rewrites every input with random data on each
// busy cycle so the module must use what it latched at accept.
`timescale 1ns/1ps
module tb_fuzz_mars_v2;
  reg CLK = 0, RST_N = 0;
  always #1 CLK = ~CLK;
  reg [15:0] cmd_reg = 0; reg cmd_pending = 0; reg wr = 0; reg [15:0] wr_code = 0;
  reg [15:0] a_pt = 0, a_idx = 0, a_nlen = 0, a_ctxlen = 0;
  reg [255:0] a_dig = 0, a_nonce = 0, a_ctx = 0, a_sig = 0; reg [31:0] a_regsel = 0;
  reg a_restricted = 0, a_fault = 0, a_init_req = 0;
  reg [1:0] a_inj = 0;   // SelfTest only: corrupt the SHA (1), HMAC (2) or both (3) answers it sees
  localparam [255:0] PS = 256'h4865726520617265207468697274792074776f20736563726574206279746573;
  reg [255:0] a_ps = PS;
  wire ready; wire [15:0] rc, cap; wire [255:0] dout, pcr0, pcr1, snap; wire failure, st, result;
  wire [1040:0] sha_req; wire [784:0] hmac_req; wire [255:0] sha_resp, hmac_resp;
  wire busy = cmd_pending || !ready;
  always @(posedge CLK) begin
    if (!RST_N) cmd_pending <= 0;
    else if (wr && !cmd_pending) begin cmd_reg <= wr_code; cmd_pending <= 1; end
    else if (cmd_pending && ready) cmd_pending <= 0;
  end
  Example_MarsV2 dut (
      .CLK(CLK), .RST_N(RST_N), .in_cmd_out({cmd_pending, cmd_reg}), .in_cmd_arg(ready),
      .in_param_pub_in_pt_out(a_pt), .in_param_pub_in_pt_arg(), .in_param_pub_in_idx_out(a_idx), .in_param_pub_in_idx_arg(),
      .in_param_pub_in_dig_out(a_dig), .in_param_pub_in_dig_arg(),
      .in_param_sec_in_ps_out(a_ps), .in_param_sec_in_ps_arg(),
      .in_param_sec_in_init_req_out(a_init_req), .in_param_sec_in_init_req_arg(),
      .in_param_sec_in_fault_out(a_fault), .in_param_sec_in_fault_arg(),
      .in_param_pub_in_regsel_out(a_regsel), .in_param_pub_in_regsel_arg(), .in_param_pub_in_nonce_out(a_nonce), .in_param_pub_in_nonce_arg(),
      .in_param_pub_in_ctx_out(a_ctx), .in_param_pub_in_ctx_arg(), .in_param_pub_in_nlen_out(a_nlen), .in_param_pub_in_nlen_arg(),
      .in_param_pub_in_ctxlen_out(a_ctxlen), .in_param_pub_in_ctxlen_arg(),
      .in_param_pub_in_sig_out(a_sig), .in_param_pub_in_sig_arg(),
      .in_param_pub_in_restricted_out(a_restricted), .in_param_pub_in_restricted_arg(),
      .out_param_pub_out_rc_arg(rc), .out_param_pub_out_rc_out(1'b0), .out_param_pub_out_cap_arg(cap), .out_param_pub_out_cap_out(1'b0),
      .out_param_pub_out_dout_arg(dout), .out_param_pub_out_dout_out(1'b0), .out_param_pub_out_pcr0_arg(pcr0), .out_param_pub_out_pcr0_out(1'b0),
      .out_param_pub_out_pcr1_arg(pcr1), .out_param_pub_out_pcr1_out(1'b0), .out_param_pub_out_failure_arg(failure), .out_param_pub_out_failure_out(1'b0),
      .out_param_pub_out_st_arg(st), .out_param_pub_out_st_out(1'b0), .out_param_pub_out_snap_arg(snap), .out_param_pub_out_snap_out(1'b0),
      .out_param_pub_out_result_arg(result), .out_param_pub_out_result_out(1'b0),
      .ip_req_sec_ip_sha_arg(sha_req), .ip_req_sec_ip_sha_out(1'b0), .ip_resp_sec_ip_sha_out(sha_resp ^ {255'b0, a_inj[0]}), .ip_resp_sec_ip_sha_arg(),
      .ip_req_sec_ip_hmac_arg(hmac_req), .ip_req_sec_ip_hmac_out(1'b0), .ip_resp_sec_ip_hmac_out(hmac_resp ^ {255'b0, a_inj[1]}), .ip_resp_sec_ip_hmac_arg());
  mars_ip_sha_adapter  #(.DECLARED_LAT(140)) sha_ip  (.CLK(CLK), .RST_N(RST_N), .ip_req(sha_req),  .ip_resp(sha_resp));
  mars_ip_hmac_adapter #(.DECLARED_LAT(275)) hmac_ip (.CLK(CLK), .RST_N(RST_N), .ip_req(hmac_req), .ip_resp(hmac_resp));

  integer fd, fo, fl, i, nb, scr;
  reg [15:0] code, pt, idx, nlen, ctxlen; reg [31:0] regsel; reg [255:0] dig, nonce, ctx, sig; reg restricted, fault, init_req; reg [1:0] inj;
  reg [1023:0] cmds; reg [1023:0] outs; reg [1023:0] lats;
  function [255:0] r256(input dummy); r256 = {$random,$random,$random,$random,$random,$random,$random,$random}; endfunction
  initial begin
    if (!$value$plusargs("cmds=%s", cmds)) $finish;
    void'($value$plusargs("out=%s", outs)); void'($value$plusargs("lat=%s", lats));
    scr = !$test$plusargs("noscramble");
    fd = $fopen(cmds, "r"); fo = $fopen(outs, "w"); fl = $fopen(lats, "w");
    repeat (5) @(negedge CLK); RST_N = 1; repeat (3) @(negedge CLK);
    i = 0;
    while ($fscanf(fd, "%h %h %h %h %h %h %h %h %h %h %h %h %h %h\n", code, pt, idx, regsel, nlen, ctxlen, restricted, fault, init_req,
                   inj, dig, nonce, ctx, sig) == 14) begin
      a_pt = pt; a_idx = idx; a_regsel = regsel; a_nlen = nlen; a_ctxlen = ctxlen; a_dig = dig; a_nonce = nonce; a_ctx = ctx; a_sig = sig;
      a_restricted = restricted; a_fault = fault; a_init_req = init_req; a_ps = PS;
      @(negedge CLK); while (busy) @(negedge CLK);
      a_inj = inj;
      wr = 1; wr_code = code; @(posedge CLK); @(negedge CLK); wr = 0;
      @(posedge CLK); @(negedge CLK); nb = 1;
      while (busy) begin
        if (scr) begin
          a_nonce = r256(0); a_ctx = r256(0); a_dig = r256(0); a_sig = r256(0); a_ps = r256(0);
          a_regsel = $random; a_nlen = $random; a_ctxlen = $random; a_idx = $random; a_pt = $random;
          a_restricted = $random; a_fault = $random; a_init_req = $random;
        end
        nb = nb + 1; @(negedge CLK);
        if (nb > 20000) begin $display("HANG: command %0d code %04h busy for %0d cycles", i, code, nb); $fclose(fo); $fclose(fl); $finish; end
      end
      a_inj = 0;
      $fwrite(fo, "%0d %04h %0d %04h %0d %064h %064h %064h %064h %0d %0d\n", i, code, rc, cap, result, dout, snap, pcr0, pcr1, failure, st);
      $fwrite(fl, "%04h %0d %0d %0d\n", code, rc, fault, nb);
      i = i + 1;
    end
    $fclose(fo); $fclose(fl); $finish;
  end
endmodule
