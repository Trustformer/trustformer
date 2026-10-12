// Behavioural two-block SHA-1 IP for tb_knox_otp: no SHA-1 core exists under external/.
package sha1_ref;
  localparam logic [159:0] IV = 160'h67452301_efcdab89_98badcfe_10325476_c3d2e1f0;

  function automatic logic [159:0] compress(input logic [159:0] h, input logic [511:0] blk);
    logic [31:0] w [0:79];
    logic [31:0] a, b, c, d, e, f, k, t;
    for (int i = 0; i < 16; i++) w[i] = blk[511 - 32*i -: 32];
    for (int i = 16; i < 80; i++) begin
      t = w[i-3] ^ w[i-8] ^ w[i-14] ^ w[i-16];
      w[i] = {t[30:0], t[31]};
    end
    {a, b, c, d, e} = h;
    for (int i = 0; i < 80; i++) begin
      if (i < 20)      begin f = (b & c) | (~b & d);          k = 32'h5a827999; end
      else if (i < 40) begin f = b ^ c ^ d;                   k = 32'h6ed9eba1; end
      else if (i < 60) begin f = (b & c) | (b & d) | (c & d); k = 32'h8f1bbcdc; end
      else             begin f = b ^ c ^ d;                   k = 32'hca62c1d6; end
      t = {a[26:0], a[31:27]} + f + e + k + w[i];
      e = d; d = c; c = {b[1:0], b[31:2]}; b = a; a = t;
    end
    return {h[159:128] + a, h[127:96] + b, h[95:64] + c, h[63:32] + d, h[31:0] + e};
  endfunction

  function automatic logic [159:0] sha1_2blk(input logic [511:0] b1, input logic [511:0] b2);
    return compress(compress(IV, b1), b2);
  endfunction
endpackage

module sha1_2blk_model #(parameter int DECLARED_LAT = 180) (
    input  wire          CLK,
    input  wire          RST_N,
    input  wire [1024:0] ip_req,
    output wire [159:0]  ip_resp
);
  import sha1_ref::*;

  int answer_at = DECLARED_LAT - 1;
  bit override_en = 1'b0;
  logic [159:0] override_digest = '0;
  int requests = 0, last_lat = 0, fails = 0;
  logic [1023:0] req_log [0:1];

  wire strobe = ip_req[1024];
  logic strobe_d = 1'b0, waiting = 1'b0;
  logic [159:0] result = '0, resp = '0;
  int cnt = 0;
  assign ip_resp = resp;

  always @(posedge CLK) begin
    if (!RST_N) begin
      strobe_d <= 1'b0; waiting <= 1'b0; resp <= '0;
    end else begin
      strobe_d <= strobe;
      if (strobe && !strobe_d) begin
        if (waiting) begin
          $display("FAIL: SHA-1 request while one is in flight"); fails++;
        end
        result <= override_en ? override_digest
                              : sha1_2blk(ip_req[1023:512], ip_req[511:0]);
        req_log[requests % 2] <= ip_req[1023:0];
        requests <= requests + 1;
        waiting <= 1'b1;
        cnt <= 1;
        resp <= {$urandom, $urandom, $urandom, $urandom, $urandom};
      end else if (waiting) begin
        if (cnt >= answer_at) begin
          resp <= result;
          waiting <= 1'b0;
          last_lat <= cnt;
          if (cnt > DECLARED_LAT - 1) begin
            $display("FAIL: SHA-1 answered after %0d cycles, ip_lat is %0d", cnt, DECLARED_LAT);
            fails++;
          end
        end else begin
          resp <= {$urandom, $urandom, $urandom, $urandom, $urandom};
        end
        cnt <= cnt + 1;
      end
    end
  end
endmodule
