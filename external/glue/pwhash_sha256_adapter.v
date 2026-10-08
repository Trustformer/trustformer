// Adapts sha256_core to the Knox password hasher's one-block SHA-256 IP port.
module pwhash_sha256_adapter #(parameter integer DECLARED_LAT = 72) (
    input  wire          CLK,
    input  wire          RST_N,
    input  wire [512:0]  ip_req,
    output wire [255:0]  ip_resp
);
  wire         strobe = ip_req[512];
  reg          strobe_d, waiting, core_init;
  reg [511:0]  blk;
  reg [255:0]  held;
  wire         core_ready, core_dv;
  wire [255:0] core_digest;

  sha256_core core (
      .clk(CLK), .reset_n(RST_N),
      .init(core_init), .next(1'b0), .mode(1'b1),
      .block(blk),
      .ready(core_ready), .digest(core_digest), .digest_valid(core_dv));

  assign ip_resp = held;

  always @(posedge CLK) begin
    if (!RST_N) begin
      strobe_d <= 1'b0; waiting <= 1'b0; core_init <= 1'b0;
      blk <= 512'd0; held <= 256'd0;
    end else begin
      strobe_d  <= strobe;
      core_init <= 1'b0;
      if (strobe && !strobe_d) begin
        blk       <= ip_req[511:0];
        core_init <= 1'b1;
        waiting   <= 1'b1;
      end else if (waiting && !core_init && core_dv) begin
        held    <= core_digest;
        waiting <= 1'b0;
      end
    end
  end

  integer errors = 0, requests = 0, answers = 0, age = 0, lat_last = 0, lat_max = 0;
  always @(posedge CLK) begin
    if (!RST_N) age <= 0;
    else if (strobe && !strobe_d) begin
      requests <= requests + 1;
      age <= 0;
      if (waiting) begin
        $display("FAIL: adapter: SHA request while one is in flight");
        errors <= errors + 1;
      end
    end else if (waiting) begin
      age <= age + 1;
      if (!core_init && core_dv) begin
        answers  <= answers + 1;
        lat_last <= age + 1;
        if (age + 1 > lat_max) lat_max <= age + 1;
        if (age + 1 > DECLARED_LAT - 1) begin
          $display("FAIL: adapter: SHA answered %0d edges after the strobe, budget %0d (ip_lat %0d)",
                   age + 1, DECLARED_LAT - 1, DECLARED_LAT);
          errors <= errors + 1;
        end
      end
    end
  end
endmodule
