module DUT (
    input  logic clk,
    output logic req,
    output logic ack
);

`ifdef FORMAL

  logic [1:0] reqs_seen;
  logic [31:0] cycle_count;

  // Deterministic initial state
  initial begin
    // req       = 1'b0;
    reqs_seen = 2'b00;
    cycle_count = 32'b0;
  end

  always @ (posedge clk) begin
    if (req) reqs_seen <= reqs_seen + 1;
    cycle_count <= cycle_count + 1;
  end

  // Req is only high for one cycle
  assume property (@(posedge clk)
    req |-> ##1 !req
  );

  // Reqs are at least 8 cycles apart
  assume property (@(posedge clk)
    req |-> ##1 (!req [*7])
  );

  // ack comes exactly 4 cycles after req
  assume property (@(posedge clk) 
    req |-> ##4 ack
  );

  // ack must remain low if no req 4 cycles ago
  assume property (@(posedge clk)
    !$past(req,4) |-> !ack
  );

  // For the purpose of demonstration, stop exactly when second req pulse
  // occurs. This leaves us in a state where we're waiting for the second ack.
  always @(posedge clk) begin
    (* phase = "1" *)
    cover(reqs_seen == 2);
  end

  // In phase 2, assume that there's no more reqs; despite this, assert that
  // an ack will eventually come for the second req.
  always @ (posedge clk) begin
    (* phase = "2" *)
    assume(!req);
  end
  always @(posedge clk) begin
    (* phase = "2" *)
    cover(ack);
  end


`endif

endmodule
