module DUT (
        input  logic clk,
        output logic req,
        output logic ack
);

`ifdef FORMAL

        logic [31:0] reqs_seen;
        logic [31:0] acks_seen;
        logic [31:0] cycle_count;

        // Deterministic initial state
        initial begin
                reqs_seen = 32'b0;
                acks_seen = 32'b0;
                cycle_count = 32'b0;
        end

        always @ (posedge clk) begin
                if (req) reqs_seen <= reqs_seen + 1;
                if (ack && !$past(ack)) acks_seen <= acks_seen + 1;
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
        // occurs. This leaves us in a state where we're waiting for the second
        // ack.
        always @(posedge clk) begin
                phase1_reqs_seen: cover(reqs_seen == 2);
        end

        // In phase 2, cover that the first ack arrives within a bounded window
        // after the first req + another req arrives.
        phase2_cover_ack_and_new_req: cover property (@(posedge clk)
                $rose(ack) ##[1:$] (reqs_seen == 3)
        );


        // In phase 3, assume that there's no more reqs.
        always @ (posedge clk) begin
                phase3_shared_no_new_req: assume(!req);
        end

        // In phase 3a, cover the second ack arriving eventually.
        always @(posedge clk) begin
                phase3a_cover_ack: cover(ack);
        end

        // In phase 3b, assert that once we've seen 3 acks, we stay at 3 acks.
        phase3b_acks_remains_3: assert property (
                @(posedge clk) $rose(acks_seen == 3) |-> (acks_seen == 3)[*1:$]
        );

`endif

endmodule
