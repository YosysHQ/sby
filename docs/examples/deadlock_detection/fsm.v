module fsm (
    input clk,
    input rst,
    input req,
    output reg grant
);

parameter IDLE  = 2'b00;
parameter WAIT  = 2'b01;
parameter GRANT = 2'b10;

reg [1:0] state;

always @(posedge clk) begin
    if (rst) begin
        state <= IDLE;
        grant <= 0;
    end else begin
        case (state)
            IDLE: begin
                if (req)
                    state <= WAIT;
            end

            WAIT: begin
                // Deadlock: no exit from WAIT state
                state <= WAIT;
            end

            GRANT: begin
                grant <= 1;
                state <= IDLE;
            end
        endcase
    end
end

`ifdef FORMAL

// Check if GRANT state is reachable
always @(posedge clk) begin
    cover(grant);
end

`endif

endmodule