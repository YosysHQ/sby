`ifndef WIDTH
`define WIDTH 4
`endif

module divider #(
    parameter WIDTH=`WIDTH
) (
    input wire clk,
    input wire start,
    input wire [WIDTH-1:0] dividend,
    input wire [WIDTH-1:0] divisor,

    output reg done,
    output reg [WIDTH-1:0] quotient,
    output wire [WIDTH-1:0] remainder
);

    reg [WIDTH-1:0] acc;

    reg [WIDTH*2-1:0] sub;
    reg [WIDTH-1:0] pos;

    assign remainder = acc;

    always @(posedge clk) begin
        if (start) begin
            acc <= dividend;
            quotient <= 0;
            sub <= divisor << (WIDTH - 1);
            pos <= 1 << (WIDTH - 1);
            done <= 0;
        end else if (!done) begin
            if (acc >= sub) begin
                acc <= acc - sub[WIDTH-1:0];
                quotient <= quotient + pos;
            end

            sub <= sub >> 1;
            {pos, done} <= pos;
        end
    end


`ifdef FORMAL
    reg [WIDTH-1:0] start_dividend = 0;
    reg [WIDTH-1:0] start_divisor = 0;

    reg started = 0;
    reg finished = 0;
    reg [$clog2(WIDTH + 1):0] counter = 0;

    always @(posedge clk) begin
        // Bound the number of cycles until the result is ready
        assert (counter <= WIDTH);

        if (started) begin
            if (finished || done) begin
                finished <= 1;
                // Make sure result stays until we start a new division
                assert (done);

                // Check the result
                if (start_divisor == 0) begin
                    assert (&quotient);
                    assert (remainder == start_dividend);
                end else begin
                    assert (quotient == start_dividend / start_divisor);
                    assert (remainder == start_dividend % start_divisor);
                end
            end else begin
                counter <= counter + 1'b1;
            end
        end

        // Track the requested inputs
        if (start) begin
            start_divisor <= divisor;
            start_dividend <= dividend;
            started <= 1;
            counter <= 0;
            finished <= 0;
        end
    end
`endif
endmodule
