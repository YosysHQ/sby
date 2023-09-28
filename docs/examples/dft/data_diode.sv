// Simple sync FIFO implementation using an extra bit in the read and write
// pointers to distinguish the completely full and completely empty case.
module fifo #(
    DEPTH_BITS = 4,
    WIDTH = 8
) (
    input wire clk,
    input wire rst,

    input wire             in_valid,
    input wire [WIDTH-1:0] in_data,
    output reg             in_ready,

    output reg             out_valid,
    output reg [WIDTH-1:0] out_data,
    input wire             out_ready
);

    reg [WIDTH-1:0] buffer [1<<DEPTH_BITS];

    reg [DEPTH_BITS:0] write_addr;
    reg [DEPTH_BITS:0] read_addr;

    wire in_transfer = in_valid && in_ready;
    wire out_transfer = out_valid && out_ready;

    wire [DEPTH_BITS:0] write_limit = read_addr ^ (1 << DEPTH_BITS);

    assign in_ready = write_addr != write_limit;
    assign out_valid = read_addr != write_addr;

    assign out_data = buffer[read_addr[DEPTH_BITS-1:0]];

    always @(posedge clk) begin
        if (rst) begin
            read_addr <= 0;
            write_addr <= 0;
        end else begin
            if (in_transfer) begin
                buffer[write_addr[DEPTH_BITS-1:0]] <= in_data;
                write_addr <= write_addr + 1'b1;
            end

            if (out_transfer) begin
                read_addr <= read_addr + 1'b1;
            end
        end
    end

endmodule

// This module sends some data and should not be able to receive any
// information back, even under the assumption that it can trick the other side
// into performing unintended operations that would attempt to establish a
// covert channel.
module untrusted_module (
    input wire clk,
    input wire rst,

    input wire en,

    output reg        out_valid,
    output reg [31:0] out_data,
    input wire        out_ready
);

    reg [31:0] lfsr;

    always @(posedge clk) begin
        if (rst) begin
            lfsr <= '1;
        end else if (en && out_valid && out_ready) begin
            lfsr <= (lfsr << 1) ^ (lfsr[31] ? 32'h04C11DB7 : 0);
        end
    end

    assign out_valid = out_ready && en;
    assign out_data = lfsr;

endmodule

// This module receives data and contains secret data. It should guard this
// secret data even if there are bugs in this module's implementations that the
// other side could exploit in an attempt to establish a covert channel to
// exfiltrate the secrets.
module secret_storing_module (
    input wire clk,
    input wire rst,

    input wire en,
    output reg [31:0] counter,

    input wire        in_valid,
    input wire [31:0] in_data,
    output reg        in_ready
);

    reg [3:0] busy;

    always @(posedge clk) begin
        if (rst) begin
            counter <= '0;
            busy <= '0;
        end else if (en) begin
            if (busy) begin
                busy <= busy - 4'b1;
            end else if (in_valid && in_ready) begin
                busy <= counter[3:0];
                counter <= counter + in_data;
            end
        end
    end

    assign in_ready = en && !busy;

endmodule


// This data diode wraps a FIFO, but ensures that there is no backwards data
// flow via the handshaking signals. Instead it limits the sender to send with
// a fixed rate and only notifies the receiver
module data_diode #(
    DEPTH_BITS = 4,
    WIDTH = 8,
    RATE = 2
) (
    input wire clk,
    input wire rst,

    input wire             in_valid,
    input wire [WIDTH-1:0] in_data,
    output reg             in_ready,

    output reg             out_valid,
    output reg [WIDTH-1:0] out_data,
    input wire             out_ready,

    output reg overflow
);
    reg [$clog2(RATE):0] delay;
    wire fifo_ready;

    always @(posedge clk) begin
        if (rst) begin
            delay <= 0;
            overflow <= 0;
        end else begin
            if (in_valid && in_ready) begin
                if (!fifo_ready) begin
                    overflow <= 1;
                end
                delay <= RATE - 1;
            end else if (delay) begin
                delay <= delay - 1'b1;
            end
        end
    end

    assign in_ready = !delay;

    fifo #(.DEPTH_BITS(DEPTH_BITS), .WIDTH(WIDTH)) fifo (
        .clk(clk),
        .rst(rst),

        .in_valid(in_valid),
        .in_data(in_data),
        .in_ready(fifo_ready),

        .out_valid(out_valid),
        .out_data(out_data),
        .out_ready(out_ready)
    );

endmodule

// The top module either connects the untrusted and secret storing modules
// directly or via the data diode.
module top(
    input wire clk,
    input wire rst,

    input wire source_en,
    input wire sink_en,

`ifdef USE_DIODE
    output reg overflow,
`endif
    output reg [31:0] counter

);

    wire        source_valid;
    wire [31:0] source_data;
    wire        source_ready;

    wire        sink_valid;
    wire [31:0] sink_data;
    wire        sink_ready;

    untrusted_module source (
        .clk(clk),
        .rst(rst),
        .en(source_en),

        .out_valid(source_valid),
        .out_data(source_data),
        .out_ready(source_ready)
    );

`ifdef USE_DIODE
    data_diode #(.WIDTH(32)) data_diode (
        .clk(clk),
        .rst(rst),

        .in_valid(source_valid),
        .in_data(source_data),
        .in_ready(source_ready),

        .out_valid(sink_valid),
        .out_data(sink_data),
        .out_ready(sink_ready),

        .overflow(overflow)
    );
`else
    fifo #(.WIDTH(32)) fifo (
        .clk(clk),
        .rst(rst),

        .in_valid(source_valid),
        .in_data(source_data),
        .in_ready(source_ready),

        .out_valid(sink_valid),
        .out_data(sink_data),
        .out_ready(sink_ready)
    );
`endif

    secret_storing_module sink (
        .clk(clk),
        .rst(rst),
        .en(sink_en),

        .in_valid(sink_valid),
        .in_data(sink_data),
        .in_ready(sink_ready),

        .counter(counter)
    );
endmodule

// We can inject a tag into signals of a module by binding a checker that
// contains an `$overwrite_tag` item.
checker mark_secret(counter);
    $overwrite_tag("secret", counter);
endchecker

bind secret_storing_module mark_secret counter_is_secret(counter);

// We cen inject a check for a tag by binding a checker that has an assertion
// that uses `$get_tag`.
//
// When using a direct connection, this assertion will fail as there is a
// covert channel via the FIFO's handshaking signals. When the data-diode is
// used, we are able to prove the absance of such a covert channel.
checker leak_check(clk, signal);
   secret_leaked: assert property (@(posedge clk) !$get_tag("secret", signal));
endchecker

bind untrusted_module leak_check leak_check(clk, out_ready);


checker initial_reset(clk, rst);
    assume property (@(posedge clk) $initstate |-> rst);
endchecker

bind top initial_reset initial_reset(clk, rst);
