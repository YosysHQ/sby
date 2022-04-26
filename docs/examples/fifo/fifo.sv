// Define the fifo storage
module storage (
    input wen, ren, clk, rst_n,
    input [3:0] waddr, raddr,
    input [7:0] wdata,
    output [7:0] rdata
);
    parameter MAX_DATA = 16;

    // 8 bit data, fifo depth 16 / 4 bit address
    // reset not defined
    reg [7:0] data [MAX_DATA-1:0];
    always @(posedge clk) begin
        if (wen) 
            data[waddr] <= wdata;
    end
    
    assign rdata = data[raddr];
endmodule

// address generator/counter
module addr_gen (
    input en, clk, rst_n,
    output reg [3:0] addr
);
    parameter MAX_DATA = 16;

    initial begin
        addr <= 0;
    end

    // async reset
    // increment address when enabled
    always @(posedge clk or negedge rst_n) begin
        if (~rst_n)
            addr <= 0;
        else if (en)
            if (addr == MAX_DATA-1)
                addr <= 0;
            else
                addr <= addr + 1;
        else
            addr <= addr;
    end
endmodule
