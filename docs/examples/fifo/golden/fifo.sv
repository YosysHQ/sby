// address generator/counter
module addr_gen 
#(  parameter MAX_DATA=16,
    parameter ADDR_BITS=5
) ( input en, clk, rst,
    output reg [ADDR_BITS-1:0] addr
);
    initial addr <= 0;

    // async reset
    // increment address when enabled
    always @(posedge clk or posedge rst)
        if (rst)
            addr <= 0;
        else if (en) begin
            if (addr == MAX_DATA-1)
                addr <= 0;
            else
                addr <= addr + 1;
        end
endmodule

// Define our top level fifo entity
module fifo 
#(  parameter MAX_DATA=16,
    parameter ADDR_BITS=5
) ( input wen, ren, clk, rst,
    input [7:0] wdata,
    output [7:0] rdata,
    output [ADDR_BITS:0] count,
    output full, empty
);
    wire wskip, rskip;
    reg [ADDR_BITS:0] data_count;

    // fifo storage
    // async read, sync write
    wire [ADDR_BITS-1:0] waddr, raddr;
    reg [7:0] data [MAX_DATA-1:0];
    always @(posedge clk)
        if (wen) 
            data[waddr] <= wdata;
    assign rdata = data[raddr];
    // end storage

    // addr_gen for both write and read addresses
    addr_gen #(.MAX_DATA(MAX_DATA), .ADDR_BITS(ADDR_BITS)) 
    fifo_writer (
        .en     (wen || wskip),
        .clk    (clk  ),
        .rst    (rst),
        .addr   (waddr)
    );

    addr_gen #(.MAX_DATA(MAX_DATA), .ADDR_BITS(ADDR_BITS)) 
    fifo_reader (
        .en     (ren || rskip),
        .clk    (clk  ),
        .rst    (rst),
        .addr   (raddr)
    );

    // status signals
    initial data_count <= 0;

    always @(posedge clk or posedge rst) begin
        if (rst)
            data_count <= 0;
        else if (wen && !ren && data_count < MAX_DATA)
            data_count <= data_count + 1;
        else if (ren && !wen && data_count > 0)
            data_count <= data_count - 1;
    end

    assign full  = data_count == MAX_DATA;
    assign empty = (data_count == 0) && ~rst;
    assign count = data_count;

    // overflow protection
`ifndef NO_FULL_SKIP
    // write while full => overwrite oldest data, move read pointer
    assign rskip = wen && !ren && data_count >= MAX_DATA;
    // read while empty => read invalid data, keep write pointer in sync
    assign wskip = ren && !wen && data_count == 0;
`else
    assign rskip = 0;
    assign wskip = 0;
`endif // NO_FULL_SKIP

`ifdef FORMAL
    // observers
    wire [ADDR_BITS:0] addr_diff;
    assign addr_diff = waddr >= raddr 
                  ? waddr - raddr 
                  : waddr + MAX_DATA - raddr;

    // tests
    always @(posedge clk) begin
        if (~rst) begin
            // waddr and raddr can only be non zero if reset is low
            w_nreset: cover (waddr || raddr);

            // count never more than max
            a_oflow:  assert (count <= MAX_DATA);
            a_oflow2: assert (waddr < MAX_DATA);

            // count should be equal to the difference between writer and reader address
            a_count_diff: assert (count == addr_diff 
                               || count == MAX_DATA && addr_diff == 0);

            // count should only be able to increase or decrease by 1
            a_counts: assert (count == 0
                           || count == $past(count)
                           || count == $past(count) + 1
                           || count == $past(count) - 1);

            // read/write addresses can only increase (or stay the same)
            a_raddr: assert (raddr == 0
                          || raddr == $past(raddr)
                          || raddr == $past(raddr + 1));
            a_waddr: assert (waddr == 0
                          || waddr == $past(waddr)
                          || waddr == $past(waddr + 1));

            // full and empty work as expected
            a_full:  assert (!full || count == MAX_DATA);
            w_full:  cover  (wen && !ren && count == MAX_DATA-1);
            a_empty: assert (!empty || count == 0);
            w_empty: cover  (ren && !wen && count == 1);

            // reading/writing non zero values
            w_nzero_write: cover (wen && wdata);
            w_nzero_read:  cover (ren && rdata);
        end else begin
            // waddr and raddr are zero while reset is high
            a_reset: assert (!waddr && !raddr);
            w_reset: cover  (rst);

            // outputs are zero while reset is high
            a_zero_out: assert (!empty && !full && !count);
        end
    end

`ifdef VERIFIC
    // if we have verific we can also do the following additional tests
    // read/write enables enable
    ap_raddr2: assert property (@(posedge clk) disable iff (rst) ren |=> $changed(raddr));
    ap_waddr2: assert property (@(posedge clk) disable iff (rst) wen |=> $changed(waddr));

    // read/write needs enable UNLESS full/empty
    ap_raddr3: assert property (@(posedge clk) disable iff (rst) !ren && !full  |=> $stable(raddr));
    ap_waddr3: assert property (@(posedge clk) disable iff (rst) !wen && !empty |=> $stable(waddr));

    // can we corrupt our data?
    w_underfill: cover property (@(posedge clk) disable iff (rst) !wen |=> $changed(waddr));
    // look for an overfill where the value in memory changes
    let d_change = (wdata != rdata);
    w_overfill:  cover property (@(posedge clk) disable iff (rst) !ren && d_change |=> $changed(raddr));
`else // !VERIFIC
    always @(posedge clk) begin
        if (~rst) begin
            // this is less reliable because $past() can sometimes give false
            //  positives in the first cycle
            w_overfill:  cover ($past(rskip) && raddr);
            w_underfill: cover ($past(wskip) && waddr);

        end
    end
`endif // VERIFIC

`endif // FORMAL

endmodule
