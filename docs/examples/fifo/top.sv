// Define our top level fifo entity
module fifo (
    input wen, ren, clk, rst_n,
    input [7:0] wdata,
    output [7:0] rdata,
    output [3:0] count,
    output full, empty
);
    parameter MAX_DATA = 16;

    // internals
    reg [3:0] data_count;
    initial begin
        data_count <= 0;
    end

    // wire up our sub modules
    wire [3:0] waddr, raddr;
    wire wskip, rskip;
    storage #(.MAX_DATA(MAX_DATA)) fifo_storage (
        .wen    (wen  ),
        .ren    (ren  ),
        .clk    (clk  ),
        .rst_n  (rst_n),
        .waddr  (waddr),
        .raddr  (raddr),
        .wdata  (wdata),
        .rdata  (rdata)
    );

    addr_gen #(.MAX_DATA(MAX_DATA)) fifo_writer (
        .en     (wen || wskip),
        .clk    (clk  ),
        .rst_n  (rst_n),
        .addr   (waddr)
    );

    addr_gen #(.MAX_DATA(MAX_DATA)) fifo_reader (
        .en     (ren || rskip),
        .clk    (clk  ),
        .rst_n  (rst_n),
        .addr   (raddr)
    );

    always @(posedge clk or negedge rst_n) begin
        if (~rst_n)
            data_count <= 0;
        else if (wen && !ren && data_count < MAX_DATA-1)
            data_count <= data_count + 1;
        else if (ren && !wen && data_count > 0)
            data_count <= data_count - 1;
        else
            data_count <= data_count;
    end

    assign full  = data_count == MAX_DATA-1;
    assign empty = data_count == 0;
    assign count = data_count;

    // write while full => overwrite oldest data, move read pointer
    assign rskip = wen && !ren && data_count >= MAX_DATA-1;
    // read while empty => read invalid data, keep write pointer in sync
    assign wskip = ren && !wen && data_count == 0;

`ifdef FORMAL
    // observers
    wire [4:0] addr_diff;
    assign addr_diff = waddr >= raddr ? waddr - raddr : waddr + MAX_DATA - raddr;

    // tests should not run through a reset
    // not entirely sure what this actually does
    default clocking @(posedge clk); endclocking
	default disable iff (~rst_n);

    // tests
    always @(posedge clk or negedge rst_n) begin
        // waddr and raddr are zero while reset is low
        ap_reset: assert property (~rst_n |=> !waddr && !raddr);
        wp_reset: cover  property (rst_n);

        // waddr and raddr can only be non zero if reset is high
        ap_nreset: assert property (waddr || raddr |=> $past(rst_n));
        wp_nreset: cover  property (waddr || raddr);

        // count never less than zero, or more than max
        ap_uflow:  assert (count >= 0);
        ap_uflow2: assert (raddr >= 0);
        ap_oflow:  assert (count < MAX_DATA);
        ap_oflow2: assert (waddr < MAX_DATA);

        // count should be equal to the difference between writer and reader address
        ap_count_diff: assert (count == addr_diff);

        // count should only be able to increase or decrease by 1
        ap_counts: assert (count == 0
                        || count == $past(count)
                        || count == $past(count) + 1
                        || count == $past(count) - 1);

        // read/write addresses can only increase (or stay the same)
        ap_raddr:  assert (raddr == 0
                        || raddr == $past(raddr)
                        || raddr == $past(raddr + 1));
        ap_waddr:  assert (waddr == 0
                        || waddr == $past(waddr)
                        || waddr == $past(waddr + 1));

        // read/write enables enable
        ap_raddr2: assert property (ren |=> raddr != $past(raddr));
        ap_waddr2: assert property (wen |=> waddr != $past(waddr));

        // read/write needs enable UNLESS full/empty
        ap_raddr3: assert property (!ren && !full  |=> raddr == $past(raddr));
        ap_waddr3: assert property (!wen && !empty |=> waddr == $past(waddr));

        // full and empty work as expected
        ap_full:  assert property (wen && !ren && count == MAX_DATA-2 |=> full);
        wp_full:  cover  property (wen && !ren && count == MAX_DATA-2);
        ap_empty: assert property (ren && !wen && count == 1 |=> empty);
        wp_empty: cover  property (ren && !wen && count == 1);
        
        // can we corrupt our data?
        ap_overfill:  assert property (wen && full |=> raddr != $past(raddr));
        wp_overfill:  cover  property (wen && full);
        ap_underfill: assert property (ren && empty |=> waddr != $past(waddr));
        wp_underfill: cover  property (ren && empty);
    end

    // assumptions
    always @(posedge clk or negedge rst_n) begin
        // data will change when writing (and only when writing) so we can line up reads with writes
        assume property (wen |=> wdata != $past(wdata));
        assume property (!wen |=> wdata == $past(wdata));
    end
`endif

endmodule
