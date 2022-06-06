// Define our top level fifo entity
module fifo (
    input wen, ren, clk, rst_n,
    input [7:0] wdata,
    output [7:0] rdata,
    output [4:0] count,
    output full, empty
);
    parameter MAX_DATA = 16;

    // internals
    reg [4:0] data_count;
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
        else if (wen && !ren && data_count < MAX_DATA)
            data_count <= data_count + 1;
        else if (ren && !wen && data_count > 0)
            data_count <= data_count - 1;
        else
            data_count <= data_count;
    end

    assign full  = data_count == MAX_DATA;
    assign empty = (data_count == 0) && rst_n;
    assign count = data_count;

    // write while full => overwrite oldest data, move read pointer
    assign rskip = wen && !ren && data_count >= MAX_DATA;
    // read while empty => read invalid data, keep write pointer in sync
    assign wskip = ren && !wen && data_count == 0;

`ifdef FORMAL
    // observers
    wire [4:0] addr_diff;
    assign addr_diff = waddr >= raddr 
                     ? waddr - raddr 
                     : waddr + MAX_DATA - raddr;

    reg init = 0;
    always @(posedge clk) begin
        if (rst_n)
            init <= 1;
        // if init is low we don't care about the value of rst_n
        // if init is high (rst_n has ben high), then rst_n must remain high
        assume (!init || init && rst_n);
    end

    // tests
    always @(posedge clk) begin
        if (rst_n) begin
            // waddr and raddr can only be non zero if reset is high
            w_nreset: cover (waddr || raddr);

            // count never less than zero, or more than max
            a_uflow:  assert (count >= 0);
            a_uflow2: assert (raddr >= 0);
            a_oflow:  assert (count <= MAX_DATA);
            a_oflow2: assert (waddr < MAX_DATA);

            // count should be equal to the difference between writer and reader address
            a_count_diff: assert  (count == addr_diff 
                                || count == MAX_DATA && addr_diff == 0);

            // count should only be able to increase or decrease by 1
            a_counts: assert (count == 0
                            || count == $past(count)
                            || count == $past(count) + 1
                            || count == $past(count) - 1);

            // read/write addresses can only increase (or stay the same)
            a_raddr:  assert (raddr == 0
                            || raddr == $past(raddr)
                            || raddr == $past(raddr + 1));
            a_waddr:  assert (waddr == 0
                            || waddr == $past(waddr)
                            || waddr == $past(waddr + 1));

            // full and empty work as expected
            a_full:  assert (!full || full && count == MAX_DATA);
            w_full:  cover  (wen && !ren && count == MAX_DATA-1);
            a_empty: assert (!empty || empty && count == 0);
            w_empty: cover  (ren && !wen && count == 1);
            
            // can we corrupt our data?
            w_overfill:  cover ($past(rskip) && raddr);
            w_underfill: cover ($past(wskip) && waddr);
        end else begin
            // waddr and raddr are zero while reset is low
            a_reset: assert (!waddr && !raddr);
            w_reset: cover  (~rst_n);

            // outputs are zero while reset is low
            a_zero_out: assert (!empty && !full && !count);
        end
    end

`ifdef USE_VERIFIC
    // if we have verific we can also do the following additional tests
    always @(posedge clk) begin
        if (rst_n) begin
            // read/write enables enable
            ap_raddr2: assert property (ren |=> $changed(raddr));
            ap_waddr2: assert property (wen |=> $changed(waddr));

            // read/write needs enable UNLESS full/empty
            ap_raddr3: assert property (!ren && !full  |=> $stable(raddr));
            ap_waddr3: assert property (!wen && !empty |=> $stable(waddr));
                    
            // can we corrupt our data?
            ap_overfill:  assert property (wen && full  |=> $changed(raddr));
            ap_underfill: assert property (ren && empty |=> $changed(waddr));
            
            // change data when writing (and only when writing) so we can line
            // up reads with writes
            assume property (wen |=> $changed(wdata));
            assume property (!wen |=> $stable(wdata));
        end
    end
`else // !USE_VERIFIC
    // without verific we are more limited in describing the above assumption
    always @(posedge clk) begin
        assume ((wen && wdata != $past(wdata)) 
            || (!wen && wdata == $past(wdata)));
    end
`endif // USE_VERIFIC

`endif // FORMAL

endmodule
