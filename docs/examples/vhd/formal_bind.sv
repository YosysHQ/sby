module formal_bind(input clk, rst, up, down, [3:0] count);

    initial assume(rst);

    assert property(@(posedge clk) count != 4'd15);
    cover property(@(posedge clk) count == 4'd10);

endmodule

bind updowncount formal_bind fb_inst(.*);
