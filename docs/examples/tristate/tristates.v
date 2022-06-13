`default_nettype none
module module1 (input wire active, output wire tri_out);
    assign tri_out = active ? 1'b0 : 1'bz;
endmodule

module module2 (input wire active, output wire tri_out);
    assign tri_out = active ? 1'b0 : 1'bz;
endmodule

module top_pass (input wire clk, input wire active1, output wire out);
    module1 module1 (.active(active1), .tri_out(out));
    module2 module2 (.active(!active1), .tri_out(out));
endmodule

module top_fail (input wire clk, input wire active1, input wire active2, output wire out);
    module1 module1 (.active(active1), .tri_out(out));
    module2 module2 (.active(active2), .tri_out(out));
endmodule
