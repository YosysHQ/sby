module test(input [7:0] I, output O);
assign O = ^I;

always @(*) begin
cover(O==1'b0);
cover(O==1'b1);
end
endmodule
