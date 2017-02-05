module top (
	input clk,
	input [7:0] din
);
	reg [31:0] state = 0;

	always @(posedge clk) begin
		state <= ((state << 5) + state) ^ din;
	end

	cover property (state == 'd 12345678);
	cover property (state == 'h 12345678);
endmodule
