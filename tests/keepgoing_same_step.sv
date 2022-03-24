module test (
	input clk, a
);
	reg [7:0] counter = 0;

	always @(posedge clk) begin
		counter <= counter + 1;
	end

	always @(posedge clk) begin
		if (counter == 3) begin
			assert(a);
			assert(!a);
			assert(0);
		end
	end
endmodule
