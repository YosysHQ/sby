module test (
	input clk, a
);
	reg [7:0] counter = 0;

	always @(posedge clk) begin
		counter <= counter + 1;
	end

	always @(posedge clk) begin
		assert(0);
		if (counter == 3 || counter == 7) begin
			assert(a); // step 3,7
		end
		if (counter == 5) begin
			assert(a); // step 5
		end
		if (counter == 7) begin
			assert(a); // step 7
		end
		assert(1);
	end
endmodule
