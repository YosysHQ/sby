module demo (
	input clock,
	input reset,
	output A, B, C, D
);
	reg [19:0] counter = 0;

	always @(posedge clock) begin
		if (reset)
			counter <= 0;
		else
			counter <= counter + 20'd 1;
	end

	assign A = counter == 123456;
	assign B = counter == 234567;
	assign C = counter == 345678;
	assign D = counter == 456789;
endmodule
