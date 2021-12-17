module example(clk, state); 
	input logic clk;
	output logic [4:0] state = 27;

	always_ff @(posedge clk) state <= (5'd 2 * state - 5'd 1) ^ (state & 5'd 7);

	let p0 = (state != 0);
	let p1 = (state inside {28, 19, 6, 13});
	let p2 = (state inside {28, 19, 6, 13, 22, 27});
	let p3 = (state[0] & state[1]) ^ state[2];

`ifdef ASSERT_PX
	always_comb assert (`ASSERT_PX);
`endif
`ifdef ASSUME_PX
	always_comb assume (`ASSUME_PX);
`endif
endmodule
