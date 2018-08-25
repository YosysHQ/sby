// You are given an 8 litre bucket of water, and two empty buckets which can
// contain 5 and 3 litre respectively. You are required to divide the water into
// two by pouring water between buckets (that is, to end up with 4 litre in the 8
// litre bucket, and 4 litre in the 5 litre bucket).
//
// Inspired by:
// https://github.com/DennisYurichev/random_notes/blob/master/Z3/pour.py

module pour_853_to_4 (
	input clk,
	input [1:0] src, dst
);
	reg [3:0] state [0:2];
	reg [3:0] max_amount [0:2];
	reg [3:0] xfer_amount;

	initial begin
		state[0] = 8;
		state[1] = 0;
		state[2] = 0;

		max_amount[0] = 8;
		max_amount[1] = 5;
		max_amount[2] = 3;
	end

	always @* begin
		assume (src < 3);
		assume (dst < 3);
		assume (src != dst);

		if (state[src] > (max_amount[dst] - state[dst]))
			xfer_amount = max_amount[dst] - state[dst];
		else
			xfer_amount = state[src];

		cover (state[0] == 4 && state[1] == 4);
	end

	always @(posedge clk) begin
		state[src] <= state[src] - xfer_amount;
		state[dst] <= state[dst] + xfer_amount;
	end
endmodule
