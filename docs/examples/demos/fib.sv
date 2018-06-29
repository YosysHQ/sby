module fib (
	input clk, pause, start,
	input [3:0] n,
	output reg busy, done,
	output reg [9:0] f
);
	reg [3:0] count;
	reg [9:0] q;

	initial begin
		done = 0;
		busy = 0;
	end

	always @(posedge clk) begin
		done <= 0;
		if (!pause) begin
			if (!busy) begin
				if (start)
					busy <= 1;
				count <= 0;
				q <= 1;
				f <= 0;
			end else begin
				q <= f;
				f <= f + q;
				count <= count + 1;
				if (count == n) begin
					busy <= 0;
					done <= 1;
				end
			end
		end
	end

`ifdef FORMAL
	always @(posedge clk) begin
		if (busy) begin
			assume (!start);
			assume ($stable(n));
		end

		if (done) begin
			case ($past(n))
				0: assert (f == 1);
				1: assert (f == 1);
				2: assert (f == 2);
				3: assert (f == 3);
				4: assert (f == 5);
				5: assert (f == 8);
			endcase
			cover (f == 13);
			cover (f == 144);
			cover ($past(n) == 15);
		end

		assume property (s_eventually !pause);

		if (start && !pause)
			assert property (s_eventually done);
	end
`endif
endmodule
