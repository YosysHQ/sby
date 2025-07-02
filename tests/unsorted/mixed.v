module test (input CP, CN, input A, B, output reg XP, XN);
	reg [7:0] counter = 0;
	always @* begin
		assume (A || B);
		assume (!A || !B);
		assert (A != B);
		cover (counter == 3 && A);
		cover (counter == 3 && B);
	end
	always @(posedge CP)
		counter <= counter + 1;
	always @(posedge CP)
		XP <= A;
	always @(negedge CN)
		XN <= B;
endmodule
