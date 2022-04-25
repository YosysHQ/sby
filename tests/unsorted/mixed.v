module test (input CP, CN, CX, input A, B, output reg XP, XN, YP, YN);
	always @* begin
		assume (A || B);
		assume (!A || !B);
		assert (A != B);
		cover (A);
		cover (B);
	end
	always @(posedge CP)
		XP <= A;
	always @(negedge CN)
		XN <= B;
	always @(posedge CX)
		YP <= A;
	always @(negedge CX)
		YN <= B;
endmodule
