module demo_props (
	input clock, reset,
	input A, B, C, D
);
	default clocking @(posedge clock); endclocking
	default disable iff (reset);

	assert property (A |-> !{B,C,D} [*] ##1 B);
	assert property (B |-> !{A,C,D} [*] ##1 C);
	assert property (C |-> !{A,B,D} [*] ##1 D);
	assert property (D |-> !{A,B,C} [*] ##1 A);

	cover property (A ##[+] B ##[+] C ##[+] D ##[+] A);
endmodule

bind demo demo_props demo_props_i (.*);
