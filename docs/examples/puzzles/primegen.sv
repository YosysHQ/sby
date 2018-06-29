module primegen;
	(* anyconst *) reg [31:0] prime;
	(* allconst *) reg [15:0] factor;

	always @* begin
		if (1 < factor && factor < prime)
			assume ((prime % factor) != 0);
		assume (prime > 1000000000);
		cover (1);
	end
endmodule

module primes;
	parameter [8:0] offset = 500;
	(* anyconst *) reg [8:0] prime1;
	wire [9:0] prime2 = prime1 + offset;
	(* allconst *) reg [4:0] factor;

	always @* begin
		if (1 < factor && factor < prime1)
			assume ((prime1 % factor) != 0);
		if (1 < factor && factor < prime2)
			assume ((prime2 % factor) != 0);
		assume (1 < prime1);
		cover (1);
	end
endmodule
