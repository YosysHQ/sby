module primegen;
	wire [31:0] prime = $anyconst;
	wire [15:0] factor = $allconst;

	always @* begin
		if (1 < factor && factor < prime)
			assume((prime % factor) != 0);
		assume(prime > 1000000000);
		cover(1);
	end
endmodule

module primes;
	parameter [8:0] offset = 500;
	wire [8:0] prime1 = $anyconst;
	wire [9:0] prime2 = prime1 + offset;
	wire [4:0] factor = $allconst;

	always @* begin
		if (1 < factor && factor < prime1)
			assume((prime1 % factor) != 0);
		if (1 < factor && factor < prime2)
			assume((prime2 % factor) != 0);
		assume(1 < prime1);
		cover(1);
	end
endmodule
