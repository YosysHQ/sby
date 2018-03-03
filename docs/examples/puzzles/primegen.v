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
