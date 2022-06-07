module dpmem (
	input            rc,
	input      [3:0] ra,
	output reg [3:0] rd,

	input            wc,
	input            we,
	input      [3:0] wa,
	input      [3:0] wd
);
	reg [3:0] mem [0:15];

	always @(posedge rc) begin
		rd <= mem[ra];
	end

	always @(posedge wc) begin
		if (we) mem[wa] <= wd;
	end
endmodule

module top (
	input            rc,
	input      [3:0] ra,
	output     [3:0] rd,

	input            wc,
	input            we,
	input      [3:0] wa,
	input      [3:0] wd
);
	dpmem uut (
		.rc(rc),
		.ra(ra),
		.rd(rd),
		.wc(wc),
		.we(we),
		.wa(wa),
		.wd(wd)
	);

	reg shadow_valid = 0;
	reg [3:0] shadow_data;
	(* anyconst *) reg [3:0] shadow_addr;

	reg init = 1;
	(* gclk *) reg gclk;

	always @(posedge gclk) begin
		if (!init) begin
			assume ($stable(rc) || $stable(wc));

			if ($rose(rc) && shadow_valid && shadow_addr == $past(ra)) begin
				assert (shadow_data == rd);
			end

			if ($rose(wc) && $past(we) && shadow_addr == $past(wa)) begin
				shadow_data <= $past(wd);
				shadow_valid <= 1;
			end
		end

		init <= 0;
	end
endmodule
