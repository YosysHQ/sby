module prv32fmcmp (
	input         clock,
	input         resetn,
	output        mem_valid_a, mem_valid_b,
	output        mem_instr_a, mem_instr_b,
	input         mem_ready_a, mem_ready_b,
	output [31:0] mem_addr_a, mem_addr_b,
	output [31:0] mem_wdata_a, mem_wdata_b,
	output [ 3:0] mem_wstrb_a, mem_wstrb_b,
	input  [31:0] mem_rdata_a, mem_rdata_b
);
	picorv32 #(
		.REGS_INIT_ZERO(1),
		.COMPRESSED_ISA(1)
	) prv32_a (
		.clk       (clock      ),
		.resetn    (resetn     ),
		.mem_valid (mem_valid_a),
		.mem_instr (mem_instr_a),
		.mem_ready (mem_ready_a),
		.mem_addr  (mem_addr_a ),
		.mem_wdata (mem_wdata_a),
		.mem_wstrb (mem_wstrb_a),
		.mem_rdata (mem_rdata_a)
	);

	picorv32 #(
		.REGS_INIT_ZERO(1),
		.COMPRESSED_ISA(1)
	) prv32_b (
		.clk       (clock      ),
		.resetn    (resetn     ),
		.mem_valid (mem_valid_b),
		.mem_instr (mem_instr_b),
		.mem_ready (mem_ready_b),
		.mem_addr  (mem_addr_b ),
		.mem_wdata (mem_wdata_b),
		.mem_wstrb (mem_wstrb_b),
		.mem_rdata (mem_rdata_b)
	);

	reg [31:0] rom [0:255];

	integer mem_access_cnt_a = 0;
	integer mem_access_cnt_b = 0;

	always @* begin
		assume(resetn == !$initstate);

		if (resetn) begin
			// only consider programs without data memory read/write
			if (mem_valid_a) assume(mem_instr_a);
			if (mem_valid_b) assume(mem_instr_b);

			// when the access cnt matches, the addresses must match
			if (mem_valid_a && mem_valid_b && mem_access_cnt_a == mem_access_cnt_b) begin
				assert(mem_addr_a == mem_addr_b);
			end

			// hook up to memory
			assume(mem_rdata_a == rom[mem_addr_a[9:2]]);
			assume(mem_rdata_b == rom[mem_addr_b[9:2]]);
		end

		// it will pass when this is enabled
		//assume(mem_ready_a == mem_ready_b);
	end

	always @(posedge clock) begin
		mem_access_cnt_a <= mem_access_cnt_a + (resetn && mem_valid_a && mem_ready_a);
		mem_access_cnt_b <= mem_access_cnt_b + (resetn && mem_valid_b && mem_ready_b);
	end
endmodule
