// find a hash collision for DJB2 hash where it visits the same state twice
module djb2hash (input clock);
	(* keep *) rand const reg [31:0] magic;
	(* keep *) rand reg [7:0] inputval;
	(* keep *) reg [31:0] state = 5381;
	(* keep *) integer cnt = 0;

	always @(posedge clock) begin
		state <= ((state << 5) + state) ^ inputval;
		if (state == magic) cnt <= cnt + 1;
		assert (cnt < 2);
	end
endmodule
