// A person needs to cross a river with a wolf, a goat and a cabbage. Their boat is only large
// enough to carry themselves and one of their three possessions, so they must transport these
// items one at a time. However, if they leave the wolf and the goat together unattended,
// then the wolf will eat the goat; similarly, if they leave the goat and the cabbage together
// unattended, then the goat will eat the cabbage. How can the person get across safely with
// their three items?

module wolf_goat_cabbage (input clk, input w, g, c);
	// everyone starts at the 1st river bank
	reg bank_w = 0; // wolf
	reg bank_g = 0; // goat
	reg bank_c = 0; // cabbage
	reg bank_p = 0; // person

	always @(posedge clk) begin
		// person travels and takes the selected item with them
		bank_p <= !bank_p;
		if (w && (bank_w == bank_p)) bank_w <= !bank_p;
		if (g && (bank_g == bank_p)) bank_g <= !bank_p;
		if (c && (bank_c == bank_p)) bank_c <= !bank_p;

		// maximum one of the control signals must be high
		assume (w+g+c <= 1);

		// we want wolf, goat, and cabbage on the 2nd river bank
		cover(bank_w == 1 && bank_g == 1 && bank_c == 1);

		// don't leave wolf and goat unattended
		if (bank_w != bank_p) begin
			assume (bank_w != bank_g);
		end

		// don't leave goat and cabbage unattended
		if (bank_g != bank_p) begin
			assume (bank_g != bank_c);
		end
	end
endmodule
