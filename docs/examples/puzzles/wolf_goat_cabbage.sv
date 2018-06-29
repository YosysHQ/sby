// A man needs to cross a river with a wolf, a goat and a cabbage. His boat is only large
// enough to carry himself and one of his three possessions, so he must transport these
// items one at a time. However, if he leaves the wolf and the goat together unattended,
// then the wolf will eat the goat; similarly, if he leaves the goat and the cabbage together
// unattended, then the goat will eat the cabbage. How can the man get across safely with
// his three items?

module wolf_goat_cabbage (input clk, input w, g, c);
	// everyone starts at the 1st river bank
	reg bank_w = 0; // wolf
	reg bank_g = 0; // goat
	reg bank_c = 0; // cabbage
	reg bank_m = 0; // man

	always @(posedge clk) begin
		// maximum one of the control signals must be high
		assume (w+g+c <= 1);

		// we want wolf, goat, and cabbage on the 2nd river bank
		cover (bank_w && bank_g && bank_c);

		// don't leave wolf and goat unattended
		if (bank_w != bank_m) begin
			assume (bank_w != bank_g);
		end

		// don't leave goat and cabbage unattended
		if (bank_g != bank_m) begin
			assume (bank_g != bank_c);
		end

		// man travels and takes the selected item with him
		if (w && (bank_w == bank_m)) bank_w <= !bank_m;
		if (g && (bank_g == bank_m)) bank_g <= !bank_m;
		if (c && (bank_c == bank_m)) bank_c <= !bank_m;
		bank_m <= !bank_m;
	end
endmodule
