module demo_counter_abstr (
	input clock, reset,
	input [19:0] counter
);
	default clocking @(posedge clock); endclocking
	default disable iff (reset);

	// make sure the counter doesn't jump over any of the "magic values"
	`demo_counter_abstr_mode property ((counter < 123456) |=> (counter <= 123456));
	`demo_counter_abstr_mode property ((counter < 234567) |=> (counter <= 234567));
	`demo_counter_abstr_mode property ((counter < 345678) |=> (counter <= 345678));
	`demo_counter_abstr_mode property ((counter < 456789) |=> (counter <= 456789));

	// strictly increasing, only allow overflow by visiting the max value
	`demo_counter_abstr_mode property (counter != 20'hfffff |=> $past(counter) < counter);
	`demo_counter_abstr_mode property (counter == 20'hfffff |=> counter == 20'h00000);
endmodule

bind demo demo_counter_abstr demo_counter_abstr_i (.*);
