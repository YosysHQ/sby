module testbench (
  input clk,
  input reset,
  input [7:0] din,
  output reg [7:0] dout
);
  demo uut (
    .clk  (clk  ),
    .reset(reset),
    .din  (din  ),
    .dout (dout ),
  );

  initial assume (reset);
  assert property (reset || !dout[1:0]);
endmodule

module demo (
  input clk,
  input reset,
  input [7:0] din,
  output reg [7:0] dout
);
  reg [7:0] buffer;
  reg [2:0] state;

  always @(posedge clk) begin
    if (reset) begin
      dout <= 0;
      state <= 0;
    end else
    case (state)
      3'b 001: begin
        buffer <= din;
	state <= 1;
      end
      3'b 010: begin
        if (buffer[1:0])
	  buffer <= buffer + 1;
	else
	  state <= 2;
      end
      3'b 100: begin
        dout <= dout + buffer;
	state <= 0;
      end
    endcase
  end
endmodule
