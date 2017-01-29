module demo (
  input clk,
  output [5:0] counter
);
  reg [5:0] counter = 0;

  always @(posedge clk) begin
    if (counter == 15)
      counter <= 0;
    else
      counter <= counter + 1;
  end

  assert property (counter < 32);
endmodule
