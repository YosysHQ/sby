module demo (
  input clk,
  output [5:0] counter
);
  reg [5:0] counter = 0;

  always @(posedge clk) begin
    if (counter == 50)
      counter <= 0;
    else
      counter <= counter + 1;
  end

`ifdef FORMAL
  always @(posedge clk) begin
    assert (counter < 32);
  end
`endif
endmodule
