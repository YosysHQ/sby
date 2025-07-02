module demo (
  input clk,
  output reg [5:0] counter
);
  initial counter = 0;

  always @(posedge clk) begin
    if (counter == 15)
      counter <= 0;
    else
      counter <= counter + 1;
  end

`ifdef FORMAL
  always @(posedge clk) begin
    assert (1);
    assert (counter < 7);
    assert (0);
  end
`endif
endmodule
