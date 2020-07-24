module test(
  input clk,
  input [7:0] data
  );

localparam MAX_COUNT = 8'd111;
reg [7:0] count = 8'd0;
reg [7:0] margin = MAX_COUNT;

always @ (posedge clk) begin
  if (data > margin) begin
    count <= 8'd0;
    margin <= MAX_COUNT;
  end else begin
    count <= count + data;
    margin <= margin - data;
  end

  assume (data < 8'd40);
  assert (count <= MAX_COUNT);
  cover (count == 8'd42);
  cover (count == 8'd111);
end

endmodule
