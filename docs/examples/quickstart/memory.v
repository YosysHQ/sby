module testbench (
  input clk, wen,
  input [15:0] addr,
  input [7:0] wdata,
  output [7:0] rdata
);
  memory uut (
    .clk  (clk  ),
    .wen  (wen  ),
    .addr (addr ),
    .wdata(wdata),
    .rdata(rdata)
  );

  wire [15:0] test_addr = $anyconst;
  reg test_data_valid = 0;
  reg [7:0] test_data;

  always @(posedge clk) begin
    if (addr == test_addr) begin
      if (wen) begin
        test_data <= wdata;
	test_data_valid <= 1;
      end
      if (test_data_valid) begin
        assert(test_data == rdata);
      end
    end
  end
endmodule

module memory (
  input clk, wen,
  input [15:0] addr,
  input [7:0] wdata,
  output [7:0] rdata
);
  reg [7:0] bank0 [0:'h3fff];
  reg [7:0] bank1 [0:'h3fff];
  reg [7:0] bank2 [0:'h3fff];
  reg [7:0] bank3 [0:'h3fff];

  always @(posedge clk) begin
    case (addr[15:14])
      0: if (wen) bank0[addr[13:0]] <= wdata;
      1: if (wen) bank1[addr[13:0]] <= wdata;
      2: if (wen) bank1[addr[13:0]] <= wdata;  // BUG: Should assign to bank2
      3: if (wen) bank3[addr[13:0]] <= wdata;
    endcase
  end

  assign rdata =
    addr[15:14] == 0 ? bank0[addr[13:0]] :
    addr[15:14] == 1 ? bank1[addr[13:0]] :
    addr[15:14] == 2 ? bank2[addr[13:0]] :
    addr[15:14] == 3 ? bank3[addr[13:0]] : 'bx;
endmodule
