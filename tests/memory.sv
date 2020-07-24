module testbench (
  input clk, wen,
  input [9:0] addr,
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

  (* anyconst *) reg [9:0] test_addr;
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
  input [9:0] addr,
  input [7:0] wdata,
  output [7:0] rdata
);
  reg [7:0] bank0 [0:255];
  reg [7:0] bank1 [0:255];
  reg [7:0] bank2 [0:255];
  reg [7:0] bank3 [0:255];

  wire [1:0] mem_sel = addr[9:8];
  wire [7:0] mem_addr = addr[7:0];

  always @(posedge clk) begin
    case (mem_sel)
      0: if (wen) bank0[mem_addr] <= wdata;
      1: if (wen) bank1[mem_addr] <= wdata;
      2: if (wen) bank1[mem_addr] <= wdata;  // BUG: Should assign to bank2
      3: if (wen) bank3[mem_addr] <= wdata;
    endcase
  end

  assign rdata =
    mem_sel == 0 ? bank0[mem_addr] :
    mem_sel == 1 ? bank1[mem_addr] :
    mem_sel == 2 ? bank2[mem_addr] :
    mem_sel == 3 ? bank3[mem_addr] : 'bx;
endmodule
