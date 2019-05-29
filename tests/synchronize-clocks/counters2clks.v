module counters2clks(clk0, clk1, out0, out1);
   input clk0, clk1;
   output reg [15:0] out0 = 0;
   output reg [15:0] out1 = 0;

   always @(posedge clk0) begin
      out0 <= out0 + 16'd1;
   end

   always @(posedge clk1) begin
      out1 <= out1 + 16'd1;
   end

endmodule // counters2clks

