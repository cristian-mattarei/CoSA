module pipelined_counter(clk, rst, out);
   input clk, rst;
   output reg [15:0] out;

   reg [15:0] out1, out2, out3;

   always @(posedge clk) begin
      if(rst) begin
         out <= 0;
         out1 <= 1;
         out2 <= 2;
         out3 <= 3;
      end
      else begin
         out <= out1;
         out1 <= out2;
         out2 <= out3;
         out3 <= out3 + 1;
      end
   end

endmodule // pipelined_counter
