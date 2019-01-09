module counter #(parameter SIZE = 4)
   (
    input             clk,
    input             rst_n,
    input [SIZE-1:0]  initval,
    output reg [SIZE-1:0] out
    );

//   initial out = 'b0;

   always @(posedge clk or negedge rst_n)
     begin
        if (!rst_n)
          out <= initval;
        else
          out <= out + 1;
     end

//   assert property (@(posedge clk) out != 2'b11);

endmodule
