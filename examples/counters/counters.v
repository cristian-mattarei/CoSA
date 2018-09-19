module Counters #(parameter SIZE = 8)
   (
    input             clk1, 
    input             clk2, 
    input             rst, 
    output [SIZE-1:0] out
    );


   initial begin
      clk1 = 0;
      clk2 = 1;
      forever begin
         #1 clk1 = !clk1;
         #1 clk2 = !clk2;
      end
   end
   
   reg [SIZE-1:0] val1;
   reg [SIZE-1:0] val2;

   reg [SIZE-1:0] init1;
   reg [SIZE-1:0] init2;

   assign init1 = 'd0;
   assign init2 = 'd1;
   
   Counter #(.SIZE(SIZE)) counter_1 (.clk (clk1), .rst (rst), .out (val1), .initval (init1));
   Counter #(.SIZE(SIZE)) counter_2 (.clk (clk2), .rst (rst), .out (val2), .initval (init2));
   Adder #(.SIZE(SIZE)) adder (.in1 (val1), .in2 (val2), .out (out));
   Reset #(.SIZE(SIZE)) reset (.clk1 (clk1), .clk2 (clk2), .rst (rst), .in (out) );

endmodule

module Counter #(parameter SIZE = 16) 
   (
    input             clk,
    input             rst,
    input [SIZE-1:0]  initval,
    output [SIZE-1:0] out
    );

   initial out = 'b0;
   
   always @(posedge clk or posedge rst)
     begin
        if (rst)
          out <= initval;
        else
          out <= out + 1;
     end

endmodule

module Adder #(parameter SIZE = 16) 
   (
    input [SIZE-1:0]  in1, 
    input [SIZE-1:0]  in2, 
    output [SIZE-1:0] out
    );

   assign out = in1 + in2;
   
endmodule


module Reset #(parameter SIZE = 16) 
   (
    input             clk1, 
    input             clk2, 
    output             rst, 
    input [SIZE-1:0]  in
    );

   always @ (posedge clk1 or posedge clk2)
        if (in > 'd10)
          begin
             rst = 0;
             rst <= 1;
          end
        else
          begin
             rst <= 0;
          end

endmodule
