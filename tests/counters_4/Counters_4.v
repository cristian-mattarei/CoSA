module Counters_4 #(parameter SIZE = 8)
   (
    input             clk, 
    input             rst, 
    output [(SIZE*2)-1:0] out
    );

   reg [SIZE-1:0] val1;
   reg [(SIZE/2)-1:0] val2;
   reg [(SIZE/2)-1:0] val3;
   reg [(SIZE/4)-1:0] val4;

   reg [1:0] sel;

   wire      clk1;
   wire      clk2;
   wire      clk3;
   wire      clk4;
   
   assign clk1 = (sel == 'd0);
   assign clk2 = (sel == 'd1);
   assign clk3 = (sel == 'd2);
   assign clk4 = (sel == 'd3);
   
   Counter #(.SIZE(SIZE)) counter_1 (.clk (clk1), .rst (rst), .out (val1));
   Counter #(.SIZE(SIZE/2)) counter_2 (.clk (clk2), .rst (rst), .out (val2));
   Counter #(.SIZE(SIZE/2)) counter_3 (.clk (clk3), .rst (rst), .out (val3));
   Counter #(.SIZE(SIZE/4)) counter_4 (.clk (clk4), .rst (rst), .out (val4));
   
   Counter #(.SIZE(2)) counter_clk (.clk (clk), .rst (rst), .out (sel));
   
   Adder4 #(.SIZE(SIZE)) adder (.in1 (val1), .in2 (val2), .in3 (val3), .in4 (val4), .out (out));

endmodule

module Counter #(parameter SIZE = 16) 
   (
    input             clk,
    input             rst,
    output [SIZE-1:0] out
    );

   always @(posedge clk or posedge rst)
     begin
        if (rst)
          out <= 'b0;
        else
          out <= out + 1;
     end

endmodule

module Adder4 #(parameter SIZE = 16) 
   (
    input [SIZE-1:0]  in1, 
    input [(SIZE/2)-1:0]  in2, 
    input [(SIZE/2)-1:0]  in3, 
    input [(SIZE/4)-1:0]  in4, 
    output [(SIZE*2)-1:0] out
    );

   assign out = (in1 + in2 + in3 + in4);
   
endmodule
