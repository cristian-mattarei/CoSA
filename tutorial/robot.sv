// cardinal directions
`define N 0
`define E 1
`define S 2
`define W 3

`define WIDTH 5
`define BOUND_X 10
`define BOUND_Y 10
`define STEP 1

`define EMBEDDED

module UPDATE_LOC(x, y, direction, next_x, next_y);
   parameter WIDTH = `WIDTH;
   parameter STEP = `STEP;

   input [WIDTH-1:0]  x;
   input [WIDTH-1:0]  y;
   input [1:0]        direction;
   output reg [WIDTH-1:0] next_x;
   output reg [WIDTH-1:0] next_y;

   always @* begin
      case(direction)
        `N: begin
           next_x = x;
           next_y = y + `STEP;
        end
        `E: begin
           next_x = x + `STEP;
           next_y = y;
        end
        `S: begin
           next_x = x;
           next_y = y - `STEP;
        end
        `W: begin
           next_x = x - `STEP;
           next_y = y;
        end
      endcase // case (direction)
    end
endmodule // UPDATE_LOC

module robot(clk, rst, direction, x, y, next_x, next_y);
   parameter WIDTH=`WIDTH;
   parameter BOUND_X=`BOUND_X;
   parameter BOUND_Y=`BOUND_Y;

   input clk;
   input rst;
   input [1:0] direction;

   output reg [WIDTH-1:0]  x;
   output reg [WIDTH-1:0]  y;

   output [WIDTH-1:0] next_x;
   output [WIDTH-1:0] next_y;

   UPDATE_LOC ul(.x(x),
                 .y(y),
                 .direction(direction),
                 .next_x(next_x),
                 .next_y(next_y));

   always @(posedge clk) begin
      if (rst) begin
         x <= 0;
         y <= 0;
      end
      else begin
         if (next_x < `BOUND_X)
           x <= next_x;
         if (next_y < `BOUND_Y)
           y <= next_y;
      end
   end // always @ (posedge clk)

`ifdef EMBEDDED
   assert property (@(posedge clk) x < `BOUND_X);
   assert property (@(posedge clk) y < `BOUND_Y);

   // FALSE assertion
   // assert property (@(posedge clk) (!$stable(x) | !$stable(y)));

   // Fixed assertion
   assert property (@(posedge clk) (((x > 0) &&
                                     (x < `BOUND_X - 1) &&
                                     (y > 0) &&
                                     (y < `BOUND_Y - 1)) |->
                                    (!$stable(x) | !$stable(y))));


`endif

endmodule // robot
