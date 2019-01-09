module FF(rst, clk, en, D, Q);
   parameter WIDTH = 1;
   parameter INIT  = 0;

   input wire                rst;
   input wire                clk;
   input wire                en;
   input wire [WIDTH-1:0]    D;

   output reg [WIDTH-1:0]    Q = INIT;

   always @ (posedge clk) begin
      if (rst) begin
         Q <= INIT;
      end
      else if(en) begin
         Q <= D;
      end
   end
endmodule

module fifo(clk, rst, push, pop, data_in,
            full, empty, data_out);
  parameter WIDTH = 8;
  parameter DEPTH = 8;
  parameter PTRWID = $clog2(DEPTH) + 1;

  input wire clk;
  input wire rst;
  input wire push;
  input wire pop;
  input wire [WIDTH-1:0] data_in;

  output wire full;
  output wire empty;
  output wire [WIDTH-1:0] data_out;

  wire clkEn = push | pop | rst;

  //************** wrPtr logic *****************//

 (* keep *)
  logic [PTRWID-1:0] wrPtr;
  wire  [PTRWID-1:0] wrPtrNxt;

  assign wrPtrNxt = rst ? {PTRWID{1'b0}} : wrPtr + {{(PTRWID-1){1'b0}}, push};

  FF #(.WIDTH(PTRWID)) ff_wrPtr (.rst(rst),
				                 .clk(clk),
                                 .en(clkEn),
                        	     .D(wrPtrNxt),
                        	     .Q(wrPtr)
  				                 );

  //************** rdPtr logic ****************//

  (* keep *)
  logic [PTRWID-1:0] rdPtr;
  wire  [PTRWID-1:0] rdPtrNxt;

  assign rdPtrNxt = rst ? {PTRWID{1'b0}} : rdPtr + {{(PTRWID-1){1'b0}}, pop};

  FF #(.WIDTH(PTRWID)) ff_rdPtr (.rst(rst),
				                 .clk(clk),
                                 .en(clkEn),
                                 .D(rdPtrNxt),
                                 .Q(rdPtr));

  //************** empty and full logic ********//
  assign empty = rdPtr == wrPtr;
  assign full = (rdPtr[PTRWID-2:0] == wrPtr[PTRWID-2:0]) & (rdPtr[PTRWID-1] != wrPtr[PTRWID-1]);

  //************** latch entries ***************//

`ifdef ARRAY
   reg [WIDTH-1:0]   entries [DEPTH-1:0];
   wire [WIDTH-1:0]  input_data;

   assign input_data = push ? data_in : entries[wrPtr[PTRWID-2:0]];

   always @(posedge clk) begin
	    entries[wrPtr[PTRWID-2:0]] <= input_data;
   end
`else
  wire [WIDTH-1:0] entries [DEPTH-1:0];
  generate
    genvar i;
    for(i = 0; i < DEPTH; i = i + 1) begin : entry_gen
      FF #(.WIDTH(WIDTH)) ff_entry_inst(.rst(rst),
					                    .clk(clk),
                                        .en(push & (wrPtr[PTRWID-2:0] == i)),
                                        .D(data_in),
                                        .Q(entries[i])
      				                    );
    end
  endgenerate
`endif



  //******************** output *******************//
  assign data_out = entries[rdPtr[PTRWID-2:0]];

`ifdef FORMAL
 `ifdef SANITY
   assert property ((rdPtr[2:0] != 'd6) | (data_out != 'd5));
 `endif
`endif


endmodule
