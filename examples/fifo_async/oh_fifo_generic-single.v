//#############################################################################
//# Function: Generic Async FIFO                                              #
//# Based on article by Clifford Cummings,                                    #
//  "Simulation and Synthesis Techniques for Asynchronous FIFO Design"        #
//# (SNUG2002)                                                                #
//#############################################################################
//# Author:   Andreas Olofsson                                                #
//# License:  MIT (see LICENSE file in OH! repository)                        # 
//#############################################################################

module oh_fifo_generic #(parameter DW        = 104,      // FIFO width
			 parameter DEPTH     = 32,       // FIFO depth (entries)
			 parameter PROG_FULL = (DEPTH/2),// full threshold   
			 parameter AW = $clog2(DEPTH)    // read count width
			 )
   (
    input 	    nreset, // asynch active low reset for wr_clk
    input 	    wr_clk, // write clock   
    input 	    wr_en, // write enable
    input [DW-1:0]  din, // write data
    input 	    rd_clk, // read clock   
    input 	    rd_en, // read enable
    output [DW-1:0] dout, // read data
    output 	    empty, // fifo is empty
    output 	    full, // fifo is full
    output 	    prog_full, // fifo is "half empty"
    output [AW-1:0] rd_count, // NOT IMPLEMENTED 
    output [AW-1:0] wr_count // NOT IMPLEMENTED
    );

   //regs 
   reg [AW:0]    wr_addr;       // extra bit for wraparound comparison
   reg [AW:0] 	 wr_addr_ahead; // extra bit for wraparound comparison   
   reg [AW:0] 	 rd_addr;  
   wire [AW:0] 	 rd_addr_gray;
   wire [AW:0] 	 wr_addr_gray;
   wire [AW:0] 	 rd_addr_gray_sync;
   wire [AW:0] 	 wr_addr_gray_sync;
   wire [AW:0] 	 rd_addr_sync;
   wire [AW:0] 	 wr_addr_sync;
   wire 	 wr_nreset;
   wire 	 rd_nreset;
   
   //###########################
   //# Full/empty indicators
   //###########################

   // uses one extra bit for compare to track wraparound pointers 
   // careful clock synchronization done using gray codes
   // could get rid of gray2bin for rd_addr_sync... 
   
   // fifo indicators
   assign empty    =  (rd_addr_gray[AW:0] == wr_addr_gray_sync[AW:0]);

   // fifo full
   assign full     =  (wr_addr[AW-1:0] == rd_addr_sync[AW-1:0]) &
		      (wr_addr[AW]     != rd_addr_sync[AW]);


   // programmable full
   assign prog_full = (wr_addr_ahead[AW-1:0] == rd_addr_sync[AW-1:0]) &
		      (wr_addr_ahead[AW]     != rd_addr_sync[AW]);

   //###########################
   //# Reset synchronizers
   //###########################

   oh_rsync wr_rsync (.nrst_out (wr_nreset),
	     .clk      (wr_clk), 
	     .nrst_in	(nreset));

   oh_rsync rd_rsync (.nrst_out (rd_nreset),
	     .clk      (rd_clk), 
	     .nrst_in	(nreset));
   
   //###########################
   //#write side address counter
   //###########################

   always @ ( posedge wr_clk or negedge wr_nreset) 
     if(!wr_nreset) 
       wr_addr[AW:0]  <= 'b0;
     else if(wr_en) 
       wr_addr[AW:0]  <= wr_addr[AW:0]  + 'd1;

   //address lookahead for prog_full indicator
   always @ (posedge wr_clk or negedge wr_nreset)
     if(!wr_nreset)
       wr_addr_ahead[AW:0] <= 'b0;   
     else if(~prog_full)
       wr_addr_ahead[AW:0] <= wr_addr[AW:0]  + PROG_FULL;

   //###########################
   //# Synchronize to read clk
   //###########################

   // convert to gray code (only one bit can toggle)
   oh_bin2gray #(.DW(AW+1))
   wr_b2g (.out    (wr_addr_gray[AW:0]),
	   .in	   (wr_addr[AW:0]));
   
   // synchronize to read clock
   oh_dsync wr_sync[AW:0] (.dout (wr_addr_gray_sync[AW:0]),
        		   .clk  (rd_clk),
        		   .nreset(rd_nreset),
        		   .din  (wr_addr_gray[AW:0]));
   
   //###########################
   //#read side address counter
   //###########################

   always @ ( posedge rd_clk or negedge rd_nreset) 
     if(!rd_nreset) 
       rd_addr[AW:0] <= 'd0;   
     else if(rd_en) 
       rd_addr[AW:0] <= rd_addr[AW:0] + 'd1;

   //###########################
   //# Synchronize to write clk
   //###########################
   
   //covert to gray (can't have multiple bits toggling)
   oh_bin2gray #(.DW(AW+1))
   rd_b2g (.out   (rd_addr_gray[AW:0]),
	   .in	  (rd_addr[AW:0]));
   
   //synchronize to wr clock
   oh_dsync  rd_sync[AW:0] (.dout   (rd_addr_gray_sync[AW:0]),
        		    .clk    (wr_clk),
        		    .nreset (wr_nreset),
        		    .din    (rd_addr_gray[AW:0]));
   
   //convert back to binary (for ease of use, rd_count)
   oh_gray2bin #(.DW(AW+1))
   rd_g2b (.out (rd_addr_sync[AW:0]),
	   .in (rd_addr_gray_sync[AW:0]));
   
   //###########################
   //#dual ported memory
   //###########################
   oh_memory_dp  #(.DW(DW),
		   .DEPTH(DEPTH))
   fifo_mem(// Outputs
	    .rd_dout	(dout[DW-1:0]),
	    // Inputs
	    .wr_clk	(wr_clk),
	    .wr_en	(wr_en),
	    .wr_wem	({(DW){1'b1}}),
	    .wr_addr	(wr_addr[AW-1:0]),
	    .wr_din	(din[DW-1:0]),
	    .rd_clk	(rd_clk),
	    .rd_en	(rd_en),
	    .rd_addr	(rd_addr[AW-1:0]));
   
endmodule // oh_fifo_generic
		    

//#############################################################################
//# Function: Reset synchronizer (async assert, sync deassert)                #
//#############################################################################
//# Author:   Andreas Olofsson                                                #
//# License:  MIT (see LICENSE file in OH! repository)                        # 
//#############################################################################
module oh_rsync #(parameter PS = 2          // number of sync stages
		  )
   (
    input  clk,
    input  nrst_in,
    output nrst_out
    );

	   reg [PS-1:0] sync_pipe;   
	   always @ (posedge clk or negedge nrst_in)		 
	     if(!nrst_in)
	       sync_pipe[PS-1:0] <= 'b0;
	     else
	       sync_pipe[PS-1:0] <= {sync_pipe[PS-2:0],1'b1};	      	      
	   assign nrst_out = sync_pipe[PS-1];
      
endmodule // oh_rsync

//#############################################################################
//# Function: Binary to gray encoder                                          #
//#############################################################################
//# Author:   Andreas Olofsson                                                #
//# License:  MIT (see LICENSE file in OH! repository)                        # 
//#############################################################################

module oh_bin2gray #(parameter DW = 32 // width of data inputs
		     ) 
   (
    input [DW-1:0]  in, //binary encoded input
    output [DW-1:0] out //gray encoded output
    );
   
   reg [DW-1:0]    gray; 
   wire [DW-1:0]   bin;

   integer 	   i;   

   assign bin[DW-1:0]  = in[DW-1:0];
   assign out[DW-1:0]  = gray[DW-1:0];
  
   always @*
     begin
	gray[DW-1] = bin[DW-1];   
	for (i=0; i<(DW-1); i=i+1)
	  gray[i] = bin[i] ^ bin[i+1];	      
     end
   
endmodule // oh_bin2gray
//#############################################################################
//# Function: Clock synchronizer                                              #
//#############################################################################
//# Author:   Andreas Olofsson                                                #
//# License:  MIT (see LICENSE file in OH! repository)                        # 
//#############################################################################

// added by Makai

module oh_dsync  #(parameter PS    = 2,        // number of sync stages
		   parameter DELAY = 0        // random delay
		   )
   (
    input  clk, // clock
    input  nreset, // clock
    input  din, // input data
    output dout    // synchronized data
    );
   
	   reg [PS:0]   sync_pipe; 
	   always @ (posedge clk or negedge nreset)		 
	     if(!nreset)
	       sync_pipe[PS:0] <= 'b0;
	     else
	       sync_pipe[PS:0] <= {sync_pipe[PS-1:0],din};	      	      
	   // drive randomize delay from testbench
	   assign dout = (DELAY & sync_pipe[PS]) |  //extra cycle
			 (~DELAY & sync_pipe[PS-1]); //default
   
endmodule // oh_dsync


//#############################################################################
//# Function: Gray to binary encoder                                          #
//#############################################################################
//# Author:   Andreas Olofsson                                                #
//# License:  MIT (see LICENSE file in OH! repository)                        # 
//#############################################################################

module oh_gray2bin #(parameter DW = 32) // width of data inputs
   (
    input [DW-1:0]  in,  //gray encoded input
    output [DW-1:0] out  //binary encoded output
    );
   
   reg [DW-1:0]     bin;
   wire [DW-1:0]    gray;
   
   integer 	   i,j;

   assign gray[DW-1:0] = in[DW-1:0];
   assign out[DW-1:0]  = bin[DW-1:0];

   always @*
     begin
	bin[DW-1] = gray[DW-1];   
	for (i=0; i<(DW-1); i=i+1)
	  begin
	     bin[i] = 1'b0;	
	     for (j=i; j<DW; j=j+1)
	       bin[i] = bin[i] ^ gray [j];
	  end
     end

endmodule // oh_gray2bin



//#############################################################################
//# Function: Dual Port Memory                                                #
//#############################################################################
//# Author:   Andreas Olofsson                                                #
//# License:  MIT (see LICENSE file in OH! repository)                        # 
//#############################################################################

module oh_memory_dp # (parameter DW    = 104,      //memory width
		       parameter DEPTH = 32,       //memory depth
		       parameter PROJ  = "",       //project name
		       parameter MCW   = 8,         //repair/config vector width
		       parameter AW    = $clog2(DEPTH) // address bus width
		       ) 
   (// Memory interface (dual port)
    input           wr_clk, //write clock
    input           wr_en, //write enable
    input [DW-1:0]  wr_wem, //per bit write enable
    input [AW-1:0]  wr_addr,//write address
    input [DW-1:0]  wr_din, //write data
    input           rd_clk, //read clock
    input           rd_en, //read enable
    input [AW-1:0]  rd_addr,//read address
    output [DW-1:0] rd_dout);
 //,//read output data
    // Power/repair (ASICs)
    // input 	    shutdown, // shutdown signal from always on domain   
    // input [MCW-1:0] memconfig, // generic memory config      
    // input [MCW-1:0] memrepair, // repair vector
    // // BIST interface (ASICs)
    // input 	    bist_en, // bist enable
    // input 	    bist_we, // write enable global signal   
    // input [DW-1:0]  bist_wem, // write enable vector
    // input [AW-1:0]  bist_addr, // address
    // input [DW-1:0]  bist_din  // data input
    // );

	   oh_memory_ram #(.DW(DW),
			   .DEPTH(DEPTH))	     
	   memory_dp (//read port
		      .rd_dout	(rd_dout[DW-1:0]),
		      .rd_clk	(rd_clk),
		      .rd_en	(rd_en),
		      .rd_addr	(rd_addr[AW-1:0]),
		      //write port
		      .wr_en	(wr_en),
		      .wr_clk	(wr_clk),
		      .wr_addr	(wr_addr[AW-1:0]),
		      .wr_wem	(wr_wem[DW-1:0]),
		      .wr_din	(wr_din[DW-1:0]));


      
endmodule // oh_memory_dp



//#############################################################################
//# Function: Generic RAM memory                                              #
//#############################################################################
//# Author:   Andreas Olofsson                                                #
//# License:  MIT  (see LICENSE file in OH! repository)                       # 
//#############################################################################

module oh_memory_ram  # (parameter DW    = 104,           //memory width
			 parameter DEPTH = 32,            //memory depth
			 parameter AW    = $clog2(DEPTH)  // address width  
			 ) 
   (// read-port
    input 		rd_clk,// rd clock
    input 		rd_en, // memory access
    input [AW-1:0] 	rd_addr, // address
    output reg [DW-1:0] rd_dout, // data output   
    // write-port
    input 		wr_clk,// wr clock
    input 		wr_en, // memory access
    input [AW-1:0] 	wr_addr, // address
    input [DW-1:0] 	wr_wem, // write enable vector    
    input [DW-1:0] 	wr_din // data input
    );
   
   reg [DW-1:0]        ram    [DEPTH-1:0];  
   integer 	       i;
      
   //registered read port
   always @ (posedge rd_clk)
     if(rd_en)       
       rd_dout[DW-1:0] <= ram[rd_addr[AW-1:0]];
   
   //write port with vector enable
   always @(posedge wr_clk)    
     for (i=0;i<DW;i=i+1)
       if (wr_en & wr_wem[i]) 
         ram[wr_addr[AW-1:0]][i] <= wr_din[i];
  
endmodule // oh_memory_ram





  
     

