// =======================================================================
//   Filename:     EXEC_BFM.sv
//   Description:  Bus functional model for the Memory unit for use in 
//		   		   the IFD unit level validation
//
//   Created by:   Rohit Kulkarni
//   Date:         May 24, 2015
//
// =======================================================================

`include "pdp8_pkg.sv"
import pdp8_pkg::*;

module memory_bfm
(
   // Global input
   input clk,

   //IFU interface signals	
   input                    ifu_rd_req,
   input  [`ADDR_WIDTH-1:0] ifu_rd_addr,
   output reg [`DATA_WIDTH-1:0] ifu_rd_data
);

//Localparams
localparam instr_cnt = 10;
localparam JMP_MAIN  = (12'ha80);

//Internal variables
integer no_instr = 0;
int count = 1;

 /*
 -----------------------------------------------------------------------------
 Following procedural block generates a random instruction (ifu_rd_data)
 when a read request is made by the IFU.
 Some deterministic stimulus is included since 1 of the opcdes was not 
 generated even after running for more than 10 million simulation cycles.
----------------------------------------------------------------------------
 */
always @(posedge clk)
begin
  //This is inserted to cover for CLA_1 since
  //Even after 10 million cycles, CLA_1 never occurred in the stimuli
 if(ifu_rd_req && count == 1)
 begin
  ifu_rd_data  <= 12'o7200;
  count <= count + 1;
 end
 else if(ifu_rd_req && count > 1)
 begin
  ifu_rd_data  <= ({$random} % 12'hfff);
  count <= count + 1;
 end
 else
 begin
  ifu_rd_data <= ifu_rd_data;
 end
end


endmodule

