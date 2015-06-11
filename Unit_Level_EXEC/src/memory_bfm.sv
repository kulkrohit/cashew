// =======================================================================
//   Filename:     EXEC_BFM.sv
//   Description:  Bus functional model for the Memory unit for use in 
//		   		   the EXEC unit level validation
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

   // EXEC Read signals
   input                    exec_rd_req,
   input  [`ADDR_WIDTH-1:0] exec_rd_addr,
   output reg [`DATA_WIDTH-1:0] exec_rd_data,

   // EXEC Write signals
   input                    exec_wr_req,
   input  [`ADDR_WIDTH-1:0] exec_wr_addr,
   input  [`DATA_WIDTH-1:0] exec_wr_data

);

/*
	Following procedural block drives random exec_rd_data which 
	is used as a operand by EXEC unit
*/
always @(posedge clk)
begin
 if(exec_rd_req)
 begin
  exec_rd_data  <= ({$random} % 12'hfff);
 end
 else
 begin
  exec_rd_data <= exec_rd_data;
 end
end


endmodule

