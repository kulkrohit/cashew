// =======================================================================
//   Filename:     EXEC_BFM.sv
//   Description:  Bus functional model for the EXEC unit for use in 
//		   the IFD unit level validation
//
//   Created by:   Rohit Kulkarni
//   Date:         May 24, 2015
//
// =======================================================================

`include "pdp8_pkg.sv"
import pdp8_pkg::*;

module Memory_BFM
(
   // Global input
   input clk,

   input                    exec_rd_req,
   input  [`ADDR_WIDTH-1:0] exec_rd_addr,
   output reg [`DATA_WIDTH-1:0] exec_rd_data,

   input                    exec_wr_req,
   input  [`ADDR_WIDTH-1:0] exec_wr_addr,
   input  [`DATA_WIDTH-1:0] exec_wr_data

);


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

