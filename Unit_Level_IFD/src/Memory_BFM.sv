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

   //IFU interface signals	
   input                    ifu_rd_req,
   input  [`ADDR_WIDTH-1:0] ifu_rd_addr,
   output reg [`DATA_WIDTH-1:0] ifu_rd_data
);



always @(posedge clk)
begin
 if(ifu_rd_req)
 begin
  ifu_rd_data  <= ({$random} % 12'hfff);
 end
 else
 begin
  ifu_rd_data <= ifu_rd_data;
 end
end


endmodule
