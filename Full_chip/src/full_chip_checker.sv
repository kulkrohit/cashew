/*
Module name : pdp8_checker.sv
Author name: Anuja Vaidya
Date: 5/30/2015
Description: This module checkes the 

*/

`include "pdp8_pkg.sv"
import pdp8_pkg::*;


module pdp8_checker(
	input 					  clk,
	input 					  reset_n,
	input 					  stall,
	input   [`ADDR_WIDTH-1:0] PC_value,
	input                     ifu_rd_req,
    input  [`ADDR_WIDTH-1:0]  ifu_rd_addr,
	input   [`DATA_WIDTH-1:0] ifu_rd_data,
	
	input                     exec_rd_req,
	input  [`ADDR_WIDTH-1:0]  exec_rd_addr,
	input   [`DATA_WIDTH-1:0] exec_rd_data,
	input                     exec_wr_req,
	input  [`ADDR_WIDTH-1:0]  exec_wr_addr,
	input  [`DATA_WIDTH-1:0]  exec_wr_data,
  
	
	input [`ADDR_WIDTH-1:0]   base_addr,
	input pdp_mem_opcode_s pdp_mem_opcode,
	input pdp_op7_opcode_s pdp_op7_opcode
		
);


	
/////////////////////
// Properties 
/////////////////////


// property to check if the ifu_rd_addr  is stable and valid 3 cycles prior to ifu _rd_req and when the Exec unit de-asserts the stall. 

property valid_ifu_read_saddress ; 
@(posedge clk) (!stall) |-> (ifu_rd_addr !== 12'bx || ifu_rd_addr !== 12'bz);
endproperty  

//

////////////////////////
// Assertions 
/////////////////////////
assert property (valid_ifu_read_address)
else 
$display("ifu_rd_add is not valid 3 cycles prior to the request is been made");
	
		
	
					
endmodule 