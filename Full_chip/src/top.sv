// =======================================================================
//   Department of Electrical and Computer Engineering
//   Portland State University
//
//   Course name:  ECE 510 - Pre-Silicon Validation
//   Term & Year:  Spring 2015
//   Instructor :  Tareque Ahmad
//
//   Project:      PDP8 Hardware Simulator top level testbench
//                
//
//   Filename:     top.sv
//   Description:  TBD
//   Created by:   Tareque Ahmad
//   Modified by : Anuja Vaidya 
//   Date:         May 03, 2015
//   Date modified: june 1,2015	
//   Copyright:    Tareque Ahmad 
// =======================================================================

`include "pdp8_pkg.sv"
import pdp8_pkg::*;

module top ();

   wire clk;
   wire reset_n;

   wire stall;
   wire [`ADDR_WIDTH-1:0] PC_value;
   wire                   ifu_rd_req;
   wire [`ADDR_WIDTH-1:0] ifu_rd_addr;
   wire [`DATA_WIDTH-1:0] ifu_rd_data;

   wire                   exec_rd_req;
   wire [`ADDR_WIDTH-1:0] exec_rd_addr;
   wire [`DATA_WIDTH-1:0] exec_rd_data;

   wire                   exec_wr_req;
   wire [`ADDR_WIDTH-1:0] exec_wr_addr;
   wire [`DATA_WIDTH-1:0] exec_wr_data;

   wire [`ADDR_WIDTH-1:0] base_addr;

   pdp_mem_opcode_s pdp_mem_opcode;
   pdp_op7_opcode_s pdp_op7_opcode;

   // instances of modules used 
   memory_pdp      memory_pdp (.*);
   instr_decode    instr_decode(.*);
   instr_exec      instr_exec(.*);
   pdp8_checker	   pdp8_checker(.*);    	     // full chip checker 
	
   //bind instr_exec   exec_checker exec_checker(.*); // unit level checker for exec module 
//   bind instr_decode ifd_checker  ifd_checker(.*);  // uit level checker for decode module 

// clock generator 
  clkgen_driver #(
      .CLOCK_PERIOD(10),
      .RESET_DURATION(500)) clkgen_driver (
      .clk     (clk),
      .reset_n (reset_n));




endmodule
