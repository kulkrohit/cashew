// =======================================================================
//   Department of Electrical and Computer Engineering
//   Portland State University
//
//   Course name:  ECE 510 - Pre-Silicon Validation
//   Term & Year:  Spring 2015
//   Instructor :  Tareque Ahmad
//
//   Project:      Hardware implementation of PDP8
//         
//   Filename:     top.sv
//   Description:  Unit Level Testbench for IFD Unit of PDP8
//   Created by:   Rohit Kulkarni
//   Date:         May 24, 2015
//
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

   clkgen_driver #(
      .CLOCK_PERIOD(10),
      .RESET_DURATION(500)) clkgen_driver (
      .clk     (clk),
      .reset_n (reset_n));


   //Instantiate memory_bfm here
   Memory_BFM	   Memory_BFM(.*);

   //Instantiate instr_decode here
   instr_decode    instr_decode(.*);

   //Instantiate exec_bfm here
   EXEC_BFM	  EXEC_BFM(.*);

   //Bind checker instance here	
   bind instr_decode ifd_checker IFD_CHECKER(.*);

endmodule
