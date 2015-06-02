// =======================================================================
//   Filename:     instr_decode_BFM.sv
//
//   Description:  Checker implementation for EXEC unit level testbench
//
//   Created by:   Rohit Kulkarni
//   Date:         May 30, 2015
// =======================================================================


`include "pdp8_pkg.sv"
import pdp8_pkg::*;


module exec_checker
  (
   // From clkgen_driver module
   input clk,                              // Free running clock
   input reset_n,                          // Active low reset signal

   // From instr_decode module
   input [`ADDR_WIDTH-1:0] base_addr,      // Address for first instruction
   input pdp_mem_opcode_s pdp_mem_opcode,  // Decoded signals for memory instructions
   input pdp_op7_opcode_s pdp_op7_opcode,  // Decoded signals for op7 instructions

   // From instr_decode module
   input                   stall,         // Signal to stall instruction decoder
   input [`ADDR_WIDTH-1:0] PC_value,      // Current value of Program Counter

   // From memory_pdp module
   input                    exec_wr_req,  // Write request to memory
   input  [`ADDR_WIDTH-1:0] exec_wr_addr, // Write address 
   input  [`DATA_WIDTH-1:0] exec_wr_data, // Write data to memory
   input                    exec_rd_req,  // Read request to memory
   input  [`ADDR_WIDTH-1:0] exec_rd_addr, // Read address

   // From memory_pdp module
   input   [`DATA_WIDTH-1:0] exec_rd_data  	// Read data returned by memory
   );

   reg	is_mem_opcode; 			 	// Signal to detect a new memory instruction
   reg	is_op7_opcode; 				// Signal to detect a new op7 instruction
   reg [`DATA_WIDTH-1:0] operand;		// operand read from memory for certain instructions
   reg [`DATA_WIDTH-1:0] DUT_result;		// DUT result written to memory
   reg [`DATA_WIDTH-1:0] chkr_result;		// CHKR result written to memory
   reg [`DATA_WIDTH:0]   chkr_Acc;		// Golden Accumulator with 1 extra bit for carry 
   reg [`ADDR_WIDTH-1:0] chkr_PC;		// Golden PC
   reg chkr_Link;


   //Enums for EXEC state machine (should have been defined in the package)
   // Define enums for the state machine
   enum {IDLE,
         STALL,
         BRANCH,
         CLA,
         CLA_CLL,
         MEM_RD_REQ,
         DATA_RCVD,
         ADD_ACC_MEM,
         AND_ACC_MEM,
         ISZ_WR_REQ,
         ISZ_UPDT_PC,
         DCA,
         JMS_WR_REQ,
         JMS_UPDT_PC,
         JMP,
         NOP,
         UNSTALL } current_state, next_state;


 initial
 begin
  fork
   latch_exec_rd_data;
   latch_exec_wr_data;
   compute_golden_result;
  join
 end

 //Task to latch exec_rd_data
 task latch_exec_rd_data;
 begin
  while(1)
  begin
   @(posedge clk);
   if(exec_rd_req)
   begin
    @(posedge clk);
     operand = exec_rd_data;
   end   
  end  
 end
 endtask 


 //Task to latch exec_wr_data
 task latch_exec_wr_data;
 begin
  while(1)
  begin
   @(posedge clk);
   if(exec_wr_req)
   begin
    @(posedge clk);
    DUT_result = exec_wr_data;
   end   
  end  
 end
 endtask 
 

 //Task to compute golden result
 task compute_golden_result;
 begin

  //Initialize variables
  chkr_PC = `START_ADDRESS;

  while(1)
  begin
   @(posedge clk);
   if(instr_exec.current_state == UNSTALL)
   begin
    if (pdp_op7_opcode.CLA_CLL)
    begin
     chkr_Acc 	= '0;
     chkr_Link	= '0;    	
     chkr_PC    = chkr_PC + 1;
    end
    else if (pdp_mem_opcode.TAD)
    begin
     chkr_Acc 	= chkr_Acc + operand;
     chkr_Link	= chkr_Acc[`DATA_WIDTH];	
     chkr_PC    = chkr_PC + 1;
    end
    else if (pdp_mem_opcode.AND)
    begin
     chkr_Acc 	= chkr_Acc & operand;
     chkr_PC    = chkr_PC + 1;
    end
    else if (pdp_mem_opcode.ISZ)
    begin
     chkr_result = operand + 1;
     if(operand == 0)
     begin
      chkr_PC    = chkr_PC + 2;
     end
     else
     begin
      chkr_PC    = chkr_PC + 1;
     end
    end
    else if (pdp_mem_opcode.DCA)
    begin
     chkr_result = chkr_Acc;
     chkr_Acc 	= '0;
    end
    else if (pdp_mem_opcode.JMS)
    begin
      chkr_result = operand;
      chkr_PC    = chkr_PC + 1;
    end
    else if (pdp_mem_opcode.JMP)
    begin
      chkr_PC    = operand;   	 
    end
    else
    begin
     chkr_PC    = chkr_PC + 1;
     //Do nothing else since unsupported instruction is encountered	
    end
   end
  end
 end
 endtask

endmodule


