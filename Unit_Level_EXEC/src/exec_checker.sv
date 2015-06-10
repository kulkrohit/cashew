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

   reg [1:0]	exec_ref_counter;		// reference counter 
   
   // Enums for EXEC state machine (should have been defined in the package)
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
     if(chkr_Acc[`DATA_WIDTH])
     begin
      chkr_Link	= ~chkr_Link;	
     end
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
     chkr_PC    = chkr_PC + 1;
    end
    else if (pdp_mem_opcode.JMS)
    begin
      chkr_result = chkr_PC + 1;
      chkr_PC    = pdp_mem_opcode.mem_inst_addr + 1;
    end
    else if (pdp_mem_opcode.JMP)
    begin
      chkr_PC    = pdp_mem_opcode.mem_inst_addr;   	 
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

// reference counter for exec_rd_req
	always_comb
		begin 
			if(int_exec_rd_req ==1)begin
				exec_ref_counter = exec_ref_counter + 1; 
				end 
			else 
				exec_ref_counter = 0 ;
			end 		
 

//------------------------------------
//	Checks / Assertions
//------------------------------------


// For all instructions that require writing the result back to memory,
// 1: ISZ : C(EAddr) <- C(EAddr) + 1
// 2: DCA : C(EAddr) <- C(AC)  
// 3: JMS : C(EAddr) <- C(PC)
//
//The following acts as a common check for any instruction
//that requires EXEC unit to write into the memory.
//We tap it at the mem boundary and compare actual and golden result.
//Check if result written to memory is correct for all instructions that write to memory
property check_result_written_to_memory;
 @(posedge clk)
 (exec_wr_req) |=> ##2 (chkr_result == DUT_result)
endproperty
Check_Result_Written_to_Memory: assert property(check_result_written_to_memory)
else
begin
 $error("[ERROR] Incorrect result is written to memory");
 $display("DUT result = %h, CHK result = %h\n", DUT_result, chkr_result);		
end


// For all instructions that require writing the result into Accumulator
// 1: AND : C(AC) <- C(AC) AND C(EAddr)
// 2: TAD : C(AC) <- C(AC) + C(EAddr)
// 3: DCA : C(AC) <- 0
// 4: CLA_CLL: C(AC) <- 0 
//
//The following acts as a common check for any instruction
//that requires EXEC unit to write into accumulator.
//We check after every instruction retire (UNSTALL), and compare golden and actual results

//Check accumulator at the end of every instruction retire
property check_Acc_after_instr_retire;
 @(posedge clk)
 (instr_exec.current_state == UNSTALL) |=> ##2 (chkr_Acc[`DATA_WIDTH-1:0] == instr_exec.intAcc[`DATA_WIDTH-1:0])
endproperty
Check_Acc_after_Instr_Retire: assert property(check_Acc_after_instr_retire)
else
begin
 $error("[ERROR] Incorrect accumulator contents on instruction retire");
 $display("DUT Acc = %h, CHK Acc = %h\n", instr_exec.intAcc[`DATA_WIDTH-1:0], chkr_Acc[`DATA_WIDTH-1:0]);		
end



// For all instructions that may change the Link bit
// 1: TAD : If carry out then complement Link
// 2: CLA_CLL: Link <- 0 
//
//The following acts as a common check for any instruction
//that requires EXEC unit to write into link bit.
//We check after every instruction retire (UNSTALL), and compare golden and actual results

//Check Link bit at the end of every instruction retire
property check_Link_bit_after_instr_retire;
 @(posedge clk)
 (instr_exec.current_state == UNSTALL) |=> ##2 (chkr_Link == instr_exec.intLink)
endproperty
Check_Link_bit_after_Instr_Retire: assert property(check_Link_bit_after_instr_retire)
else
begin
 $error("[ERROR] Incorrect link bit contents on instruction retire");
 $display("DUT link bit = %h, CHK link bit = %h\n", instr_exec.intLink, chkr_Link);		
end


// PC changes invariably increments by 1 after every instruction
// except a few special ones like 
// 1: ISZ : C(PC) <- C(PC) + 2
// 2: JMS : C(PC) <- EAddr + 1
// 3: JMP : C(PC) <- EAddr
// 4: All other instructions: C(PC) <- C(PC) + 1
//
//The following acts as a common check for any instruction
//to check the PC after every instruction retire
//We check after every instruction retire (UNSTALL), and compare golden and actual results

//Check PC at the end of every instruction retire
property check_PC_after_instr_retire;
 @(posedge clk)
 (instr_exec.current_state == UNSTALL) |=> (chkr_PC == PC_value)
endproperty
Check_PC_after_Instr_Retire: assert property(check_PC_after_instr_retire)
else
begin
 $error("[ERROR] Incorrect PC contents on instruction retire");
 $display("DUT PC = %h, CHK PC = %h\n", PC_value, chkr_PC);		
end


// 5. checks the cycle latency the FSM  has in MEM_RD_REQ state  
//based on opcodes if the DUT gets one of the following opcodes (TAD),(AND),(ISZ) it performs read operation for which the FSM jumps to MEM_RD_REQ state ,ideally the FSM should remain in this state for not more than one cycle 
// This check is intended to 
property exec_read_request_asserted; 
	@(posedge clk)(exec_ref_counter ==1) |->##[0:1] !exec_rd_req;
endproperty;
exec_read_request_asserted: assert property (exec_read_request_asserted)
else 
$error("[ERROR] FSM is stuck in the MEM_RD_REQ state for more then one cycle")
$display("DUT is in MEM_RD_REQ state for ",exec_ref_counter"cycles");
endmodule


