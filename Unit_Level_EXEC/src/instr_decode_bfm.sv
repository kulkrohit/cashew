// =======================================================================
//   Filename:     instr_decode_BFM.sv
//   Description:  Bus functional model of instruction fetch and decode unit
//		   		   providing stimulus to the instr_exec unit
//		   		   in the unit level testbench
//
//   Created by:   Rohit Kulkarni
//   Date:         May 30, 2015
// =======================================================================

`include "pdp8_pkg.sv"
import pdp8_pkg::*;

module instr_decode_bfm
  (
   // Global inputs
   input clk,
   input reset_n,

   // From Execution unit
   input stall,
   input [`ADDR_WIDTH-1:0] PC_value,

   // To memory unit
   output                    ifu_rd_req,
   output  [`ADDR_WIDTH-1:0] ifu_rd_addr,

   // From memory unit
   input [`DATA_WIDTH-1:0] ifu_rd_data,

   // To Execution unit (decode struct)
   output [`ADDR_WIDTH-1:0] base_addr,
   output pdp_mem_opcode_s pdp_mem_opcode,
   output pdp_op7_opcode_s pdp_op7_opcode
   );

 //Internal variables  
 reg [17:0] rand_fetched_instr;

 //Assign base address to point to first instruction 
 assign base_addr = `START_ADDRESS;

 initial
 begin
  $display("**************************************************");
  $display("Simulation has started."); 
  $display("Running more than 10 million cycles."); 
  $display("Please wait until simulation finishes."); 
  $display("**************************************************");

  clear_Acc_link_and_drive_op;
 end

  /*
 -----------------------------------------------------------------------------
	Task 		: clear_Acc_link_and_drive_op
	Description	: Clear accumulator and link contents and drive random opcodes.
 
	Notes		: To clear Acc and Link at start of test
				  Otherwise Acc and Link remain X throughout sim
				  Some deterministic stimulus is driven to attain required 
				  coverage.
				  Some of the opcodes were not getting generated even after running 
				  more than a million simulation cycles.
----------------------------------------------------------------------------
 */
 task clear_Acc_link_and_drive_op;
 begin 
  //Make both opcodes
  pdp_op7_opcode = '0;
  pdp_mem_opcode = '0;

  while(stall !== 1'b0)
  begin
    @(posedge clk);
   //Do nothing since system might be in reset sequence
   //wait until stall becomes 0	
  end
  //Clear Acc and Link before driving any other opcodes
  pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0};
  repeat (4) @(posedge clk);   	//Wait until stall is asserted before going ahead

  while(stall !== 1'b0)
  begin
    @(posedge clk);
   //wait until stall becomes 0	
  end

   //Inserting a NOP to get full state coverage
   //We could not get the FSM to go into NOP state even after running for more than 10 million opcodes
   //We personally think it is just something to do with statistical probability behind $random
   //Any illegal opcode is executed as NOP
   pdp_op7_opcode = '{1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
   repeat (4) @(posedge clk);   	//Wait until stall is asserted before going ahead

  while(stall !== 1'b0)
  begin
    @(posedge clk);
   //wait until stall becomes 0	
  end

  repeat (4) @(posedge clk);   	//Wait until stall is asserted before going ahead

   //Start driving random mem opcodes
   drive_rand_mem_opcodes;

   //Start driving random op7 opcodes
   drive_rand_op7_opcodes;
 end
 endtask



  /*
 -----------------------------------------------------------------------------
	Task 		: drive_rand_mem_opcodes
	Description	: Drives purely random opcodes to be executed by EXEC unit
 ----------------------------------------------------------------------------
 */
 //Drive mem opcodes 
 task drive_rand_mem_opcodes;
 static integer no_instr = 0; 
 begin

  pdp_op7_opcode = '0;
  pdp_mem_opcode = '0;

  while(no_instr < 10000000)
  begin
   @(posedge clk);
   if(!stall)
   begin
    rand_fetched_instr  = ({$random} % 18'h3ffff);
    pdp_mem_opcode = rand_fetched_instr;
    no_instr++;  
   end
  end
  $finish;
 end
 endtask



  /*
 -----------------------------------------------------------------------------
	Task 		: drive_rand_op7_opcodes
	Description	: Drives purely random opcodes to be executed by EXEC unit
 ----------------------------------------------------------------------------
 */
 //Drive op7 opcodes 
 task drive_rand_op7_opcodes;
 static integer no_instr = 0; 
 begin

  pdp_op7_opcode = '0;
  pdp_mem_opcode = '0;

  while(no_instr < 100)
  begin
   @(posedge clk);
   if(!stall)
   begin
    rand_fetched_instr  = ({$random} % 18'h3ffff);
    pdp_op7_opcode = rand_fetched_instr;
    no_instr++;  
   end
  end
  $finish;
 end
 endtask

endmodule


