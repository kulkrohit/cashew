// =======================================================================
//   Filename:     EXEC_BFM.sv
//   Description:  Bus functional model for the EXEC unit for use in 
//		   		   the IFD unit level validation
//
//   Created by:   Rohit Kulkarni
//   Date:         May 24, 2015
//
// =======================================================================

`include "pdp8_pkg.sv"
import pdp8_pkg::*;


module exec_bfm
(
   // From clkgen_driver module
   input clk,                              // Free running clock
   input reset_n,                          // Active low reset signal

   // From instr_decode module
   input [`ADDR_WIDTH-1:0] base_addr,      // Address for first instruction
   input pdp_mem_opcode_s pdp_mem_opcode,  // Decoded signals for memory instructions
   input pdp_op7_opcode_s pdp_op7_opcode,  // Decoded signals for op7 instructions

   // To instr_decode module
   output reg                  stall,         // Signal to stall instruction decoder
   output reg [`ADDR_WIDTH-1:0] PC_value       // Current value of Program Counter
   
   // No need of EXEC module connections to Memory since this is a unit-level IFD testbench.
   // All we require is connections to IFD module
);


 //Internal variables
 int i = 0;
 reg [3:0] delay;

 
 initial
 begin
  $display("**************************************************");
  $display("Simulation has started."); 
  $display("Running more than 10 million cycles."); 
  $display("Please wait until simulation finishes."); 
  $display("**************************************************");

  gen_rand_stim;
 end

 /*
 -----------------------------------------------------------------------------
	Task 		: gen_rand_stim
	Description	: Generates random stimulus to be given to the IFU module
				  Stimulus involves:
				  1: Stall	: Signal to stall instruction decoder
				  2: PC value	: Current value of Program Counter
				  
				  Stall is randomly generated to be asserted or deasserted.
				  PC value is randomly generated 12 bit number
				  
	Notes		: Some deterministic stimulus is added in this task to obtain
				  hard to achieve cases.
----------------------------------------------------------------------------
 */
 
 task gen_rand_stim;
 begin

   //Generate a consrained random PC but not equal to base address
   //Since generating a PC equal to base address will cause IFD to 
   //not process any further instructions
  do
  begin
   PC_value = ({$random} % 12'hfff);
  end
  while(PC_value == `START_ADDRESS);
  stall = 0;

  //One cycle delay to set up initial values at start of simulation
  @(posedge clk);   	

 
  //Wait till reset sequence finishes
  while(reset_n == 1'b0)
  begin
   @(posedge clk);   	
  end

  //Start generating random stall and PC values
  while(i < 100000)
  begin
   @(posedge clk);	   
  //After coming out of reset, no need to stall since no instruction is getting executed
   stall = 1'b0;
   repeat (delay+2)  @(posedge clk);  

   stall = {$random};
   delay = ({$random} % 4'hf);
   repeat (delay+2)  @(posedge clk);  
   i++;

   //Generate a consrained random PC but not equal to base address
   //Since generating a PC equal to base address will cause IFD to 
   //not process any further instructions
   do
   begin
    PC_value = ({$random} % 12'hfff);
   end
   while(PC_value == `START_ADDRESS);
   repeat (delay+2)  @(posedge clk);
  end



  //Hard to achive case:
  //Jump back to first instruction to enter DONE state
  stall = 1'b0;	
  PC_value =  12'h80;
  repeat (delay+2) @(posedge clk);
  stall = 1;


  //Drive some more random instructions required for some checks
  i = 0;
  while(i < 5)
  begin
   @(posedge clk);
   stall = ~stall;
   delay = ({$random} % 4'hf);
   repeat (delay+2)  @(posedge clk);  
   i++;

   //Generate a consrained random PC but not equal to base address
   //Since generating a PC equal to base address will cause IFD to 
   //not process any further instructions
  do
  begin
   PC_value = ({$random} % 12'hfff);
  end
  while(PC_value == `START_ADDRESS);

   repeat (delay+2)  @(posedge clk);
  end

  $finish;

 end
 endtask

endmodule

