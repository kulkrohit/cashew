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


module EXEC_BFM
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
);

 int i;
 reg [3:0] delay;

 initial
 begin
  gen_rand_stim;
 end


 task gen_rand_stim;
 begin
  PC_value = 12'o200;
  stall = 1;
  while(i < 10)
  begin
   if(reset_n)
   @(posedge clk);
   begin 	
    stall = ~stall;
    delay = ({$random} % 4'hf);
    repeat (delay+2)  @(posedge clk);  
    i++;
    PC_value = PC_value + 1;	
    repeat (delay+2)  @(posedge clk);
   end
  end

  //Jump back to first instruction to enter DONE state
  stall = 1'b0;	
  PC_value =  12'h80;
  repeat (delay+2) @(posedge clk);
  stall = 1;


  //Drive some more random instructions required for some checks
  i = 0;
  while(i < 5)
  begin
   if(reset_n)
   @(posedge clk);
   begin 	
    stall = ~stall;
    delay = ({$random} % 4'hf);
    repeat (delay+2)  @(posedge clk);  
    i++;
    PC_value = PC_value + 1;	
    repeat (delay+2)  @(posedge clk);
   end
  end



 end
 endtask

endmodule

