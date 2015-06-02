// =======================================================================
//   Filename:     instr_decode_BFM.sv
//   Description:  Bus functional model of instruction fetch and decode unit
//		   providing stimulus to the instr_exec unit
//		   in the unit level testbench
//
//   Created by:   Rohit Kulkarni
//   Date:         May 30, 2015
// =======================================================================

`include "pdp8_pkg.sv"
import pdp8_pkg::*;

module instr_decode_BFM
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

 //localparams
 localparam no_opcodes = 10;

 reg [17:0] rand_fetched_instr;

 //Assign base address to point to first instruction 
 assign base_addr = `START_ADDRESS;


 initial
 begin
  clear_Acc_link_and_drive_op;
 end



 //Task for clearing accumulator and link 
 //Need to clear Acc and Link at start of test
 //Otherwise Acc and Link remain X throughout sim
 task clear_Acc_link_and_drive_op;
 begin 
  while(stall !== 1'b0)
  begin
    @(posedge clk);
   //Do nothing since system might be in reset sequence
   //wait until stall becomes 0	
  end
   pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0};

   repeat (4) @(posedge clk);   	//Wait until stall is asserted before going ahead

   //Start driving random opcodes
   drive_rand_mem_opcodes;
 end
 endtask



 //Drive mem opcodes 
 task drive_rand_mem_opcodes;
 static integer no_instr = 0; 
 begin

  pdp_op7_opcode = 'x;
  pdp_mem_opcode = 'x;

  while(no_instr < 10)
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

endmodule


