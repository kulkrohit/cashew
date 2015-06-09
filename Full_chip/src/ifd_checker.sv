// =======================================================================
//   Filename:     checker_ifd.sv
//   Description:  Checker implementation for:
//		   Unit Level IFD Testbench
//
//   Created by:   Rohit Kulkarni and Anuja Vaidya 
//   Date:         May 25, 2015
//   Modified on : June 6, 2015
// =======================================================================

`include "pdp8_pkg.sv"
import pdp8_pkg::*;


module ifd_checker
(
   // Global inputs
   input clk,
   input reset_n,

   // From Execution unit
   input stall,
   input [`ADDR_WIDTH-1:0] PC_value,

   // From IFD
   input                    ifu_rd_req,
   input  [`ADDR_WIDTH-1:0] ifu_rd_addr,

   // From memory unit
   input [`DATA_WIDTH-1:0] ifu_rd_data,

   // From IFD (decode struct)
   input [`ADDR_WIDTH-1:0] base_addr,
   input pdp_mem_opcode_s pdp_mem_opcode,
   input pdp_op7_opcode_s pdp_op7_opcode
);

//Internal variables
logic [`DATA_WIDTH-1:0] fetched_instr;
logic [1:0] 			rst_ref_counter;
logic [2:0]				ifu_ref_counter =0;

pdp_mem_opcode_s pdp_mem_opcode_chk = '0;
pdp_op7_opcode_s pdp_op7_opcode_chk = '0;


initial
begin
 get_fetched_instr;
end

//--------------------------
//Task : get_fetched_instr
//--------------------------
task get_fetched_instr;
begin
 while(1)
 begin
  if(ifu_rd_req)
  begin	
   @(negedge clk)
   fetched_instr  = ifu_rd_data;
   compute_golden_decoded_output;
  end
  @(posedge clk);
 end
end
endtask

//------------------------------------
//Task : compute_golden_decoded_output
//------------------------------------

task compute_golden_decoded_output;
begin
  pdp_mem_opcode_chk <= '{0,0,0,0,0,0,9'bz};
  pdp_op7_opcode_chk <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};

  if (fetched_instr[`DATA_WIDTH-1:`DATA_WIDTH-3] < 6) 
  begin
     case (fetched_instr[`DATA_WIDTH-1:`DATA_WIDTH-3])
        `AND: pdp_mem_opcode_chk    <= '{1,0,0,0,0,0,fetched_instr[8:0]};
        `TAD: pdp_mem_opcode_chk    <= '{0,1,0,0,0,0,fetched_instr[8:0]};
        `ISZ: pdp_mem_opcode_chk    <= '{0,0,1,0,0,0,fetched_instr[8:0]};
        `DCA: pdp_mem_opcode_chk    <= '{0,0,0,1,0,0,fetched_instr[8:0]};
        `JMS: pdp_mem_opcode_chk    <= '{0,0,0,0,1,0,fetched_instr[8:0]};
        `JMP: pdp_mem_opcode_chk    <= '{0,0,0,0,0,1,fetched_instr[8:0]};
        default: pdp_mem_opcode_chk <= '{0,0,0,0,0,0,9'bz};
     endcase
  end 
  else if (fetched_instr[`DATA_WIDTH-1:`DATA_WIDTH-3] == 7) begin
     case (fetched_instr)
        `NOP    : pdp_op7_opcode_chk <= '{1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
        `IAC    : pdp_op7_opcode_chk <= '{0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
        `RAL    : pdp_op7_opcode_chk <= '{0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
        `RTL    : pdp_op7_opcode_chk <= '{0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
        `RAR    : pdp_op7_opcode_chk <= '{0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
        `RTR    : pdp_op7_opcode_chk <= '{0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
        `CML    : pdp_op7_opcode_chk <= '{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
        `CMA    : pdp_op7_opcode_chk <= '{0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
        `CIA    : pdp_op7_opcode_chk <= '{0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0};
        `CLL    : pdp_op7_opcode_chk <= '{0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0};
        `CLA1   : pdp_op7_opcode_chk <= '{0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0};
        `CLA_CLL: pdp_op7_opcode_chk <= '{0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0};
        `HLT    : pdp_op7_opcode_chk <= '{0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0};
        `OSR    : pdp_op7_opcode_chk <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0};
        `SKP    : pdp_op7_opcode_chk <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0};
        `SNL    : pdp_op7_opcode_chk <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0};
        `SZL    : pdp_op7_opcode_chk <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0};
        `SZA    : pdp_op7_opcode_chk <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0};
        `SNA    : pdp_op7_opcode_chk <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0};
        `SMA    : pdp_op7_opcode_chk <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0};
        `SPA    : pdp_op7_opcode_chk <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0};
        `CLA2   : pdp_op7_opcode_chk <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1};
        default : pdp_op7_opcode_chk <= '{1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0}; //NOP
     endcase
  end 
  else
  begin
     pdp_mem_opcode_chk <= '{0,0,0,0,0,0,9'bz};
     pdp_op7_opcode_chk <= '{1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0}; // NOP
  end
end
endtask

//------------------------------------
//Properties 
//------------------------------------

// with reset_n == 1 the following conditions should take place with 1 clock cycle 
// ifu_rd_req == 0 , pdp_op7_opcode = 0      
// ifu_rd_add and base_addr == start_address 
	property reset_asserted;
		@(posedge clk)  (rst_ref_counter == 1) |-> ((ifu_rd_addr === `START_ADDRESS) && (base_addr === `START_ADDRESS) && (ifu_rd_req === 0) && (pdp_op7_opcode == 0)) ; 
	endproperty 

// when Exec unit sends a stall signal the ifu unit shouldnt fetch the new instruction. 
	property stall_asserted;
		@(posedge clk) stall |-> ifu_rd_req;
	endproperty 
	
// when the Exec unit de- asserts the stall signal and ifu_rd_add !== start_address, ifu unit should fetch the next instuction. 
	property stall_deasserted;
		@(posedge clk) (!stall && ifu_rd_addr ==!`START_ADDRESS)  |-> (ifu_rd_req ==1);  
	endproperty 	
	
// when the Exec unit de-asserts the stall signal and ifu_rd_add == start_address , ifu unit should go into done state
	property done_state_reached;
		@(posedge clk) (!stall && ifu_rd_addr == `START_ADDRESS) |-> ((pdp_mem_opcode === '{0,0,0,0,0,0,9'bz})&& (pdp_op7_opcode === 0));
	endproperty
		
	
// to check if the memory opcode was correctly decoded after 3 cycles 
	property mem_opcode_check;
		@(posedge clk) disable iff (!reset_n)
		(ifu_rd_req) |-> (pdp_mem_opcode == pdp_mem_opcode_chk);	
	endproperty

// to check if the op7_opcode are decoded correctly after 3 cycles 
	
	property Op7_opcode_check ;
		@(posedge clk) disable iff (! reset_n)
		(ifu_rd_req ==1) |-> (pdp_op7_opcode == pdp_op7_opcode_chk );
	endproperty

	
// to check if thr fsm stays in 	send_req state for just 1 cycle 

	property fsm_state_check_decode; 
		@(posedge clk)
		(ifu_ref_counter == 1) |->##1 (!ifu_rd_req);
	endproperty 
	

//------------------------------------
//Assertions 
//------------------------------------
/*p1: assert property (reset_asserted)
	else
		$display (" ERROR: Assertion failed:conditions not met --> base_addr and ifu_rd_addr are not equal to start address and ifu_rd_req and pdp_op7_opcode are not set to 0 instead they have following - base_address =",base_addr," ifu_rd_add =",ifu_rd_addr, " pdp_op7_opcode = ", pdp_op7_opcode," ifu_rd_req = ",ifu_rd_req);
		
p2: assert property (stall_asserted) 
	else 
		$display(" ERROR : Assertion failed : conditions not met --> decode unit fetches a new instruction in presence of stall from Exec unit");
		
p3: assert property (stall_deasserted)
	else 
		$display(" ERROR : Assertion failed : condition not met -- > ifu unit fails to fetch the new instruction when the stall is de-assered and ifu_rd_addr is not equal to the start address");
		
p4: assert property (done_state_reached)		
	else 
		$display("ERROR : Assertion failed : condition not met --> when stall is de-asserted but ifu_rd_add == start address the decode unit should jump to the done state");

p5: assert property (mem_opcode_check)		
	else 
		$display(" ERROR : Assertion failed : condition not met -- > decode unit failed to correctly decode the memory opcode,obtained mem_opcode =", pdp_mem_opcode,"Expected mem_opcode =",pdp_mem_opcode_chk );
		
p6: assert property (Op7_opcode_check)	
	else 
		$display(" ERROR : Assertion failed : condition not met -- > decode unit failed to correctly decode the memory opcode,obtained op7_opcode =", pdp_op7_opcode,"Expected op7_opcode =",pdp_op7_opcode_chk );

*/
		
p7: assert property (fsm_state_check_decode)
	else 
	$display("ERROR: Assertion failed: conditions not met --> FSM is in send_req state for more than 1 cycle",ifu_rd_req);
//-----------------------------------------reference counters  ---------------------------------------------//  
	// for reset 
	always_comb
		begin 
			if(reset_n==1)begin
				rst_ref_counter = rst_ref_counter + 1; 
				end 
			else 
				rst_ref_counter = 0 ;
			end 
			
			
	// for ifu_rd_req		
	
	always_comb
		begin
			if(ifu_rd_req ==1 )begin 
				ifu_ref_counter = ifu_ref_counter + 1;
				end 
			else 
				ifu_ref_counter = 0 ;
		end 		
		
//-----------------------------------------------------------------------------------------------------------------------//	

endmodule


