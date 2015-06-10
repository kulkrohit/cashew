// =======================================================================
//   Filename:     checker_ifd.sv
//   Description:  Checker implementation for:
//		   Unit Level IFD Testbench
//
//   Created by:   Rohit Kulkarni, Anuja Vaidya
//   Date:         May 25, 2015
//
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
reg [`DATA_WIDTH-1:0] fetched_instr;
pdp_mem_opcode_s pdp_mem_opcode_chk = '0;
pdp_op7_opcode_s pdp_op7_opcode_chk = '0;
reg [1:0] ifu_ref_counter;

//Enums copied from design. Should have been in a package
   enum {IDLE,
         READY,
         SEND_REQ,
         DATA_RCVD,
         INST_DEC,
         STALL,
         DONE } current_state, next_state;

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


// reference counter for ifu_rd_req

	always_comb
		begin
			if(ifu_rd_req ==1 )begin 
				ifu_ref_counter = ifu_ref_counter + 1;
				end 
			else 
				ifu_ref_counter = 0 ;
		end 

//------------------------------------
//	Assertions
//------------------------------------

//Once IFU_RD_REQ is asserted, decoded mem opcode must be correct after 2 clock cycles  
property check_pdp_mem_decoded_output;
 @(posedge clk)
 $rose(ifu_rd_req) |=> ##2 (pdp_mem_opcode_chk === pdp_mem_opcode)
endproperty
CHECK_DEC_PDP_MEM: assert property(check_pdp_mem_decoded_output)
else
begin
 $error("[ERROR] Checker decoded instr does not match DUT decoded instr");
 $display("For fetched instruction: %h", fetched_instr);
 $display("DUT decoded instruction = %h, CHK decoded instruction = %h\n", pdp_mem_opcode, pdp_mem_opcode_chk);		
end


//Once IFU_RD_REQ is asserted, decoded op7 opcode must be correct after 2 clock cycles  
property check_pdp_op7_decoded_output;
 @(posedge clk)
 $rose(ifu_rd_req) |=> ##2 (pdp_op7_opcode_chk === pdp_op7_opcode)
endproperty
CHECK_DEC_PDP_OP7: assert property(check_pdp_mem_decoded_output)
else
begin
 $error("[ERROR] Checker decoded instr does not match DUT decoded instr");
 $display("For fetched instruction: %h", fetched_instr);
 $display("DUT decoded instruction = %h, CHK decoded instruction = %h\n", pdp_op7_opcode, pdp_op7_opcode_chk);		
end


//When STALL is asserted, IFD should not fetch the next instruction and no new requests sent to EXEC unit
property no_fetch_on_stall;
 @(posedge clk)
 (stall) |=> (ifu_rd_req !== 1)
endproperty
No_Fetch_On_Stall: assert property(no_fetch_on_stall)
else
begin
 $error("[ERROR] IFD fetched an instruction when STALL was asserted.");
 $display("At fetched instruction: %h", fetched_instr);
end


//Once out of reset, then all outputs are cleared in the same clock cycle
property all_outputs_cleared_on_reset;
 @(posedge reset_n)
 (reset_n) |-> (((ifu_rd_req | ifu_rd_addr | ifu_rd_data | pdp_op7_opcode) === '0) && (pdp_mem_opcode === '{0,0,0,0,0,0,9'bz}))
endproperty
All_Outputs_Cleared_On_Reset: assert property(all_outputs_cleared_on_reset)
else
begin
 $error("[ERROR] Outputs of IFD did not go 0 on coming out of reset.");
end


//On asserting reset, next instruction should be fetched from base address = o200
property fetch_from_base_addr_on_reset;
 @(posedge reset_n)
 (reset_n) |=> (ifu_rd_addr == `START_ADDRESS)
endproperty
Fetch_from_Base_Addr_on_Reset: assert property(fetch_from_base_addr_on_reset)
else
begin
 $error("[ERROR] On coming out of reset, first instruction was not fetched from base address.");
end



//No instructions are fetched after going into DONE state
property no_instr_fetched_after_done;
 @(posedge reset_n) 
 (instr_decode.current_state == DONE) |-> (!ifu_rd_req)
endproperty
No_Instr_Fetched_After_DONE: assert property(no_instr_fetched_after_done)
else
begin
 $error("[ERROR] Instructions are still fetched after going into DONE state.");
end

	
//When the Exec unit deasserts the stall signal and ifu_rd_add !== start_address, ifu unit should fetch the next instruction. 
property fetch_instr_on_stall_deassert;
 @(posedge clk) 
(!stall && ifu_rd_addr != `START_ADDRESS && (instr_decode.current_state == STALL))  |=> (ifu_rd_req);  
endproperty
Fetch_Instr_on_Stall_Deassert:  assert property(fetch_instr_on_stall_deassert) 
else
begin
 $error("[ERROR] IFU did not fetch the next instruction on deasserting Stall.");
end


//When the Exec unit de-asserts the stall signal and ifu_rd_add == start_address , ifu unit should go into done state
property done_state_reached;
 @(posedge clk) 
(!stall && ifu_rd_addr == `START_ADDRESS && (instr_decode.current_state == STALL)) |-> ##2 ((pdp_mem_opcode === '{0,0,0,0,0,0,9'bz})&& (pdp_op7_opcode === 0));
endproperty
Done_State_Reached: assert property(done_state_reached)
else
begin
 $error("[ERROR] IFU did not go to DONE state when Done_State_Reached.");
end


// this property checks when the read request to the memory in SEND_REQ state the FSM stays in that state for just 1 cycles and the jumps to fetching the data 
property ifu_read_request_asserted;
	@(posedge clk) (ifu_ref_counter ==1) |->##[0:1] !ifu_rd_req ;
endproperty
Ifu_Read_Request_Asserted:assert property (ifu_read_request_asserted)
else 
begin 
$error("[ERROR] FSM is stuck in the SEND_REQ state for more than 1 cycle");
$display("FSM is stuck in the SEND_REQ state for",ifu_ref_counter,"cycles");
end 

//property to check if the ifu_rd_addr is valid and stable for fetching the new data when the Exec unit de-asserts the stall. 
property valid_ifu_read_address ; 
		@(posedge clk) (!stall) |-> (ifu_rd_addr !== 12'bx || ifu_rd_addr !== 12'bz);
endproperty  
Valid_Ifu_Read_Address:assert property (valid_ifu_read_address)
else 
$display("IFU read address is not stable or valid after the stall is de-asserted by the Execution unit");

endmodule
