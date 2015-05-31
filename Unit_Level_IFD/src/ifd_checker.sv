// =======================================================================
//   Filename:     checker_ifd.sv
//   Description:  Checker implementation for:
//		   Unit Level IFD Testbench
//
//   Created by:   Rohit Kulkarni
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
//Assertions
//------------------------------------

//Once IFU_RD_REQ is asserted, decoded output must be correct after 2 clock cycles  
property check_pdp_mem_decoded_output;
 @(posedge clk)
 $rose(ifu_rd_req) |=> ##2 (pdp_mem_opcode_chk === pdp_mem_opcode)
endproperty
CHECK_DEC_PDP_MEM: assert property(check_pdp_mem_decoded_output)
else
begin
 $error("Checker decoded instr does not match DUT decoded instr");
 $display("For fetched instruction: %h", fetched_instr);
 $display("[ERROR] DUT decoded instruction = %h, CHK decoded instruction = %h\n", pdp_mem_opcode, pdp_mem_opcode_chk);		
end








/*
task compute_golden_decoded_output;
begin
 case (fetched_instr[`DATA_WIDTH-1:`DATA_WIDTH-3])
  3'h0:
   begin
    $display("AND");	
   end
  3'h1:
   begin
    $display("TAD");	
   end
  3'h2:
   begin
    $display("ISZ");	
   end
  3'h3:
   begin
    $display("DCA");	
   end
  3'h4:
   begin
    $display("JMS");	
   end
  3'h5:
   begin
    $display("JMP");	
   end
  //Microinstructions
  3'h7:
   begin
    if(fetched_instr[`DATA_WIDTH-4]) //Group 1 Microinstructions
    begin
     case (fetched_instr[`DATA_WIDTH-5])

     endcase	        
    end
    else
    begin
	
    end

    $display("Microinstruction");	
   end
  default: 
   begin
    $display("Illegal instruction.");	
   end
 endcase 
end
endtask
*/


endmodule
