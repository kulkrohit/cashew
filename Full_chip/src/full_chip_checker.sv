/*
Module name : pdp8_checker.sv
Author name: Anuja Vaidya
Date: 5/30/2015
Description:

*/

`include "pdp8_pkg.sv"
import pdp8_pkg::*;


module pdp8_checker(
	input 					  clk,
	input 					  reset_n,
	input 					  stall,
	input   [`ADDR_WIDTH-1:0] PC_value,
	input                     ifu_rd_req,
    input  [`ADDR_WIDTH-1:0]  ifu_rd_addr,
	input   [`DATA_WIDTH-1:0] ifu_rd_data,
	
	input                     exec_rd_req,
	input  [`ADDR_WIDTH-1:0]  exec_rd_addr,
	input   [`DATA_WIDTH-1:0] exec_rd_data,
	input                     exec_wr_req,
	input  [`ADDR_WIDTH-1:0]  exec_wr_addr,
	input  [`DATA_WIDTH-1:0]  exec_wr_data,
  
	
	input [`ADDR_WIDTH-1:0]   base_addr,
	input pdp_mem_opcode_s pdp_mem_opcode,
	input pdp_op7_opcode_s pdp_op7_opcode
		
);


	logic [`ADDR_WIDTH-1:0] int_PC_Value;
	logic [`ADDR_WIDTH-1:0] int_base_addr;
	logic 			int_ifu_rd_req;
	logic [`ADDR_WIDTH-1:0] int_ifu_rd_addr;
	logic 			int_exec_rd_req;
	logic 			int_exec_wr_req;
	logic [`ADDR_WIDTH-1:0] int_exec_rd_addr;
	logic [`ADDR_WIDTH-1:0] reference_int_exec_rd_addr;
	logic [`DATA_WIDTH-1:0] reference_int_exec_rd_data;
	logic [`DATA_WIDTH-1:0] ref_int_exec_wr_data;
	
	logic [`ADDR_WIDTH-1:0] int_exec_wr_addr;
	logic [`ADDR_WIDTH-1:0]	ref_int_exec_wr_addr;
	logic [`DATA_WIDTH-1:0]	int_exec_wr_data;
	logic [`DATA_WIDTH-1:0] ref_int_exec_rd_data;
	logic [`DATA_WIDTH-1:0] int_exec_rd_data;
	logic [2:0]				ifu_ref_counter,exec_ref_counter;

	assign 	int_exec_rd_req	 = exec_rd_req;
	assign  int_base_addr 	 = base_addr;
	assign  int_PC_value     = PC_value;
	assign  int_ifu_rd_req   = ifu_rd_req ;
	assign  int_ifu_rd_addr  = ifu_rd_addr;
	assign  int_exec_rd_addr =  exec_rd_addr;
	
	assign  int_exec_wr_addr = exec_wr_addr;
	assign  int_exec_wr_data = exec_wr_data;
	assign  int_exec_rd_data = exec_rd_data;
	
	

	property reset_assert;
	@(posedge clk)  reset_n |-> (base_addr == `START_ADDRESS); 
	endproperty 
 
	property stall_asserted;
	@(posedge clk) stall |-> !int_ifu_rd_req;
	endproperty 

	property stall_deasserted;
	@(posedge clk) (!stall && int_PC_Value ==!`START_ADDRESS)  |-> (int_ifu_rd_req ==0);  
	endproperty 

	property exec_write_request ;
	@(posedge clk)(int_exec_wr_req ==1 && (pdp_mem_opcode.DCA || pdp_mem_opcode.ISZ || pdp_mem_opcode.JMS ))|-> (int_exec_wr_data == ref_int_exec_wr_data);
	endproperty
	
	
	property exec_read_request;
	@(posedge clk) (int_exec_rd_req ==1 && (pdp_mem_opcode.TAD || pdp_mem_opcode.AND || pdp_mem_opcode.ISZ )) |-> (int_exec_rd_data== ref_int_exec_rd_data);
	endproperty
	
	property ifu_read_request_assertion;
	@(posedge clk) (ifu_ref_counter ==1) |->##[0:1] !int_ifu_rd_req ;
	endproperty

	property exec_read_request_assertion; 
	@(posedge clk)(exec_ref_counter ==1) |->##[0:1] !int_exec_rd_req;
	endproperty;
	
	always @ (posedge clk)
	begin 
	/*A1: assert property (reset_assert)
		else 
			$display("ERROR: Assertion failed: base address and ifu_rd_req and ifu_rd_add are not zero after the assertion of reset");*/

	A2:assert property (stall_asserted)
		else 
			$display("ERROR:Assertion failed: instruction decode logic jumped to fetch the new instruction");
	A3: assert property (stall_deasserted)
		else 
			$display("ERROR:Assertion failed:stall is deaaserted and base address is not equal to 0200 so decode logic fetches the new instruction");
	end 
	
	A4: assert property (exec_write_request)
		else 
			$display("ERROR:Assertion failed: the write data in the memory does match the actual write data");
			
	A5: assert property (exec_read_request)
		else 
			$display("ERROR:Assertion failed: read data from the memory doesnt match the actual read data");
	
	
	A6: assert property (ifu_read_request_assertion)
		else 
			$display("ERROR:Assertion failed: ifu read request is asserted high for more than 1 cycle.");
			
	
	A7: assert property (exec_read_request_assertion)
		else 
			$display("ERROR:Assertion failed: exec read request is asserted high for more than 1 cycle ");
			
	// reference module to check the write operation 
	
always_comb 
	begin 
	
		if (int_exec_wr_req == 1)begin 
			if (pdp_mem_opcode.DCA)begin 
				ref_int_exec_wr_addr <= pdp_mem_opcode.mem_inst_addr;
				ref_int_exec_wr_data <= int_exec_wr_data;
			end 
			if (pdp_mem_opcode.ISZ)begin 
				ref_int_exec_wr_addr <= pdp_mem_opcode.mem_inst_addr;
				ref_int_exec_wr_data <= int_exec_rd_data + 1;
			end 
			if(pdp_mem_opcode.JMS)begin
				ref_int_exec_wr_addr <= pdp_mem_opcode.mem_inst_addr;
				ref_int_exec_wr_data <= int_PC_Value;
			end 
		end 
	end 	
	
// reference module to check the read operation 
always_comb
	begin 
		if (int_exec_rd_req == 1)begin
			if (pdp_mem_opcode.TAD || pdp_mem_opcode.AND || pdp_mem_opcode.ISZ )begin 
				reference_int_exec_rd_addr <= int_exec_rd_addr;
			end 
		else 
			reference_int_exec_rd_data <= int_exec_rd_data;
		end 
end
// reference counter for ifu_rd_req

	always_comb
		begin
			if(int_ifu_rd_req ==1 )begin 
				ifu_ref_counter = ifu_ref_counter + 1;
				end 
			else 
				ifu_ref_counter = 0 ;
		end 
		
		
// reference counter for exec_rd_req
	always_comb
		begin 
			if(int_exec_rd_req ==1)begin
				exec_ref_counter = exec_ref_counter + 1; 
				end 
			else 
				exec_ref_counter = 0 ;
			end 
		
		
					
endmodule 