
	property ifu_read_request_assertion;

	@(posedge clk) (ifu_ref_counter ==1) |->##[0:1] !int_ifu_rd_req ;
	endproperty

	property exec_read_request_assertion; 
	@(posedge clk)(exec_ref_counter ==1) |->##[0:1] !int_exec_rd_req;
	endproperty;
	
////////////////////////
// Assertions 
/////////////////////////

	always @ (posedge clk)
	begin 
	A1: assert property (ifu_read_request_assertion)
		else 
			$display("ERROR:Assertion failed: FSM stays for more than one cycle in send_req stage");
			
	
	A2: assert property (exec_read_request_assertion)
		else 
			$display("ERROR:Assertion failed: FSM stays for more than one cycle in Mem_rd_req stage ");
			
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