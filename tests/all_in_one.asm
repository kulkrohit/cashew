/ Instruction 


	*0200  						/ start address  
	Main ,  		cla cll 	/ clear Accumulator and link 
					tad A   	/ add A to acc
					tad B   	/ add A + B 
					dca C   	/ stores the result of A + B  in c 
					
					/cla cll 
					/iac 		/ Acc = 1
					/and C   	/ Acc = C * Acc 
					/iac 		/ Acc = Acc old + 1  
					/isz			/ mem= mem + 1 
					/cla cll 
					/iac 
					/isz 		/ increments pc = pc + 1 
					/cma
					/cla cll
					/and D 
					
					/rar
					/rtl
					/ral
					/rtr
					/sma
					/sna
					/spa
					/sza
					/szl 
					/jms subroutine
					/cla cll 
					
					jmp main 
		
	/subroutine,	tad E 
				/	tad F
				/	dca 
				/	jmp subroutine
					
			
			
	* 2000
					A,  1
					B,	1
					C,	7
					D,	1
					E,  2
					F,  4
			
	
	$Main 
