/ Instruction 


	*0200			/ start at address 0200
Main, 	cla cll 	/ clear AC and Link
	tad A 			/ add A to Accumulator
	tad B 			/ add B
	dca C 			/ store sum at C
	hlt 			/ Halt program
	jmp Main		/ To continue - goto Main
	cla cll 
	iac 			/ Acc = 1
	and C   		/ Acc = C * Acc 
	iac 			/ Acc = Acc old + 1  
	isz				/ mem= mem + 1 
	cla cll 
	iac 
	isz 			/ increments pc = pc + 1 
	cma
	cla cll
	and D 
	rar
	rtl
	ral
	rtr
	sma
	sna
	spa
	sza
	szl 
	jms subroutine
	cla cll 
	jmp Main
	
subroutine,	tad E 
			tad F
			dca 
			jmp subroutine
						
	
	* 0300
	
	A,  1
	B,	1
	C,	0
	D,  5
	E,  2
	F,  3
				
	$Main 
