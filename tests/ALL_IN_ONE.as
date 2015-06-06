/ Instruction 


	*0200			/ start at address 0200
Main, 	cla cll 	/ clear AC and Link
	tad A 			/ add A to Accumulator A = 7777
	tad B 			/ add B  7777+ 1 
	dca C 			/ store sum at C
	cla cll 
	iac 			/ Acc = Acc + 1 
	and B   		/ Acc = B * Acc   
	isz				/ mem= mem + 1 
	cla cll 
	dca
	isz 			/ increments pc = pc + 1 
	cma
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
done,jmp exit 
	
subroutine,	tad E 
			dca F
			jmp done

exit, hlt						
	

	* 0300
	
	A,  7777
	B,	1
	C,	0
	D,  1055
	E,  2
	F,  0				
	$Main 
