/this assembly file is directed to cover all the test cases ,it includes all the instrutions 
/it is a deterministic type of stimuli which follows certain pattern to achieve all possible test conditions.
/main highlights include : to check if the link bit is generated and complemented,
						 / to check condition for isz with 0 and non-zero memory contents
						 / subroutines and jumps 
						 / to check if the instruction are turned as NOP which are not supported by the DUT 

	*0200			/ start at address 0200
Main, 	cla cll 	/ clear AC and Link
	tad A 			/ add A 
	tad B 			/ add B  
	dca C 			/ store sum at C
	cla cll 		/ clear AC and Link 
	iac 			/ Acc = Acc + 1 
	and B   		/ Acc = B * Acc   
	isz				/ mem= mem + 1 
	cla cll 		/ clear AC and Link 
	dca				/ deposit contents of Acc and clear it 
	isz 			/ increments pc = pc + 1 
	cma				/ complement ACC 
	and D 			/ And D 
	rar				/ rotate accumulator and link right 
	rtl				/ rotate accumulator and link left twice
	ral				/ rotate accumulator and link left 
	rtr				/  rotate accumulator and link right twice
	sma				/ skip on minus Acc
	sna				/ skip on non-zero Acc
	spa				/ skip on positive Acc 
	sza				/ skip on non -zero Acc 
	szl 			/ skip on zero link 
	jms subroutine	/ jump to subroutine
done,jmp exit       / unconditional jump 
	
subroutine,	tad E 	/ add E
			dca F   / deposit Acc to F and clear 
			jmp done/ unconditional jump

exit, hlt			/ halt 			
	
// memory locations which store the data 
	* 0300
	
	A,  7777
	B,	1
	C,	0
	D,  1055
	E,  2
	F,  0				
	$Main 
