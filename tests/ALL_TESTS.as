/ INSTRUCTION : CIA

*200
Main,	cla cll		
		tad A		
		and C				
		cma			
		cml			
		iac			
		isz			
		jmp Next
		
Done:	dca Z
		hlt	

Next:	nop			
		and D
		ral
		rar
		rtl
		rtr
		skp
		tad B
		sma
		sna
		snl
		spa
		sza
		szl
		jmp Done
		
		
*3000				/ Place data at 3000
		A,	1		
		B,	2
		C,	3
		D, 	4
		Z,  0
$Main