open NRP_correct

check nrp_correct { 

	    some A:Main | FSM[A] and all B:Main | FSM[B] implies
	    (
	        (eventually A.line=I3) 
	        and 
	        (eventually A.line=I5) 
	        and 
	        (eventually A.line=I6)
	    ) 
	    and
	    ( 
	        (always
	            (A.sender_actions = B.sender_actions)
	        ) 
	        implies 
	        (
	            (eventually
	                B.line=I5
	            ) 
	            iff 
	            (eventually
	                B.line=I6
	            )
	        ) 
	    ) 
	    and
	    ( 
	        (always 
	            (A.receiver_actions = B.receiver_actions) 
	        ) 
	        implies 
	        (
	            (eventually 
	                B.line=I5
	            )
	            iff 
	            (eventually 
	                B.line=I6
	            )
	        ) 
	    )
} for 15 steps expect 0