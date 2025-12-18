open bakery_3procs

check bakery3_s1 {
    some A,B:Main | FSM[A] and FSM[B] and
        always 
        (
            (A.p1_line=I0 iff B.p2_line=I0) 
             and 
            (A.p2_line=I0 iff B.p1_line=I0)
             and 
            (A.p1_line=I1 iff B.p2_line=I1)
             and 
            (A.p2_line=I1 iff B.p1_line=I1)
             and 
            (A.p1_line=I4 iff B.p2_line=I4)
             and 
            (A.p2_line=I4 iff B.p1_line=I4)
        )
         and 
         eventually   
        (
            not (A.p1_line = B.p2_line) 
             or  
            not (A.p2_line = B.p1_line)
        )
} for 7 steps expect 1
