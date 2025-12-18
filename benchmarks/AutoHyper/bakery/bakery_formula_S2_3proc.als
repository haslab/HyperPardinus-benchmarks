open bakery_3procs

check bakery3_s2 {
    all A:Main | FSM[A] implies some B:Main | FSM[B] and
        always (
            (A.p1_line=I0 iff B.p2_line=I0)
             and 
            (A.p2_line=I0 iff B.p1_line=I0)
             and 
            (A.p1_line=I1 iff B.p2_line=I1)
             and 
            (A.p2_line=I1 iff B.p1_line=I1)
             and 
            (A.p1_line=I3 iff B.p2_line=I3)
             and 
            (A.p2_line=I3 iff B.p1_line=I3)
             and 
            (A.p1_line=I4 iff B.p2_line=I4)
             and 
            (A.p2_line=I4 iff B.p1_line=I4)
        )
         and 
         eventually   (
            not (A.p1_line = B.p2_line) 
             or  
            not (A.p2_line = B.p1_line)
        )
} for 12 steps expect 1
