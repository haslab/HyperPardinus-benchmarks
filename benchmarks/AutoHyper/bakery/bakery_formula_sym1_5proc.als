open bakery_5procs

check bakery5_sym1 {
    all A:Main | FSM[A] implies some B:Main | FSM[B] and
        always (
            (
                (A.p1_TOKEN=T iff B.p2_TOKEN=T)
                 and 
                (A.p2_TOKEN=T iff B.p1_TOKEN=T)
                 and 
                (A.p1_line = B.p2_line)
                 and 
                (A.p2_line = B.p1_line)
                 and 
                (A.p1_TOKEN=T iff B.p3_TOKEN=T)
                 and 
                (A.p3_TOKEN=T iff B.p1_TOKEN=T)
                 and 
                (A.p1_line = B.p3_line)
                 and 
                (A.p3_line = B.p1_line)
                 and  
                (A.p1_TOKEN=T iff B.p4_TOKEN=T)
                 and 
                (A.p4_TOKEN=T iff B.p1_TOKEN=T)
                 and 
                (A.p1_line = B.p4_line)
                 and 
                (A.p4_line = B.p1_line)
                 and  
                (A.p1_TOKEN=T iff B.p5_TOKEN=T)
                 and 
                (A.p5_TOKEN=T iff B.p1_TOKEN=T)
                 and 
                (A.p1_line = B.p5_line)
                 and 
                (A.p5_line = B.p1_line)
            )
        )
} for 10 steps expect 1
