open bakery_3procs

check bakery3_sym1 {
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
                (A.p2_TOKEN=T iff B.p3_TOKEN=T)
                 and 
                (A.p3_TOKEN=T iff B.p2_TOKEN=T)
                 and 
                (A.p2_line = B.p3_line)
                 and 
                (A.p3_line = B.p2_line)
            )
        )
} for 10 steps expect 1
