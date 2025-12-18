open bakery_5procs

check bakery5_sym2 {
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
                 and 
                (
                    (not A.p1_TOKEN=T  and  not A.p2_TOKEN=T  and  not A.p3_TOKEN=T)
                     or
                    (B.p1_TOKEN=T  or B.p2_TOKEN=T  or B.p3_TOKEN=T)
                )
            )
        )
} for 10 steps expect 1
