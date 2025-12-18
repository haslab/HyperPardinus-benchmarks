open robotic_sp_100

check robot_sp_100 {
    some A:Main | FSM[A] and all B:Main | FSM[B] implies
        (eventually (A.GOAL=T))
        and
        (always
            (
                (A.GOAL=F)
                implies
                (B.GOAL=F)
            )
        )
} for 20 steps expect 1


