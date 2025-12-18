open robotic_robustness_100

check robot_robustness_100 {
    some A:Main | FSM[A] and all B:Main | FSM[B] implies
        (eventually A.GOAL=T)
        and
        (always
            (
                (A.act=I1 iff B.act=I1)
                and
                (A.act=I2 iff B.act=I2)
                and
                (A.act=I3 iff B.act=I3)
                and
                (A.act=I4 iff B.act=I4)
            )
            implies
            (eventually B.GOAL=T)
        )
} for 20 steps expect 1

