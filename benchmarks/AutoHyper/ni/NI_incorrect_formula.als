open NI_incorrect

check ni_incorrect {
    all A:Main | FSM[A] implies some B:Main | FSM[B] and
        (
            eventually not 
                (
                    (A.PIN_2 = B.PIN_2) 
                    and
                    (A.PIN_1 = B.PIN_1) 
                    and
                    (A.PIN_0 = B.PIN_0)
                ) 
        )
        and
        ( 
            (
                A.halt=F 
                or 
                B.halt=F
            ) 
            until 
            (
                (A.halt=T and B.halt=T) 
                and
                (
                    (A.RESULT_2 = B.RESULT_2) 
                    and
                    (A.RESULT_1 = B.RESULT_1) 
                    and
                    (A.RESULT_0 = B.RESULT_0)
                )
            )
        )
} for 57 steps expect 1
