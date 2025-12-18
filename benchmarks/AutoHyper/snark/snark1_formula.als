open snark1_M1_concurrent as M1
open snark1_M2_sequential as M2

check snark {
    all A:M1/Main | M1/FSM[A] implies some X:M2/Main | M2/FSM[X] and
        (always (not M1/FAIL[A]) implies
        (always ((
                (
                            (M1/proc1_popRightSTART[A] iff M2/proc1_popRightSTART[X]) and
                            (M1/proc1_popRightEND[A] iff M2/proc1_popRightEND[X]) and
                            (M1/proc1_pushRightSTART[A] iff M2/proc1_pushRightSTART[X]) and     
                            (M1/proc1_pushRightEND[A] iff M2/proc1_pushRightEND[X]) and
                            (M1/proc1_popLeftSTART[A] iff M2/proc1_popLeftSTART[X]) and
                            (M1/proc1_popLeftEND[A] iff M2/proc1_popLeftEND[X]) and 
                            (M1/proc2_popRightSTART[A] iff M2/proc2_popRightSTART[X]) and   
                            (M1/proc2_popRightEND[A] iff M2/proc2_popRightEND[X]) and
                            (M1/proc2_pushRightSTART[A] iff M2/proc2_pushRightSTART[X]) and 
                            (M1/proc2_pushRightEND[A] iff M2/proc2_pushRightEND[X]) and
                            (M1/proc2_popLeftSTART[A] iff M2/proc2_popLeftSTART[X]) and
                            (M1/proc2_popLeftEND[A] iff M2/proc2_popLeftEND[X])
                        )
                        and
                        (
                            (A.popRightFAIL = F iff X.popRightFAIL = F)
                        )
             )
        )
))
} for 41 steps expect 1
