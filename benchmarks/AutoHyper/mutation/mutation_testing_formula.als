open mutation_testing

check mutation { 
        some A:Main | FSM[A] and all B:Main | FSM[B] implies
        (
            (
                A.action = B.action
            ) 
            until 
            ( 
                (A.beverage = B.beverage) 
                or
                (A.water = B.water) 
                or
                not (A.NO_water=T iff B.NO_water=T) 
                or
                not (A.NO_output=T iff B.NO_output=T)
            )
        )
} for 8 steps expect 0
