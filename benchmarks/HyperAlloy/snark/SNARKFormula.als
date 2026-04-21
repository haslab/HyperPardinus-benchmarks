// DCAS is not a Silver Bullet for Nonblocking Algorithm Design
// https://doi.org/10.1145/1007912.1007945

open SNARKShared as V
open SNARKConcurrent as C
open SNARKSequential as S

pred Linearizability[vari:C/Variant] {
  all A:C/Con | RunCon[A,vari] implies always (notFail[A,vari] and noConsecutiveHistories[A]) implies
    some B:S/Seq | RunSeq[B] and
      always sameHistory[A,B]
}

pred sameHistory[A:C/Con,B:S/Seq] {
    all p:Process | isHistory[A,p] implies {
        p.(A.op)=B.op
        p.(A.oparg)=B.oparg
        p.(A.result)=B.retval
        p.(A.loc)=Done iff B.ret=True
        p.(A.loc)=Error iff B.ret=False
    }
}

pred isHistory[W:Con,p:Process] { 
    p.(W.loc) in Done + Error
}

// The concurrent semantics is in fact not linearizable since multiple processes can terminate in consecutive states, while in the sequential semantics additional reset steps are needed. We ignore such cases by assigning higher priority to reset.
pred noConsecutiveHistories[W:Con] {
    all p : Process | p.(W.loc) in Done + Error implies after p.(W.loc) = L1
}

// clearly not sequentially consistent. ignore bugs that we know are linearizable to find the bug from the paper
pred notFail[W:Con,vari:C/Variant] {
    all p : Process {
    
        // no later error because of early acquired resource
        (p.(W.loc) = L2 and some p.(W.op) & Pop and p.(W.rh).(W.R)=p.(W.rh)) implies not p.(W.rh) = Dummy
        
        // atomic after DCAS
        vari=Buggy implies {
            (p.(W.loc) = L3 and some p.(W.op) & Pop) implies p.(W.loc)' = L4
            (p.(W.loc) = L5 and some p.(W.op) & Pop) implies p.(W.loc)' = L6
            (p.(W.loc) = L4 and some p.(W.op) & Pop) implies p.(W.loc)' = Done
            (p.(W.loc) = L6 and some p.(W.op) & Pop) implies p.(W.loc)' = Done
        } else {
            (p.(W.loc) = L4 and some p.(W.op) & Pop) implies after (p.(W.loc) in Error + L5)
            (p.(W.loc) = L5 and some p.(W.op) & Pop) implies after (p.(W.loc) in Error + L6)
            (p.(W.loc) = L6 and some p.(W.op) & Pop) implies after (p.(W.loc) = Done)
        }
    }
}

// not (p.(W.loc)=Error and some p.(W.op) & Push)

assert Incorrect { Linearizability[Buggy] }
check Incorrect for exactly 2 Val, exactly 2 Process, exactly 3 Node, 30 steps expect 1
// bug1 found with k=8

assert Correct { Linearizability[Fixed] }
check Correct for exactly 2 Val, exactly 2 Process, exactly 3 Node, 30 steps expect 0

