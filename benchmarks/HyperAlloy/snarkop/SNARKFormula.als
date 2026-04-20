// DCAS is not a Silver Bullet for Nonblocking Algorithm Design
// https://doi.org/10.1145/1007912.1007945

open SNARKShared as V
open SNARKConcurrent as C
open SNARKSequential as S

pred Linearizability[vari:C/Variant] {
  all A:C/Con | RunCon[A,vari] implies
    some B:S/Seq | RunSeq[B] and sameOps[A,B] and
      always sameHistory[A,B]
}

pred sameOps[A:C/Con,B:S/Seq] {
	A._op = B._op
	A._ag = B._ag
}

pred sameHistory[A:C/Con,B:S/Seq] {
    Process.(A.loc) in Done+Error implies Process.(A.log) = B.log
}

// The concurrent semantics is in fact not linearizable since multiple processes can terminate in consecutive states, while in the sequential semantics additional reset steps are needed. We ignore such cases by assigning higher priority to reset.
pred noConsecutiveHistories[W:Con] {
    all p : Process | p.(W.loc) in Done + Error implies after p.(W.loc) = L1
}

// not (p.(W.loc)=Error and some p.(W.op) & Push)

assert Incorrect { Linearizability[Buggy] }
check Incorrect for exactly 2 Val, exactly 2 Process, exactly 3 Node, 30 steps, exactly 4 OpId expect 1

assert Correct { Linearizability[Fixed] }
check Correct for exactly 2 Val, exactly 2 Process, exactly 3 Node, 30 steps, exactly  3 OpId expect 0
