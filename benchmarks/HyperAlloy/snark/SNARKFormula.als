// DCAS is not a Silver Bullet for Nonblocking Algorithm Design
// https://doi.org/10.1145/1007912.1007945

open SNARKShared as V
open SNARKConcurrent as C
open SNARKSequential as S

pred Linearizability[vari:C/Variant] {
  all A:C/Con | RunCon[A,vari] implies 
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

assert Incorrect { Linearizability[Buggy] }
check Incorrect for exactly 1 Val, exactly 2 Process, exactly 3 Node, 30 steps expect 1

assert Correct { Linearizability[Fixed] }
check Correct for exactly 2 Val, exactly 2 Process, exactly 3 Node, 30 steps expect 0

