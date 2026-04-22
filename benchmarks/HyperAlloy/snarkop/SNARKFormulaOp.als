// DCAS is not a Silver Bullet for Nonblocking Algorithm Design
// https://doi.org/10.1145/1007912.1007945

open SNARKSharedOp as V
open SNARKConcurrentOp as C
open SNARKSequentialOp as S


pred Linearizability[vari:C/Variant] {
  all A:C/Con | RunCon[A,vari] implies
    some B:S/Seq | RunSeq[B] and sameOps[A,B] and always precedes[A,B]
}

pred precedes[A:C/Con,B:S/Seq] {
	Process.(A.loc) in Done+Error implies // stable point
		{ 
			A._log = B.log
		 	A._pre in B.pre
		}
}

pred sameOps[A:C/Con,B:S/Seq] {
	A._op = B._op
	A._ag = B._ag
}

/*pred sameHistory[A:C/Con,B:S/Seq] {
    Process.(A.loc) in Done+Error implies Process.(A.log) = B.log
}*/

pred samePrecedes[op1 : one OpId, op2 : one OpId, A:C/Con , B:S/Seq] {
    (some p : Process | p.(A.op) = op1 and some p.(A.loc) and p.(A.loc) in Done+Error and after (eventually p.(A.op) = op2)) implies {
        (B.op) = op1 and some B.ret and after (eventually B.op = op2)
    }
}

assert Incorrect { Linearizability[Buggy] }
check Incorrect for exactly 2 Val, exactly 2 Process, exactly 3 Node, 30 steps, exactly 4 OpId expect 1

assert Correct { Linearizability[Fixed] }
check Correct for exactly 2 Val, exactly 2 Process, exactly 3 Node, 30 steps, exactly  3 OpId expect 0

/*

run Ok {
  RunCon[Con,Buggy]
  Ok[Con]
  RunSeq[Seq]
  sameOps[Con,Seq]

  eventually (some Seq.pre and precedes[Con,Seq])
} for 1..16 steps, 3 Val, 3 Node, 2 Process, 4 OpId expect 1

run Bug1 {
  RunCon[Con,Buggy]
  Bug1[Con]
  RunSeq[Seq]
  sameOps[Con,Seq]
  always precedes[Con,Seq]
} for 1..16 steps, 3 Val, 3 Node, 2 Process, 4 OpId expect 0

*/
