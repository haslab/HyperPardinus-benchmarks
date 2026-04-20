open util/boolean
open SNARKShared

trace sig Seq { // Sequential model
  var LeftHat : lone Node,
  var RightHat : lone Node,

  var ret : lone Bool, // return code
  var retval : lone Val, // return value

  var op : one OpId, // the operation
  var log : set OpId,

  _op : OpId -> one Op,
  _ag : OpId -> lone Val,

  var V : Node -> lone Val, // used to signal if it is empty
  var L : Node -> lone Node,
  var R : Node -> lone Node
}

pred RunSeq[W:Seq] {
    (W.V)[Dummy] = Claimed // we don't really care which value
    all n:Node-Dummy | no (W.V)[n] 
    W.L = Dummy -> Dummy 
    W.R = Dummy -> Dummy
    Dummy.(W.L) = Dummy
    Dummy.(W.R) = Dummy
    W.LeftHat = Dummy
    W.RightHat = Dummy
    no W.ret and no W.retval and no W.log

	W._ag in (W._op).Push -> one (Val - Claimed)

    // transitions
    always {
        stutter[W] or reset[W] or pushRight[W] or pushLeft[W] or popRight[W] or popLeft[W]
		some W.ret' implies W.log' = W.log + W.op else W.log' = W.log
    }
}

pred noEnv[W:Seq] { no W.ret and no W.retval }
pred noNextEnv[W:Seq] { no W.ret' and no W.retval' }

pred stutter[W:Seq] { stutterGlobal[W] and stutterProcess[W] }
pred stutterNodes[W:Seq,ns:set Node] { all n:ns | n.(W.V)'=n.(W.V) and n.(W.L)'=n.(W.L) and n.(W.R)'=n.(W.R) }
pred stutterAllNodes[W:Seq] { stutterNodes[W,Node] }
pred stutterGlobal[W:Seq] { W.LeftHat'=W.LeftHat and W.RightHat'=W.RightHat and stutterAllNodes[W] }
pred stutterEnv[W:Seq] { W.op'=W.op and W.ret'=W.ret and W.retval'=W.retval }
pred stutterProcess[W:Seq] { stutterEnv[W] }
pred reset[W:Seq] { // calls a new operation
    stutterGlobal[W]
    some W.ret
    no W.ret'
    no W.retval'
	W.op' not in W.log
}

pred fail[W:Seq] { // return failure
    stutterGlobal[W]
    W.op'=W.op
    W.ret'=False
    no W.retval' 
}

pred isFull[W:Seq] { all n:Node | some n.(W.V) }

pred pushRight[W:Seq] {
    W.op.(W._op)=PushRight
    no W.ret
    isFull[W] implies {
        fail[W]
    } else {
        W.RightHat.(W.R)=W.RightHat implies pushRight2[W] else pushRight3[W]
    }
}
pred pushRight2[W:Seq] {
    W.op'=W.op
    W.ret'=True
    no W.retval'
    one nd:Node {
        no nd.(W.V)
        nd.(W.V)'=W.op.(W._ag)
        nd.(W.L)'=Dummy
        nd.(W.R)'=Dummy
        stutterNodes[W,Node-nd]
        W.LeftHat'=nd and W.RightHat'=nd
    }
}
pred pushRight3[W:Seq] {
    W.op'=W.op
    W.ret'=True
    no W.retval'
    one nd:Node {
        no nd.(W.V)
        nd.(W.V)'=W.op.(W._ag)
        nd.(W.L)'=W.RightHat
        nd.(W.R)'=Dummy
        W.RightHat.(W.V)'=W.RightHat.(W.V)
        W.RightHat.(W.L)'=W.RightHat.(W.L)
        W.RightHat.(W.R)'=nd
        stutterNodes[W,Node-nd-W.RightHat]
        W.LeftHat'=W.LeftHat
        W.RightHat'=nd
    }
}

pred pushLeft[W:Seq] {
    W.op.(W._op)=PushLeft
    no W.ret
    isFull[W] implies {
        fail[W]
    } else {
        W.LeftHat.(W.L)=W.LeftHat implies pushLeft2[W] else pushLeft3[W]
    }
}
pred pushLeft2[W:Seq] {
    W.op'=W.op
    W.ret'=True
    no W.retval'
    one nd:Node {
        no nd.(W.V)
        nd.(W.V)'=W.op.(W._ag)
        nd.(W.L)'=Dummy
        nd.(W.R)'=Dummy
        stutterNodes[W,Node-nd]
        W.LeftHat'=nd
        W.RightHat'=nd
    }
}
pred pushLeft3[W:Seq] {
    W.op'=W.op
    W.ret'=True
    no W.retval'
    one nd:Node {
        no nd.(W.V)
        nd.(W.V)'=W.op.(W._ag)
        nd.(W.L)'=Dummy
        nd.(W.R)'=W.LeftHat
        W.LeftHat.(W.V)'=W.LeftHat.(W.V)
        W.LeftHat.(W.L)'=nd
        W.LeftHat.(W.R)'=W.LeftHat.(W.R)
        stutterNodes[W,Node-nd-W.LeftHat]
        W.LeftHat'=nd
        W.RightHat'=W.RightHat
    }
}

pred popRight[W:Seq] {
    W.op.(W._op)=PopRight
    no W.ret
    W.RightHat.(W.R)=W.RightHat implies {
        fail[W]
    } else {
        W.RightHat=W.LeftHat implies popRight2[W] else popRight3[W]
    }
}
pred popRight2[W:Seq] {
    W.RightHat'=Dummy
    W.LeftHat'=Dummy
	W.V' = W.V
	W.R' = W.R
	W.L' = W.L
--    no W.RightHat.(W.V)'
--    no W.RightHat.(W.L)'
--    no W.RightHat.(W.R)'
    stutterNodes[W,Node-W.RightHat]
    W.op'=W.op
    W.ret'=True
    W.retval'=W.RightHat.(W.V)
}
pred popRight3[W:Seq] {
    W.RightHat'=W.RightHat.(W.L)
    W.LeftHat'=W.LeftHat
	W.V' = W.V
	W.R' = W.R
	W.L' = W.L ++ W.RightHat -> W.RightHat
--    no W.RightHat.(W.V)'
--    no W.RightHat.(W.L)'
--    no W.RightHat.(W.R)'
    stutterNodes[W,Node-W.RightHat]
    W.op'=W.op
    W.ret'=True
    W.retval'=W.RightHat.(W.V)
}

pred popLeft[W:Seq] {
    W.op.(W._op)=PopLeft
    no W.ret
    W.LeftHat.(W.L)=W.LeftHat implies {
        fail[W]
    } else {
        W.LeftHat=W.RightHat implies popLeft2[W] else popLeft3[W]
    }
}
pred popLeft2[W:Seq] {
    W.LeftHat'=Dummy
    W.RightHat'=Dummy
	W.V' = W.V
	W.R' = W.R
	W.L' = W.L
--    no W.LeftHat.(W.V)'
--    no W.LeftHat.(W.L)'
--    no W.LeftHat.(W.R)'
    stutterNodes[W,Node-W.LeftHat]
    W.op'=W.op
    W.ret'=True
    W.retval'=W.LeftHat.(W.V)
}
pred popLeft3[W:Seq] {
    W.RightHat'=W.RightHat
    W.LeftHat'=W.LeftHat.(W.R)
	W.V' = W.V
	W.R' = W.R ++ W.LeftHat -> W.LeftHat
	W.L' = W.L
--    no W.LeftHat.(W.V)'
--    no W.LeftHat.(W.L)'
--    no W.LeftHat.(W.R)'
    stutterNodes[W,Node-W.LeftHat]
    W.op'=W.op
    W.ret'=True
    W.retval'=W.LeftHat.(W.V)
}

run { RunSeq[Seq]
	  pushRight[Seq];no none;
	  pushRight[Seq];no none;
	  popRight[Seq];no none;
      popRight[Seq];Seq.ret = True 
} for 3 Val, 3 Node, 4 OpId

run { RunSeq[Seq] and eventually popLeft[Seq] and Seq.ret' = True } for 3 Val, 2 Node, 3 OpId
