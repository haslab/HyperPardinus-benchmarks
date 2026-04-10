open util/boolean
open SNARKShared

trace sig Seq { // Sequential model
  var LeftHat : lone Node,
  var RightHat : lone Node,
  // we inline the process state here, as in sequential mode there is only one process
  // environment
  var op : one Op, // the operation
  var oparg : lone Val, // operation argument 
  var ret : lone Bool, // return code
  var retval : lone Val, // return value

  var V : Node -> lone Val, // used to signal if it is empty
  var L : Node -> lone Node,
  var R : Node -> lone Node
}

pred RunSeq[W:Seq] {
// initially
// Dummy != null and 
 (W.V)[Dummy] = Claimed // we don't really care which value
 all n:Node-Dummy | no (W.V)[n] 
// we encode Dummy statically, always exists
// Dummy->L == Dummy and Dummy->R == Dummy and
  W.L = Dummy -> Dummy 
  W.R = Dummy -> Dummy
  Dummy.(W.L) = Dummy and Dummy.(W.R) = Dummy and
// LeftHat == Dummy and RightHat == Dummy
  W.LeftHat = Dummy and W.RightHat = Dummy
// initialize processes
  no W.ret and no W.retval
// transitions
  always (stutter[W] or call[W] or pushRight[W] or pushLeft[W] or popRight[W] or popLeft[W])
}

pred noEnv[W:Seq] { no W.op and no W.oparg and no W.ret and no W.retval }
pred noNextEnv[W:Seq] { no W.op' and no W.oparg' and no W.ret' and no W.retval' }

pred stutter[W:Seq] { stutterGlobal[W] and stutterProcess[W] }
pred stutterNodes[W:Seq,ns:set Node] { all n:ns | n.(W.V)'=n.(W.V) and n.(W.L)'=n.(W.L) and n.(W.R)'=n.(W.R) }
pred stutterAllNodes[W:Seq] { stutterNodes[W,Node] }
pred stutterGlobal[W:Seq] { W.LeftHat'=W.LeftHat and W.RightHat'=W.RightHat and stutterAllNodes[W] }
pred stutterEnv[W:Seq] { W.op'=W.op and W.oparg'=W.oparg and W.ret'=W.ret and W.retval'=W.retval }
pred stutterProcess[W:Seq] { stutterEnv[W] }
pred call[W:Seq] { // calls an operation
  stutterGlobal[W] 
  no W.ret' and no W.retval'
  some W.op' & Push implies some W.oparg' - Claimed
  some W.op' & Pop implies no W.oparg'
}

pred fail[W:Seq] { // return failure
  stutterGlobal[W] and
  W.op'=W.op and W.oparg'=W.oparg and W.ret'=False and no W.retval' 
}

pred isFull[W:Seq] { all n:Node | some n.(W.V) }

// pushRight(val v) {
pred pushRight[W:Seq] {
W.op=PushRight and no W.ret and (
// nd = new Node();
// if (nd == null) return "full";
// nd->R = Dummy;
// nd->V = v;
// while (true) { // the DCAS always succeed, this cycle runs exactly once
// if (RightHat->R == RightHat) { pushRight2
// } else { pushRight3
// } } }
isFull[W] implies fail[W] else W.RightHat.(W.R)=W.RightHat implies pushRight2[W] else pushRight3[W]
) }
// nd->L = Dummy;
// if (DCAS(&RightHat, &LeftHat, RightHat, LeftHat, nd, nd))
// return "ok";
pred pushRight2[W:Seq] {
  W.op'=W.op and W.oparg'=W.oparg and W.ret'=True and no W.retval' and
  one nd:Node | no nd.(W.V) and nd.(W.V)'=W.oparg and nd.(W.L)'=Dummy and nd.(W.R)'=Dummy and stutterNodes[W,Node-nd] and
    W.LeftHat'=nd and W.RightHat'=nd
}
// nd->L = RightHat; 
// if (DCAS(&RightHat, &RightHat->R,RightHat, RightHat->R, nd, nd))
// return "ok";
pred pushRight3[W:Seq] {
  W.op'=W.op and W.oparg'=W.oparg and W.ret'=True and no W.retval' and
  one nd:Node | no nd.(W.V) and nd.(W.V)'=W.oparg and nd.(W.L)'=W.RightHat and nd.(W.R)'=Dummy and 
    W.RightHat.(W.V)'=W.RightHat.(W.V) and W.RightHat.(W.L)'=W.RightHat.(W.L) and W.RightHat.(W.R)'=nd and stutterNodes[W,Node-nd-W.RightHat] and
    W.LeftHat'=W.LeftHat and W.RightHat'=nd
}

// val pushLeft(val v) {
pred pushLeft[W:Seq] {
W.op=PushLeft and no W.ret and (
// nd = new Node(); 
// if (nd == null) return "full";
// nd->L = Dummy;
// nd->V = v;
// while (true) { // the DCAS always succeed, this cycle runs exactly once
// if (LeftHat->L == LeftHat) { pushLeft2
// } else { pushLeft3
// } } } 
isFull[W] implies fail[W] else W.LeftHat.(W.L)=W.LeftHat implies pushLeft2[W] else pushLeft3[W]
) }
// nd->R = Dummy;
// if (DCAS(&LeftHat, &RightHat, LeftHat, RightHat, nd, nd)) 
// return "okay";
pred pushLeft2[W:Seq] {
  W.op'=W.op and W.oparg'=W.oparg and W.ret'=True and no W.retval' and
  one nd:Node | no nd.(W.V) and nd.(W.V)'=W.oparg and nd.(W.L)'=Dummy and nd.(W.R)'=Dummy and stutterNodes[W,Node-nd] and
    W.LeftHat'=nd and W.RightHat'=nd
}
// nd->R = LeftHat;
// L4: if (DCAS(&LeftHat, &LeftHat->L, LeftHat, LeftHat->L, nd, nd))
// return "okay";
pred pushLeft3[W:Seq] {
  W.op'=W.op and W.oparg'=W.oparg and W.ret'=True and no W.retval' and
  one nd:Node | no nd.(W.V) and nd.(W.V)'=W.oparg and nd.(W.L)'=Dummy and nd.(W.R)'=W.LeftHat and 
    W.LeftHat.(W.V)'=W.LeftHat.(W.V) and W.LeftHat.(W.L)'=nd and W.LeftHat.(W.R)'=W.LeftHat.(W.R) and stutterNodes[W,Node-nd-W.LeftHat] and
    W.LeftHat'=nd and W.RightHat'=W.RightHat
}

// val popRight() {
pred popRight[W:Seq] {
W.op=PopRight and no W.ret and (
// while (true) { // runs exactly once
// if (RightHat->R == RightHat) return "empty";
// if (RightHat == LeftHat) { popRight2
// } else { popRight3
// } } } }
W.RightHat.(W.R)=W.RightHat implies fail[W]
else W.RightHat=W.LeftHat implies popRight2[W]
else popRight3[W]
) }
// if (DCAS(&RightHat, &LeftHat, RightHat, LeftHat, Dummy, Dummy)) 
// result=RightHat->V;
// RightHat->V=null;
// return result;
pred popRight2[W:Seq] {
  W.RightHat'=Dummy and W.LeftHat'=Dummy and
  no W.RightHat.(W.V)' and no W.RightHat.(W.L)' and no W.RightHat.(W.R)' and stutterNodes[W,Node-W.RightHat] and
  W.op'=W.op and W.oparg'=W.oparg and W.ret'=True and W.retval'=W.RightHat.(W.V)
}
// if (DCAS(&RightHat, &RightHat->L, RightHat, RightHat->L, RightHat->L, RightHat)) { 
// result = RightHat->V;
// RightHat->R = Dummy; 
// RightHat->V = null; 
// return result;
pred popRight3[W:Seq] {
  W.RightHat'=W.RightHat.(W.L) and W.LeftHat'=W.LeftHat and
  no W.RightHat.(W.V)' and no W.RightHat.(W.L)' and no W.RightHat.(W.R)' and stutterNodes[W,Node-W.RightHat] and
  W.op'=W.op and W.oparg'=W.oparg and W.ret'=True and W.retval'=W.RightHat.(W.V)
}

// val popLeft() {
pred popLeft[W:Seq] {
W.op=PopLeft and no W.ret and (
// while (true) { // runs exactly once
// if (LeftHat->L == LeftHat) return "empty"; 
// if (LeftHat == RightHat) { popLeft2
// } else { popLeft3
// } } } }
W.RightHat.(W.R)=W.RightHat implies fail[W]
else W.RightHat=W.LeftHat implies popLeft2[W]
else popLeft3[W]
) }
// if (DCAS(&LeftHat, &RightHat, LeftHat, RightHat, Dummy, Dummy))
// result = LeftHat->V;
// LeftHat->V=null;
// return result;
pred popLeft2[W:Seq] {
  W.RightHat'=Dummy and W.LeftHat'=Dummy and
  no W.LeftHat.(W.V)' and no W.LeftHat.(W.L)' and no W.LeftHat.(W.R)' and stutterNodes[W,Node-W.LeftHat] and
  W.op'=W.op and W.oparg'=W.oparg and W.ret'=True and W.retval'=W.LeftHat.(W.V)
}
// if (DCAS(&LeftHat, &LeftHat->R, LeftHat,  LeftHat->R,  LeftHat->R, LeftHat)) { 
// result = LeftHat->V;
// LeftHat->L = Dummy; 
// LeftHat->V = null;
// return result;
pred popLeft3[W:Seq] {
  W.RightHat'=W.RightHat and W.LeftHat'=W.LeftHat.(W.R) and
  no W.LeftHat.(W.V)' and no W.LeftHat.(W.L)' and no W.LeftHat.(W.R)' and stutterNodes[W,Node-W.LeftHat] and
  W.op'=W.op and W.oparg'=W.oparg and W.ret'=True and W.retval'=W.LeftHat.(W.V)
}


run { RunSeq[Seq] and eventually popLeft[Seq] and Seq.ret' = True } for 3 Val, 2 Node

