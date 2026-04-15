open SNARKShared

abstract sig LoC {}
one sig L1,L2,L3,L4,L5,L6,Done,Error extends LoC {}

abstract sig Variant {}
one sig Buggy, Fixed extends Variant {}

// Node *Dummy, *LeftHat, *RightHat;
trace sig Con { // Concurrent model

    // selected process
    var acting : one Process,

    // Global Hats
    var LeftHat : lone Node,
    var RightHat : lone Node,
    
    // Global nodes
    var V : Node -> lone Val, // used to signal if it is null
    var L : Node -> lone Node,
    var R : Node -> lone Node,
    
    // Process environment: to mediate call or return to an operation
    var op : Process -> one Op, // the operation
    var oparg : Process -> lone Val, // operation argument 
    
    // Process state: internal state variables
    var nd : Process -> lone Node,
    var rh : Process -> lone Node,
    var lh : Process -> lone Node,
    var aux : Process -> lone Node, // for rhL,rhR,lhL,lhR (since only one is used at a time)
    var result : Process -> lone Val,
    
    // Process loc: line of code if executing an op
    var loc : Process -> one LoC, 

}

sig Process {
}

pred RunCon[W:Con,variant:Variant] {

    /*
    initially
        Dummy != null and
        Dummy->L == Dummy and
        Dummy->R == Dummy and
        LeftHat == Dummy and
        RightHat == Dummy
    */

    (W.V)[Dummy] = Claimed // we don't really care which value
    all n:Node-Dummy | no (W.V)[n]
    
    W.L = Dummy -> Dummy
    W.R = Dummy -> Dummy
    W.LeftHat = Dummy
    W.RightHat = Dummy 

    // initialize processes
    all p:Process {
        p.(W.loc)=L1
        noState[W,p]
    }
    
    // transitions
    always {
        all p:Process {
            (some p.(W.oparg) - Claimed) iff (some p.(W.op) & Push)
            (no p.(W.oparg)) iff (some p.(W.op) & Pop)
        }
    
        stutter[W] or reset[W,W.acting] or pushRight[W,W.acting] or popRight[W,W.acting,variant] or pushLeftAtomic[W,W.acting] or popLeft[W,W.acting,variant]
        
        all p2:Process-W.acting | stutterProcess[W,p2]
    }
}

// history registers only atomic events (ret)
pred isHistory[W:Con,p:Process] { 
    p.(W.loc) in Done + Error
    all p2 : Process | after p2.(W.loc) not in Done + Error // the concurrent semantics has two processes, which can both finish 2 ops in sequence. the sequential semantics requires an additional step for that (to reset call status), hence we forbid these cases
}

pred noState[W:Con,p:Process] { 
    no p.(W.nd) + p.(W.rh) + p.(W.lh) + p.(W.aux) + p.(W.result) 
}

pred stutter[W:Con] { 
    stutterGlobal[W] 
    all p:Process | stutterProcess[W,p] 
}

pred stutterHats[W:Con] {
    W.LeftHat'=W.LeftHat
    W.RightHat'=W.RightHat
}

pred stutterNodes[W:Con,ns:set Node] { 
    all n:ns | n.(W.V)'=n.(W.V) and n.(W.L)'=n.(W.L) and n.(W.R)'=n.(W.R) 
}  

pred stutterGlobal[W:Con] { 
    stutterHats[W]
    stutterNodes[W,Node]  
}

pred stutterEnv[W:Con,p:Process] { 
    p.(W.op)' = p.(W.op)
    p.(W.oparg)' = p.(W.oparg)
}

pred stutterState[W:Con,p:Process] { 
    p.(W.nd)' = p.(W.nd)
    p.(W.rh)' = p.(W.rh)
    p.(W.lh)' = p.(W.lh)
    p.(W.aux)' = p.(W.aux)
    p.(W.result)' = p.(W.result)
}

pred stutterProcess[W:Con,p:Process] { 
    stutterEnv[W,p] 
    stutterState[W,p]
    p.(W.loc)'=p.(W.loc) 
}

pred reset[W:Con,p:Process] { // exits an operation
    stutterGlobal[W] 
    p.(W.loc) in Done+Error
    p.(W.loc)' = L1
    all x:p | after noState[W,x] 
}

pred isFull[W:Con] { 
    all n:Node | some n.(W.V) 
}

pred failProcess[W:Con,p:Process] {
      stutterEnv[W,p]
      p.(W.nd)' = p.(W.nd)
      no p.(W.result')
      p.(W.lh)' = p.(W.lh)
      p.(W.rh)' = p.(W.rh)
      p.(W.aux)' = p.(W.aux) 
      p.(W.loc)' = Error
}

pred newNode[W:Con,p:Process,lptr:lone Node,rptr:lone Node,v:Val,l:LoC] { // nd == new Node(); nd->L=null; nd->R=rptr and jump to line
    stutterHats[W]
    stutterEnv[W,p] 
    one n:Node { 
        no n.(W.V) 
        n.(W.V)'=v 
        n.(W.L)'=lptr 
        n.(W.R)'=rptr 
        stutterNodes[W,Node-n] 
        p.(W.nd)'=n 
        p.(W.rh)'=p.(W.rh) 
        p.(W.lh)'=p.(W.lh) 
        p.(W.aux)'=p.(W.aux) 
        p.(W.result)'=p.(W.result)
        p.(W.loc)' = l
    }
}

pred newNode_V_nd[W:Con,p:Process,v:Val] { // nd == new Node(); nd->L=null; nd->R=rptr and jump to line
    stutterEnv[W,p] 
    one n:Node { 
        no n.(W.V) 
        n.(W.V)'=v 
        p.(W.nd)'=n 
    }
}

pred freeNode[W:Con,n:Node] { // we consider nodes with n->V=null as free
    W.V' = W.V - n -> Val
    W.L' = W.L - n -> Node
    W.R' = W.R - n -> Node
}

pred step[W:Con,p:Process,l:LoC] {
    stutterGlobal[W] 
    stepProcess[W,p,l]
}

pred stepProcess[W:Con,p:Process,l:LoC] {
    stutterEnv[W,p] 
    stutterState[W,p]
    p.(W.loc)' = l
}

pred assignState_lh[W:Con,p:Process,v:lone Node] {
    p.(W.nd)'=p.(W.nd) 
    p.(W.rh)'=p.(W.rh) 
    p.(W.lh)'=v 
    p.(W.aux)'=p.(W.aux) 
    p.(W.result)'=p.(W.result)
}

pred assignState_rh[W:Con,p:Process,v:lone Node] {
    p.(W.nd)'=p.(W.nd) 
    p.(W.lh)'=p.(W.lh) 
    p.(W.rh)'=v 
    p.(W.aux)'=p.(W.aux) 
    p.(W.result)'=p.(W.result)
}

pred assignState_aux[W:Con,p:Process,v:lone Node] {
    p.(W.nd)'=p.(W.nd) 
    p.(W.lh)'=p.(W.lh) 
    p.(W.rh)'=p.(W.rh) 
    p.(W.aux)'=v
    p.(W.result)'=p.(W.result)
}

pred assignState_result[W:Con,p:Process,v:lone Val] {
    p.(W.nd)'=p.(W.nd) 
    p.(W.lh)'=p.(W.lh) 
    p.(W.rh)'=p.(W.rh) 
    p.(W.aux)'=p.(W.aux) 
    p.(W.result)'=v
}

pred assignNode_L[W:Con,p:Process,n:Node,v:lone Node] {
    W.L' = W.L ++ n->v 
    W.R' = W.R 
    W.V' = W.V 
}
pred assignNode_R[W:Con,p:Process,n:Node,v:lone Node] {
    W.L' = W.L 
    W.R' = W.R ++ n->v
    W.V' = W.V
}

pred pushRightAtomic[W:Con,p:Process] {

    p.(W.op)=PushRight
    p.(W.loc) not in Done + Error 
    some p.(W.oparg) - Claimed
    no p.(W.result)
    
    p.(W.loc)=L1 implies {
        isFull[W] implies {
              stutterGlobal[W]
              failProcess[W,p]
        } else {
            newNode_V_nd[W,p,p.(W.oparg)]
            p.(W.nd).(W.R)' = Dummy
            p.(W.rh)' = W.RightHat
            p.(W.aux)' = (W.RightHat).(W.R)
            (W.RightHat).(W.R) = W.RightHat implies {
                p.(W.nd).(W.L)' = Dummy
                p.(W.lh)' = W.LeftHat
                W.RightHat' = p.(W.nd)'
                W.LeftHat' = p.(W.nd)'
                p.(W.result)' = p.(W.result)
                stutterNodes[W,Node-p.(W.nd)'] 
                p.(W.loc)' = Done
            } else {
                p.(W.nd).(W.L)' = p.(W.rh)'
                no p.(W.lh)'
                W.RightHat' = p.(W.nd)'
                W.LeftHat' = W.LeftHat
                p.(W.result)' = p.(W.result)
                stutterNodes[W,Node-p.(W.nd)'-W.RightHat] 
                W.RightHat.(W.V)' = W.RightHat.(W.V)
                W.RightHat.(W.L)' = W.RightHat.(W.L)
                W.RightHat.(W.R)' = p.(W.nd)'
                p.(W.loc)' = Done
            }
        }
    }
}
/*
pushRight(val v) { // var aux stands for rhR
    nd = new Node(); // L1
    if (nd == null) return "full";
    nd->R = Dummy;
    nd->V = v
    while (true) { // L2
        rh = RightHat;
        rhR = rh->R;
        if (rhR == rh) { // L3
            nd->L = Dummy;
            lh = LeftHat;
            if (DCAS(&RightHat, &LeftHat, rh, lh, nd, nd)) return "ok"; // L4
        } else { 
            nd->L = rh;
            if (DCAS(&RightHat, &rh->R, rh, rhR, nd, nd)) return "ok"; // L5
        }
    }
}
*/
pred pushRight[W:Con,p:Process] {

    p.(W.op)=PushRight
    p.(W.loc) not in Done + Error 
    some p.(W.oparg) - Claimed
    no p.(W.result)
    
    p.(W.loc)=L1 implies {
        isFull[W] implies {
              stutterGlobal[W]
              failProcess[W,p]
        } else {
            newNode[W,p,none,Dummy,p.(W.oparg),L2]
        }
    }
    
    p.(W.loc)=L2 implies {
        stutterGlobal[W] 
        stutterEnv[W,p] 
        p.(W.nd)'=p.(W.nd) 
        p.(W.rh)' = W.RightHat
        p.(W.aux)' = p.(W.rh)'.(W.R)
        p.(W.lh)' = p.(W.lh)
        p.(W.result)' = p.(W.result)
        p.(W.loc)' = L3
    }
    
    p.(W.loc)=L3 implies {
        p.(W.aux)=p.(W.rh) implies {
            stutterHats[W]
            stutterEnv[W,p] 
            assignNode_L[W,p,p.(W.nd),Dummy]
            assignState_lh[W,p,W.LeftHat]
            p.(W.loc)' = L4
        } else {
            stutterHats[W]
            assignNode_L[W,p,p.(W.nd),p.(W.rh)]
            stepProcess[W,p,L5]
        }
    }

    p.(W.loc)=L4 implies {
        (W.RightHat=p.(W.rh) and W.LeftHat=p.(W.lh)) implies {
              DCAS_RightHat_LeftHat[W,p,p.(W.nd),p.(W.nd),Done]
        } else {
            step[W,p,L2]
        }
    }
  
    p.(W.loc)=L5 implies {
          (W.RightHat=p.(W.rh) and p.(W.rh).(W.R)=p.(W.aux)) implies {
              DCAS_RightHat_rh_R[W,p,p.(W.nd),p.(W.nd),Done]
          } else {
              step[W,p,L2]
          }
    }
}

pred pushLeftAtomic[W:Con,p:Process] {

    p.(W.op)=PushLeft
    p.(W.loc) not in Done + Error 
    some p.(W.oparg) - Claimed
    no p.(W.result)
    
    p.(W.loc)=L1 implies {
        isFull[W] implies {
              stutterGlobal[W]
              failProcess[W,p]
        } else {
            newNode_V_nd[W,p,p.(W.oparg)]
            p.(W.nd).(W.L)' = Dummy
            p.(W.lh)' = W.LeftHat
            p.(W.aux)' = (W.LeftHat).(W.L)
            (W.LeftHat).(W.L) = W.LeftHat implies {
                p.(W.nd).(W.R)' = Dummy
                p.(W.rh)' = W.RightHat
                W.LeftHat' = p.(W.nd)'
                W.RightHat' = p.(W.nd)'
                p.(W.result)' = p.(W.result)
                stutterNodes[W,Node-p.(W.nd)'] 
                p.(W.loc)' = Done
            } else {
                p.(W.nd).(W.R)' = p.(W.lh)'
                no p.(W.rh)'
                W.LeftHat' = p.(W.nd)'
                W.RightHat' = W.RightHat
                p.(W.result)' = p.(W.result)
                stutterNodes[W,Node-p.(W.nd)'-W.LeftHat] 
                W.RightHat.(W.V)' = W.RightHat.(W.V)
                W.RightHat.(W.R)' = W.RightHat.(W.R)
                W.RightHat.(W.L)' = p.(W.nd)'
                p.(W.loc)' = Done
            }
        }
    }
}
/*
pushLeft(val v) { // var aux stands for lhL
    nd = new Node(); // L1
    if (nd == null) return "full";
    nd->L = Dummy;
    nd->V = v
    while (true) { // L2
        lh = LeftHat;
        lhL = lh->L;
        if (lhL == lh) { // L3
            nd->R = Dummy;
            rh = RightHat;
            if (DCAS(&LeftHat, &RightHat, lh, rh, nd, nd)) return "ok"; // L4
        } else { 
            nd->R = lh;
            if (DCAS(&LeftHat, &lh->L, lh, lhL, nd, nd)) return "ok"; // L5
        }
    }
}
*/
pred pushLeft[W:Con,p:Process] {

    p.(W.op)=PushLeft
    p.(W.loc) not in Done + Error 
    some p.(W.oparg) - Claimed
    no p.(W.result)
    
    p.(W.loc)=L1 implies {
        isFull[W] implies {
              stutterGlobal[W]
              failProcess[W,p]
        } else {
            newNode[W,p,Dummy,none,p.(W.oparg),L2]
        }
    }
    
    p.(W.loc)=L2 implies {
        stutterGlobal[W] 
        stutterEnv[W,p] 
        p.(W.nd)'=p.(W.nd) 
        p.(W.lh)' = W.LeftHat
        p.(W.aux)' = p.(W.lh)'.(W.L)
        p.(W.rh)' = p.(W.rh)
        p.(W.result)' = p.(W.result)
        p.(W.loc)' = L3
    }
    
    p.(W.loc)=L3 implies {
        p.(W.aux)=p.(W.lh) implies {
            stutterHats[W]
            stutterEnv[W,p] 
            assignNode_R[W,p,p.(W.nd),Dummy]
            assignState_rh[W,p,W.RightHat]
            p.(W.loc)' = L4
        } else {
            stutterHats[W]
            assignNode_R[W,p,p.(W.nd),p.(W.lh)]
            stepProcess[W,p,L5]
        }
    }

    p.(W.loc)=L4 implies {
        (W.LeftHat=p.(W.lh) and W.RightHat=p.(W.rh)) implies {
              DCAS_LeftHat_RightHat[W,p,p.(W.nd),p.(W.nd),Done]
        } else {
            step[W,p,L2]
        }
    }
  
    p.(W.loc)=L5 implies {
          (W.LeftHat=p.(W.lh) and p.(W.lh).(W.L)=p.(W.aux)) implies {
              DCAS_LeftHat_lh_L[W,p,p.(W.nd),p.(W.nd),Done]
          } else {
              step[W,p,L2]
          }
    }
}

pred popRight[W:Con,p:Process,v:Variant] {
  p.(W.op)=PopRight 
  no p.(W.oparg)
  p.(W.loc) not in Done + Error 
  no p.(W.result)
  (v=Buggy implies popRightBuggy[W,p] else popRightFixed[W,p])
}

/*
val popRight() { // var aux stands for rhL
    while (true) { // L1
        rh = RightHat;
        lh = LeftHat;
        if (rh->R == rh) return "empty"; // L2
        if (rh == lh) { 
            if (DCAS(&RightHat, &LeftHat, rh, lh, Dummy, Dummy)) // L3
                return rh->V; // L4
        } else {
            rhL = rh->L;
            if (DCAS(&RightHat, &rh->L, rh, rhL, rhL, rh)) { // L5
                result = rh->V; // L4
                rh->R = Dummy; // we are freeing nodes explicitely
                rh->V = null; // this makes no difference in our setting
                return result; // hence the jump to L4
            }
        }
    }
}
*/
pred popRightBuggy[W:Con,p:Process] {
    
    p.(W.loc)=L1 implies {
        stutterEnv[W,p]
        stutterGlobal[W]
        p.(W.rh)' = W.RightHat
        p.(W.lh)' = W.LeftHat
        p.(W.nd)' = p.(W.nd)
        p.(W.aux)' = p.(W.aux)
        p.(W.result)' = p.(W.result) 
        p.(W.loc)' = L2
    }
    
    p.(W.loc)=L2 implies {
        p.(W.rh).(W.R)=p.(W.rh) implies {
            stutterGlobal[W]
            failProcess[W,p]
        } else {
            p.(W.rh)=p.(W.lh) implies {
                step[W,p,L3]
            } else {
                stutterGlobal[W]
                stutterEnv[W,p]
                assignState_aux[W,p,p.(W.rh).(W.L)]
                p.(W.loc)' = L5
            }
        }
    }
   
    p.(W.loc)=L3 implies {
        (W.RightHat=p.(W.rh) and W.LeftHat=p.(W.lh)) implies {
            DCAS_RightHat_LeftHat[W,p,Dummy,Dummy,L4]
        } else {
            step[W,p,L1]
        }
    }
    
    p.(W.loc)=L4 implies { 
        stutterHats[W]
        stutterEnv[W,p] 
        freeNode[W,p.(W.rh)]
        assignState_result[W,p,p.(W.rh).(W.V)]
        p.(W.loc') = Done
    }
    
    p.(W.loc)=L5 implies {
        (W.RightHat=p.(W.rh) and p.(W.rh).(W.L)=p.(W.aux)) implies {
            DCAS_RightHat_rh_L[W,p,p.(W.aux),p.(W.rh),L4]
        } else {
            step[W,p,L1]
        }
    }
}

/*
val popRight() {
    while (true) { // L1
        rh = RightHat;
        rhL = rh->L;
        if (rh->R == rh) { // L2
            if (RightHat == rh) return "empty";
        } else { // L2
            if (DCAS (&RightHat, &rh->L, rh, rhL, rhL, rh)) { // L3
                result = rh->V; // L4
                if (result != "claimed"){
                    if (CAS(&rh->V, result, "claimed")) { // L5
                        rh->R = Dummy; // L6
                        return result;
                    } else return "empty";
                } else return "empty";
            }
        }
    }
}
*/
pred popRightFixed[W:Con,p:Process] { // var aux stands for rhL
    p.(W.loc)=L1 implies {
        stutterEnv[W,p]
        stutterGlobal[W]
        p.(W.rh)' = W.RightHat
        p.(W.aux)' = p.(W.rh).(W.L)
        p.(W.lh)' = p.(W.lh)
        p.(W.nd)' = p.(W.nd)
        p.(W.result)' = p.(W.result) 
        p.(W.loc)' = L2
    }
    
    p.(W.loc)=L2 implies {
        p.(W.rh).(W.R)=p.(W.rh) implies {
            W.RightHat = p.(W.rh) implies {
                stutterGlobal[W]
                failProcess[W,p]
            } else {
                step[W,p,L1]
            }
        } else {
            step[W,p,L3]
        }
    }
    
    p.(W.loc)=L3 implies {
        (W.RightHat=p.(W.rh) and p.(W.rh).(W.L)=p.(W.aux)) implies {
            DCAS_RightHat_rh_L[W,p,p.(W.aux),p.(W.rh),L4]
        } else {
            step[W,p,L1]
        }
    }
    
    p.(W.loc)=L4 implies { 
        stutterGlobal[W]
        stutterEnv[W,p] 
        p.(W.result') = p.(W.rh).(W.V)
        p.(W.result') = Claimed implies {
            p.(W.nd)' = p.(W.nd)
            p.(W.lh)' = p.(W.lh)
            p.(W.rh)' = p.(W.rh)
            p.(W.aux)' = p.(W.aux) 
            p.(W.loc)' = Error
        } else {
            p.(W.nd)' = p.(W.nd)
            p.(W.lh)' = p.(W.lh)
            p.(W.rh)' = p.(W.rh)
            p.(W.aux)' = p.(W.aux) 
            p.(W.loc)' = L5
        }
    }
    
    p.(W.loc)=L5 implies {
        p.(W.rh).(W.V)=p.(W.result) implies {
            CAS_rh_V[W,p,Claimed,L6]
        } else {
            stutterGlobal[W]
            failProcess[W,p]
        }
    }
    
    p.(W.loc)=L6 implies {
        stutterHats[W]
        //assignNode_R[W,p,p.(W.rh),Dummy]
        freeNode[W,p.(W.rh)]
        stepProcess[W,p,Done]
    }
}

pred popLeft[W:Con,p:Process,v:Variant] {
  p.(W.op)=PopLeft 
  no p.(W.oparg)
  p.(W.loc) not in Done + Error 
  no p.(W.result)
  (v=Buggy implies popLeftBuggy[W,p] else popLeftFixed[W,p])
}

/*
val popLeft() { // var aux stands for lhR
    while (true) { // L1
        lh = LeftHat;
        rh = RightHat; 
        if (lh->L == lh) return "empty"; // L2
        if (lh == rh) {
            if (DCAS(&LeftHat, &RightHat, lh, rh, Dummy, Dummy)) // L3
                return lh->V; // L4
        } else {
            lhR = lh->R;
            if (DCAS(&LeftHat, &lh->R, lh, lhR, lhR, lh)) { // L5
                result = lh->V; // L4
                lh->L = Dummy;
                lh->V = null; 
                return result;
            }
        }
    }
}
*/
pred popLeftBuggy[W:Con,p:Process] {
    
    p.(W.loc)=L1 implies {
        stutterEnv[W,p]
        stutterGlobal[W]
        p.(W.lh)' = W.LeftHat
        p.(W.rh)' = W.RightHat
        p.(W.nd)' = p.(W.nd)
        p.(W.aux)' = p.(W.aux)
        p.(W.result)' = p.(W.result) 
        p.(W.loc)' = L2
    }
    
    p.(W.loc)=L2 implies {
        p.(W.lh).(W.L)=p.(W.lh) implies {
            stutterGlobal[W]
            failProcess[W,p]
        } else {
            p.(W.lh)=p.(W.rh) implies {
                step[W,p,L3]
            } else {
                stutterGlobal[W]
                stutterEnv[W,p]
                assignState_aux[W,p,p.(W.lh).(W.R)]
                p.(W.loc') = L5
            }
        }
    }
   
    p.(W.loc)=L3 implies {
        (W.LeftHat=p.(W.lh) and W.RightHat=p.(W.rh)) implies {
            DCAS_LeftHat_RightHat[W,p,Dummy,Dummy,L4]
        } else {
            step[W,p,L1]
        }
    }
    
    p.(W.loc)=L4 implies { 
        stutterHats[W]
        stutterEnv[W,p]
        freeNode[W,p.(W.lh)]
        assignState_result[W,p,p.(W.lh).(W.V)]
        p.(W.loc') = Done
    }
    
    p.(W.loc)=L5 implies {
        (W.LeftHat=p.(W.lh) and p.(W.lh).(W.R)=p.(W.aux)) implies {
            DCAS_LeftHat_lh_R[W,p,p.(W.aux),p.(W.lh),L4]
        } else {
            step[W,p,L1]
        }
    }
}

/*
val popLeft() {
    while (true) { // L1
        lh = LeftHat;
        lhR = lh->R;
        if (lh->L == lh) { // L2
            if (LeftHat == lh) return "empty";
        } else { // L2
            if (DCAS (&LefttHat, &lh->R, lh, lhR, lhR, lh)) { // L3
                result = lh->V; // L4
                if (result != "claimed"){
                    if (CAS(&lh->V, result, "claimed")) { // L5
                        lh->L = Dummy; // L6
                        return result;
                    } else return "empty";
                } else return "empty";
            }
        }
    }
}
*/
pred popLeftFixed[W:Con,p:Process] { // var aux stands for lhR
    p.(W.loc)=L1 implies {
        stutterEnv[W,p]
        stutterGlobal[W]
        p.(W.lh)' = W.LeftHat
        p.(W.aux)' = p.(W.lh).(W.R)
        p.(W.rh)' = p.(W.rh)
        p.(W.nd)' = p.(W.nd)
        p.(W.result)' = p.(W.result) 
        p.(W.loc)' = L2
    }
    
    p.(W.loc)=L2 implies {
        p.(W.lh).(W.L)=p.(W.lh) implies {
            W.LeftHat = p.(W.lh) implies {
                stutterGlobal[W]
                failProcess[W,p]
            } else {
                step[W,p,L1]
            }
        } else {
            step[W,p,L3]
        }
    }
    
    p.(W.loc)=L3 implies {
        (W.LeftHat=p.(W.lh) and p.(W.lh).(W.R)=p.(W.aux)) implies {
            DCAS_LeftHat_lh_R[W,p,p.(W.aux),p.(W.lh),L4]
        } else {
            step[W,p,L1]
        }
    }
    
    p.(W.loc)=L4 implies { 
        stutterGlobal[W]
        stutterEnv[W,p] 
        p.(W.result') = p.(W.lh).(W.V)
        p.(W.result') = Claimed implies {
            p.(W.nd)' = p.(W.nd)
            p.(W.lh)' = p.(W.lh)
            p.(W.rh)' = p.(W.rh)
            p.(W.aux)' = p.(W.aux) 
            p.(W.loc)' = Error
        } else {
            p.(W.nd)' = p.(W.nd)
            p.(W.lh)' = p.(W.lh)
            p.(W.rh)' = p.(W.rh)
            p.(W.aux)' = p.(W.aux) 
            p.(W.loc)' = L5
        }
    }
    
    p.(W.loc)=L5 implies {
        p.(W.lh).(W.V)=p.(W.result) implies {
            CAS_lh_V[W,p,Claimed,L6]
        } else {
            stutterGlobal[W]
            failProcess[W,p]
        }
    }
    
    p.(W.loc)=L6 implies {
        stutterHats[W]
        //assignNode_L[W,p,p.(W.lh),Dummy]
        freeNode[W,p.(W.lh)]
        stepProcess[W,p,Done]
    }
}

//boolean DCAS(val *addr1, val *addr2, val old1, val old2, val new1, val new2) {
// atomically {
// if ((*addr1 == old1) && (*addr2 == old2)) {
// *addr1 = new1;
// *addr2 = new2;
// return true;
// } else return false;
// }}
pred DCAS_RightHat_LeftHat[W:Con,p:Process,new1:Node,new2:Node,l:LoC] {
  W.RightHat'=new1 
  W.LeftHat'=new2 
  stutterNodes[W,Node]  
  p.(W.loc)'=l 
  stutterEnv[W,p]
  stutterState[W,p]
}
pred DCAS_RightHat_rh_R[W:Con,p:Process,new1:Node,new2:Node,l:LoC] {
  W.RightHat'=new1 
  W.LeftHat'=W.LeftHat 
  p.(W.rh).(W.V)'=p.(W.rh).(W.V) 
  p.(W.rh).(W.L)'=p.(W.rh).(W.L) 
  p.(W.rh).(W.R)'=new2 
  stutterNodes[W,Node-p.(W.rh)] 
  p.(W.loc)'=l 
  stutterEnv[W,p] 
  stutterState[W,p]
}
pred DCAS_RightHat_rh_L[W:Con,p:Process,new1:Node,new2:Node,l:LoC] {
  W.RightHat'=new1 
  W.LeftHat'=W.LeftHat 
  p.(W.rh).(W.V)'=p.(W.rh).(W.V) 
  p.(W.rh).(W.L)'=new2 
  p.(W.rh).(W.R)'=p.(W.rh).(W.R) 
  stutterNodes[W,Node-p.(W.rh)] 
  p.(W.loc)'=l 
  stutterEnv[W,p]
  stutterState[W,p]
}
pred DCAS_LeftHat_RightHat[W:Con,p:Process,new1:Node,new2:Node,l:LoC] {
  W.RightHat'=new2 
  W.LeftHat'=new1 
  stutterNodes[W,Node] 
  p.(W.loc)'=l 
  stutterEnv[W,p]
  stutterState[W,p]
}
pred DCAS_LeftHat_lh_L[W:Con,p:Process,new1:Node,new2:Node,l:LoC] {
  W.RightHat'=W.RightHat 
  W.LeftHat'=new1 
  p.(W.lh).(W.V)'=p.(W.lh).(W.V) 
  p.(W.lh).(W.L)'=new2 
  p.(W.lh).(W.R)'=p.(W.lh).(W.R) 
  stutterNodes[W,Node-p.(W.lh)] 
  p.(W.loc)'=l 
  stutterEnv[W,p]
  stutterState[W,p]
}
pred DCAS_LeftHat_lh_R[W:Con,p:Process,new1:Node,new2:Node,l:LoC] {
  W.RightHat'=W.RightHat 
  W.LeftHat'=new1 
  p.(W.lh).(W.V)'=p.(W.lh).(W.V) 
  p.(W.lh).(W.L)'=p.(W.lh).(W.L) 
  p.(W.lh).(W.R)'=new2 
  stutterNodes[W,Node-p.(W.lh)] 
  p.(W.loc)'=l 
  stutterEnv[W,p] 
  stutterState[W,p]
}
pred CAS_rh_V[W:Con,p:Process,new:Val,l:LoC] {
  W.RightHat'=W.RightHat 
  W.LeftHat'=W.LeftHat 
  p.(W.rh).(W.V)'=new 
  p.(W.rh).(W.L)'=p.(W.rh).(W.L) 
  p.(W.rh).(W.R)'=p.(W.rh).(W.R) 
  stutterNodes[W,Node-p.(W.rh)] 
  p.(W.loc)'=l 
  stutterEnv[W,p] 
  stutterState[W,p]
} 
pred CAS_lh_V[W:Con,p:Process,new:Val,l:LoC] {
  W.RightHat'=W.RightHat 
  W.LeftHat'=W.LeftHat 
  p.(W.lh).(W.V)'=new 
  p.(W.lh).(W.L)'=p.(W.lh).(W.L) 
  p.(W.lh).(W.R)'=p.(W.lh).(W.R) 
  stutterNodes[W,Node-p.(W.lh)] 
  p.(W.loc)'=l 
  stutterEnv[W,p] 
  stutterState[W,p]
} 

run EmptyNeverEmptyBuggy {
  RunCon[Con,Buggy]
  some disj p:Process {
    eventually {
      p.(Con.op) = PopRight and p.(Con.loc) = L1 and Con.LeftHat != Dummy and Con.RightHat != Dummy
      (p.(Con.op) = PopRight and Con.LeftHat != Dummy and Con.RightHat != Dummy) until (p.(Con.op) = PopRight and p.(Con.loc) = Error)
  } }
} for 19..20 steps, 2 Val, 3 Node, 2 Process expect 1 // ~4min sat4j, with initial state empty, needs 18 steps
--} for 13..20 steps, 2 Val, 3 Node, 2 Process expect 1 // ~1min sat4j, with initial state non-empty, needs 13 steps

run EmptyNeverEmptyFixed {
  RunCon[Con,Fixed]
  some disj p:Process {
    eventually {
      p.(Con.op) = PopRight and p.(Con.loc) = L1 and Con.LeftHat != Dummy and Con.RightHat != Dummy
      (p.(Con.op) = PopRight and Con.LeftHat != Dummy and Con.RightHat != Dummy) until (p.(Con.op) = PopRight and p.(Con.loc) = Error)
  } }
} for 19..20 steps, 2 Val, 3 Node, 2 Process expect 0 // >10min sat4j, with initial state empty
--} for 13..20 steps, 2 Val, 3 Node, 2 Process expect 0 // 5min sat4j, with initial state non-empty

