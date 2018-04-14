module ringElection 

open util/ordering[Time] 
open util/ordering[NID] 

sig NID {} 

sig Node {  
    nid: NID, 
    succ: Node, 
} 

sig Time {
    leader: set NID, 
    pnd: Node -> NID, 
    // op: Node -> Op, 
} 

// abstract sig Op {} 

// one sig Skip, Send, Recv extends Op {} 

fact unique_ids { 
    all n, m: Node | (n.nid = m.nid) => n=m
    all i: NID | some nid.i
} 

fact ring_topology { 
    all n, m: Node | m in n.^succ
} 

pred init (t: Time) { 
    no t.pnd 
    no t.leader 
//    all n: Node | (t.op)[n] = Skip
} 

pred step (t1, t2: Time) { 
    some n: Node | { 
        send[n, t1, t2] 
         || 
        receive[n, t1, t2] 
    } 
} 

pred send (n: Node, t1, t2: Time) { 
}

pred receive (n: Node, t1, t2: Time) { 
    
}

fact Trace {
    init [ first ] 
    all t: Time - last | step[t, next[t]] 
} 

assert one_leader { 
  all t: Time | lone t.leader
}

pred show {} 

run show for 3 but 2 Time
