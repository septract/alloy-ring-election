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
    operation: Op, 
    target: Node, 
} 

abstract sig Op {} 

one sig Send, Recv extends Op {} 

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
    (t1.operation = Send && send[t1.target, t1, t2]) 
     ||
    (t1.operation = Recv && receive[t1.target, t1, t2]) 
} 

pred send (n: Node, t1, t2: Time) { 
    no t1.pnd[n.succ]
    t2.pnd = t1.pnd + (n.succ -> n.nid)
    t2.leader = t1.leader
}

pred receive (n: Node, t1, t2: Time) { 
    some i: t1.pnd[n] |  
    let pnd' = t1.pnd - (n -> i) |
        {
          ( i = n.nid && 
            t2.leader = t1.leader + i && 
            t2.pnd = pnd' )
           || 
          ( i in n.nid.^next && 
            t2.leader = t1.leader && 
            t2.pnd = pnd' ) 
           || 
          ( (not i in n.nid.^next) && 
            t2.leader = t1.leader && 
            t2.pnd = pnd' + (n.succ -> i) )
        } 
}

fact Trace {
    init [ first ] 
    all t: Time - last | step[t, next[t]] 
} 

assert one_leader { 
  all t: Time | lone t.leader
}

pred show {} 

pred findleader { 
    some t : Time | some t.leader
} 

assert multileader { 
    all t : Time | all i,j : NID | 
        i in t.leader && j in t.leader => i = j
} 

run show for 3 but 10 Time

// run findleader for 3 but 20 Time

// check multileader for 5 but 80 Time 
