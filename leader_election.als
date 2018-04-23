module leaderElection 

open util/ordering[Time]

abstract sig Msg {} 
one sig Request, Vote extends Msg {} 

sig Node {} 

sig Time { 
    msg: Node -> Msg -> Node,
    alreadyvoted: set Node, 
    leader: set Node, 
    voters: Node -> Node, 
} 

pred init (t: Time) { 
    no t.msg
    no t.alreadyvoted
    no t.leader 
    no t.voters
} 

pred step (t1, t2: Time) { 
    some n : Node | {
        client_request [n, t1, t2] 
          ||
        recv [n, t1, t2] 
    } 
     || 
    skip[t1, t2] 
} 

pred client_request ( n: Node, t1, t2: Time ) {
    not n in t1.alreadyvoted 
    t2.msg = t1.msg + (n -> Request -> (Node - n)) 
    t2.alreadyvoted = t1.alreadyvoted + n 
    t2.voters = t1.voters 
    t2.leader = t1.leader 
} 

pred recv ( n: Node, t1, t2: Time ) {
    some src: Node | { 
        { (src -> Request -> n) in t1.msg 
            && 
          handle_request[n, src, t1, t2] } 
          
          || 

        { (src -> Vote -> n) in t1.msg 
            && 
          handle_vote[n, src, t1, t2] } 
    }
} 

pred handle_request ( n, src: Node, t1, t2: Time ) {
    not n in t1.alreadyvoted 
    t2.msg = (t1.msg - (src -> Request -> n)) + (n -> Vote -> src) 
    t2.alreadyvoted = t1.alreadyvoted + n 
    t2.voters = t1.voters 
    t2.leader = t1.leader 
} 

pred handle_vote ( n, src: Node, t1, t2: Time ) {
    t2.msg = t1.msg - (src -> Vote -> n)
    t2.alreadyvoted = t1.alreadyvoted
    t2.voters = t1.voters + (n -> src) 
    { 
        ( quorum[ t1.voters[n] ] && t2.leader = t1.leader + n ) 
           ||   
        ( (not quorum[ t1.voters[n] ]) && t2.leader = t1.leader ) 
    } 
} 

// Note we count the nodes before updating
pred quorum ( s: set Node ) { 
    #s >= (#Node).div[2]
} 

pred skip ( t1, t2: Time ) { 
    some t1.leader // Only if we've found a leader
    
    t2.msg = t1.msg
    t2.alreadyvoted = t1.alreadyvoted
    t2.voters = t1.voters 
    t2.leader = t1.leader
} 

pred trace {
    init [ first ] 
    all t: Time - last | step[t, next[t]] 
} 

// run { 
//     trace
//     some Time.leader 
// } for 10 but exactly 3 Node, 10 Time

check { 
    trace => no t: Time | #(t.leader) > 1
} for 10 

run trace for 10 
