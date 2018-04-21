module leaderElection 

open util/ordering[Time]
open util/boolean

sig Node {} 

sig Time { 
    voters: Node -> set Node, 
    alreadyvoted: set Bool, 
} 

pred init (t: Time) { 

} 

pred step (t1, t2: Time) { 
    some n : Nodes | 
        request_vote_msg[n, t1, t2] 
          || 
        recv_request_msg[n,t1,t2]  
          || 
        recv_vote_msg[n,t1,t2]  
} 

fact Trace {
    init [ first ] 
    all t: Time - last | step[t, next[t]] 
} 

pred show {} 

run show for 3 but 10 Time
