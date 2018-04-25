EXTENDS TLC

(* --algorithm hello_world
variable s \in {"Hello", "World!"};
begin
  A:
    print s;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES s, pc

vars == << s, pc >>

Init == (* Global variables *)
        /\ s \in {"Hello", "World!"}
        /\ pc = "A"

A == /\ pc = "A"
     /\ PrintT(s)
     /\ pc' = "Done"
     /\ s' = s

Next == A
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
