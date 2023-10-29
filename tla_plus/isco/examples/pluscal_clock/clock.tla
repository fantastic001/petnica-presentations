---- MODULE clock ----
EXTENDS TLC, Integers


(*--algorithm clock
variable x \in 1..12;
begin
countToTwelve:
    while x < 12 do
        x := x + 1
    end while;
reset:
    x := 1;
    goto countToTwelve;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "784a1b12" /\ chksum(tla) = "8b659359")
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x \in 1..12
        /\ pc = "countToTwelve"

countToTwelve == /\ pc = "countToTwelve"
                 /\ IF x < 12
                       THEN /\ x' = x + 1
                            /\ pc' = "countToTwelve"
                       ELSE /\ pc' = "reset"
                            /\ x' = x

reset == /\ pc = "reset"
         /\ x' = 1
         /\ pc' = "countToTwelve"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == countToTwelve \/ reset
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
varIsOne == <>(x = 1)
\* https://old.learntla.com/temporal-logic/operators/
====

