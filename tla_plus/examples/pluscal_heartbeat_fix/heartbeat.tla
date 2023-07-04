---- MODULE heartbeat ----
EXTENDS TLC, Integers, FiniteSets

(*--algorithm heartbeat
variables alive =  1..3, replOwner = [x \in 1..3 |-> x], replStuck = [x \in 1..3 |-> FALSE], killed = {};
fair process node \in 1..3
begin P:
    while self \in alive do 
        CheckIfStuck:
            if {x \in 1..3 : replOwner[x] = self /\ replStuck[x]} /= {} then 
                killed := killed \cup {x \in 1..3 : replStuck[x] /\ replOwner[x] = self};
            end if;
        RestartReplicator:
            if {x \in 1..3 : replOwner[x] = self /\ replStuck[x]} /= {} then 
                replStuck := [x \in 1..3 |-> CASE replOwner[x] = self -> FALSE [] OTHER -> replStuck[x]];
                killed := killed \ {x \in 1..3 : replOwner[x] = self};
            end if; 
    end while;
    NodeDown:
    await self \in alive; 
    goto P;
end process

fair+ process orchestrator = 0
begin Orchestrator:
    while alive /= {} do 
        either 
            RebootNode:
                if Cardinality(alive) > 1 then 
                    with x \in alive do
                        alive := alive \ {x};
                        replOwner := [ z \in 1..3 |-> 
                            CASE replOwner[z] = x -> CHOOSE y \in alive : x /= y 
                            [] OTHER -> replOwner[z]
                        ]; 
                    end with;
                end if;
        or 
            MakeReplicatorStuck:
                with x \in 1..3 do 
                    replStuck[x] := TRUE;
                end with;
        end either;
    end while;
end process
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "23f8c013" /\ chksum(tla) = "d5065706")
VARIABLES alive, replOwner, replStuck, killed, pc

vars == << alive, replOwner, replStuck, killed, pc >>

ProcSet == (1..3) \cup {0}

Init == (* Global variables *)
        /\ alive = 1..3
        /\ replOwner = [x \in 1..3 |-> x]
        /\ replStuck = [x \in 1..3 |-> FALSE]
        /\ killed = {}
        /\ pc = [self \in ProcSet |-> CASE self \in 1..3 -> "P"
                                        [] self = 0 -> "Orchestrator"]

P(self) == /\ pc[self] = "P"
           /\ IF self \in alive
                 THEN /\ pc' = [pc EXCEPT ![self] = "CheckIfStuck"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "NodeDown"]
           /\ UNCHANGED << alive, replOwner, replStuck, killed >>

CheckIfStuck(self) == /\ pc[self] = "CheckIfStuck"
                      /\ IF {x \in 1..3 : replOwner[x] = self /\ replStuck[x]} /= {}
                            THEN /\ killed' = (killed \cup {x \in 1..3 : replStuck[x] /\ replOwner[x] = self})
                            ELSE /\ TRUE
                                 /\ UNCHANGED killed
                      /\ pc' = [pc EXCEPT ![self] = "RestartReplicator"]
                      /\ UNCHANGED << alive, replOwner, replStuck >>

RestartReplicator(self) == /\ pc[self] = "RestartReplicator"
                           /\ IF {x \in 1..3 : replOwner[x] = self /\ replStuck[x]} /= {}
                                 THEN /\ replStuck' = [x \in 1..3 |-> CASE replOwner[x] = self -> FALSE [] OTHER -> replStuck[x]]
                                      /\ killed' = killed \ {x \in 1..3 : replOwner[x] = self}
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << replStuck, killed >>
                           /\ pc' = [pc EXCEPT ![self] = "P"]
                           /\ UNCHANGED << alive, replOwner >>

NodeDown(self) == /\ pc[self] = "NodeDown"
                  /\ self \in alive
                  /\ pc' = [pc EXCEPT ![self] = "P"]
                  /\ UNCHANGED << alive, replOwner, replStuck, killed >>

node(self) == P(self) \/ CheckIfStuck(self) \/ RestartReplicator(self)
                 \/ NodeDown(self)

Orchestrator == /\ pc[0] = "Orchestrator"
                /\ IF alive /= {}
                      THEN /\ \/ /\ pc' = [pc EXCEPT ![0] = "RebootNode"]
                              \/ /\ pc' = [pc EXCEPT ![0] = "MakeReplicatorStuck"]
                      ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                /\ UNCHANGED << alive, replOwner, replStuck, killed >>

RebootNode == /\ pc[0] = "RebootNode"
              /\ IF Cardinality(alive) > 1
                    THEN /\ \E x \in alive:
                              /\ alive' = alive \ {x}
                              /\ replOwner' =              [ z \in 1..3 |->
                                                  CASE replOwner[z] = x -> CHOOSE y \in alive' : x /= y
                                                  [] OTHER -> replOwner[z]
                                              ]
                    ELSE /\ TRUE
                         /\ UNCHANGED << alive, replOwner >>
              /\ pc' = [pc EXCEPT ![0] = "Orchestrator"]
              /\ UNCHANGED << replStuck, killed >>

MakeReplicatorStuck == /\ pc[0] = "MakeReplicatorStuck"
                       /\ \E x \in 1..3:
                            replStuck' = [replStuck EXCEPT ![x] = TRUE]
                       /\ pc' = [pc EXCEPT ![0] = "Orchestrator"]
                       /\ UNCHANGED << alive, replOwner, killed >>

orchestrator == Orchestrator \/ RebootNode \/ MakeReplicatorStuck

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == orchestrator
           \/ (\E self \in 1..3: node(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..3 : WF_vars(node(self))
        /\ SF_vars(orchestrator)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

MyProperty == \A x \in 1..3 : (<>(replStuck[x] ~> ~replStuck[x] \/ alive = {x} \/ x \in killed))

====
