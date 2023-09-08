---- MODULE heartbeat ----
EXTENDS TLC, Integers, FiniteSets

(*--algorithm heartbeat
variables alive =  1..3, instanceOwner = [x \in 1..3 |-> x], instanceStuck = [x \in 1..3 |-> FALSE], killed = {};
fair process node \in 1..3
begin P:
    while self \in alive do 
        CheckIfStuck:
            if {x \in 1..3 : instanceOwner[x] = self /\ instanceStuck[x]} /= {} then 
                killed := killed \cup {x \in 1..3 : instanceStuck[x] /\ instanceOwner[x] = self};
            end if;
        RestartService:
            if {x \in 1..3 : instanceOwner[x] = self /\ instanceStuck[x]} /= {} then 
                instanceStuck := [x \in 1..3 |-> CASE instanceOwner[x] = self -> FALSE [] OTHER -> instanceStuck[x]];
                killed := killed \ {x \in 1..3 : instanceOwner[x] = self};
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
                        instanceOwner := [ z \in 1..3 |-> 
                            CASE instanceOwner[z] = x -> CHOOSE y \in alive : x /= y 
                            [] OTHER -> instanceOwner[z]
                        ]; 
                    end with;
                end if;
        or 
            MakeServiceStuck:
                with x \in 1..3 do 
                    instanceStuck[x] := TRUE;
                end with;
        end either;
    end while;
end process
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "8d1fe120" /\ chksum(tla) = "e25b6c75")
VARIABLES alive, instanceOwner, instanceStuck, killed, pc

vars == << alive, instanceOwner, instanceStuck, killed, pc >>

ProcSet == (1..3) \cup {0}

Init == (* Global variables *)
        /\ alive = 1..3
        /\ instanceOwner = [x \in 1..3 |-> x]
        /\ instanceStuck = [x \in 1..3 |-> FALSE]
        /\ killed = {}
        /\ pc = [self \in ProcSet |-> CASE self \in 1..3 -> "P"
                                        [] self = 0 -> "Orchestrator"]

P(self) == /\ pc[self] = "P"
           /\ IF self \in alive
                 THEN /\ pc' = [pc EXCEPT ![self] = "CheckIfStuck"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "NodeDown"]
           /\ UNCHANGED << alive, instanceOwner, instanceStuck, killed >>

CheckIfStuck(self) == /\ pc[self] = "CheckIfStuck"
                      /\ IF {x \in 1..3 : instanceOwner[x] = self /\ instanceStuck[x]} /= {}
                            THEN /\ killed' = (killed \cup {x \in 1..3 : instanceStuck[x] /\ instanceOwner[x] = self})
                            ELSE /\ TRUE
                                 /\ UNCHANGED killed
                      /\ pc' = [pc EXCEPT ![self] = "RestartService"]
                      /\ UNCHANGED << alive, instanceOwner, instanceStuck >>

RestartService(self) == /\ pc[self] = "RestartService"
                        /\ IF {x \in 1..3 : instanceOwner[x] = self /\ instanceStuck[x]} /= {}
                              THEN /\ instanceStuck' = [x \in 1..3 |-> CASE instanceOwner[x] = self -> FALSE [] OTHER -> instanceStuck[x]]
                                   /\ killed' = killed \ {x \in 1..3 : instanceOwner[x] = self}
                              ELSE /\ TRUE
                                   /\ UNCHANGED << instanceStuck, killed >>
                        /\ pc' = [pc EXCEPT ![self] = "P"]
                        /\ UNCHANGED << alive, instanceOwner >>

NodeDown(self) == /\ pc[self] = "NodeDown"
                  /\ self \in alive
                  /\ pc' = [pc EXCEPT ![self] = "P"]
                  /\ UNCHANGED << alive, instanceOwner, instanceStuck, killed >>

node(self) == P(self) \/ CheckIfStuck(self) \/ RestartService(self)
                 \/ NodeDown(self)

Orchestrator == /\ pc[0] = "Orchestrator"
                /\ IF alive /= {}
                      THEN /\ \/ /\ pc' = [pc EXCEPT ![0] = "RebootNode"]
                              \/ /\ pc' = [pc EXCEPT ![0] = "MakeServiceStuck"]
                      ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                /\ UNCHANGED << alive, instanceOwner, instanceStuck, killed >>

RebootNode == /\ pc[0] = "RebootNode"
              /\ IF Cardinality(alive) > 1
                    THEN /\ \E x \in alive:
                              /\ alive' = alive \ {x}
                              /\ instanceOwner' =                  [ z \in 1..3 |->
                                                      CASE instanceOwner[z] = x -> CHOOSE y \in alive' : x /= y
                                                      [] OTHER -> instanceOwner[z]
                                                  ]
                    ELSE /\ TRUE
                         /\ UNCHANGED << alive, instanceOwner >>
              /\ pc' = [pc EXCEPT ![0] = "Orchestrator"]
              /\ UNCHANGED << instanceStuck, killed >>

MakeServiceStuck == /\ pc[0] = "MakeServiceStuck"
                    /\ \E x \in 1..3:
                         instanceStuck' = [instanceStuck EXCEPT ![x] = TRUE]
                    /\ pc' = [pc EXCEPT ![0] = "Orchestrator"]
                    /\ UNCHANGED << alive, instanceOwner, killed >>

orchestrator == Orchestrator \/ RebootNode \/ MakeServiceStuck

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

MyProperty == \A x \in 1..3 : (<>(instanceStuck[x] ~> ~instanceStuck[x] \/ alive = {x} \/ x \in killed))

====
