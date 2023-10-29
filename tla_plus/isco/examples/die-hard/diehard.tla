---- MODULE diehard ----
EXTENDS  Integers, TLC
VARIABLES big, small 

typeOk == /\ small \in 0 .. 3 
          /\ big \in 0 .. 5 

Init == small = 0 /\ big = 0 

fillSmall == /\ small' = 3
             /\ big' = big 

fillBig == /\ small' = small 
           /\ big' = 5 

emptySmall == /\ small' = 0 
              /\ big' = big 

emptyBig == /\ big' = 0 
            /\ small' = small 
smallToBig == IF small + big =< 5 THEN 
                /\ big' = big + small 
                /\ small' = 0 
            ELSE 
                /\ big' = 5 
                /\ small' = small - 5 + big 

bigToSmall == IF small + big =< 3 THEN 
                /\ small' = big + small
                /\ big' = 0
            ELSE 
                /\ big' = big - 3 + small
                /\ small' = 3 
            

Next == \/ fillSmall
        \/ fillBig  
        \/ emptySmall
        \/ emptyBig
        \/ smallToBig
        \/ bigToSmall 


bigNotFour == big /= 4 
====