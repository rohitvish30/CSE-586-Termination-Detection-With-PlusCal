-------------------- MODULE termDet -------------------
EXTENDS Integers, Sequences, FiniteSets
CONSTANT N, MaxT
ASSUME N \in Nat \ {0,1}
Procs == 1..N

(* 
--algorithm termDet {
  variables
  chan = [n \in 0..N |-> <<>>];  \* FIFO channels 


  macro send(des, msg) {
      chan[des] := Append(chan[des], msg);
  }

  macro receive(msg) {
      when Len(chan[self]) > 0;
      msg := Head(chan[self]);
      chan[self] := Tail(chan[self]);
  }


  fair process (j \in Procs)
  variables
  T=0;
  m=0;
  active=TRUE;
  outc =0;
  inc  =0;
  {
P:    while (T<MaxT){  
        T := T+1;
        \* Write the code for the actions using either or 
      }
  }


  fair process (d \in {0}) \* Detector process
  variables
  done=FALSE;
  msg= <<>>;
  notified={};
  outS= 0;
  inS = 0;
  {
D:  while(~done) {
        receive(msg);
        \* Write the code to implement detector logic 
    }
  }

}
*)
\* BEGIN TRANSLATION
VARIABLES chan, pc, T, m, active, outc, inc, done, msg, notified, outS, inS

vars == << chan, pc, T, m, active, outc, inc, done, msg, notified, outS, inS
        >>

ProcSet == (Procs) \cup ({0})

Init == (* Global variables *)
        /\ chan = [n \in 0..N |-> <<>>]
        (* Process j *)
        /\ T = [self \in Procs |-> 0]
        /\ m = [self \in Procs |-> 0]
        /\ active = [self \in Procs |-> TRUE]
        /\ outc = [self \in Procs |-> 0]
        /\ inc = [self \in Procs |-> 0]
        (* Process d *)
        /\ done = [self \in {0} |-> FALSE]
        /\ msg = [self \in {0} |-> <<>>]
        /\ notified = [self \in {0} |-> {}]
        /\ outS = [self \in {0} |-> 0]
        /\ inS = [self \in {0} |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Procs -> "P"
                                        [] self \in {0} -> "D"]

P(self) == /\ pc[self] = "P"
           /\ IF T[self]<MaxT
                 THEN /\ T' = [T EXCEPT ![self] = T[self]+1]
                      /\ pc' = [pc EXCEPT ![self] = "P"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ T' = T
           /\ UNCHANGED << chan, m, active, outc, inc, done, msg, notified, 
                           outS, inS >>

j(self) == P(self)

D(self) == /\ pc[self] = "D"
           /\ IF ~done[self]
                 THEN /\ Len(chan[self]) > 0
                      /\ msg' = [msg EXCEPT ![self] = Head(chan[self])]
                      /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
                      /\ pc' = [pc EXCEPT ![self] = "D"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << chan, msg >>
           /\ UNCHANGED << T, m, active, outc, inc, done, notified, outS, inS >>

d(self) == D(self)

Next == (\E self \in Procs: j(self))
           \/ (\E self \in {0}: d(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))
        /\ \A self \in {0} : WF_vars(d(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Safety   ==  \* remove the leftmost comment sign and fill the Safety Property after == 
\* Progress == \* remove the leftmost comment sign and fill the Progress property 

==================================================

\* Include the team member names here 
