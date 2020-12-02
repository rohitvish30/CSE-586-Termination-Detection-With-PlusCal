-------------------- MODULE termDet -------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT N, MaxT
ASSUME N \in Nat \ {0,1}
Procs == 1..N

(* 
--algorithm termDet2 {
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
  m= 99;
  active=TRUE;
  outc = [n \in 1..N |-> 0];
  inc  = 0;
  {
P:    while (T<MaxT)
        {  
            T := T+1;
            \* Write the code for the actions using either or 
            {
                either
                    {
                        await (active=TRUE);
                       
                        with (i \in Procs)
                        {
                            send(i,m);
                            outc[i] := outc[i]+1;
                        };
                        
                    };
                or
                    {
                        receive(m);
                        active := TRUE;
                        inc := inc+1;
                    };
                or
                    {
                        await(active=TRUE);
                        active := FALSE;
                        send(0,<<self,outc,inc>>);
                        outc := [n \in 1..N |-> 0];
                    };
            }
        
        
      }
  }


  fair process (d \in {0}) \* Detector process
  variables
  done=FALSE;
  msg= <<>>;
  notified={};
  outS = [n \in 1..N |-> 0];
  inS = [n \in 1..N |-> 0];
  {
D:  while(~done) 
    {
            receive(msg);
            notified := UNION {{msg[1]}, notified};
            inS[msg[1]] := msg[3];
            outS := [i \in 1..N |-> outS[i] + msg[2][i]];
            done := {x : x \in Procs} \subseteq notified /\ (inS = outS);
     };
   };
    
  }

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-c0e174b569f5ec08be18c5d1d2014c0f
VARIABLES chan, pc, T, m, active, outc, inc, done, msg, notified, outS, inS

vars == << chan, pc, T, m, active, outc, inc, done, msg, notified, outS, inS
        >>

ProcSet == (Procs) \cup ({0})

Init == (* Global variables *)
        /\ chan = [n \in 0..N |-> <<>>]
        (* Process j *)
        /\ T = [self \in Procs |-> 0]
        /\ m = [self \in Procs |-> 99]
        /\ active = [self \in Procs |-> TRUE]
        /\ outc = [self \in Procs |-> [n \in 1..N |-> 0]]
        /\ inc = [self \in Procs |-> 0]
        (* Process d *)
        /\ done = [self \in {0} |-> FALSE]
        /\ msg = [self \in {0} |-> <<>>]
        /\ notified = [self \in {0} |-> {}]
        /\ outS = [self \in {0} |-> [n \in 1..N |-> 0]]
        /\ inS = [self \in {0} |-> [n \in 1..N |-> 0]]
        /\ pc = [self \in ProcSet |-> CASE self \in Procs -> "P"
                                        [] self \in {0} -> "D"]

P(self) == /\ pc[self] = "P"
           /\ IF T[self]<MaxT
                 THEN /\ T' = [T EXCEPT ![self] = T[self]+1]
                      /\ \/ /\ (active[self]=TRUE)
                            /\ \E i \in Procs:
                                 /\ chan' = [chan EXCEPT ![i] = Append(chan[i], m[self])]
                                 /\ outc' = [outc EXCEPT ![self][i] = outc[self][i]+1]
                            /\ UNCHANGED <<m, active, inc>>
                         \/ /\ Len(chan[self]) > 0
                            /\ m' = [m EXCEPT ![self] = Head(chan[self])]
                            /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
                            /\ active' = [active EXCEPT ![self] = TRUE]
                            /\ inc' = [inc EXCEPT ![self] = inc[self]+1]
                            /\ outc' = outc
                         \/ /\ (active[self]=TRUE)
                            /\ active' = [active EXCEPT ![self] = FALSE]
                            /\ chan' = [chan EXCEPT ![0] = Append(chan[0], (<<self,outc[self],inc[self]>>))]
                            /\ outc' = [outc EXCEPT ![self] = [n \in 1..N |-> 0]]
                            /\ UNCHANGED <<m, inc>>
                      /\ pc' = [pc EXCEPT ![self] = "P"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << chan, T, m, active, outc, inc >>
           /\ UNCHANGED << done, msg, notified, outS, inS >>

j(self) == P(self)

D(self) == /\ pc[self] = "D"
           /\ IF ~done[self]
                 THEN /\ Len(chan[self]) > 0
                      /\ msg' = [msg EXCEPT ![self] = Head(chan[self])]
                      /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
                      /\ notified' = [notified EXCEPT ![self] = UNION {{msg'[self][1]}, notified[self]}]
                      /\ inS' = [inS EXCEPT ![self][msg'[self][1]] = msg'[self][3]]
                      /\ outS' = [outS EXCEPT ![self] = [i \in 1..N |-> outS[self][i] + msg'[self][2][i]]]
                      /\ done' = [done EXCEPT ![self] = {x : x \in Procs} \subseteq notified'[self] /\ (inS'[self] = outS'[self])]
                      /\ pc' = [pc EXCEPT ![self] = "D"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << chan, done, msg, notified, outS, inS >>
           /\ UNCHANGED << T, m, active, outc, inc >>

d(self) == D(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: j(self))
           \/ (\E self \in {0}: d(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))
        /\ \A self \in {0} : WF_vars(d(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-3758338fae569d6103012b9dd41391f6

Safety   == done[0]=>((\A self \in Procs:active[self] =FALSE) /\ (\A self \in Procs:chan[self] = <<>>))


Progress == ((\A self \in Procs:active[self] = FALSE) /\ (\A self \in Procs:chan[self] = <<>>))  ~> done[0]


\* remove the leftmost comment sign and fill the Progress property 

==================================================

\* Include the team member names here
Rohit Lalchand Vishwakarma : 50320038
Abhishek Dalvi: 50320110

 
