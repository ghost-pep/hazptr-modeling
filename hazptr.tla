---- MODULE hazptr ----
EXTENDS Naturals, TLC, FiniteSets, Sequences
CONSTANTS NumReaders, NumWrites

R == 2

(* --algorithm hazptr
variables cur = 0, hzdreclist = {}, timeline = <<>>

process writer = 1
variables old = 0, rlist = {}, write = 0
begin
WriterLoop:
    while write /= NumWrites do
    Update:
        old := cur;
        cur := cur + 1;
        timeline := Append(timeline, write);
    Retire:
        rlist := rlist \cup {old};
    Scan:
        if Cardinality(rlist) >= R then
            \* free all ones without hazard pointers
            rlist := {x \in rlist : x \in hzdreclist};
            print "cleaned rlist";
        end if;
        write := write + 1
end while;
end process;

process reader \in 2..NumReaders+1
variables saved_read = 0, saved_read_ptr = 0
begin
Acquire:
    await 1 \in DOMAIN timeline; 
    \* wait until something can be read. This mimics a real function that would
    \* check for the data to not be null
    hzdreclist := hzdreclist \cup {cur};
Read:
    saved_read_ptr := cur;
    saved_read := timeline[cur];
Check:
    \* mimic a pointer dereference
    assert saved_read = timeline[saved_read_ptr];
Release:
    hzdreclist := hzdreclist \ {cur};
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "e300f735" /\ chksum(tla) = "456bb21d")
VARIABLES cur, hzdreclist, timeline, pc, old, rlist, write, saved_read, 
          saved_read_ptr

vars == << cur, hzdreclist, timeline, pc, old, rlist, write, saved_read, 
           saved_read_ptr >>

ProcSet == {1} \cup (2..NumReaders+1)

Init == (* Global variables *)
        /\ cur = 0
        /\ hzdreclist = {}
        /\ timeline = <<>>
        (* Process writer *)
        /\ old = 0
        /\ rlist = {}
        /\ write = 0
        (* Process reader *)
        /\ saved_read = [self \in 2..NumReaders+1 |-> 0]
        /\ saved_read_ptr = [self \in 2..NumReaders+1 |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "WriterLoop"
                                        [] self \in 2..NumReaders+1 -> "Acquire"]

WriterLoop == /\ pc[1] = "WriterLoop"
              /\ IF write /= NumWrites
                    THEN /\ pc' = [pc EXCEPT ![1] = "Update"]
                    ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
              /\ UNCHANGED << cur, hzdreclist, timeline, old, rlist, write, 
                              saved_read, saved_read_ptr >>

Update == /\ pc[1] = "Update"
          /\ old' = cur
          /\ cur' = cur + 1
          /\ timeline' = Append(timeline, write)
          /\ pc' = [pc EXCEPT ![1] = "Retire"]
          /\ UNCHANGED << hzdreclist, rlist, write, saved_read, saved_read_ptr >>

Retire == /\ pc[1] = "Retire"
          /\ rlist' = (rlist \cup {old})
          /\ pc' = [pc EXCEPT ![1] = "Scan"]
          /\ UNCHANGED << cur, hzdreclist, timeline, old, write, saved_read, 
                          saved_read_ptr >>

Scan == /\ pc[1] = "Scan"
        /\ IF Cardinality(rlist) >= R
              THEN /\ rlist' = {x \in rlist : x \in hzdreclist}
                   /\ PrintT("cleaned rlist")
              ELSE /\ TRUE
                   /\ rlist' = rlist
        /\ write' = write + 1
        /\ pc' = [pc EXCEPT ![1] = "WriterLoop"]
        /\ UNCHANGED << cur, hzdreclist, timeline, old, saved_read, 
                        saved_read_ptr >>

writer == WriterLoop \/ Update \/ Retire \/ Scan

Acquire(self) == /\ pc[self] = "Acquire"
                 /\ 1 \in DOMAIN timeline
                 /\ hzdreclist' = (hzdreclist \cup {cur})
                 /\ pc' = [pc EXCEPT ![self] = "Read"]
                 /\ UNCHANGED << cur, timeline, old, rlist, write, saved_read, 
                                 saved_read_ptr >>

Read(self) == /\ pc[self] = "Read"
              /\ saved_read_ptr' = [saved_read_ptr EXCEPT ![self] = cur]
              /\ saved_read' = [saved_read EXCEPT ![self] = timeline[cur]]
              /\ pc' = [pc EXCEPT ![self] = "Check"]
              /\ UNCHANGED << cur, hzdreclist, timeline, old, rlist, write >>

Check(self) == /\ pc[self] = "Check"
               /\ Assert(saved_read[self] = timeline[saved_read_ptr[self]], 
                         "Failure of assertion at line 44, column 5.")
               /\ pc' = [pc EXCEPT ![self] = "Release"]
               /\ UNCHANGED << cur, hzdreclist, timeline, old, rlist, write, 
                               saved_read, saved_read_ptr >>

Release(self) == /\ pc[self] = "Release"
                 /\ hzdreclist' = hzdreclist \ {cur}
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << cur, timeline, old, rlist, write, saved_read, 
                                 saved_read_ptr >>

reader(self) == Acquire(self) \/ Read(self) \/ Check(self) \/ Release(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == writer
           \/ (\E self \in 2..NumReaders+1: reader(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
