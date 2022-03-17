---- MODULE simple_lock ----
EXTENDS Naturals, TLC
CONSTANTS NumReaders, NumWrites

(* --algorithm simple_lock
variables cur = 0, lock = 0

process writer = 1
variable write = 0
begin
Writer_Loop:
    while write /= NumWrites do
        Write_Acquire:
            await lock = 0;
            lock := 1;
        Update:
            cur := write;
        Write_Release:
            lock := 0;
    end while;
end process;

process reader \in 2..(NumReaders + 1)
variables saved_read
begin
Read_Acquire:
    await lock = 0;
    lock := 1;
Read:
    saved_read := cur;
Check:
    assert saved_read = cur;
Read_Release:
    lock := 0;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "1359a2df" /\ chksum(tla) = "8136cae")
CONSTANT defaultInitValue
VARIABLES cur, lock, pc, write, saved_read

vars == << cur, lock, pc, write, saved_read >>

ProcSet == {1} \cup (2..(NumReaders + 1))

Init == (* Global variables *)
        /\ cur = 0
        /\ lock = 0
        (* Process writer *)
        /\ write = 0
        (* Process reader *)
        /\ saved_read = [self \in 2..(NumReaders + 1) |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "Writer_Loop"
                                        [] self \in 2..(NumReaders + 1) -> "Read_Acquire"]

Writer_Loop == /\ pc[1] = "Writer_Loop"
               /\ IF write /= NumWrites
                     THEN /\ pc' = [pc EXCEPT ![1] = "Write_Acquire"]
                     ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
               /\ UNCHANGED << cur, lock, write, saved_read >>

Write_Acquire == /\ pc[1] = "Write_Acquire"
                 /\ lock = 0
                 /\ lock' = 1
                 /\ pc' = [pc EXCEPT ![1] = "Update"]
                 /\ UNCHANGED << cur, write, saved_read >>

Update == /\ pc[1] = "Update"
          /\ cur' = write
          /\ pc' = [pc EXCEPT ![1] = "Write_Release"]
          /\ UNCHANGED << lock, write, saved_read >>

Write_Release == /\ pc[1] = "Write_Release"
                 /\ lock' = 0
                 /\ pc' = [pc EXCEPT ![1] = "Writer_Loop"]
                 /\ UNCHANGED << cur, write, saved_read >>

writer == Writer_Loop \/ Write_Acquire \/ Update \/ Write_Release

Read_Acquire(self) == /\ pc[self] = "Read_Acquire"
                      /\ lock = 0
                      /\ lock' = 1
                      /\ pc' = [pc EXCEPT ![self] = "Read"]
                      /\ UNCHANGED << cur, write, saved_read >>

Read(self) == /\ pc[self] = "Read"
              /\ saved_read' = [saved_read EXCEPT ![self] = cur]
              /\ pc' = [pc EXCEPT ![self] = "Check"]
              /\ UNCHANGED << cur, lock, write >>

Check(self) == /\ pc[self] = "Check"
               /\ Assert(saved_read[self] = cur, 
                         "Failure of assertion at line 32, column 5.")
               /\ pc' = [pc EXCEPT ![self] = "Read_Release"]
               /\ UNCHANGED << cur, lock, write, saved_read >>

Read_Release(self) == /\ pc[self] = "Read_Release"
                      /\ lock' = 0
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << cur, write, saved_read >>

reader(self) == Read_Acquire(self) \/ Read(self) \/ Check(self)
                   \/ Read_Release(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == writer
           \/ (\E self \in 2..(NumReaders + 1): reader(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
