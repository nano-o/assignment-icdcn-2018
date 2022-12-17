----------------------------- MODULE Allocation -----------------------------

EXTENDS FiniteSets, Naturals, Sequences

CONSTANT N, R, f, Bot
P == 1..N
Rs == 1..R

(*
--algorithm Alloc {
    variables
        (*******************************************************************)
        (* vector of test-and-set objects:                                 *)
        (*******************************************************************)
        T = [i \in P |-> FALSE];
        (*******************************************************************)
        (* the outputs of the processors                                   *)
        (*******************************************************************)
        D = [p \in P |-> Bot];
        (*******************************************************************)
        (* return value of TestAndSet procedure:                           *)
        (*******************************************************************)
        ret = [p \in P |-> Bot];
    define {
        Correctness == 
            /\  \A p,q \in P : D[p] # Bot /\ D[q] # Bot /\ p # q
                => D[p] \cap D[q] = {}
            /\  LET Part == {p \in P : pc[p] # "l0"}
                IN Part # {} /\ (\A p \in Part : pc[p] = "Done") 
                    => UNION {D[p] : p \in Part} = 1..f[Cardinality(Part)] 
    }
    procedure TestAndSet(j) {
l0:     if (\neg T[j]) {
            T[j] := TRUE;
            ret[self] := TRUE
        } 
        else  ret[self] := FALSE;
        return
    }
    process (p \in P) variables j = 1; {
l0:     skip; \* a participant is a process past l0
l1:     while (j <= N) {
            call TestAndSet(j);
l2:         if (ret[self]) {
                if (j = 1) D[self] := 1..f[1]
                else D[self] := (f[j-1]+1)..f[j];
                goto "Done" } 
            else j := j+1 } } }
*)

=============================================================================
\* Modification History
\* Last modified Tue Jul 25 10:41:28 PDT 2017 by nano
\* Created Tue Jul 25 10:35:41 PDT 2017 by nano
