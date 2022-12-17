----------------------------- MODULE Assignment -----------------------------

EXTENDS FiniteSets, Naturals, Sequences

CONSTANT P, R, Bot
N == Cardinality(P)
Item == 1..R

(*
--algorithm Assignment {
    variables
        participating = [p \in P |-> FALSE];
        firstItem = [p \in P |-> Bot]; \* variable to post first item to shared memory.
        is = [p \in P |-> Bot]; \* immediate snapshot output.
        name = [i \in SUBSET P |-> [p \in P |-> Bot]]; \* renaming instances output.
        a = [p \in P |-> Bot]; \* processor outputs
        startedRenaming = [i \in SUBSET P |-> [p \in P |-> FALSE]]; \* tracking participants in renaming instances.
    define {
        (*******************************************************************)
        (* The correctness properties:                                     *)
        (*******************************************************************)
        Prop1 == \A p\in P : pc[p] = "Done"
            => \E i \in DOMAIN a[p] : a[p][i] = p
        Prop2 == \A p,q \in P, i \in Item :
            /\  pc[p] = "Done" /\ pc[q] = "Done"
            /\ i \in DOMAIN a[p] /\ i \in DOMAIN a[q]
            => a[p][i] = a[q][i]
        Prop3 == 
            LET 
                Participant == {p \in P : participating[p]}
                NParticipant == Cardinality(Participant)
            IN (\A p \in Participant : pc[p] = "Done") /\ Participant # {}
                => \E p \in Participant : DOMAIN a[p] = 1..2*NParticipant-1
        Correctness == Prop1 /\ Prop2 /\ Prop3
        
        (*******************************************************************)
        (* Specification of the Immediate Snapshot task:                   *)
        (*******************************************************************) 
        ISSpec(ISs) ==  
            \A p \in P : ISs[p] # Bot =>
                /\  p \in ISs[p]
                /\  \A q \in ISs[p] : pc[q] = "im1" \/ is[q] # Bot
                /\  \A q \in P : ISs[q] # Bot => 
                    /\  ISs[p] \subseteq ISs[q] \/ ISs[q] \subseteq ISs[p]
                    /\  p \in ISs[q] => ISs[p] \subseteq ISs[q]
        (*******************************************************************)
        (* Specification of the Renaming task:                             *)
        (*******************************************************************)
        RenamingSpec(Instance, Name) == 
            \A p \in P : Name[p] # Bot => 
                /\  \A q \in P : q # p /\ Name[q] # Bot => Name[p] # Name[q]
                /\  Name[p] \in 1..2*Cardinality({r \in P : startedRenaming[Instance][r]})-1        
        
        (*******************************************************************)
        (* Computing the allocation on an interval (two sets of processors *)
        (* S1 \subseteq S2):                                               *)
        (*******************************************************************)
        Name(p) == name[is[p]][p]
        Assign(Participant) ==
            LET Posted == {i \in Item : \E p \in Participant : firstItem[p] = i}
                Domain == 1..2*Cardinality(Participant)-1
                Free == Domain \ Posted
                (***********************************************************)
                (* The free item i has position k when it is the kth       *)
                (* smallest free item:                                     *)
                (***********************************************************) 
                Position(i) == Cardinality({j \in Free : j \leq i})
                (***********************************************************)
                (* A processor has rank i when its first item is the ith   *)
                (* smallest posted item:                                   *)
                (***********************************************************) 
                Rank(p) == Cardinality({q \in Participant : firstItem[q] \leq firstItem[p]})
            IN [i \in Domain |-> IF i \in Posted 
                    THEN CHOOSE p \in Participant : firstItem[p] = i
                    ELSE CHOOSE p \in Participant : Rank(p) = Position(i)] }
    procedure ImmediateSnapshot() {
im1:    with (Valid = {S \in SUBSET P : ISSpec([is EXCEPT ![self] = S])},
            S \in Valid )
        is[self] := S;
        return
    }
    procedure Renaming(group) {
rn1:    startedRenaming[group][self] := TRUE;
rn2:    with (Valid = {Nm \in 1..2*N-1 : RenamingSpec(group, [name[group] EXCEPT ![self] = Nm])},
            Nm \in Valid)
        name[group][self] := Nm;
        return
    }
fair process (proc \in P) {
l1:     participating[self] := TRUE;
        call ImmediateSnapshot();
l2:     call Renaming(is[self]);
l3:     firstItem[self] := 2*Cardinality(is[self])-Name(self);
l4:     with (Participant = {p \in P : participating[p]})
        if (\E p \in Participant : firstItem[p] = Bot) a[self] := [i \in {firstItem[self]} |-> self]
        else a[self] := Assign(Participant); } }
*)

=============================================================================
\* Modification History
\* Last modified Tue Jul 25 10:41:16 PDT 2017 by nano
\* Created Tue Jul 25 10:36:59 PDT 2017 by nano
