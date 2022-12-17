------------------------ MODULE LongLivedAssignment ------------------------

EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANT P, R, Bot, Item

Min(X, Leq(_,_)) == CHOOSE x \in X : \A y \in X : Leq(x,y)
Maximal(X, Leq(_,_)) == {x \in X : \A y \in X : x # y => \neg Leq(x,y)}

(* startDisplay *)
(*
--algorithm LongLivedAssignment {
    variables
        name = [i \in SUBSET P |-> [p \in P |-> Bot]]; \* return values from renaming.
        is = [p \in P |-> Bot]; \* return values from immediate snapshot.
        postedIS = [p \in P |-> Bot];
        firstItem = [p \in P |-> Bot];
        a = [p \in P |-> Bot]; \* processor outputs
(* endDisplay *)
        startedRenaming = [i \in SUBSET P |-> [p \in P |-> FALSE]]; \* tracking participants in renaming instances.
(* startDisplay *)
    define {
(* endDisplay *)
        (*******************************************************************)
        (* The correctness properties:                                     *)
        (*******************************************************************)
        Prop1 == \A p\in P : pc[p] = "Done"
            => \E i \in DOMAIN a[p] : a[p][i] = p
        Prop2 == \A p,q \in P, i \in Item :
            /\  pc[p] = "Done" /\ pc[q] = "Done"
            /\ i \in DOMAIN a[p] /\ i \in DOMAIN a[q]
            => a[p][i] = a[q][i]
        (*******************************************************************)
        (* Here we require that the union of the domains cover the items.  *)
        (*******************************************************************)
        Prop3 == 
            LET Participants == {p \in P : pc[p] # "l1"}
                NParticipants == Cardinality(Participants)
            IN (\A p \in Participants : pc[p] = "Done") /\ Participants # {}
                => UNION {DOMAIN a[p] : p \in Participants} = 1..2*NParticipants-1
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
        

(* startDisplay *)
        Name(p) == name[is[p]][p]
        (*******************************************************************)
        (* A frame for p consists of two immediate snapshots IS1 and IS2   *)
        (* such that p is in IS2 but not in IS1                            *)
        (*******************************************************************) 
        Frame(p, PostedIS) == LET IS == PostedIS \cup {{}} IN
            {<<IS1,IS2>> \in IS\times IS : p \in IS2 /\ p \notin IS1}
        MaxFrame(F) == CHOOSE <<IS1,IS2>> \in F : \A I \in F : IS1 \subseteq I[1] /\ I[2] \subseteq IS2
        (*******************************************************************)
        (* Computing the assignment on an frame <<Low,High>>:              *)
        (*******************************************************************)
        Assign(Low, High) ==
            LET ItemsPosted == {i \in Item : \E p \in High \ Low : firstItem[p] = i}
                Domain == 2*Cardinality(Low)+1..2*Cardinality(High)-1
                Free == Domain \ ItemsPosted
                Position(i) == Cardinality({j \in Free : j \leq i}) 
                Rank(p) == Cardinality({q \in High \ Low : firstItem[q] \leq firstItem[p]}) 
            IN [i \in Domain |-> IF i \in ItemsPosted 
                    THEN CHOOSE p \in High \ Low : firstItem[p] = i
                    ELSE CHOOSE p \in High \ Low : Rank(p) = Position(i)] }
(* endDisplay *)
    procedure ImmediateSnapshot() {
im1:    with (Valid = {S \in SUBSET P : ISSpec([is EXCEPT ![self] = S])},
            S \in Valid )
        is[self] := S;
        return
    }
    procedure Renaming(group) {
rn1:    startedRenaming[group][self] := TRUE;
rn2:    with (N = Cardinality({p \in P : startedRenaming[group][p]}),
            Valid = {Nm \in 1..2*N-1 : RenamingSpec(group, [name[group] EXCEPT ![self] = Nm])},
            Nm \in Valid)
        name[group][self] := Nm;
        return
    }
(* startDisplay *)
fair process (proc \in P) {
l1:     call ImmediateSnapshot();
l1b:    postedIS[self] := is[self];
l2:     call Renaming(is[self]);
l3:     firstItem[self] := 2*Cardinality(is[self])-Name(self);
l4:     with (PostedIS = {postedIS[p] : p \in P} \ {Bot})
        if (\A F \in Frame(self, PostedIS) : \E p \in F[2] \ F[1] : firstItem[p] = Bot)
            a[self] := [i \in {firstItem[self]} |-> self]
        else with (Complete = {F \in Frame(self, PostedIS) : \A p \in F[2] \ F[1] : firstItem[p] # Bot},
                MaxF = MaxFrame(Complete) )
            a[self] := Assign(MaxF[1], MaxF[2]) } }
*)
=============================================================================
\* Modification History
\* Last modified Tue Jul 25 10:40:58 PDT 2017 by nano
\* Created Tue Jul 25 10:38:12 PDT 2017 by nano
