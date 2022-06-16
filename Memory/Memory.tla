-------------------- MODULE Memory --------------------

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals

-------------------------------------------------------

CONSTANT NPROCESSES
CONSTANT NGROUPS

-------------------------------------------------------

VARIABLE
    MemoryBuffer

vars == <<MemoryBuffer>>

-------------------------------------------------------

LOCAL InsertOrUpdate(S, t) ==
    {<<msg, ignore1, ignore2>> \in S: msg.id /= t[1].id} \cup {t}

Insert(g, p, t) ==
    /\ MemoryBuffer' = [MemoryBuffer EXCEPT ![g][p] = InsertOrUpdate(MemoryBuffer[g][p], t)]

Contains(g, p, Fn(_)) ==
    \E t \in MemoryBuffer[g][p]: Fn(t)

ForAllFilter(g, p, Fn(_, _)) ==
    {t_1 \in MemoryBuffer[g][p]: \A t_2 \in (MemoryBuffer[g][p] \ {t_1}): Fn(t_1, t_2)}

Remove(g, p, S) ==
    /\ MemoryBuffer' = [MemoryBuffer EXCEPT ![g][p] = @ \ S]

-------------------------------------------------------

Init ==
    /\ MemoryBuffer = [g \in 1 .. NGROUPS |-> [p \in 1 .. NPROCESSES |-> {}]]

=======================================================
