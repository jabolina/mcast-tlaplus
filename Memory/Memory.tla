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

LOCAL Filter(s, op(_)) ==
          {x \in s: op(x)}

LOCAL InsertOrUpdate(s, m) ==
          Filter(s, LAMBDA n: n.id /= m.id) \cup {m}

Insert(g, p, m) ==
    /\ MemoryBuffer' = [MemoryBuffer EXCEPT ![g][p] = InsertOrUpdate(MemoryBuffer[g][p], m)]

Contains(g, p, Fn(_)) ==
    \E m \in MemoryBuffer[g][p]: Fn(m)

Remove(g, p, S) ==
    /\ MemoryBuffer' = [MemoryBuffer EXCEPT ![g][p] = @ \ S]

-------------------------------------------------------

Init ==
    /\ MemoryBuffer = [g \in 1 .. NGROUPS |-> [p \in 1 .. NPROCESSES |-> {}]]

=======================================================
