-------------------- MODULE AtomicBroadcast --------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

---------------------------------------------------------------------

CONSTANT NPROCESSES
CONSTANT NGROUPS
CONSTANT INITIAL_MESSAGES

---------------------------------------------------------------------

VARIABLES
    \* The underlying buffer that holds all the messages.
    AtomicBroadcastBuffer

vars == <<AtomicBroadcastBuffer>>

---------------------------------------------------------------------
LOCAL HasValue(g, p) ==
    Len(AtomicBroadcastBuffer[g][p]) > 0

LOCAL AlreadyHasMessage(F, m) ==
    \E x \in DOMAIN F:
        /\ Len(F[x]) > 0
        /\ \E y \in DOMAIN F[x]: F[x][y][1].id = m[1].id

LOCAL PropagateInGroup(G, m) ==
    [i \in DOMAIN G |-> Append(G[i], m)]

ABroadcast(g, m) ==
    IF ~AlreadyHasMessage(AtomicBroadcastBuffer[g], m)
        THEN AtomicBroadcastBuffer' = [AtomicBroadcastBuffer EXCEPT ![g] = PropagateInGroup(AtomicBroadcastBuffer[g], m)]
    ELSE UNCHANGED AtomicBroadcastBuffer

ABDeliver(g, p, Fn(_)) ==
    /\ HasValue(g, p)
    /\ LET
        m == Head(AtomicBroadcastBuffer[g][p])
       IN
        /\ Fn(m)
        /\ AtomicBroadcastBuffer' = [AtomicBroadcastBuffer EXCEPT ![g][p] = Tail(AtomicBroadcastBuffer[g][p])]

---------------------------------------------------------------------

Init ==
    /\ AtomicBroadcastBuffer = [g \in 1 .. NGROUPS |-> [p \in 1 .. NPROCESSES |-> INITIAL_MESSAGES[g]]]

Next ==
    \/ UNCHANGED vars

=====================================================================
