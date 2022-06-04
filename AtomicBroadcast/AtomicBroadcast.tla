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

LOCAL PropagateInGroup(G, m) ==
    [i \in DOMAIN G |-> Append(G[i], m)]

ABroadcast(g, m) ==
    /\ AtomicBroadcastBuffer' = [AtomicBroadcastBuffer EXCEPT ![g] = PropagateInGroup(AtomicBroadcastBuffer[g], m)]

ABDeliver(g, p, Fn(_)) ==
    /\ HasValue(g, p)
    /\ LET
        m == Head(AtomicBroadcastBuffer[g][p])
       IN
        /\ Fn(m)
        /\ AtomicBroadcastBuffer' = [AtomicBroadcastBuffer EXCEPT ![g][p] = Tail(AtomicBroadcastBuffer[g][p])]

---------------------------------------------------------------------

Init ==
    /\ AtomicBroadcastBuffer = [g \in 1 .. NGROUPS |-> [p \in 1 .. NPROCESSES |-> INITIAL_MESSAGES]]

Next ==
    \/ UNCHANGED vars

=====================================================================
