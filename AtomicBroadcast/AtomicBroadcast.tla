-------------------- MODULE AtomicBroadcast --------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
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
GroupHasValue ==
    Len(AtomicBroadcastBuffer) > 0

GroupABroadcast(g, m) ==
    [i \in 1..Len(AtomicBroadcastBuffer) |-> Append(AtomicBroadcastBuffer[i], m)]

GroupABDeliver(g) ==
    Tail(AtomicBroadcastBuffer)

GroupPeek(g) ==
    Head(AtomicBroadcastBuffer)

---------------------------------------------------------------------

Init ==
    /\ AtomicBroadcastBuffer = [i \in 1 .. NPROCESSES |-> INITIAL_MESSAGES]

Next ==
    \/ UNCHANGED vars

=====================================================================
