-------------------- MODULE ReliableMulticast --------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Sequences

------------------------------------------------------------------

CONSTANT NPROCESSES
CONSTANT NGROUPS
CONSTANT INITIAL_MESSAGES

------------------------------------------------------------------

VARIABLES
    ReliableMulticastBuffer

vars == <<ReliableMulticastBuffer>>

------------------------------------------------------------------

LOCAL PropagateInGroup(F, m) ==
    [i \in DOMAIN F |-> F[i] \cup {m}]

RMulticast(g, m) ==
    /\ ReliableMulticastBuffer' = [ReliableMulticastBuffer EXCEPT ![g] = PropagateInGroup(ReliableMulticastBuffer[g], m)]

RMDelivered(g, p, Fn(_)) ==
    /\ \E m \in ReliableMulticastBuffer[g][p]:
        /\ Fn(m)
        /\ ReliableMulticastBuffer' = [ReliableMulticastBuffer EXCEPT ![g][p] = @ \ {m}]

------------------------------------------------------------------

Init ==
    /\ ReliableMulticastBuffer = [g \in 1 .. NGROUPS |-> [p \in 1 .. NPROCESSES |-> INITIAL_MESSAGES]]

------------------------------------------------------------------

ASSUME IsFiniteSet(INITIAL_MESSAGES)

==================================================================
