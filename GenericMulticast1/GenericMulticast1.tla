-------------------- MODULE GenericMulticast1 --------------------

LOCAL INSTANCE Commons
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets

CONSTANT NPROCESSES
CONSTANT NGROUPS
CONSTANT INITIAL_MESSAGES
CONSTANT CONFLICTR(_,_)

-----------------------------------------------------------------

LOCAL Processes == {p : p \in 1 .. NPROCESSES}
LOCAL Groups == {g : g \in 1 .. NGROUPS}

-----------------------------------------------------------------
VARIABLE AtomicBroadcastBuffer
AtomicBroadcast == INSTANCE AtomicBroadcast WITH
    INITIAL_MESSAGES <- <<>>

VARIABLE ReliableMulticastBuffer
ReliableMulticast == INSTANCE ReliableMulticast

VARIABLE QuasiReliableChannel
QuasiReliable == INSTANCE QuasiReliable WITH
    INITIAL_MESSAGES <- {}

VARIABLE MemoryBuffer
Memory == INSTANCE Memory

-----------------------------------------------------------------

VARIABLES
    K,
    PreviousMsgs,
    Delivered,
    Votes

vars == <<K, MemoryBuffer, PreviousMsgs, Delivered, Votes,
          AtomicBroadcastBuffer, ReliableMulticastBuffer, QuasiReliableChannel>>
-----------------------------------------------------------------
EnqueueMessageHandler(g, p, m) ==
    /\ AtomicBroadcast!ABroadcast(g, m)
    /\ Memory!Insert(g, p, m)
    /\ UNCHANGED <<K, PreviousMsgs, Delivered, Votes, QuasiReliableChannel>>

EnqueueMessage(g, p) ==
    /\ ReliableMulticast!RMDelivered(g, p, LAMBDA m: EnqueueMessageHandler(g, p, m))

-----------------------------------------------------------------

LOCAL InitProtocol ==
    /\ K = [i \in Groups |-> [p \in Processes |-> 0]]
    /\ Memory!Init
    /\ PreviousMsgs = [i \in Groups |-> [p \in Processes |-> {}]]
    /\ Delivered = [i \in Groups |-> [p \in Processes |-> {}]]
    /\ Votes = [i \in Groups |-> [p \in Processes |-> {}]]

LOCAL InitCommunication ==
    /\ AtomicBroadcast!Init
    /\ ReliableMulticast!Init
    /\ QuasiReliable!Init

Init == InitProtocol /\ InitCommunication

-----------------------------------------------------------------
Step(g, p) ==
    \/ EnqueueMessage(g, p)

LOCAL GroupStep(g) ==
    \E p \in Processes: Step(g, p)

Next ==
    \/ \E g \in Groups: GroupStep(g)
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

SpecFair == Spec /\ WF_vars(\E g \in Groups: GroupStep(g))

-----------------------------------------------------------------
ASSUME
    /\ NGROUPS \in (Nat \ {0})
    /\ NPROCESSES \in (Nat \ {0})
=================================================================
