------------------ MODULE Collision ----------------------
EXTENDS Naturals, FiniteSets, Commons

CONSTANT NGROUPS
CONSTANT NPROCESSES
CONSTANT NMESSAGES
CONSTANT CONFLICTR(_, _)

----------------------------------------------------------

LOCAL Processes == 1 .. NPROCESSES
LOCAL Groups == 1 .. NGROUPS
LOCAL ProcessesInGroup == [g \in Groups |-> Processes]

LOCAL ChooseGroup == CHOOSE x \in Groups : TRUE
LOCAL ChooseProcess == CHOOSE x \in Processes : TRUE
LOCAL RetrieveOriginator == <<ChooseGroup, ChooseProcess>>

LOCAL AllMessages == {[id |-> m, d |-> Groups, o |-> RetrieveOriginator]: m \in 1 .. NMESSAGES}

----------------------------------------------------------

VARIABLES
    K,
    PreviousMsgs,
    Delivered,
    Votes,
    MemoryBuffer,
    QuasiReliableChannel,
    ReliableMulticastBuffer,
    AtomicBroadcastBuffer
Algorithm == INSTANCE GenericMulticast1 WITH
    INITIAL_MESSAGES <- AllMessages

vars == <<
    K,
    PreviousMsgs,
    Delivered,
    Votes,
    MemoryBuffer,
    QuasiReliableChannel,
    ReliableMulticastBuffer,
    AtomicBroadcastBuffer
>>

----------------------------------------------------------

Spec == Algorithm!Spec

----------------------------------------------------------
(*
If a correct process p, delivers both m1 and m2, where p in
m1.d and m2.d, then p delivers m1 before m2 or delivers m2
before m1.
*)
Collision ==
    []\A g \in Groups:
        \A p \in ProcessesInGroup[g]:
            \A m1, m2 \in AllMessages: m1.id /= m2.id
                /\ Algorithm!WasDelivered(g, p, m1)
                /\ Algorithm!WasDelivered(g, p, m2)
                /\ CONFLICTR(m1, m2) => Algorithm!DeliveredInstant(g, p, m1) /= Algorithm!DeliveredInstant(g, p, m2)
==========================================================
