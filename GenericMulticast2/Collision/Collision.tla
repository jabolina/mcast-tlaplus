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

LOCAL AllMessages == CreateMessages(NMESSAGES, Groups, Processes)
LOCAL MessagesCombinations == CreatePossibleMessages(AllMessages)

----------------------------------------------------------

VARIABLES
    K,
    PreviousMsgs,
    Delivered,
    Votes,
    MemoryBuffer,
    QuasiReliableChannel,
    GenericBroadcastBuffer
Algorithm == INSTANCE GenericMulticast2 WITH
    INITIAL_MESSAGES <- [g \in Groups |-> MessagesToTupleSet(MessagesCombinations[(g % NMESSAGES) + 1])]

vars == <<
    K,
    PreviousMsgs,
    Delivered,
    Votes,
    MemoryBuffer,
    QuasiReliableChannel,
    GenericBroadcastBuffer
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
