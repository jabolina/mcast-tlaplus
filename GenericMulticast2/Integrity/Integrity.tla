-------------------- MODULE Integrity --------------------
EXTENDS Naturals, FiniteSets, Sequences, Commons

CONSTANT NPROCESSES
CONSTANT NGROUPS
CONSTANT NMESSAGES
CONSTANT CONFLICTR(_, _)

----------------------------------------------------------

LOCAL Processes == 1 .. NPROCESSES
LOCAL Groups == 1 .. NGROUPS
LOCAL ProcessesInGroup == [g \in Groups |-> Processes]

LOCAL AcceptableMessageIds == {id : id \in 1 .. NMESSAGES}
LOCAL AllMessages == CreateMessages(NMESSAGES + 1, Groups, Processes)
LOCAL MessagesCombinations == CreatePossibleMessages(AllMessages)
LOCAL SentMessage == {m \in AllMessages: m.id \in AcceptableMessageIds}
LOCAL CombinationsToSend == [i \in DOMAIN MessagesCombinations |-> SelectSeq(MessagesCombinations[i], LAMBDA m: m \in SentMessage)]

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
    INITIAL_MESSAGES <- [g \in Groups |-> MessagesToTupleSet(CombinationsToSend[(g % NMESSAGES) + 1])]

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

Spec == Algorithm!SpecFair

----------------------------------------------------------

(*
for any message m in AllMessages, every correct process p in m.d
deliver m at most once, and only if m was previously sent by some
process p in Processes*)
LOCAL DeliveredOnlyOnce(g, p, m) == Cardinality(Algorithm!FilterDeliveredMessages(g, p, m)) = 1
Integrity ==
    <>[]\A m \in AllMessages:
        \A g \in m.d:
            \A p \in ProcessesInGroup[g]:
                (p \in Processes /\ DeliveredOnlyOnce(g, p, m)) <=> m \in SentMessage
==========================================================