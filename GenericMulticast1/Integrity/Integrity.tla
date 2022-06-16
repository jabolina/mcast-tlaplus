-------------------- MODULE Integrity --------------------
EXTENDS Naturals, FiniteSets, Commons

CONSTANT NPROCESSES
CONSTANT NGROUPS
CONSTANT NMESSAGES
CONSTANT CONFLICTR(_, _)

----------------------------------------------------------

LOCAL Processes == 1 .. NPROCESSES
LOCAL Groups == 1 .. NGROUPS
LOCAL ProcessesInGroup == [g \in Groups |-> Processes]

LOCAL ChooseGroup == CHOOSE x \in Groups : TRUE
LOCAL ChooseProcess == CHOOSE x \in Processes : TRUE
LOCAL RetrieveOriginator == <<ChooseGroup, ChooseProcess>>

LOCAL AcceptableMessageIds == {id : id \in 1 .. NMESSAGES}
LOCAL AllMessages == {[id |-> m, d |-> Groups, o |-> RetrieveOriginator]: m \in 1 .. (NMESSAGES + 1)}
LOCAL SentMessage == {m \in AllMessages: m.id \in AcceptableMessageIds}

----------------------------------------------------------

VARIABLES
    K,
    PreviousMsgs,
    Delivered,
    Votes,
    MemoryBuffer,
    QuasiReliableChannel,
    AtomicBroadcastBuffer
Algorithm == INSTANCE GenericMulticast1 WITH
    INITIAL_MESSAGES <- SentMessage

vars == <<
    K,
    PreviousMsgs,
    Delivered,
    Votes,
    MemoryBuffer,
    QuasiReliableChannel,
    AtomicBroadcastBuffer
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
