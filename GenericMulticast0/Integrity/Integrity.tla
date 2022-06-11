-------------------- MODULE Integrity --------------------
EXTENDS Naturals, FiniteSets, Commons

CONSTANT NPROCESSES
CONSTANT NMESSAGES
CONSTANT CONFLICTR(_, _)

----------------------------------------------------------

LOCAL Processes == {i : i \in 1 .. NPROCESSES}
LOCAL ChooseProcess == CHOOSE x \in Processes : TRUE
LOCAL AcceptableMessageIds == {id : id \in 1 .. NMESSAGES}
LOCAL AllMessages == { [ id |-> id, d |-> Processes, o |-> ChooseProcess ] : id \in 1 .. (NMESSAGES + 1) }
LOCAL SentMessage == {m \in AllMessages: m.id \in AcceptableMessageIds}

----------------------------------------------------------

VARIABLES
    K,
    Pending,
    Delivering,
    Delivered,
    PreviousMsgs,
    Votes,
    QuasiReliableChannel
Algorithm == INSTANCE GenericMulticast0 WITH
    INITIAL_MESSAGES <- {<<"S0", 0, m>>: m \in SentMessage}


vars == <<
    K,
    Pending,
    Delivering,
    Delivered,
    PreviousMsgs,
    Votes,
    QuasiReliableChannel
>>
----------------------------------------------------------

Spec == Algorithm!SpecFair

----------------------------------------------------------
LOCAL DeliveredOnlyOnce(p, m) == Cardinality(Algorithm!FilterDeliveredMessages(p, m)) = 1
Integrity ==
    <>[]\A m \in AllMessages:
        \A p \in m.d:
            (p \in Processes /\ DeliveredOnlyOnce(p, m)) <=> m \in SentMessage
==========================================================
