------------------- MODULE Strictness --------------------
EXTENDS Naturals, FiniteSets, Commons

CONSTANT NPROCESSES
CONSTANT NMESSAGES
CONSTANT CONFLICTR(_, _)

----------------------------------------------------------

LOCAL Processes == {i : i \in 1 .. NPROCESSES}
LOCAL ChooseProcess == CHOOSE x \in Processes : TRUE
LOCAL AllMessages == { [ id |-> id, d |-> Processes, o |-> ChooseProcess ] : id \in 1 .. NMESSAGES }

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
    INITIAL_MESSAGES <- {<<"S0", m>>: m \in AllMessages}


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

Step(self) ==
    \/ Algorithm!AssignTimestamp(self)
    \/ Algorithm!ComputeSeqNumber(self)
    \/ Algorithm!AssignSeqNumber(self)
    \/ Algorithm!DoDeliver(self)

Next ==
    \/ \E self \in Processes: Step(self)
    \/ UNCHANGED vars

Spec == Algorithm!Init /\ [][Next]_vars

SpecFair == Spec /\ WF_vars(\E self \in Processes: Step(self))

----------------------------------------------------------
LOCAL DeliveredOrder(p, m, n) ==
    Algorithm!DeliveredInstant(p, m) < Algorithm!DeliveredInstant(p, n)
LOCAL DeliveredMessages(p, m, n) ==
    /\ Algorithm!WasDelivered(p, m)
    /\ Algorithm!WasDelivered(p, n)
LOCAL ExistRun ==
    \E p, q \in Processes:
        \E m, n \in AllMessages:
            /\ DeliveredMessages(p, m, n) /\ DeliveredMessages(q, m, n)
            /\ DeliveredOrder(p, m, n) /\ DeliveredOrder(q, n, m)
Strictness ==
    <>\E p, q \in Processes:
        \E m, n \in AllMessages:
            /\ DeliveredMessages(p, m, n) /\ DeliveredMessages(q, m, n)
            /\ DeliveredOrder(p, m, n) /\ DeliveredOrder(q, n, m)
==========================================================
