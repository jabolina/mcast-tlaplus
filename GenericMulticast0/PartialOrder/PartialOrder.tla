----------------- MODULE PartialOrder --------------------
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
    INITIAL_MESSAGES <- {<<"S0", 0, m>>: m \in AllMessages}


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

Spec == Algorithm!Spec

----------------------------------------------------------
LOCAL BothDelivered(p, q, m, n) ==
    /\ Algorithm!WasDelivered(p, m) /\ Algorithm!WasDelivered(p, n)
    /\ Algorithm!WasDelivered(q, m) /\ Algorithm!WasDelivered(q, n)
LOCAL LHS(p, q, m, n) ==
    /\ {p, q} \subseteq (m.d \intersect n.d)
    /\ CONFLICTR(m, n)
    /\ BothDelivered(p, q, m, n)
LOCAL RHS(p, q, m, n) ==
    /\ LET
        pm == Algorithm!DeliveredInstant(p, m)
        pn == Algorithm!DeliveredInstant(p, n)
        qm == Algorithm!DeliveredInstant(q, m)
        qn == Algorithm!DeliveredInstant(q, n)
        IN
         /\ (pm < pn) <=> (qm < qn)
PartialOrder ==
    []\A p, q \in Processes:
        \A m, n \in AllMessages:
            LHS(p, q, m, n) => RHS(p, q, m, n)
==========================================================
