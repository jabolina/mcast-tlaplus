------------------ MODULE Collision ----------------------
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
Collision ==
    []\A p \in Processes:
        \A m, n \in AllMessages: /\ m.id /= n.id
            /\ Algorithm!WasDelivered(p, m) /\ Algorithm!WasDelivered(p, n)
            /\ CONFLICTR(m, n) => Algorithm!DeliveredInstant(p, m) /= Algorithm!DeliveredInstant(p, n)
==========================================================
