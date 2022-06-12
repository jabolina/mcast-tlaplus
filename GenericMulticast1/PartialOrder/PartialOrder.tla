----------------- MODULE PartialOrder --------------------
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
LOCAL BothDelivered(g, p1, p2, m1, m2) ==
    /\ Algorithm!WasDelivered(g, p1, m1) /\ Algorithm!WasDelivered(g, p1, m2)
    /\ Algorithm!WasDelivered(g, p2, m1) /\ Algorithm!WasDelivered(g, p2, m2)
LOCAL LHS(g, p1, p2, m1, m2) ==
    /\ {p1, p2} \subseteq (m1.d \intersect m2.d)
    /\ CONFLICTR(m1, m2)
    /\ BothDelivered(g, p1, p2, m1, m2)
LOCAL RHS(g, p1, p2, m1, m2) ==
    /\ LET
        pm == Algorithm!DeliveredInstant(g, p1, m1)
        pn == Algorithm!DeliveredInstant(g, p1, m2)
        qm == Algorithm!DeliveredInstant(g, p2, m1)
        qn == Algorithm!DeliveredInstant(g, p2, m2)
        IN
         /\ (pm < pn) <=> (qm < qn)
(*
If a correct processes p1, p2 both deliver messages m1 and m2,
m1 conflict with m2, and p1 and p2 are both in m1.d and m2.d,
then p1 delivers m1 before m2, if, and only if, p2 deliver m1 before m2.
*)
PartialOrder ==
    []\A g \in Groups:
        \A p1, p2 \in ProcessesInGroup[g]:
            \A m1, m2 \in AllMessages:
                LHS(g, p1, p2, m1, m2) => RHS(g, p1, p2, m1, m2)
==========================================================
