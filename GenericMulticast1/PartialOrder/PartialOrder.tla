----------------- MODULE PartialOrder --------------------
EXTENDS Naturals, FiniteSets, Commons

CONSTANT NGROUPS
CONSTANT NPROCESSES
CONSTANT NMESSAGES
CONSTANT CONFLICTR(_, _)

----------------------------------------------------------
(************************************************************************************)
(*                                                                                  *)
(* This algorithm works in an environment with crash-stop failures, but we do not   *)
(* model processes failing. The set of all processes contains all correct ones.     *)
(*                                                                                  *)
(************************************************************************************)
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
    AtomicBroadcastBuffer

(************************************************************************************)
(*                                                                                  *)
(* Initialize the instance for the Generic Multicast 1. The INITIAL_MESSAGES is a   *)
(* sequence, totally ordered within a group, wherein the elements are tuples with   *)
(* the message, state, and timestamp.                                               *)
(*                                                                                  *)
(************************************************************************************)
Algorithm == INSTANCE GenericMulticast1 WITH
    INITIAL_MESSAGES <- [g \in Groups |-> TotallyOrdered(MessagesCombinations[1])]
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
    (Algorithm!DeliveredInstant(g, p1, m1) <
        Algorithm!DeliveredInstant(g, p1, m2))
            <=> (Algorithm!DeliveredInstant(g, p2, m1) <
                    Algorithm!DeliveredInstant(g, p2, m2))

(************************************************************************************)
(*                                                                                  *)
(* For every two messages, if they conflict, given a pair of processes, they are in *)
(* the messages' destination, then both must deliver in the same order.             *)
(*                                                                                  *)
(************************************************************************************)
PartialOrder ==
    []\A g \in Groups:
        \A p1, p2 \in ProcessesInGroup[g]:
            \A m1, m2 \in AllMessages:
                LHS(g, p1, p2, m1, m2) => RHS(g, p1, p2, m1, m2)
==========================================================
