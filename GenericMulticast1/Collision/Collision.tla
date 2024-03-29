------------------ MODULE Collision ----------------------
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
(************************************************************************************)
(*                                                                                  *)
(* If a correct process p delivers messages m and n, p is in the destination of     *)
(* both messages, m and n do not commute. Then, p delivers either m and then n or n *)
(* and then m.                                                                      *)
(*                                                                                  *)
(************************************************************************************)
Collision ==
    []\A g \in Groups:
        \A p \in ProcessesInGroup[g]:
            \A m1, m2 \in AllMessages: m1.id /= m2.id
                /\ Algorithm!WasDelivered(g, p, m1)
                /\ Algorithm!WasDelivered(g, p, m2)
                /\ CONFLICTR(m1, m2)
                    => Algorithm!DeliveredInstant(g, p, m1) /= Algorithm!DeliveredInstant(g, p, m2)
==========================================================
