-------------------- MODULE Agreement --------------------
EXTENDS Naturals, FiniteSets, Commons, TLC

CONSTANT NPROCESSES
CONSTANT NGROUPS
CONSTANT NMESSAGES
CONSTANT CONFLICTR(_, _)

----------------------------------------------------------
(************************************************************************************)
(*                                                                                  *)
(* This algorithm works in an environment with crash-stop failures, but we do not   *)
(* model processes failing. The set of all processes contains all correct ones.     *)
(*                                                                                  *)
(************************************************************************************)
LOCAL Processes == {i : i \in 1 .. NPROCESSES}
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
    INITIAL_MESSAGES <- [
        g \in Groups |-> TotallyOrdered(MessagesCombinations[1])]
----------------------------------------------------------

\* Weak fairness is necessary.
Spec == Algorithm!SpecFair

----------------------------------------------------------
(************************************************************************************)
(*                                                                                  *)
(* If a correct process deliver a message `m', then all correct processes in `m.d'  *)
(* eventually delivers `m'.                                                         *)
(*                                                                                  *)
(* We verify that all messages in AllMessages, for all the processes that delivered *)
(* a message, eventually, all the correct members in the destination will deliver.  *)
(*                                                                                  *)
(************************************************************************************)
LOCAL OnlyCorrects(g) == {x \in ProcessesInGroup[g]: x \in Processes}
Agreement ==
    \A m \in AllMessages:
        \A g_i \in Groups:
            \E p_i \in ProcessesInGroup[g_i]:
                Algorithm!WasDelivered(g_i, p_i, m)
                    ~> \A g_j \in m.d :
                        \E p_j \in OnlyCorrects(g_j):
                            Algorithm!WasDelivered(g_j, p_j, m)
==========================================================
