---- MODULE Validity ----
EXTENDS Naturals, FiniteSets, Commons

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
    GenericBroadcastBuffer

(************************************************************************************)
(*                                                                                  *)
(* Initialize the instance for the Generic Multicast 2. The INITIAL_MESSAGES is a   *)
(* sequence, partially ordered. The sequence elements are sets of messages,         *)
(* messages that commute can share a set.                                           *)
(*                                                                                  *)
(************************************************************************************)
Algorithm == INSTANCE GenericMulticast2 WITH
    INITIAL_MESSAGES <- [g \in Groups |-> PartiallyOrdered( MessagesCombinations[(g % NMESSAGES) + 1], CONFLICTR)]
----------------------------------------------------------

\* Weak fairness is necessary.
Spec == Algorithm!SpecFair

----------------------------------------------------------
(************************************************************************************)
(*                                                                                  *)
(* If a correct process GM-Cast a message `m' to `m.d', then some process in `m.d'  *)
(* eventually GM-Deliver `m'.                                                       *)
(*                                                                                  *)
(* We verify that all messages on the messages that will be sent, then we verify    *)
(* that exists a process on the existent processes that did sent the message and    *)
(* eventually exists a process on `m.d` that delivers the message.                  *)
(*                                                                                  *)
(************************************************************************************)
Validity ==
    \A m \in AllMessages:
        m.o[1] \in Groups /\ m.o[2] \in Processes
            ~> \E g \in m.d:
                \E p \in ProcessesInGroup[g]: Algorithm!WasDelivered(g, p, m)
==========================================================
