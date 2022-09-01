-------------------- MODULE Integrity --------------------
EXTENDS Naturals, FiniteSets, Commons, Sequences

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

(************************************************************************************)
(*                                                                                  *)
(* This property verifies that we only deliver sent messages. To assert this, we    *)
(* create `NMESSAGES + 1' and do not include the additional one in the algorithm    *)
(* execution, then check that the delivered ones are only the sent ones.            *)
(*                                                                                  *)
(************************************************************************************)
LOCAL AcceptableMessageIds == {id : id \in 1 .. NMESSAGES}
LOCAL AllMessages == CreateMessages(NMESSAGES + 1, Groups, Processes)
LOCAL SentMessage == {m \in AllMessages: m.id \in AcceptableMessageIds}

LOCAL MessagesCombinations == CreatePossibleMessages(AllMessages)
LOCAL CombinationsToSend == [
    i \in DOMAIN MessagesCombinations |->
        SelectSeq(MessagesCombinations[i], LAMBDA m: m \in SentMessage)]

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
    INITIAL_MESSAGES <- [g \in Groups |->
        TotallyOrdered(CombinationsToSend[1])]
----------------------------------------------------------

Spec == Algorithm!Spec

----------------------------------------------------------

LOCAL DeliveredOnlyOnce(g, p, m) ==
    Cardinality(Algorithm!FilterDeliveredMessages(g, p, m)) = 1
(************************************************************************************)
(*                                                                                  *)
(* For every message, all the correct processes in the destination deliver it only  *)
(* once, and a process previously sent it.                                          *)
(*                                                                                  *)
(************************************************************************************)
Integrity ==
    []\A m \in AllMessages:
        \A g \in Groups:
            \A p \in ProcessesInGroup[g]:
                Algorithm!WasDelivered(g, p, m) =>
                    (DeliveredOnlyOnce(g, p, m) /\ g \in m.d /\ m \in SentMessage)
==========================================================
