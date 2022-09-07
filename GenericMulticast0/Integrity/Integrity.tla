-------------------- MODULE Integrity --------------------
EXTENDS Naturals, FiniteSets, Commons

CONSTANT NPROCESSES
CONSTANT NMESSAGES
CONSTANT CONFLICTR(_, _)

----------------------------------------------------------

(************************************************************************************)
(*                                                                                  *)
(* Since this algorithm is for failure-free environments, the set of all processes  *)
(* is the same as the correct ones.                                                 *)
(*                                                                                  *)
(************************************************************************************)
LOCAL Processes == {i : i \in 1 .. NPROCESSES}
LOCAL ChooseProcess == CHOOSE x \in Processes : TRUE

(************************************************************************************)
(*                                                                                  *)
(* This property verifies that we only deliver sent messages. To assert this, we    *)
(* create `NMESSAGES + 1' and do not include the additional one in the algorithm    *)
(* execution, then check that the delivered ones are only the sent ones.            *)
(*                                                                                  *)
(************************************************************************************)
LOCAL AcceptableMessageIds == {id : id \in 1 .. NMESSAGES}
LOCAL Create(id) == [ id |-> id, d |-> Processes, o |-> ChooseProcess ]
LOCAL AllMessages == { Create(id) : id \in 1 .. (NMESSAGES + 1) }
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

(************************************************************************************)
(*                                                                                  *)
(* Initialize the instance for the Generic Multicast 0. The INITIAL_MESSAGES is a   *)
(* set with NMESSAGES, unordered, a tuple with the starting state S0 and the        *)
(* message.                                                                         *)
(*                                                                                  *)
(************************************************************************************)
Algorithm == INSTANCE GenericMulticast0 WITH
    INITIAL_MESSAGES <- {<<"S0", m>>: m \in SentMessage}
----------------------------------------------------------

Spec == Algorithm!Spec

----------------------------------------------------------
LOCAL DeliveredOnlyOnce(p, m) ==
    Cardinality(Algorithm!FilterDeliveredMessages(p, m)) = 1

(************************************************************************************)
(*                                                                                  *)
(* For every message, all the correct processes in the destination deliver it only  *)
(* once, and a process previously sent it.                                          *)
(*                                                                                  *)
(************************************************************************************)
Integrity ==
    []\A m \in AllMessages:
        \A p \in Processes:
            Algorithm!WasDelivered(p, m) =>
                (DeliveredOnlyOnce(p, m) /\ p \in m.d /\ m \in SentMessage)
==========================================================
