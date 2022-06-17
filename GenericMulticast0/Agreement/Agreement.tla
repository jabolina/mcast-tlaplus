-------------------- MODULE Agreement --------------------
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
LOCAL Create(id) == [ id |-> id, d |-> Processes, o |-> ChooseProcess ]
LOCAL AllMessages == { Create(id) : id \in 1 .. NMESSAGES }

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
    INITIAL_MESSAGES <- {<<"S0", m>>: m \in AllMessages}
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
Agreement ==
    \A m \in AllMessages:
        \A p \in Processes:
            Algorithm!WasDelivered(p, m)
                ~> \A q \in m.d:
                    q \in Processes /\ Algorithm!WasDelivered(q, m)
==========================================================
