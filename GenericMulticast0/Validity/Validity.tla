---- MODULE Validity ----
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
        m.o \in Processes ~> \E q \in m.d: Algorithm!WasDelivered(q, m)
==========================================================
