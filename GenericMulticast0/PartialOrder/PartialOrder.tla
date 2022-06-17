----------------- MODULE PartialOrder --------------------
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

Spec == Algorithm!Spec

----------------------------------------------------------
LOCAL BothDelivered(p, q, m, n) ==
    /\ Algorithm!WasDelivered(p, m) /\ Algorithm!WasDelivered(p, n)
    /\ Algorithm!WasDelivered(q, m) /\ Algorithm!WasDelivered(q, n)

LOCAL LHS(p, q, m, n) ==
    {p, q} \subseteq (m.d \intersect n.d) /\ BothDelivered(p, q, m, n) /\ CONFLICTR(m, n)

LOCAL RHS(p, q, m, n) ==
     (Algorithm!DeliveredInstant(p, m) < Algorithm!DeliveredInstant(p, n))
        <=> (Algorithm!DeliveredInstant(q, m) < Algorithm!DeliveredInstant(q, n))

(************************************************************************************)
(*                                                                                  *)
(* For every two messages, if they conflict, given a pair of processes, they are in *)
(* the messages' destination, then both must deliver in the same order.             *)
(*                                                                                  *)
(************************************************************************************)
PartialOrder ==
    []\A p, q \in Processes:
        \A m, n \in AllMessages:
            LHS(p, q, m, n) => RHS(p, q, m, n)
==========================================================
