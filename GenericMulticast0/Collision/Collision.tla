------------------ MODULE Collision ----------------------
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

(************************************************************************************)
(*                                                                                  *)
(* If a correct process p delivers messages m and n, p is in the destination of     *)
(* both messages, m and n do not commute. Then, p delivers either m and then n or n *)
(* and then m.                                                                      *)
(*                                                                                  *)
(************************************************************************************)
Collision ==
    []\A p \in Processes:
        \A m, n \in AllMessages: /\ m.id /= n.id
            /\ Algorithm!WasDelivered(p, m)
            /\ Algorithm!WasDelivered(p, n)
            /\ CONFLICTR(m, n)
                => Algorithm!DeliveredInstant(p, m) /=
                    Algorithm!DeliveredInstant(p, n)
==========================================================
