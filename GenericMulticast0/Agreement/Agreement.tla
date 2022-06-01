-------------------- MODULE Agreement --------------------
EXTENDS Naturals, FiniteSets, Commons

CONSTANT NPROCESSES
CONSTANT NMESSAGES
CONSTANT CONFLICTR(_, _)

----------------------------------------------------------

LOCAL Processes == {i : i \in 1 .. NPROCESSES}
LOCAL ChooseProcess == CHOOSE x \in Processes : TRUE
LOCAL AllMessages == { [ id |-> id, d |-> Processes, ts |-> 0, s |-> ChooseProcess ] : id \in 1 .. NMESSAGES }

LOCAL CorrectProcesses == Processes \cup {15}

----------------------------------------------------------

VARIABLES
    K,
    Pending,
    Delivering,
    Delivered,
    PreviousMsgs,
    Votes,
    QuasiReliableChannel
Algorithm == INSTANCE GenericMulticast0 WITH
    INITIAL_MESSAGES <- {<<"S0", m>>: m \in AllMessages}


vars == <<
    K,
    Pending,
    Delivering,
    Delivered,
    PreviousMsgs,
    Votes,
    QuasiReliableChannel
>>
----------------------------------------------------------

Spec == Algorithm!SpecFair

----------------------------------------------------------
(***************************************************************************)
(*                                                                         *)
(*     If a correct process GM-Deliver a message `m`, then all correct     *)
(* processes in `m.d` eventually GM-Deliver `m`.                           *)
(*                                                                         *)
(*     We verify that all messages on the messages that will be send, then *)
(* we verify that exists a process and it did deliverd the message so we   *)
(* verify that eventually all processes in `m.d` also delivers `m`.        *)
(*                                                                         *)
(***************************************************************************)
Agreement ==
    \A m \in AllMessages:
        \A p \in Processes:
            Algorithm!WasDelivered(p, m) ~> \A q \in m.d : q \in Processes /\ Algorithm!WasDelivered(q, m)
==========================================================
