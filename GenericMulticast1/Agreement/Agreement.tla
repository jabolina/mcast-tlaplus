-------------------- MODULE Agreement --------------------
EXTENDS Naturals, FiniteSets, Commons

CONSTANT NPROCESSES
CONSTANT NGROUPS
CONSTANT NMESSAGES
CONSTANT CONFLICTR(_, _)

----------------------------------------------------------

LOCAL Processes == {i : i \in 1 .. NPROCESSES}
LOCAL Groups == 1 .. NGROUPS
LOCAL ProcessesInGroup == [g \in Groups |-> Processes]

LOCAL ChooseGroup == CHOOSE x \in Groups : TRUE
LOCAL ChooseProcess == CHOOSE x \in Processes : TRUE
LOCAL RetrieveOriginator == <<ChooseGroup, ChooseProcess>>

LOCAL AllMessages == {[id |-> m, d |-> Groups, o |-> RetrieveOriginator]: m \in 1 .. NMESSAGES}

----------------------------------------------------------

VARIABLES
    K,
    PreviousMsgs,
    Delivered,
    Votes,
    MemoryBuffer,
    QuasiReliableChannel,
    ReliableMulticastBuffer,
    AtomicBroadcastBuffer
Algorithm == INSTANCE GenericMulticast1 WITH
    INITIAL_MESSAGES <- AllMessages

vars == <<
    K,
    PreviousMsgs,
    Delivered,
    Votes,
    MemoryBuffer,
    QuasiReliableChannel,
    ReliableMulticastBuffer,
    AtomicBroadcastBuffer
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
        \A g_i \in Groups:
            \E p_i \in ProcessesInGroup[g_i]:
                Algorithm!WasDelivered(g_i, p_i, m)
                    ~> \A g_j \in m.d :
                        \E p_j \in ProcessesInGroup[g_j]:
                            p_j \in Processes /\ Algorithm!WasDelivered(g_j, p_j, m)
==========================================================