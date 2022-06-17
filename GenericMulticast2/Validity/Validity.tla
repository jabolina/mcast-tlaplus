---- MODULE Validity ----
EXTENDS Naturals, FiniteSets, Commons

CONSTANT NPROCESSES
CONSTANT NGROUPS
CONSTANT NMESSAGES
CONSTANT CONFLICTR(_, _)

----------------------------------------------------------

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
Algorithm == INSTANCE GenericMulticast2 WITH
    INITIAL_MESSAGES <- [g \in Groups |-> MessagesToTupleSet(MessagesCombinations[(g % NMESSAGES) + 1])]

vars == <<
    K,
    PreviousMsgs,
    Delivered,
    Votes,
    MemoryBuffer,
    QuasiReliableChannel,
    GenericBroadcastBuffer
>>
----------------------------------------------------------

Spec == Algorithm!SpecFair

----------------------------------------------------------
(***************************************************************************)
(*                                                                         *)
(*     If a correct process GM-Cast a message `m` to `m.d`, then some      *)
(* process in `m.d` eventually GM-Deliver `m`.                             *)
(*                                                                         *)
(*     We verify that all messages on the messages that will be send, then *)
(* we verify that exists a process on the existent processes that did sent *)
(* the message and eventually exists a process on `m.d` that delivers the  *)
(* message.                                                                *)
(*                                                                         *)
(***************************************************************************)
Validity ==
    \A m \in AllMessages:
        m.o[1] \in Groups /\ m.o[2] \in Processes
            ~> \E g \in m.d:
                \E p \in ProcessesInGroup[g]: Algorithm!WasDelivered(g, p, m)
==========================================================
