-------------------- MODULE Agreement --------------------

EXTENDS Naturals, FiniteSets

CONSTANT NPROCESSES
CONSTANT NMESSAGES

----------------------------------------------------------

Never(x, y) == FALSE

VARIABLES
    K,
    Pending,
    Delivering,
    Delivered,
    PreviousMsgs,
    Votes,
    QuasiReliableChannel
GenericMulticast0 == INSTANCE GenericMulticast0 WITH
    CONFLICTR <- Never,
    INITIAL_MESSAGES <- {}


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

Step(self) ==
    /\ self \in 1 .. NPROCESSES
    /\ UNCHANGED vars

Init ==
    /\ GenericMulticast0!Init

Next ==
    \/ \E self \in 1 .. NPROCESSES: Step(self)
    \/  GenericMulticast0!Next
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars
             /\ WF_vars(\E self \in 1 .. NPROCESSES: Step(self))

==========================================================
