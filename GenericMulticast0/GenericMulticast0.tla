-------------------- MODULE GenericMulticast0 --------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets

CONSTANT NPROCESSES
CONSTANT INITIAL_MESSAGES
CONSTANT CONFLICTR(_, _)

------------------------------------------------------------------

LOCAL Processes == 1 .. NPROCESSES

------------------------------------------------------------------

VARIABLE QuasiReliableChannel
QuasiReliable == INSTANCE QuasiReliable WITH
    NGROUPS <- 1

------------------------------------------------------------------

VARIABLES
    K,
    Pending,
    Delivering,
    Delivered,
    PreviousMsgs,
    Votes

vars == <<
    QuasiReliableChannel,
    Votes,
    K,
    Pending,
    Delivering,
    Delivered,
    PreviousMsgs >>

------------------------------------------------------------------

------------------------------------------------------------------

InitProtocol ==
    \* Start all nodes with clock set to 0.
    /\ K = [ i \in Processes |-> 0 ]

    \* Start all nodes with the messages set empty.
    /\ Pending = [ i \in Processes |-> {} ]
    /\ Delivering = [ i \in Processes |-> {} ]
    /\ Delivered = [ i \in Processes |-> {} ]
    /\ PreviousMsgs = [ i \in Processes |-> {} ]


InitHelpers ==
    /\ QuasiReliable!Init
    /\ Votes = [ i \in Processes |-> {} ]

Init == InitProtocol /\ InitHelpers

Next ==
    \/ UNCHANGED vars

------------------------------------------------------------------

\* Verify the input values.
ASSUME
    \* Verify that `NPROCESS` is a natural number greater than 0.
    /\ NPROCESSES \in (Nat \ {0})


==================================================================
