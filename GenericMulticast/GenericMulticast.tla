-------------------- MODULE GenericMulticast --------------------
EXTENDS Naturals

CONSTANT NPROCESSES

CONSTANT NGROUPS

CONSTANT NMESSAGES

CONSTANT CONFLICTR(_,_)

AllGroups == 1 .. NGROUPS
InitialMessages == [m \in 1 .. NMESSAGES |-> [id |-> m, d |-> AllGroups, ts |-> 0, s |-> 0]]

-----------------------------------------------------------------
VARIABLE AtomicBroadcastBuffer
AtomicBroadcast == INSTANCE AtomicBroadcast WITH
    INITIAL_MESSAGES <- InitialMessages

-----------------------------------------------------------------

NeverConflict(x, y) == FALSE

-----------------------------------------------------------------

Init == TRUE

Spec == TRUE

-----------------------------------------------------------------
ASSUME
    /\ NGROUPS \in (Nat \ {0})
    /\ NPROCESSES \in (Nat \ {0})
    /\ NMESSAGES \in (Nat \ {0})
=================================================================
