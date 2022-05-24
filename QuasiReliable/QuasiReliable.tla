-------------------- MODULE QuasiReliable --------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

--------------------------------------------------------------

CONSTANT NGROUPS

CONSTANT NPROCESSES

CONSTANT INITIAL_MESSAGES

--------------------------------------------------------------

VARIABLE QuasiReliableChannel

vars == <<QuasiReliableChannel>>

--------------------------------------------------------------

LOCAL SendToGroup(g, m) ==
    [p \in DOMAIN g |-> g[p] \cup {m}]

LOCAL SendTo(s, m) ==
    [p \in DOMAIN s |-> IF p \in m.d THEN SendToGroup(s[p], m) ELSE s[p]]

Send(m) == SendTo(QuasiReliableChannel, m)

Receive(group, process, cb(_)) ==
    /\ LET
        m == CHOOSE p \in QuasiReliableChannel[group][process]: TRUE
       IN
        /\ cb(m)
        /\ QuasiReliableChannel' = [QuasiReliableChannel EXCEPT ![group][process] = @ \ m]

--------------------------------------------------------------

Init ==
    /\ QuasiReliableChannel = [g \in 1 .. NGROUPS |-> [p \in 1 .. NPROCESSES |-> INITIAL_MESSAGES]]

Next ==
    \/ UNCHANGED vars

==============================================================
