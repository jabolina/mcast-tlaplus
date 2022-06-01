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
    [p \in DOMAIN s |-> SendToGroup(s[p], m)]

Send(m) ==
    /\ QuasiReliableChannel' = SendTo(QuasiReliableChannel, m)

LOCAL SendMapToGroup(g, Fn(_, _)) ==
    [p \in DOMAIN g |-> Fn(p, g[p])]

SendMap(Fn(_, _)) ==
    /\ QuasiReliableChannel' = [p \in DOMAIN QuasiReliableChannel |-> SendMapToGroup(QuasiReliableChannel[p], Fn)]

Receive(g, p, Fn(_)) ==
    /\ \E m \in QuasiReliableChannel[g][p]: Fn(m)

Consume(g, p, m) ==
    /\ QuasiReliableChannel' = [QuasiReliableChannel EXCEPT ![g][p] = @ \ {m}]

ReceiveAndConsume(g, p, Fn(_)) ==
    /\ Receive(g, p, LAMBDA m: Fn(m) /\ Consume(g, p, m))

--------------------------------------------------------------

Init ==
    /\ QuasiReliableChannel = [g \in 1 .. NGROUPS |-> [p \in 1 .. NPROCESSES |-> INITIAL_MESSAGES]]

Next ==
    \/ UNCHANGED vars

==============================================================
