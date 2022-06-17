----------------------- MODULE GenericBroadcast -----------------------

-----------------------------------------------------------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets

\* Number of groups.
CONSTANT NGROUPS

\* Number of processes.
CONSTANT NPROCESSES

\* The sequences of initial messages.
CONSTANT INITIAL_MESSAGES

\* The conflict relation to identify commuting messages.
CONSTANT CONFLICTR(_, _)

-----------------------------------------------------------------------

VARIABLE
    GenericBroadcastBuffer

-----------------------------------------------------------------------

LOCAL ReplaceAt(s, i, e) ==
    [s EXCEPT ![i] = e]

LOCAL Consume(S, m) ==
    IF Cardinality(Head(S)) > 1 THEN ReplaceAt(S, 1, Head(S) \ {m})
    ELSE SubSeq(S, 2, Len(S))

LOCAL Insert(S, m) ==
    IF Len(S) = 0 \/ Len(SelectSeq(S, LAMBDA V: \E n \in V: CONFLICTR(m[1], n[1]))) /= 0
        THEN Append(S, {m})
    ELSE ReplaceAt(S, Len(S), S[Len(S)] \cup {m})
-----------------------------------------------------------------------

GBroadcast(g, m) ==
    /\ GenericBroadcastBuffer' = [
        GenericBroadcastBuffer EXCEPT ![g] = [
            i \in 1 .. Len(GenericBroadcastBuffer[g]) |->
                Insert(GenericBroadcastBuffer[g][i], m)]]

GBDeliver(g, p, Fn(_)) ==
    /\ Len(GenericBroadcastBuffer[g][p]) > 0
    /\ Cardinality(Head(GenericBroadcastBuffer[g][p])) > 0
    /\ LET
        m == CHOOSE v \in Head(GenericBroadcastBuffer[g][p]): TRUE
       IN
        /\ Fn(m)
        /\ GenericBroadcastBuffer' = [
            GenericBroadcastBuffer EXCEPT ![g][p] =
                Consume(GenericBroadcastBuffer[g][p], m)]

-----------------------------------------------------------------------

Init ==
    /\ GenericBroadcastBuffer = [g \in 1 .. NGROUPS |-> [p \in 1 .. NPROCESSES |-> INITIAL_MESSAGES[g]]]

=======================================================================
