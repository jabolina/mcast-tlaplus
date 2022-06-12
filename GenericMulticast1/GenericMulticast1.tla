-------------------- MODULE GenericMulticast1 --------------------

LOCAL INSTANCE Commons
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets

CONSTANT NPROCESSES
CONSTANT NGROUPS
CONSTANT INITIAL_MESSAGES
CONSTANT CONFLICTR(_,_)

-----------------------------------------------------------------

LOCAL Processes == {p : p \in 1 .. NPROCESSES}
LOCAL Groups == {g : g \in 1 .. NGROUPS}

-----------------------------------------------------------------
VARIABLE AtomicBroadcastBuffer
AtomicBroadcast == INSTANCE AtomicBroadcast

VARIABLE ReliableMulticastBuffer
ReliableMulticast == INSTANCE ReliableMulticast

VARIABLE QuasiReliableChannel
QuasiReliable == INSTANCE QuasiReliable WITH
    INITIAL_MESSAGES <- {}

VARIABLE MemoryBuffer
Memory == INSTANCE Memory

-----------------------------------------------------------------

VARIABLES
    K,
    PreviousMsgs,
    Delivered,
    Votes

vars == <<K, MemoryBuffer, PreviousMsgs, Delivered, Votes,
          AtomicBroadcastBuffer, ReliableMulticastBuffer, QuasiReliableChannel>>
-----------------------------------------------------------------
LOCAL EnqueueMessageHandler(g, p, m) ==
    /\ AtomicBroadcast!ABroadcast(g, <<m, 0, 0>>)
    /\ Memory!Insert(g, p, <<m, 0, 0>>)
    /\ UNCHANGED <<K, PreviousMsgs, Delivered, Votes, QuasiReliableChannel>>

LOCAL ComputeGroupSeqNumberHandler(g, p, msg, state, ts) ==
    /\ \/ /\ state = 0
          /\ \/ /\ \E prev \in PreviousMsgs[g][p]: CONFLICTR(msg, prev)
                /\ K' = [K EXCEPT ![g][p] = K[g][p] + 1]
                /\ PreviousMsgs' = [PreviousMsgs EXCEPT ![g][p] = {msg}]
             \/ /\ \A prev \in PreviousMsgs[g][p]: ~CONFLICTR(msg, prev)
                /\ PreviousMsgs' = [PreviousMsgs EXCEPT ![g][p] = PreviousMsgs[g][p] \cup {msg}]
                /\ UNCHANGED K
       \/ /\ state = 2
    /\ \/ /\ Cardinality(msg.d) > 1
          /\ \/ /\ state = 0
                /\ Memory!Insert(g, p, <<msg, state, K'[g][p]>>)
                /\ QuasiReliable!Send(<<msg, g, K'[g][p]>>)
             \/ /\ state = 2
                /\ \/ /\ ts > K[g][p]
                      /\ K' = [K EXCEPT ![g][p] = ts]
                      /\ PreviousMsgs' = [PreviousMsgs EXCEPT ![g][p] = {}]
                   \/ /\ ts <= K[g][p]
                      /\ UNCHANGED <<K, PreviousMsgs>>
                /\ Memory!Insert(g, p, <<msg, 3, ts>>)
                /\ UNCHANGED <<QuasiReliableChannel>>
       \/ /\ Cardinality(msg.d) = 1
          /\ Memory!Insert(g, p, <<msg, 3, K'[g][p]>>)
          /\ UNCHANGED QuasiReliableChannel
    /\ UNCHANGED <<Delivered, ReliableMulticastBuffer, Votes>>

LOCAL GatherGroupsTimestampHandler(g, p, msg, ts, tsf) ==
    /\ \/ /\ ts >= tsf \/ \A prev \in PreviousMsgs[g][p]: ~CONFLICTR(msg, prev)
          /\ Memory!Insert(g, p, <<msg, 3, ts>>)
          /\ UNCHANGED <<K, PreviousMsgs, AtomicBroadcastBuffer, Delivered>>
       \/ /\ ts < tsf
          /\ Memory!Insert(g, p, <<msg, 2, tsf>>)
          /\ AtomicBroadcast!ABroadcast(g, <<msg, 2, tsf>>)
          /\ UNCHANGED <<K, PreviousMsgs, Delivered>>

LOCAL DoDeliverHandler(g, p, m_1, ts_1) ==
    /\ LET
        G == Memory!ForAllFilter(g, p, LAMBDA t_i, t_j: t_i[2] = 3 /\ ~CONFLICTR(t_i[1], t_j[1]))
        D == G \cup {<<m_1, 3, ts_1>>}
        F == {t[1]: t \in D}
       IN
        /\ Memory!Remove(g, p, D)
        /\ Delivered' = [Delivered EXCEPT ![g][p] = Delivered[g][p] \cup AppendEnumerating(Cardinality(Delivered[g][p]), F)]
        /\ UNCHANGED <<QuasiReliableChannel, ReliableMulticastBuffer, AtomicBroadcastBuffer, Votes, PreviousMsgs, K>>

EnqueueMessage(g, p) ==
    /\ ReliableMulticast!RMDelivered(g, p, LAMBDA m: EnqueueMessageHandler(g, p, m))

ComputeGroupSeqNumber(g, p) ==
    /\ AtomicBroadcast!ABDeliver(g, p,
        LAMBDA t:
            /\ Memory!Contains(g, p, LAMBDA memory: t[1].id = memory[1].id /\ (memory[2] = 0 \/ memory[2] = 2))
            /\ ComputeGroupSeqNumberHandler(g, p, t[1], t[2], t[3]))

GatherGroupsTimestamp(g, p) ==
    /\ QuasiReliable!ReceiveAndConsume(g, p,
        LAMBDA t:
            /\ LET
                msg == t[1]
                origin == t[2]
                vote == <<msg.id, origin, t[3]>>
                election == {v \in (Votes[g][p] \cup {vote}): v[1] = msg.id}
                elected == Max({x[3] : x \in election})
               IN
                /\ \/ /\ Cardinality(election) = Cardinality(msg.d) /\ Memory!Contains(g, p, LAMBDA memory: msg.id = memory[1].id)
                      /\ GatherGroupsTimestampHandler(g, p, msg, t[3], elected)
                      /\ Votes' = [Votes EXCEPT ![g][p] = {x \in Votes[g][p]: x[1] /= msg.id}]
                   \/ /\ Cardinality(election) < Cardinality(msg.d)
                      /\ Votes' = [Votes EXCEPT ![g][p] = Votes[g][p] \cup {vote}]
                      /\ UNCHANGED <<MemoryBuffer, K, PreviousMsgs, AtomicBroadcastBuffer>>
                /\ UNCHANGED <<Delivered, ReliableMulticastBuffer>>)

DoDeliver(g, p) ==
    \E <<m_1, state, ts_1>> \in MemoryBuffer[g][p]:
        /\ state = 3
        /\ \A <<m_2, ignore, ts_2>> \in (MemoryBuffer[g][p] \ {<<m_1, state, ts_1>>}):
            /\ \/ ~CONFLICTR(m_1, m_2)
               \/ ts_1 < ts_2 \/ (m_1.id < m_2.id /\ ts_1 = ts_2)
        /\ LET
            G == Memory!ForAllFilter(g, p, LAMBDA t_i, t_j: t_i[2] = 3 /\ ~CONFLICTR(t_i[1], t_j[1]))
            D == G \cup {<<m_1, 3, ts_1>>}
            F == {t[1]: t \in D}
           IN
            /\ Memory!Remove(g, p, D)
            /\ Delivered' = [Delivered EXCEPT ![g][p] = Delivered[g][p] \cup AppendEnumerating(Cardinality(Delivered[g][p]), F)]
            /\ UNCHANGED <<QuasiReliableChannel, ReliableMulticastBuffer, AtomicBroadcastBuffer, Votes, PreviousMsgs, K>>
-----------------------------------------------------------------

LOCAL InitProtocol ==
    /\ K = [i \in Groups |-> [p \in Processes |-> 0]]
    /\ Memory!Init
    /\ PreviousMsgs = [i \in Groups |-> [p \in Processes |-> {}]]
    /\ Delivered = [i \in Groups |-> [p \in Processes |-> {}]]
    /\ Votes = [i \in Groups |-> [p \in Processes |-> {}]]

LOCAL InitCommunication ==
    /\ AtomicBroadcast!Init
    /\ ReliableMulticast!Init
    /\ QuasiReliable!Init

Init == InitProtocol /\ InitCommunication

-----------------------------------------------------------------
Step(g, p) ==
    \/ EnqueueMessage(g, p)
    \/ ComputeGroupSeqNumber(g, p)
    \/ GatherGroupsTimestamp(g, p)
    \/ DoDeliver(g, p)

GroupStep(g) ==
    \E p \in Processes: Step(g, p)

Next ==
    \/ \E g \in Groups: GroupStep(g)
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

SpecFair == Spec /\ WF_vars(\E g \in Groups: GroupStep(g))

-----------------------------------------------------------------

ASSUME
    /\ NGROUPS \in (Nat \ {0})
    /\ NPROCESSES \in (Nat \ {0})
    /\ IsFiniteSet(INITIAL_MESSAGES)

-----------------------------------------------------------------

WasDelivered(g, p, m) ==
    /\ \E <<idx, n>> \in Delivered[g][p]: n.id = m.id

FilterDeliveredMessages(g, p, m) ==
    {<<idx, n>> \in Delivered[g][p]: n.id = m.id}

DeliveredInstant(g, p, m) ==
    (CHOOSE <<t, n>> \in Delivered[g][p]: n.id = m.id)[1]

=================================================================
