-------------------- MODULE GenericMulticast1 --------------------

LOCAL INSTANCE Commons
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE TLC

\* Number of groups in the algorithm.
CONSTANT NGROUPS

\* Number of processes in the algorithm.
CONSTANT NPROCESSES

\* Set with initial messages the algorithm starts with.
CONSTANT INITIAL_MESSAGES

\* The conflict relation.
CONSTANT CONFLICTR(_,_)

-----------------------------------------------------------------

ASSUME
    \* Verify that `NGROUPS' is a natural number greater than 0.
    /\ NGROUPS \in (Nat \ {0})
    \* Verify that `NPROCESSES' is a natural number greater than 0.
    /\ NPROCESSES \in (Nat \ {0})

-----------------------------------------------------------------

LOCAL Processes == {p : p \in 1 .. NPROCESSES}
LOCAL Groups == {g : g \in 1 .. NGROUPS}

\* The module containing the Atomic Broadcast primitive.
VARIABLE AtomicBroadcastBuffer
AtomicBroadcast == INSTANCE AtomicBroadcast

\* The module containing the quasi reliable channel.
VARIABLE QuasiReliableChannel
QuasiReliable == INSTANCE QuasiReliable WITH
    INITIAL_MESSAGES <- {}

\* The algorithm's `Mem' structure. We use a separate module.
VARIABLE MemoryBuffer
Memory == INSTANCE Memory

-----------------------------------------------------------------

VARIABLES
    \* The process local clock.
    K,

    (********************************************************************************)
    (*                                                                              *)
    (* The set contains previous messages. We use this with the CONFLICTR to verify *)
    (* conflicting messages.                                                        *)
    (*                                                                              *)
    (********************************************************************************)
    PreviousMsgs,

    (********************************************************************************)
    (*                                                                              *)
    (* The set of delivered messages. This set is not an algorithm requirement. We  *)
    (* use this to help check the algorithm's properties.                           *)
    (*                                                                              *)
    (********************************************************************************)
    Delivered,

    (********************************************************************************)
    (*                                                                              *)
    (* A set contains the processes' votes for the message's timestamp. This        *)
    (* structure is implicit in the algorithm.                                      *)
    (*                                                                              *)
    (********************************************************************************)
    Votes

vars == <<
    K,
    MemoryBuffer,
    PreviousMsgs,
    Delivered,
    Votes,
    AtomicBroadcastBuffer,
    QuasiReliableChannel
>>
-----------------------------------------------------------------

\* Check if the given message conflict with any other in the PreviousMsgs.
LOCAL HasConflict(g, p, m1) ==
    \E m2 \in PreviousMsgs[g][p]: CONFLICTR(m1, m2)

(************************************************************************************)
(*                                                                                  *)
(* These are the handlers. The actual algorithm resides here, the lambdas only      *)
(* assert the guarding predicates before calling the handler.                       *)
(*                                                                                  *)
(************************************************************************************)

LOCAL ComputeGroupSeqNumberHandler(g, p, msg, ts) ==
    /\ \/ /\ HasConflict(g, p, msg)
          /\ K' = [K EXCEPT ![g][p] = K[g][p] + 1]
          /\ PreviousMsgs' = [PreviousMsgs EXCEPT ![g][p] = {msg}]
       \/ /\ ~HasConflict(g, p, msg)
          /\ PreviousMsgs' = [PreviousMsgs EXCEPT ![g][p] =
                PreviousMsgs[g][p] \cup {msg}]
          /\ UNCHANGED K
    /\ \/ /\ Cardinality(msg.d) > 1
          /\ Memory!Insert(g, p, <<msg, "S1", K'[g][p]>>)
          /\ QuasiReliable!Send(<<msg, g, K'[g][p]>>)
       \/ /\ Cardinality(msg.d) = 1
          /\ Memory!Insert(g, p, <<msg, "S3", K'[g][p]>>)
          /\ UNCHANGED QuasiReliableChannel
    /\ UNCHANGED <<Delivered, Votes>>

LOCAL SynchronizeGroupClockHandler(g, p, m, tsf) ==
    /\ \/ /\ tsf > K[g][p]
          /\ K' = [K EXCEPT ![g][p] = tsf]
          /\ PreviousMsgs' = [PreviousMsgs EXCEPT ![g][p] = {}]
       \/ /\ tsf <= K[g][p]
          /\ UNCHANGED <<K, PreviousMsgs>>
    /\ \/ /\ \E <<n, s, ts>> \in MemoryBuffer[g][p]: s = "S1" /\ m = n
          /\ Memory!Insert(g, p, <<m, "S3", tsf>>)
       \/ UNCHANGED MemoryBuffer
    /\ UNCHANGED <<QuasiReliableChannel, Delivered, Votes>>

LOCAL GatherGroupsTimestampHandler(g, p, msg, ts, tsf) ==
   /\ \/ /\ ts < tsf
         /\ AtomicBroadcast!ABroadcast(g, <<msg, "S2", tsf>>)
      \/ UNCHANGED AtomicBroadcastBuffer
   /\ Memory!Insert(g, p, <<msg, "S3", tsf>>)
   /\ UNCHANGED <<K, PreviousMsgs, Delivered>>

-----------------------------------------------------------------

(************************************************************************************)
(*                                                                                  *)
(* Executes when process P receives a message M from the Atomic Broadcast primitive *)
(* and M is in P's memory. This procedure is extensive, with multiple branches      *)
(* based on the message's state and destination. Let's split the explanation.       *)
(*                                                                                  *)
(* When M's state is S0, we first verify if M conflicts with messages in the        *)
(* PreviousMsgs set. If a conflict exists, we increase P's local clock by one and   *)
(* clear the PreviousMsgs set.                                                      *)
(*                                                                                  *)
(* When message M has a single group as the destination, it is already in its       *)
(* desired destination and is synchronized because we received M from Atomic        *)
(* Broadcast primitive. P stores M in memory with state S3 and timestamp with the   *)
(* current clock value.                                                             *)
(*                                                                                  *)
(* When M includes multiple groups in the destination, the participants must agree  *)
(* on the final timestamp. When M's state is S0, P will send its timestamp          *)
(* proposition to all other participants, which is the current clock value, and     *)
(* update M's state to S1 and timestamp. If M's state is S2, we are synchronizing   *)
(* the local group, meaning we may need to leap the clock to the M's received       *)
(* timestamp and then set M to state S3.                                            *)
(*                                                                                  *)
(************************************************************************************)
ComputeGroupSeqNumber(g, p) ==
    /\ AtomicBroadcast!ABDeliver(g, p,
        LAMBDA t: t[2] = "S0" /\ ComputeGroupSeqNumberHandler(g, p, t[1], t[3]))

(************************************************************************************)
(*                                                                                  *)
(* After exchanging the votes between groups, processes must select the final       *)
(* timestamp. When we have one proposal from each group in message M's destination, *)
(* the highest vote is the decided timestamp. If P's local clock is smaller than    *)
(* the value, we broadcast the message to the local group with state S2 and save it *)
(* in memory. Otherwise, we update the in-memory to state S3.                       *)
(*                                                                                  *)
(* We only execute the procedure once we have proposals from all participating      *)
(* groups. Since we receive messages from the quasi-reliable channel, we keep the   *)
(* votes in the Votes structure. This structure is implicit in the algorithm.       *)
(*                                                                                  *)
(************************************************************************************)
LOCAL HasNecessaryVotes(g, p, msg, ballot) ==
    /\ Cardinality(ballot) = Cardinality(msg.d)
    /\ Memory!Contains(g, p, LAMBDA n: msg = n[1] /\ n[2] = "S1")
GatherGroupsTimestamp(g, p) ==
    /\ QuasiReliable!ReceiveAndConsume(g, p,
        LAMBDA t:
            /\ LET
                msg == t[1]
                origin == t[2]
                vote == <<msg.id, origin, t[3]>>
                ballot == {v \in (Votes[g][p] \cup {vote}): v[1] = msg.id}
                elected == Max({x[3] : x \in ballot})
               IN
                \* We only execute the procedure when we have proposals from all groups.
                /\ \/ /\ HasNecessaryVotes(g, p, msg, ballot)
                      /\ \E <<m, s, ts>> \in MemoryBuffer[g][p]: m = msg
                        /\ GatherGroupsTimestampHandler(g, p, msg, ts, elected)
                      /\ Votes' = [Votes EXCEPT ![g][p] = {
                            x \in Votes[g][p]: x[1] /= msg.id}]
                   \/ /\ ~HasNecessaryVotes(g, p, msg, ballot)
                      /\ Votes' = [Votes EXCEPT ![g][p] = Votes[g][p] \cup {vote}]
                      /\ UNCHANGED <<MemoryBuffer, K,
                            PreviousMsgs, AtomicBroadcastBuffer>>
                /\ UNCHANGED <<Delivered>>)

SynchronizeGroupClock(g, p) ==
    /\ AtomicBroadcast!ABDeliver(g, p,
        LAMBDA t: t[2] = "S2" /\ SynchronizeGroupClockHandler(g, p, t[1], t[3]))

(************************************************************************************)
(*                                                                                  *)
(* When messages are to deliver, we select them and call the delivery primitive.    *)
(* Ready means they are in state S3, and the message either does not conflict with  *)
(* any other in the memory structure or is smaller than all others. Once a message  *)
(* is ready, we also collect the messages that do not conflict with any other for   *)
(* delivery in a single batch.                                                      *)
(*                                                                                  *)
(************************************************************************************)
DoDeliver(g, p) ==
    \* We are accessing the buffer directly, and not through the `Memory` instance.
    \* We do this because is easier and because we are only reading the values here.
    \* Any changes we do through the instance.
    \E <<m_1, state, ts_1>> \in MemoryBuffer[g][p]:
        /\ state = "S3"
        /\ \A <<m_2, ignore, ts_2>> \in (MemoryBuffer[g][p] \ {<<m_1, state, ts_1>>}):
            /\ \/ ~CONFLICTR(m_1, m_2)
               \/ ts_1 < ts_2 \/ (m_1.id < m_2.id /\ ts_1 = ts_2)
        /\ LET
            G == Memory!ForAllFilter(g, p,
                LAMBDA t_i, t_j: t_i[2] = "S3" /\ ~CONFLICTR(t_i[1], t_j[1]))
            D == G \cup {<<m_1, "S3", ts_1>>}
            F == {t[1]: t \in D}
           IN
            /\ Memory!Remove(g, p, D)
            /\ Delivered' = [Delivered EXCEPT ![g][p] =
                Delivered[g][p] \cup Enumerate(Cardinality(Delivered[g][p]), F)]
            /\ UNCHANGED <<QuasiReliableChannel, AtomicBroadcastBuffer,
                    Votes, PreviousMsgs, K>>
-----------------------------------------------------------------

LOCAL InitProtocol ==
    /\ K = [i \in Groups |-> [p \in Processes |-> i]]
    /\ Memory!Init
    /\ PreviousMsgs = [i \in Groups |-> [p \in Processes |-> {}]]
    /\ Delivered = [i \in Groups |-> [p \in Processes |-> {}]]
    /\ Votes = [i \in Groups |-> [p \in Processes |-> {}]]

LOCAL InitCommunication ==
    /\ AtomicBroadcast!Init
    /\ QuasiReliable!Init

Init == InitProtocol /\ InitCommunication

-----------------------------------------------------------------
Step(g, p) ==
    \/ ComputeGroupSeqNumber(g, p)
    \/ GatherGroupsTimestamp(g, p)
    \/ SynchronizeGroupClock(g, p)
    \/ DoDeliver(g, p)

GroupStep(g) ==
    \E p \in Processes: Step(g, p)

Next ==
    \/ \E g \in Groups: GroupStep(g)
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

SpecFair == Spec /\ WF_vars(\E g \in Groups: GroupStep(g))

-----------------------------------------------------------------

\* Helper functions to aid when checking the algorithm properties.

WasDelivered(g, p, m) ==
    (********************************************************************************)
    (* Verifies if the given process `p' in group `g' delivered message `m'.        *)
    (********************************************************************************)
    /\ \E <<idx, n>> \in Delivered[g][p]: n.id = m.id

FilterDeliveredMessages(g, p, m) ==
    (********************************************************************************)
    (* Retrieve the set of messages with the same id as message `m' delivered by    *)
    (* the given process `p' in group `g'.                                          *)
    (********************************************************************************)
    {<<idx, n>> \in Delivered[g][p]: n.id = m.id}

DeliveredInstant(g, p, m) ==
    (********************************************************************************)
    (* Retrieve the instant the process `p' in group `g' delivered message `m'.     *)
    (********************************************************************************)
    (CHOOSE <<t, n>> \in Delivered[g][p]: n.id = m.id)[1]

=================================================================
