-------------------- MODULE GenericMulticast0 --------------------

LOCAL INSTANCE Commons
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets

CONSTANT NPROCESSES
CONSTANT INITIAL_MESSAGES
CONSTANT CONFLICTR(_, _)

------------------------------------------------------------------

LOCAL Processes == {i : i \in 1 .. NPROCESSES}

------------------------------------------------------------------

VARIABLE QuasiReliableChannel
QuasiReliable == INSTANCE QuasiReliable WITH
    NGROUPS <- 1

------------------------------------------------------------------

VARIABLES
    \* Structure that holds the clocks for all processes.
    K,

    \* Structure that holds all messages that were received
    \* but are still pending a final timestamp.
    Pending,

    \* Structure that holds all messages that contains a
    \* final timestamp but were not delivered yet.
    Delivering,

    \* Structure that holds all messages that contains a
    \* final timestamp and were already delivered.
    Delivered,

    \* Used to verify if previous messages conflict with
    \* the message beign processed. Using this approach
    \* is possible to deliver messages with a partially
    \* ordered delivery.
    PreviousMsgs,

    \* Set used to holds the votes that were cast for a message.
    \* Since the coordinator needs that all processes cast a vote for the
    \* final timestamp, this structure will hold the votes each process
    \* cast for each message on the system.
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

LOCAL SendOriginatorAndRemoveLocal(self, dest, curr, prev, S) ==
    IF self = dest /\ prev[2].s = self THEN (S \ {prev}) \cup {curr}
    ELSE IF prev[2].s = dest THEN S \cup {curr}
    ELSE IF self = dest THEN S \ {prev}
    ELSE S

LOCAL SendAllRemoveLocal(curr, prev, S) ==
    (S \ {prev}) \cup {curr}

LOCAL AssignTimestampHandler(self, msg) ==
    /\ \/ /\ \E prev \in PreviousMsgs[self]: CONFLICTR(msg, prev)
          /\ K' = [K EXCEPT ![self] = K[self] + 1]
          /\ PreviousMsgs' = [PreviousMsgs EXCEPT ![self] = {msg}]
       \/ /\ \A prev \in PreviousMsgs[self]: ~CONFLICTR(msg, prev)
          /\ K' = [K EXCEPT ![self] = K[self]]
          /\ PreviousMsgs' = [PreviousMsgs EXCEPT ![self] = PreviousMsgs[self] \cup {msg}]
    /\ LET
        built == CreateMessage(msg, K'[self]) | [s |-> msg.s ]
        voted == built | [ o |-> self ]
        IN
        /\ Pending' = [Pending EXCEPT ![self] = Pending[self] \cup {built}]
        /\ QuasiReliable!SendMap(LAMBDA dest, S: SendOriginatorAndRemoveLocal(self, dest, <<"S1", voted>>, <<"S0", msg>>, S))
        /\ UNCHANGED <<Delivering, Delivered, Votes>>

LOCAL ComputeSeqNumberHandler(self, msg) ==
    /\ LET
        votedTs == {<<m.o, m.ts>> : m \in {x \in Votes[self] \cup {msg}: x.id = msg.id}}
       IN
        /\ \/ /\ Cardinality(votedTs) = Cardinality(msg.d)
              /\ LET
                    curr == CreateMessage(msg, Max({x[2] : x \in votedTs}))
                 IN
                  /\ Votes' = [Votes EXCEPT ![self] = {x \in Votes[self] : x.id /= msg.id}]
                  /\ QuasiReliable!SendMap(LAMBDA dest, S: SendAllRemoveLocal(<<"S2", curr>>, <<"S1", msg>>, S))
           \/ /\ Cardinality(votedTs) < Cardinality(msg.d)
              /\ Votes' = [Votes EXCEPT ![self] = Votes[self] \cup {msg}]
              /\ QuasiReliable!Consume(1, self, <<"S1", msg>>)
        /\ UNCHANGED <<K, PreviousMsgs, Pending, Delivering, Delivered>>

LOCAL AssignSeqNumberHandler(self, m1, m2) ==
    /\ \/ /\ m2.ts > K[self]
          /\ \/ /\ \E prev \in PreviousMsgs[self]: CONFLICTR(m2, prev)
                /\ K' = [K EXCEPT ![self] = m2.ts + 1]
                /\ PreviousMsgs' = [PreviousMsgs EXCEPT ![self] = {}]
             \/ /\ \A prev \in PreviousMsgs[self]: CONFLICTR(m2, prev)
                /\ K' = [K EXCEPT ![self] = m2.ts]
                /\ UNCHANGED PreviousMsgs
       \/ /\ m2.ts <= K[self]
          /\ UNCHANGED <<K, PreviousMsgs>>
    /\ Pending' = [Pending EXCEPT ![self] = @ \ {m1}]
    /\ Delivering' = [Delivering EXCEPT ![self] = Delivering[self] \cup {m2}]
    /\ UNCHANGED <<Votes, Delivered>>

(***************************************************************************)
(*                                                                         *)
(*     This procedure executes after an initiator GM-Cast a message m to   *)
(* m.d. All processes in m.d do the same steps after receiving m, assing   *)
(* the local clock to the message timestamp, inserting the message with    *)
(* the timestamp to the process `Pending` set, and sending it to the       *)
(* initiator to choose the timestamp.                                      *)
(*                                                                         *)
(***************************************************************************)
AssignTimestamp(self) ==
    \* We delegate to the lambda to handle the message while filtering for
    \* the correct state.
    /\ QuasiReliable!Receive(1, self, LAMBDA m: m[1] = "S0" /\ AssignTimestampHandler(self, m[2]))

(***************************************************************************)
(*                                                                         *)
(*     This method is executed only by the initiator. This method          *)
(* processes messages on state `S1` and can proceed in two ways. If the    *)
(* initiator has votes from all other processes, the message's final       *)
(* timestamp is the maximum received vote, and the initiator sends the     *)
(* message back to all participants in state `S`2. Otherwise, the          *)
(* initiator only stores the received message in the `Votes` structure.    *)
(*                                                                         *)
(***************************************************************************)
ComputeSeqNumber(self) ==
    \* We delegate to the lambda handler to effectively execute the procedure.
    \* Here we verify that the message is on state S2 and the current process
    \* is the initiator.
    /\ QuasiReliable!Receive(1, self, LAMBDA m: m[1] = "S1" /\ m[2].s = self /\ ComputeSeqNumberHandler(self, m[2]))

(***************************************************************************)
(*                                                                         *)
(*    After the coordinator computes the final timestamp for the message   *)
(* `m`, all processes in `m.d` will receive the chosen timestamp. Each     *)
(* participant checks the message's timestamp against its local clock. If  *)
(* the value is greater than the process clock, we need to update the      *)
(* process clock with the message's timestamp. If `m` conflicts with a     *)
(* message in the `PreviousMsgs`, the clock updates to m's timestamp plus  *)
(* one and clears the `PreviousMsgs` set. Without any conflict with `m`,   *)
(* the clock updates to m's timestamp. The message is removed from         *)
(* `Pending` and added to `Delivering` set.                                *)
(*                                                                         *)
(***************************************************************************)
AssignSeqNumber(self) ==
    \* We delegate the procedure execution the the handler, and the message
    \* is automatically consumed after the lambda execution. In this one we
    \* only filter the messages.
    /\ QuasiReliable!ReceiveAndConsume(1, self,
        LAMBDA m:
            /\ m[1] = "S2"
            /\ \E o \in Pending[self]: m[2].id = o.id
                /\ AssignSeqNumberHandler(self, o, m[2]))

(***************************************************************************)
(*                                                                         *)
(*    Responsible for orderly delivery of messages. The messages present   *)
(* in the `Delivering` set with the smallest timestamp among others in the *)
(* `Pending` joined with `Delivering` set. We can also deliver messages    *)
(* that commute with all others, the generalized behavior in action.       *)
(*                                                                         *)
(*    Delivered messages will be added to the `Delivered` set and removed  *)
(* from the others. To store the instant of delivery, we insert delivered  *)
(* messages with the following format:                                     *)
(*                                                                         *)
(*                     <<Len(Delivered), {Message}>>                       *)
(*                                                                         *)
(*    Using this model, we know the message delivery order for all         *)
(* processes.                                                              *)
(*                                                                         *)
(***************************************************************************)
DoDeliver(self) ==
    \E m \in Delivering[self]:
        /\ \A n \in (Delivering[self] \cup Pending[self]) \ {m}: StrictlySmaller(m, n) \/ ~CONFLICTR(m, n)
        /\ LET
            T == Delivering[self] \cup Pending[self]
            G == {x \in Delivering[self]: \A y \in T \ {x}: ~CONFLICTR(x, y)}
            F == {m} \cup G
            index == Cardinality(Delivered[self])
           IN
            /\ Delivering' = [Delivering EXCEPT ![self] = @ \ F]
            /\ Delivered' = [Delivered EXCEPT ![self] = Delivered[self] \cup {<<index, F>>}]
            /\ UNCHANGED <<QuasiReliableChannel, Votes, Pending, PreviousMsgs, K>>

------------------------------------------------------------------

(***************************************************************************)
(*                                                                         *)
(*     Responsible for initializing gloabal variables used on the system.  *)
(* All variables that are defined by the protocol is a mapping from the    *)
(* node id to the corresponding process set.                               *)
(*                                                                         *)
(*     The `message` is also a structure, with the following format:       *)
(*                                                                         *)
(*          [ id |-> Nat, ts |-> Nat, d |-> Nodes, s |-> Node ]            *)
(*                                                                         *)
(* The `d` does not need to be the whole Nodes, only one of the possible   *)
(* SUBSET Nodes. The keys representation is `id` the unique message id,    *)
(* `ts` is the message timestamp/sequence number, `d` is the destination.  *)
(* In some steps, a property may be added, for example the `s` property    *)
(* that holds the initial source of the message or the property `o` that   *)
(* is used when casting votes and is used to identiy the process id,       *)
(*                                                                         *)
(***************************************************************************)
LOCAL InitProtocol ==
    /\ K = [ i \in Processes |-> 0 ]
    /\ Pending = [ i \in Processes |-> {} ]
    /\ Delivering = [ i \in Processes |-> {} ]
    /\ Delivered = [ i \in Processes |-> {} ]
    /\ PreviousMsgs = [ i \in Processes |-> {} ]

LOCAL InitHelpers ==
    \* Initialize the protocol network.
    /\ QuasiReliable!Init

    \* This structure is holding the votes the processes cast for each
    \* message on the system. Since any process can be the "coordinator",
    \* this is a mapping for processes to a set. The set will contain the
    \* vote a process has cast for a message.
    /\ Votes = [ i \in Processes |-> {} ]

Init == InitProtocol /\ InitHelpers

------------------------------------------------------------------
Step(self) ==
    \/ AssignTimestamp(self)
    \/ ComputeSeqNumber(self)
    \/ AssignSeqNumber(self)
    \/ DoDeliver(self)

Next ==
    \/ \E self \in Processes: Step(self)
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

SpecFair == Spec /\ WF_vars(\E self \in Processes: Step(self))

------------------------------------------------------------------

\* Verify the input values.
ASSUME
    \* Verify that `NPROCESS` is a natural number greater than 0.
    /\ NPROCESSES \in (Nat \ {0})
    /\ IsFiniteSet(INITIAL_MESSAGES)
------------------------------------------------------------------

WasDelivered(p, m) ==
    /\ \E <<idx, msgs>> \in Delivered[p]:
        \E n \in msgs:
            n.id = m.id

DeliveredInstant(p, m) ==
    (CHOOSE <<index, msgs>> \in Delivered[p]: \E n \in msgs: m.id = n.id)[1]

FilterDeliveredMessages(p, m) ==
    { <<idx, msgs>> \in Delivered[p] : \E n \in msgs : n.id = m.id }

==================================================================
