-------------------- MODULE GenericMulticast0 --------------------
LOCAL INSTANCE Commons
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets

------------------------------------------------------------------

\* Number of processes in the algorithm.
CONSTANT NPROCESSES

\* Set with initial messages the algorithm starts with.
CONSTANT INITIAL_MESSAGES

\* The conflict relation.
CONSTANT CONFLICTR(_, _)

------------------------------------------------------------------

ASSUME
    \* Verify that `NPROCESSES' is a natural number greater than 0.
    /\ NPROCESSES \in (Nat \ {0})

    \* The messages in the protocol must be finite.
    /\ IsFiniteSet(INITIAL_MESSAGES)

------------------------------------------------------------------

LOCAL Processes == {i : i \in 1 .. NPROCESSES}

(************************************************************************************)
(*                                                                                  *)
(* The instance of the quasi-reliable channel for process communication primitive.  *)
(* We use groups with single processes, having NPROCESSES groups.                   *)
(*                                                                                  *)
(************************************************************************************)
VARIABLE QuasiReliableChannel
QuasiReliable == INSTANCE QuasiReliable WITH
    NGROUPS <- NPROCESSES,
    NPROCESSES <- 1

------------------------------------------------------------------

VARIABLES
    \* Structure that holds the clocks for all processes.
    K,

    (* Structure that holds all messages that were received but are still pending a *)
    (* final timestamp.                                                             *)
    Pending,

    (* Structure that holds all messages that contains a final timestamp but were   *)
    (* not delivered yet.                                                           *)
    Delivering,

    (* Structure that holds all messages that contains a final timestamp and were   *)
    (* already delivered.                                                           *)
    Delivered,

    (* Used to verify if previous messages conflict with the message beign          *)
    (* processed. Using this approach is possible to deliver messages with a        *)
    (* partially ordered delivery.                                                  *)
    PreviousMsgs,

    (* Set used to holds the votes that were cast for a message. Since the          *)
    (* coordinator needs that all processes cast a vote for the final timestamp,    *)
    (* this structure will hold the votes each process cast for each message on the *)
    (* system.                                                                      *)
    Votes

vars == <<
    QuasiReliableChannel,
    Votes,
    K,
    Pending,
    Delivering,
    Delivered,
    PreviousMsgs
>>

------------------------------------------------------------------

(************************************************************************************)
(*                                                                                  *)
(* Helper to send messages. In a single operation we consume the message from our   *)
(* local network and send a request to the algorithm initiator. Is not possible to  *)
(* execute multiple operations in a single step on the same set. That is, we can    *)
(* not consume and send in different operations.                                    *)
(*                                                                                  *)
(************************************************************************************)
LOCAL SendOriginatorAndRemoveLocal(self, dest, curr, prev, S) ==
    IF self = dest /\ prev[2].o = self THEN (S \ {prev}) \cup {curr}
    ELSE IF prev[2].o = dest THEN S \cup {curr}
    ELSE IF self = dest THEN S \ {prev}
    ELSE S

\* Check if the given message conflict with any other in the PreviousMsgs.
LOCAL HasConflict(self, m1) ==
    \E m2 \in PreviousMsgs[self]: CONFLICTR(m1, m2)
------------------------------------------------------------------

(************************************************************************************)
(*                                                                                  *)
(* We have the handlers representing each step of the algorithm. The handlers are   *)
(* the actual algorithm, and the caller is the step guard predicate.                *)
(*                                                                                  *)
(************************************************************************************)

LOCAL AssignTimestampHandler(self, msg) ==
    /\ \/ /\ HasConflict(self, msg)
          /\ K' = [K EXCEPT ![self] = K[self] + 1]
          /\ PreviousMsgs' = [PreviousMsgs EXCEPT ![self] = {msg}]
       \/ /\ ~HasConflict(self, msg)
          /\ K' = [K EXCEPT ![self] = K[self]]
          /\ PreviousMsgs' = [PreviousMsgs EXCEPT ![self] = PreviousMsgs[self] \cup {msg}]
    /\ Pending' = [Pending EXCEPT ![self] = Pending[self] \cup {<<K'[self], msg>>}]
    /\ QuasiReliable!SendMap(LAMBDA dest, S: SendOriginatorAndRemoveLocal(self, dest, <<"S1", K'[self], msg, self>>, <<"S0", msg>>, S))
    /\ UNCHANGED <<Delivering, Delivered, Votes>>

LOCAL ComputeSeqNumberHandler(self, ts, msg, origin) ==
    /\ LET
        vote == <<msg.id, origin, ts>>
        election == {v \in (Votes[self] \cup {vote}) : v[1] = msg.id}
        elected == Max({x[3] : x \in election})
       IN
        /\ \/ /\ Cardinality(election) = Cardinality(msg.d)
              /\ Votes' = [Votes EXCEPT ![self] = {x \in Votes[self] : x[1] /= msg.id}]
              /\ QuasiReliable!SendMap(LAMBDA dest, S: (S \ {<<"S1", ts, msg>>}) \cup {<<"S2", elected, msg>>})
           \/ /\ Cardinality(election) < Cardinality(msg.d)
              /\ Votes' = [Votes EXCEPT ![self] = Votes[self] \cup {vote}]
              /\ QuasiReliable!Consume(1, self, <<"S1", ts, msg, origin>>)
        /\ UNCHANGED <<K, PreviousMsgs, Pending, Delivering, Delivered>>

LOCAL AssignSeqNumberHandler(self, ts, msg) ==
    /\ \/ /\ ts > K[self]
          /\ \/ /\ HasConflict(self, msg)
                /\ K' = [K EXCEPT ![self] = ts + 1]
                /\ PreviousMsgs' = [PreviousMsgs EXCEPT ![self] = {}]
             \/ /\ ~HasConflict(self, msg)
                /\ K' = [K EXCEPT ![self] = ts]
                /\ UNCHANGED PreviousMsgs
       \/ /\ ts <= K[self]
          /\ UNCHANGED <<K, PreviousMsgs>>
    /\ Delivering' = [Delivering EXCEPT ![self] = Delivering[self] \cup {<<ts, msg>>}]
    /\ UNCHANGED <<Votes, Delivered>>

------------------------------------------------------------------

(************************************************************************************)
(*                                                                                  *)
(* This procedure executes after an initiator GM-Cast a message m to `^$m.d$^'. All *)
(* processes in `^$m.d$^' do the same thing after receiving m, assing the local     *)
(* clock to the message timestamp, inserting the message with the timestamp to the  *)
(* process Pending set, and sending it to the initiator to choose the timestamp.    *)
(*                                                                                  *)
(************************************************************************************)
AssignTimestamp(self) ==
    \* We delegate to the lambda to handle the message while filtering for
    \* the correct state.
    /\ QuasiReliable!Receive(self, 1,
        LAMBDA t:
            /\ t[1] = "S0"
            /\ AssignTimestampHandler(self, t[2]))

(************************************************************************************)
(*                                                                                  *)
(* This method is executed only by the initiator. This method processes messages on *)
(* state `S1' and can proceed in two ways. If the initiator has votes from all      *)
(* other processes, the message's final timestamp is the maximum received vote, and *)
(* the initiator sends the message back to all participants in state `S2'.          *)
(* Otherwise, the initiator only store the received message in the Votes structure. *)
(*                                                                                  *)
(************************************************************************************)
ComputeSeqNumber(self) ==
    \* We delegate to the lambda handler to effectively execute the procedure.
    \* Here we verify that the message is on state `S1' and the current process
    \* is the initiator.
    /\ QuasiReliable!Receive(self, 1,
        LAMBDA t:
            /\ t[1] = "S1"
            /\ t[3].o = self
            /\ ComputeSeqNumberHandler(self, t[2], t[3], t[4]))

(************************************************************************************)
(*                                                                                  *)
(* After the coordinator computes the final timestamp for the message m, all        *)
(* processes in `^$m.d$^' will receive the chosen timestamp. Each participant       *)
(* checks the message's timestamp against its local clock. If the value is greater  *)
(* than the process clock, we need to update the process clock with the message's   *)
(* timestamp. If m conflicts with a message in the PreviousMsgs, the clock updates  *)
(* to m's timestamp plus one and clears the PreviousMsgs set. Without any conflict  *)
(* with m, the clock updates to m's timestamp. The message is removed from Pending  *)
(* and added to Delivering set.                                                     *)
(*                                                                                  *)
(************************************************************************************)
AssignSeqNumber(self) ==
    \* We delegate the procedure execution the the handler, and the message
    \* is automatically consumed after the lambda execution. In this one we
    \* only filter the messages.
    /\ QuasiReliable!ReceiveAndConsume(self, 1,
        LAMBDA t_1:
            /\ t_1[1] = "S2"
            /\ \E t_2 \in Pending[self]: t_1[3].id = t_2[2].id
                /\ AssignSeqNumberHandler(self, t_1[2], t_1[3])
                \* We remove the message here to avoid too many arguments
                \* in the procedure invocation.
                /\ Pending' = [Pending EXCEPT ![self] = @ \ {t_2}])

(************************************************************************************)
(*                                                                                  *)
(* Responsible for delivery of messages. The messages in the Delivering set with    *)
(* the smallest timestamp among others in the Pending joined with Delivering set.   *)
(* We can also deliver messages that commute with all others, the generalized       *)
(* behavior in action.                                                              *)
(*                                                                                  *)
(* Delivered messages will be added to the Delivered set and removed from the       *)
(* others. To store the instant of delivery, we insert delivered messages with the  *)
(* following format:                                                                *)
(*                                                                                  *)
(*                          `.<<Nat, Message>>.'                                    *)
(*                                                                                  *)
(*    Using this model, we know the message delivery order for all processes.       *)
(*                                                                                  *)
(************************************************************************************)
DoDeliver(self) ==
    \E <<ts_1, m_1>> \in Delivering[self]:
        /\ \A <<ts_2, m_2>> \in (Delivering[self] \cup Pending[self]) \ {<<ts_1, m_1>>}:
            \/ ~CONFLICTR(m_1, m_2)
            \/ ts_1 < ts_2 \/ (m_1.id < m_2.id /\ ts_1 = ts_2)
        /\ LET
            T == Delivering[self] \cup Pending[self]
            G == {t_i \in Delivering[self]: \A t_j \in T \ {t_i}: ~CONFLICTR(t_i[2], t_j[2])}
            F == {m_1} \cup {t[2] : t \in G}
           IN
            /\ Delivering' = [Delivering EXCEPT ![self] = @ \ (G \cup {<<ts_1, m_1>>})]
            /\ Delivered' = [Delivered EXCEPT ![self] = Delivered[self] \cup Enumerate(Cardinality(Delivered[self]), F)]
            /\ UNCHANGED <<QuasiReliableChannel, Votes, Pending, PreviousMsgs, K>>

------------------------------------------------------------------

(************************************************************************************)
(*                                                                                  *)
(* Responsible for initializing global variables used on the system. All variables  *)
(* necessary by the protocol are a mapping from the node id to the corresponding    *)
(* process set.                                                                     *)
(*                                                                                  *)
(*     The "message" is also a structure, with the following format:                *)
(*                                                                                  *)
(*               `.[ id |-> Nat, d |-> Nodes, o |-> Node ].'                        *)
(*                                                                                  *)
(* We have the properties: `id' is the messages' unique id, we use a natural number *)
(* to represent; `d' is the destination, it may be a subset of the Nodes set; and   *)
(* `o' is the originator, the process that started the execution of the algorithm.  *)
(* These properties are all static and never change.                                *)
(*                                                                                  *)
(* The mutable values we transport outside the message structure. We do this using  *)
(* the process communication channel, using a tuple to send the message along with  *)
(* the mutable values.                                                              *)
(*                                                                                  *)
(************************************************************************************)
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

\* Helper functions to aid when checking the algorithm properties.

WasDelivered(p, m) ==
    (********************************************************************************)
    (* Verifies if the given process `p' delivered message `m'.                     *)
    (********************************************************************************)
    /\ \E <<idx, n>> \in Delivered[p]: n.id = m.id

DeliveredInstant(p, m) ==
    (********************************************************************************)
    (* Retrieve the instant the given process `p' delivered message `m'.            *)
    (********************************************************************************)
    (CHOOSE <<index, n>> \in Delivered[p]: m.id = n.id)[1]

FilterDeliveredMessages(p, m) ==
    (********************************************************************************)
    (* Retrieve the set of messages with the same id as message `m' delivered by    *)
    (* the given process `p'.                                                       *)
    (********************************************************************************)
    {<<idx, n>> \in Delivered[p] : n.id = m.id}

==================================================================
