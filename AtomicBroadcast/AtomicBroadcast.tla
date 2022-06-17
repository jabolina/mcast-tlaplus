-------------------- MODULE AtomicBroadcast --------------------
(************************************************************************************)
(*                                                                                  *)
(* This module is the abstraction for the Atomic Broadcast, a primitive for group   *)
(* communication. A process can broadcast a message to its local group, where all   *)
(* members will deliver in the same order.                                          *)
(*                                                                                  *)
(* We use a sequence to maintain the same order on all processes. New messages are  *)
(* added to the back and removed from the front. A group has its own order within,  *)
(* whereas there are no ordering requirements across groups.                        *)
(*                                                                                  *)
(************************************************************************************)

---------------------------------------------------------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

\* Number of groups.
CONSTANT NGROUPS

\* Number of processes.
CONSTANT NPROCESSES

\* The sequences of initial messages.
CONSTANT INITIAL_MESSAGES

---------------------------------------------------------------------

VARIABLES
    \* The underlying buffer that holds all the messages.
    AtomicBroadcastBuffer

---------------------------------------------------------------------
(************************************************************************************)
(*                                                                                  *)
(* Broadcast the message to the given group. We add the message at the back of      *)
(* every process' sequence within this group.                                       *)
(*                                                                                  *)
(************************************************************************************)
ABroadcast(g, m) ==
    /\ AtomicBroadcastBuffer' = [
        AtomicBroadcastBuffer EXCEPT ![g] = [
            p \in DOMAIN AtomicBroadcastBuffer[g] |->
                Append(AtomicBroadcastBuffer[g][p], m)]]

(************************************************************************************)
(*                                                                                  *)
(* Deliver the message to the process in the specific group. If there is a message  *)
(* in the buffer, we pass it to the callback and consume it.                        *)
(*                                                                                  *)
(************************************************************************************)
ABDeliver(g, p, Fn(_)) ==
    /\ Len(AtomicBroadcastBuffer[g][p]) > 0
    /\ Fn(Head(AtomicBroadcastBuffer[g][p]))
    /\ AtomicBroadcastBuffer' = [
        AtomicBroadcastBuffer EXCEPT ![g][p] =
            Tail(AtomicBroadcastBuffer[g][p])]

---------------------------------------------------------------------

(************************************************************************************)
(*                                                                                  *)
(* Initialize the algorithm with the configuration values. The processes within a   *)
(* group will have the same sequence of messages in the same order.                 *)
(*                                                                                  *)
(************************************************************************************)
Init ==
    /\ AtomicBroadcastBuffer = [
        g \in 1 .. NGROUPS |-> [
            p \in 1 .. NPROCESSES |-> INITIAL_MESSAGES[g]]]
=====================================================================
