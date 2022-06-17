-------------------- MODULE Memory --------------------
(************************************************************************************)
(*                                                                                  *)
(* This module is the abstraction for the Memory structure used by Generic          *)
(* Multicast 1 and 2. Inserting a new message will either create a new entry or     *)
(* update an existing one. The requirement here is that, at any time, we must       *)
(* always have only one entry for a message, never duplicating. Besides the insert, *)
(* we have some additional procedures wrapping the buffer for verifying entries and *)
(* removing them. Each process owns a buffer and accesses only its own buffer,      *)
(* never the others'.                                                               *)
(*                                                                                  *)
(************************************************************************************)
-------------------------------------------------------

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals

\* Number of groups.
CONSTANT NGROUPS

\* Number of processes.
CONSTANT NPROCESSES

-------------------------------------------------------

\* The underlying buffer, each process owns one.
\* We use a set, and the entries are the message tuples.
VARIABLE MemoryBuffer

-------------------------------------------------------
(************************************************************************************)
(*                                                                                  *)
(* Insert the new entry into the process buffer in the specific group. We remove    *)
(* the previous entry and put the new one in its place.                             *)
(*                                                                                  *)
(************************************************************************************)
Insert(g, p, t) ==
    /\ MemoryBuffer' = [
        MemoryBuffer EXCEPT ![g][p] = {
            <<msg, state, ts>> \in MemoryBuffer[g][p]:
                msg.id /= t[1].id} \cup {t}]

(************************************************************************************)
(*                                                                                  *)
(* Verify if an entry exists in the process buffer in the specific group using the  *)
(* callback.                                                                        *)
(*                                                                                  *)
(************************************************************************************)
Contains(g, p, Fn(_)) ==
    \E t \in MemoryBuffer[g][p]: Fn(t)

(************************************************************************************)
(*                                                                                  *)
(* We filter the entries in the process buffer in the specific group using the      *)
(* callback. An entry must be valid when compared with all others except itself.    *)
(*                                                                                  *)
(************************************************************************************)
ForAllFilter(g, p, Fn(_, _)) ==
    {t_1 \in MemoryBuffer[g][p]:
        \A t_2 \in (MemoryBuffer[g][p] \ {t_1}): Fn(t_1, t_2)}

\* Remove the entries in the process buffer in the specific group.
Remove(g, p, S) ==
    /\ MemoryBuffer' = [MemoryBuffer EXCEPT ![g][p] = @ \ S]

-------------------------------------------------------

\* Initialize the structure for all processes with an empty buffer.
Init ==
    /\ MemoryBuffer = [
        g \in 1 .. NGROUPS |-> [
            p \in 1 .. NPROCESSES |-> {}]]

=======================================================
