------------------ MODULE MatchProposal ----------------------
EXTENDS Naturals, FiniteSets, Commons

CONSTANT CONFLICT_CLASSES
CONSTANT NGROUPS
CONSTANT NPROCESSES
CONSTANT NMESSAGES
CONSTANT CONFLICTR(_, _)

----------------------------------------------------------
(************************************************************************************)
(*                                                                                  *)
(* This algorithm works in an environment with crash-stop failures, but we do not   *)
(* model processes failing. The set of all processes contains all correct ones.     *)
(*                                                                                  *)
(************************************************************************************)
LOCAL Processes == 1 .. NPROCESSES
LOCAL Groups == 1 .. NGROUPS
LOCAL ProcessesInGroup == [g \in Groups |-> Processes]

LOCAL AllMessages == CreateMessages(NMESSAGES, Groups, Processes)
LOCAL MessagesCombinations == CreatePossibleMessages(AllMessages)

----------------------------------------------------------

VARIABLES
    K,
    PreviousMsgs,
    Delivered,
    Votes,
    MemoryBuffer,
    QuasiReliableChannel,
    GenericBroadcastBuffer,
    Proposal

(************************************************************************************)
(*                                                                                  *)
(* Initialize the instance for the Generic Multicast 2. The INITIAL_MESSAGES is a   *)
(* sequence, partially ordered. The sequence elements are sets of messages,         *)
(* messages that commute can share a set.                                           *)
(*                                                                                  *)
(************************************************************************************)
Algorithm == INSTANCE Algorithm2 WITH
    INITIAL_MESSAGES <- [g \in Groups |->
        PartiallyOrdered(
            MessagesCombinations[(g % NMESSAGES) + 1], CONFLICTR)],
    CL <- LAMBDA m: FindClass(m, CONFLICT_CLASSES)
----------------------------------------------------------

Spec == Algorithm!Spec

----------------------------------------------------------
(************************************************************************************)
(*                                                                                  *)
(* Consider a consensus group g. If p \in g send message Propose(m, t) and q \in g  *)
(* also sends Propose(m, t′), then t′ = t.                                          *)
(*                                                                                  *)
(************************************************************************************)
HasProposal(m, g, q) ==
    \E v \in Proposal[g][q]: v[2].id = m.id
GetProposal(m, g, q) ==
    (CHOOSE v \in Proposal[g][q]: v[2].id = m.id)[1]
MatchProposal ==
    []\A g \in Groups:
        \A p, q \in ProcessesInGroup[g]:
            \A <<pp, mp>> \in Proposal[g][p]:
                HasProposal(mp, g, q) => (pp = GetProposal(mp, g, q))
==========================================================
