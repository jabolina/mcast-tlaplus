-------------------- MODULE Commons --------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Sequences

--------------------------------------------------------

LOCAL Identity(x) == x
LOCAL Choose(S) == CHOOSE x \in S: TRUE
LOCAL IsEven(x) == x % 2 = 0
Max(S) == CHOOSE x \in S: \A y \in S: x >= y

AllConflictClass == "All"
NeverConflictClass == "Never"
OddConflictClass == "Odd"
EvenConflictClass == "Even"

FindClass(m, Classes) ==
    IF AllConflictClass \in Classes THEN AllConflictClass
    ELSE IF NeverConflictClass \in Classes THEN NeverConflictClass
    \*ELSE IF IsEven(m.id) THEN EvenConflictClass
    ELSE OddConflictClass

--------------------------------------------------------
(************************************************************************************)
(*                                                                                  *)
(* Three different conflict relations. We identify the relation to use through the  *)
(* configuration files. We verify each property with all three.                     *)
(*                                                                                  *)
(************************************************************************************)

(************************************************************************************)
(*                                                                                  *)
(* Use the message's identifier, where the evens conflict with evens and odds with  *)
(* odds. This relationship has a partial ordering.                                  *)
(*                                                                                  *)
(************************************************************************************)
IdConflict(m, n) == m.id # n.id /\ IsEven(m.id) = IsEven(n.id)

(************************************************************************************)
(*                                                                                  *)
(* All messages conflict in this relationship. The executions with this conflict    *)
(* relation are equivalent to the Atomic Multicast.                                 *)
(*                                                                                  *)
(************************************************************************************)
AlwaysConflict(m, n) == TRUE

(************************************************************************************)
(*                                                                                  *)
(* There is no conflict in this relationship. The executions with this conflict     *)
(* relation are equivalent to the Reliable Multicast.                               *)
(*                                                                                  *)
(************************************************************************************)
NeverConflict(m, n) == FALSE

--------------------------------------------------------

\* We use multiple procedures provided by the `^TLA$^+$^' community.
\* Most of the procedures are used locally to create the messages.

\* From Community Modules `~https://github.com/tlaplus/CommunityModules/blob/beb1b41f78c4e850848e1bc3e89be722a98cbb06/modules/Functions.tla#L42-L49~'
LOCAL IsInjective(f) ==
    (***************************************************************************)
    (* A function is injective iff it maps each element in its domain to a     *)
    (* distinct element.                                                       *)
    (*                                                                         *)
    (* This definition is overridden by TLC in the Java class SequencesExt.    *)
    (* The operator is overridden by the Java method with the same name.       *)
    (***************************************************************************)
    \A a,b \in DOMAIN f : f[a] = f[b] => a = b

\* From Community Modules `~https://github.com/tlaplus/CommunityModules/blob/beb1b41f78c4e850848e1bc3e89be722a98cbb06/modules/SequencesExt.tla#L22-L27~'
LOCAL SetToSeq(S) ==
  (**************************************************************************)
  (* Convert a set to some sequence that contains all the elements of the   *)
  (* set exactly once, and contains no other elements.                      *)
  (**************************************************************************)
  CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

\* From Community Modules `~https://github.com/tlaplus/CommunityModules/blob/beb1b41f78c4e850848e1bc3e89be722a98cbb06/modules/SequencesExt.tla#L29-L38~'
LOCAL SetToSeqs(S) ==
  (**************************************************************************)
  (* Convert the set S to a set containing all sequences containing the     *)
  (* elements of S exactly once and no other elements.                      *)
  (* Example:                                                               *)
  (*    SetToSeqs({}), {<<>>}                                               *)
  (*    SetToSeqs({"t","l"}) = {<<"t","l">>, <<"l","t">>}                   *)
  (**************************************************************************)
  LET D == 1..Cardinality(S)
  IN { f \in [D -> S] : \A i,j \in D : i # j => f[i] # f[j] }

\* From Community Modules `~https://github.com/tlaplus/CommunityModules/blob/beb1b41f78c4e850848e1bc3e89be722a98cbb06/modules/SequencesExt.tla#L49-L58~'
LOCAL SetToAllKPermutations(S) ==
  (**************************************************************************)
  (* Convert the set S to a set containing all k-permutations of elements   *)
  (* of S for k \in 0..Cardinality(S).                                      *)
  (* Example:                                                               *)
  (*    SetToAllKPermutations({}) = {<<>>}                                  *)
  (*    SetToAllKPermutations({"a"}) = {<<>>, <<"a">>}                      *)
  (*    SetToAllKPermutations({"a","b"}) =                                  *)
  (*                    {<<>>, <<"a">>, <<"b">>,<<"a","b">>, <<"b","a">>}   *)
  (**************************************************************************)
  UNION { SetToSeqs(s) : s \in SUBSET S  }

\* From Community Modules `~https://github.com/tlaplus/CommunityModules/blob/beb1b41f78c4e850848e1bc3e89be722a98cbb06/modules/Folds.tla#L3-L27~'
LOCAL MapThenFoldSet(op(_,_), base, f(_), choose(_), S) ==
(******************************************************************************)
(* Starting from base, apply op to f(x), for all x \in S, by choosing the set *)
(* elements with `choose'. If there are multiple ways for choosing an element,*)
(* op should be associative and commutative. Otherwise, the result may depend *)
(* on the concrete implementation of `choose'.                                *)
(*                                                                            *)
(* FoldSet, a simpler version for sets is contained in FiniteSetsEx.          *)
(* FoldFunction, a simpler version for functions is contained in Functions.   *)
(* FoldSequence, a simpler version for sequences is contained in SequencesExt.*)
(*                                                                            *)
(* Example:                                                                   *)
(*                                                                            *)
(*  MapThenFoldSet(LAMBDA x,y: x \cup y,                                      *)
(*                 {},                                                        *)
(*                 LAMBDA x: {{x}},                                           *)
(*                 LAMBDA set: CHOOSE x \in set: TRUE,                        *)
(*                 {1,2})                                                     *)
(*       = {{1},{2}}                                                          *)
(******************************************************************************)
  LET iter[s \in SUBSET S] ==
        IF s = {} THEN base
        ELSE LET x == choose(s)
             IN  op(f(x), iter[s \ {x}])
  IN  iter[S]

\* From Community Modules `~https://github.com/tlaplus/CommunityModules/blob/beb1b41f78c4e850848e1bc3e89be722a98cbb06/modules/SequencesExt.tla#L15-L20~'
LOCAL ToSet(s) ==
  (*************************************************************************)
  (* The image of the given sequence s. Cardinality(ToSet(s)) <= Len(s)    *)
  (* see https://en.wikipedia.org/wiki/Image_(mathematics)                 *)
  (*************************************************************************)
  { s[i] : i \in DOMAIN s }

\* From Community Modules `~https://github.com/tlaplus/CommunityModules/blob/beb1b41f78c4e850848e1bc3e89be722a98cbb06/modules/SequencesExt.tla#L126-L130~'
ReplaceAt(s, i, e) ==
  (**************************************************************************)
  (* Replaces the element at position i with the element e.                 *)
  (**************************************************************************)
  [s EXCEPT ![i] = e]
--------------------------------------------------------

LOCAL Originator(G, P) == <<Choose(G), Choose(P)>>

\* Initialize the message structure we use to check the algorithm.
CreateMessages(nmessage, G, P) ==
    {[id |-> m, d |-> G, o |-> Originator(G, P)]: m \in 1 .. nmessage}

(************************************************************************************)
(*                                                                                  *)
(* Create all possible different possibilities in the initial ordering. Since we    *)
(* replaced the combination of Reliable Multicast + Atomic Broadcast with multiple  *)
(* uses of Atomic Broadcast, messages can have distinct orders across groups. We    *)
(* force this distinction.                                                          *)
(*                                                                                  *)
(************************************************************************************)
CreatePossibleMessages(S) ==
    LET M == SetToAllKPermutations(S)
    IN MapThenFoldSet(
            LAMBDA x, y: <<x>> \o y,
            <<>>,
            Identity,
            Choose,
            {m \in M: Len(m) = Cardinality(S)})

\* We create the tuple with the message, state, and timestamp.
LOCAL InitialMessage(m) == <<m, "S0", 0>>

\* A totally ordered message buffer.
TotallyOrdered(F) ==
    [x \in DOMAIN F |-> InitialMessage(F[x])]

(************************************************************************************)
(*                                                                                  *)
(* Creates a partially ordered buffer from the sequence using the given predicate   *)
(* to identify conflicts between messages.                                          *)
(*                                                                                  *)
(************************************************************************************)
LOCAL ExistsConflict(x, S, Op(_, _)) ==
    \E d \in ToSet(S):
        \E <<n, s, ts>> \in d: Op(x, n)
PartiallyOrdered(F, Op(_, _)) ==
    MapThenFoldSet(
        LAMBDA x, y:
            IF Len(y) = 0 \/ ExistsConflict(x, y, Op)
                THEN <<{InitialMessage(x)}>> \o y
            ELSE <<y[1] \cup {InitialMessage(x)}>>,
            <<>>,
            Identity,
            Choose,
            ToSet(F))

--------------------------------------------------------
\* We enumerate the entries in the given set.
Enumerate(base, E) ==
    LET f == SetToSeq(E) IN {<<base + i, f[i]>>: i \in DOMAIN f}

========================================================
