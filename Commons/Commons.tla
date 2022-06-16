-------------------- MODULE Commons --------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Sequences

LOCAL IsEven(x) == x % 2 = 0

IdConflict(m, n) == IsEven(m.id) = IsEven(n.id)

AlwaysConflict(m, n) == TRUE

NeverConflict(m, n) == FALSE

--------------------------------------------------------

StrictlySmaller(m, n) ==
    /\ \/ m.ts < n.ts
       \/ m.id < n.id /\ m.ts = n.ts

--------------------------------------------------------

(***************************************************************************)
(* An infix operator that can merge two structures into a single one.      *)
(*                                                                         *)
(* Elements in the right side can override the values on the left side.    *)
(***************************************************************************)
LOCAL join(l, r, LS, RS) ==
    [p \in LS \union RS |-> IF p \in LS THEN l[p] ELSE r[p] ]
l | r ==
    join(l, r, DOMAIN l, DOMAIN r)

l / r ==
    [x \in (DOMAIN l) \ r |-> l[x]]
--------------------------------------------------------

\* https://github.com/tlaplus/CommunityModules/blob/beb1b41f78c4e850848e1bc3e89be722a98cbb06/modules/Functions.tla#L42-L49
(***************************************************************************)
(* A function is injective iff it maps each element in its domain to a     *)
(* distinct element.                                                       *)
(*                                                                         *)
(* This definition is overridden by TLC in the Java class SequencesExt.    *)
(* The operator is overridden by the Java method with the same name.       *)
(***************************************************************************)
IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b

\* https://github.com/tlaplus/CommunityModules/blob/beb1b41f78c4e850848e1bc3e89be722a98cbb06/modules/SequencesExt.tla#L22-L27
SetToSeq(S) ==
  (**************************************************************************)
  (* Convert a set to some sequence that contains all the elements of the   *)
  (* set exactly once, and contains no other elements.                      *)
  (**************************************************************************)
  CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

\* https://github.com/tlaplus/CommunityModules/blob/beb1b41f78c4e850848e1bc3e89be722a98cbb06/modules/SequencesExt.tla#L29-L38
SetToSeqs(S) ==
  (**************************************************************************)
  (* Convert the set S to a set containing all sequences containing the     *)
  (* elements of S exactly once and no other elements.                      *)
  (* Example:                                                               *)
  (*    SetToSeqs({}), {<<>>}                                               *)
  (*    SetToSeqs({"t","l"}) = {<<"t","l">>, <<"l","t">>}                   *)
  (**************************************************************************)
  LET D == 1..Cardinality(S)
  IN { f \in [D -> S] : \A i,j \in D : i # j => f[i] # f[j] }

\* https://github.com/tlaplus/CommunityModules/blob/beb1b41f78c4e850848e1bc3e89be722a98cbb06/modules/SequencesExt.tla#L49-L58
SetToAllKPermutations(S) ==
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

\* https://github.com/tlaplus/CommunityModules/blob/beb1b41f78c4e850848e1bc3e89be722a98cbb06/modules/Folds.tla#L3-L27
MapThenFoldSet(op(_,_), base, f(_), choose(_), S) ==
(******************************************************************************)
(* Starting from base, apply op to f(x), for all x \in S, by choosing the set *)
(* elements with `choose`. If there are multiple ways for choosing an element,*)
(* op should be associative and commutative. Otherwise, the result may depend *)
(* on the concrete implementation of `choose`.                                *)
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

--------------------------------------------------------

LOCAL Choose(S) == CHOOSE x \in S: TRUE
LOCAL RetrieveOriginator(G, P) == <<Choose(G), Choose(P)>>

CreateMessages(nmessage, G, P) ==
    {[id |-> m, d |-> G, o |-> RetrieveOriginator(G, P)]: m \in 1 .. nmessage}

CreatePossibleMessages(S) ==
    LET M == SetToAllKPermutations(S)
    IN MapThenFoldSet(LAMBDA x, y: <<x>> \o y, <<>>, LAMBDA x : x, Choose, {m \in M: Len(m) = Cardinality(S)})

MessagesToTuple(F) ==
    [x \in DOMAIN F |-> <<F[x], 0, 0>>]

--------------------------------------------------------

AppendEnumerating(base, E) ==
    LET f == SetToSeq(E) IN {<<base + i, f[i]>>: i \in DOMAIN f}

--------------------------------------------------------

Max(S) == CHOOSE x \in S: \A y \in S: x >= y

========================================================
