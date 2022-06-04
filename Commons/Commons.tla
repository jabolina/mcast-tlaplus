-------------------- MODULE Commons --------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE TLC

LOCAL IsEven(x) == x % 2 = 0

IdConflict(m, n) == IsEven(m.id) = IsEven(n.id)

AlwaysConflict(m, n) == TRUE

NeverConflict(m, n) == FALSE

--------------------------------------------------------

CreateMessage(m, k) == [ id |-> m.id, d |-> m.d, ts |-> k ]

StrictlySmaller(m, n) ==
    /\ \/ m.ts < n.ts
       \/ m.id < n.id /\ m.ts = n.ts

LOCAL join(l, r, LS, RS) ==
    [p \in LS \union RS |-> IF p \in LS THEN l[p] ELSE r[p] ]
l | r ==
    join(l, r, DOMAIN l, DOMAIN r)
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

AppendEnumerating(base, E) ==
    LET f == SetToSeq(E) IN {<<base + i, f[i]>>: i \in DOMAIN f}

--------------------------------------------------------

Max(S) == CHOOSE x \in S: \A y \in S: x >= y

========================================================
