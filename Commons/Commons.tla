-------------------- MODULE Commons --------------------

LOCAL IsEven(x) == x % 2 = 0

ByIdConflict(m, m) == IsEven(m.id) = IsEven(n.id)

AlwaysConflict(m, n) == TRUE

NeverConflict(m, n) == FALSE

--------------------------------------------------------

StrictlySmaller(m, n) ==
    /\ \/ m.ts < n.ts
       \/ m.id < n.id /\ m.ts = n.ts

--------------------------------------------------------

Max(S) == CHOOSE x \in S: \A y \in S: x >= y

========================================================
