-------------------- MODULE Commons --------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets

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

Max(S) == CHOOSE x \in S: \A y \in S: x >= y

========================================================
