From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Set Nested Proofs Allowed.

Definition square (a b:Z) := a^2 = b.
Definition pre_sqrt (x n:Z) := x^2 <= n.
Definition sqrt (x n:Z) := x^2 <= n < (x+1)^2.
