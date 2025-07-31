From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition square (a b:Z) := a^2 = b.
Definition pre_sqrt (x n:Z) := x^2 <= n.
Definition sqrt (x n:Z) := x^2 <= n < (x+1)^2.
