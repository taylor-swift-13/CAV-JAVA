Require Import ZArith.

Open Scope Z_scope.

Definition count_digits_spec (n r : Z) : Prop :=
  (n = 0 /\ r = 1) \/
  (0 < n /\ 1 <= r /\ 10 ^ (r - 1) <= n < 10 ^ r).
