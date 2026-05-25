Require Import ZArith.

Open Scope Z_scope.

Definition is_prime_z (n : Z) : Prop :=
  1 < n /\ forall d, 2 <= d < n -> Z.rem n d <> 0.

Definition is_prime_simple_spec (n r : Z) : Prop :=
  (r = 1 /\ is_prime_z n) \/
  (r = 0 /\ ~ is_prime_z n).
