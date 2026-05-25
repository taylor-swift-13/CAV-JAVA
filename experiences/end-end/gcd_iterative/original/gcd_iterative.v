Require Import ZArith.

Open Scope Z_scope.

Definition gcd_iterative_spec (a b r : Z) : Prop :=
  r = Z.gcd a b.
