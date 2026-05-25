Require Import ZArith.

Open Scope Z_scope.

Definition lcm_simple_value (a b : Z) : Z :=
  Z.lcm a b.

Definition lcm_simple_spec (a b r : Z) : Prop :=
  r = lcm_simple_value a b.
