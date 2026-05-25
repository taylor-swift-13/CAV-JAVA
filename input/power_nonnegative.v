Require Import ZArith.

Open Scope Z_scope.

Fixpoint power_nonnegative_nat (base : Z) (exp : nat) : Z :=
  match exp with
  | O => 1
  | S k => power_nonnegative_nat base k * base
  end.

Definition power_nonnegative_z (base exp : Z) : Z :=
  power_nonnegative_nat base (Z.to_nat exp).
