Require Import ZArith.

Open Scope Z_scope.

Fixpoint climb_stairs_nat (n : nat) : Z :=
  match n with
  | O => 1
  | S O => 1
  | S (S k) => climb_stairs_nat (S k) + climb_stairs_nat k
  end.

Definition climb_stairs_z (n : Z) : Z :=
  climb_stairs_nat (Z.to_nat n).
