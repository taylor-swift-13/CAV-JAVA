Require Import ZArith.

Open Scope Z_scope.

Fixpoint digit_sum_fuel (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S k =>
      if Z.leb n 0 then
        0
      else
        Z.rem n 10 + digit_sum_fuel (Z.div n 10) k
  end.

Definition digit_sum_z (n : Z) : Z :=
  digit_sum_fuel n (Z.to_nat n).
