Require Import ZArith.

Open Scope Z_scope.

Fixpoint reverse_digits_acc_fuel (n acc : Z) (fuel : nat) : Z :=
  match fuel with
  | O => acc
  | S k =>
      if Z.leb n 0 then
        acc
      else
        reverse_digits_acc_fuel (Z.div n 10) (acc * 10 + Z.rem n 10) k
  end.

Definition reverse_digits_z (n : Z) : Z :=
  reverse_digits_acc_fuel n 0 (Z.to_nat n).
