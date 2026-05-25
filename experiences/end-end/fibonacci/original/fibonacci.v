Require Import ZArith.

Open Scope Z_scope.

Fixpoint fib_pair (n : nat) : Z * Z :=
  match n with
  | O => (0, 1)
  | S k =>
      let p := fib_pair k in
      (snd p, fst p + snd p)
  end.

Definition fib_nat (n : nat) : Z :=
  fst (fib_pair n).

Definition fib_z (n : Z) : Z :=
  fib_nat (Z.to_nat n).
