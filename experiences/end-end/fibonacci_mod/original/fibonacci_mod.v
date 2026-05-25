Require Import ZArith.

Open Scope Z_scope.

Fixpoint fib_mod_pair (n : nat) (m : Z) : Z * Z :=
  match n with
  | O => (0, Z.rem 1 m)
  | S k =>
      let p := fib_mod_pair k m in
      (snd p, Z.rem (fst p + snd p) m)
  end.

Definition fib_mod_nat (n : nat) (m : Z) : Z :=
  fst (fib_mod_pair n m).

Definition fib_mod_z (n m : Z) : Z :=
  fib_mod_nat (Z.to_nat n) m.
