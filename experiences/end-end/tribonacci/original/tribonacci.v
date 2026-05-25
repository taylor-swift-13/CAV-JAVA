Require Import ZArith.

Open Scope Z_scope.

Fixpoint tribonacci_state (n : nat) : Z * (Z * Z) :=
  match n with
  | O => (0, (1, 1))
  | S k =>
      let s := tribonacci_state k in
      let a := fst s in
      let b := fst (snd s) in
      let c := snd (snd s) in
      (b, (c, a + b + c))
  end.

Definition tribonacci_nat (n : nat) : Z :=
  fst (tribonacci_state n).

Definition tribonacci_z (n : Z) : Z :=
  tribonacci_nat (Z.to_nat n).
