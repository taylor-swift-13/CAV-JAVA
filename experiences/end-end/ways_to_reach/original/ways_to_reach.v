Require Import ZArith.

Open Scope Z_scope.

Fixpoint ways_to_reach_pair (n : nat) : Z * Z :=
  match n with
  | O => (1, 1)
  | S k =>
      let p := ways_to_reach_pair k in
      (snd p, fst p + snd p)
  end.

Definition ways_to_reach_nat (n : nat) : Z :=
  fst (ways_to_reach_pair n).

Definition ways_to_reach_z (n : Z) : Z :=
  ways_to_reach_nat (Z.to_nat n).
