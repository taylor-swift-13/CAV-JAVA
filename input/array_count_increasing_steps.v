Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint array_count_increasing_steps_from (prev : Z) (xs : list Z) : Z :=
  match xs with
  | nil => 0
  | x :: xs' =>
      (if Z_lt_dec prev x then 1 else 0) +
      array_count_increasing_steps_from x xs'
  end.

Definition array_count_increasing_steps_spec (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs => array_count_increasing_steps_from x xs
  end.
