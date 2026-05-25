Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint array_sum_even_indices_spec (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: nil => x
  | x :: _ :: xs => x + array_sum_even_indices_spec xs
  end.
