Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint count_equal_to_k_spec (l : list Z) (k : Z) : Z :=
  match l with
  | nil => 0
  | x :: xs =>
      (if Z.eq_dec x k then 1 else 0) + count_equal_to_k_spec xs k
  end.
