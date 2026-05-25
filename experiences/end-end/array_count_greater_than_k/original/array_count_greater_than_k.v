Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint array_count_greater_than_k_spec (l : list Z) (k : Z) : Z :=
  match l with
  | nil => 0
  | x :: xs =>
      (if Z_gt_dec x k then 1 else 0) + array_count_greater_than_k_spec xs k
  end.
