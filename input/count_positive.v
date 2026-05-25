Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint count_positive_spec (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs =>
      (if Z_gt_dec x 0 then 1 else 0) + count_positive_spec xs
  end.
