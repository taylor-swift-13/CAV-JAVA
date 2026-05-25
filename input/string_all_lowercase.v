Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint string_all_lowercase_spec (l : list Z) : Z :=
  match l with
  | nil => 1
  | x :: xs =>
      if Z_lt_dec x 97 then 0
      else if Z_gt_dec x 122 then 0
      else string_all_lowercase_spec xs
  end.
