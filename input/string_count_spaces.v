Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint string_count_spaces_spec (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs =>
      (if Z.eq_dec x 32 then 1 else 0) + string_count_spaces_spec xs
  end.
