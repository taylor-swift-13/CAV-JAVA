Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint string_count_not_char_spec (l : list Z) (c : Z) : Z :=
  match l with
  | nil => 0
  | x :: xs =>
      (if Z.eq_dec x c then 0 else 1) + string_count_not_char_spec xs c
  end.
