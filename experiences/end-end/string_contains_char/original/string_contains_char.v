Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint string_contains_char_spec (l : list Z) (c : Z) : Z :=
  match l with
  | nil => 0
  | x :: xs =>
      if Z.eq_dec x c then 1 else string_contains_char_spec xs c
  end.
