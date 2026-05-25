Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint array_count_even_spec (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs =>
      (if Z.eq_dec (Z.rem x 2) 0 then 1 else 0) + array_count_even_spec xs
  end.
