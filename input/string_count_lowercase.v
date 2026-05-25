Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint string_count_lowercase_spec (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs =>
      (if Z_le_dec 97 x then
         if Z_le_dec x 122 then 1 else 0
       else 0) + string_count_lowercase_spec xs
  end.
