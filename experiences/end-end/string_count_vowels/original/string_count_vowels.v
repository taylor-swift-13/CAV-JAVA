Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint string_count_vowels_spec (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs =>
      (if Z.eq_dec x 97 then 1
       else if Z.eq_dec x 101 then 1
       else if Z.eq_dec x 105 then 1
       else if Z.eq_dec x 111 then 1
       else if Z.eq_dec x 117 then 1
       else 0) + string_count_vowels_spec xs
  end.
