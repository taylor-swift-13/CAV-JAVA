Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint array_intersection_count_sorted_spec (a b : list Z) {struct a} : Z :=
  match a with
  | nil => 0
  | x :: xs =>
      let fix count_with_b (b : list Z) {struct b} : Z :=
          match b with
          | nil => 0
          | y :: ys =>
              if Z.eq_dec x y
              then 1 + array_intersection_count_sorted_spec xs ys
              else if Z.ltb x y
                   then array_intersection_count_sorted_spec xs b
                   else count_with_b ys
          end in
      count_with_b b
  end.
