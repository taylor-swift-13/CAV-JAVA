Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint merge_sorted_arrays_spec (a b : list Z) {struct a} : list Z :=
  match a with
  | nil => b
  | x :: xs =>
      let fix merge_with_b (b : list Z) {struct b} : list Z :=
          match b with
          | nil => a
          | y :: ys =>
              if Z.leb x y
              then x :: merge_sorted_arrays_spec xs b
              else y :: merge_with_b ys
          end in
      merge_with_b b
  end.
