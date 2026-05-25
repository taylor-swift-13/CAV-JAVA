Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint array_longest_nonnegative_run_acc
         (current best : Z) (l : list Z) : Z :=
  match l with
  | nil => best
  | x :: xs =>
      if Z_le_dec 0 x then
        let current' := current + 1 in
        array_longest_nonnegative_run_acc current' (Z.max best current') xs
      else
        array_longest_nonnegative_run_acc 0 best xs
  end.

Definition array_longest_nonnegative_run_spec (l : list Z) : Z :=
  array_longest_nonnegative_run_acc 0 0 l.
