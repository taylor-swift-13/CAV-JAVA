Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint longest_increasing_run_acc
         (prev current best : Z) (xs : list Z) : Z :=
  match xs with
  | nil => best
  | x :: xs' =>
      if Z_lt_dec prev x then
        let current' := current + 1 in
        longest_increasing_run_acc x current' (Z.max best current') xs'
      else
        longest_increasing_run_acc x 1 best xs'
  end.

Definition longest_increasing_run_spec (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs => longest_increasing_run_acc x 1 1 xs
  end.
