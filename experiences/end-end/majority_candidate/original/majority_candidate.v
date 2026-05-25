Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint majority_candidate_acc (candidate count : Z) (l : list Z) : Z :=
  match l with
  | nil => candidate
  | x :: xs =>
      if Z.eq_dec count 0 then
        majority_candidate_acc x 1 xs
      else if Z.eq_dec x candidate then
        majority_candidate_acc candidate (count + 1) xs
      else
        majority_candidate_acc candidate (count - 1) xs
  end.

Definition majority_candidate_spec (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs => majority_candidate_acc x 1 xs
  end.
