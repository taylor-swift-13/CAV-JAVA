Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint remove_duplicates_sorted_cons (prev : Z) (xs : list Z) : list Z :=
  match xs with
  | nil => nil
  | x :: xs' =>
      if Z.eq_dec x prev
      then remove_duplicates_sorted_cons prev xs'
      else x :: remove_duplicates_sorted_cons x xs'
  end.

Definition remove_duplicates_sorted_spec (l : list Z) : list Z :=
  match l with
  | nil => nil
  | x :: xs => x :: remove_duplicates_sorted_cons x xs
  end.
