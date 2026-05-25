Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint array_count_transitions_from (prev : Z) (xs : list Z) : Z :=
  match xs with
  | nil => 0
  | x :: xs' =>
      (if Z.eq_dec x prev then 0 else 1) +
      array_count_transitions_from x xs'
  end.

Definition array_count_transitions_spec (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs => array_count_transitions_from x xs
  end.
