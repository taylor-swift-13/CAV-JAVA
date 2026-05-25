Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Definition max_subarray_sum_step (cur x : Z) : Z :=
  Z.max x (cur + x).

Fixpoint max_subarray_sum_acc (cur best : Z) (l : list Z) : Z :=
  match l with
  | nil => best
  | x :: xs =>
      let cur' := max_subarray_sum_step cur x in
      max_subarray_sum_acc cur' (Z.max best cur') xs
  end.

Definition max_subarray_sum_spec (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs => max_subarray_sum_acc x x xs
  end.
