Require Import ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.

Open Scope Z_scope.

Definition insertion_sort_spec (l lr : list Z) : Prop :=
  StronglySorted Z.le lr /\ Permutation l lr.
