Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint array_remove_value_to_output_spec (l : list Z) (k : Z) : list Z :=
  match l with
  | nil => nil
  | x :: xs =>
      if Z.eq_dec x k then
        array_remove_value_to_output_spec xs k
      else
        x :: array_remove_value_to_output_spec xs k
  end.
