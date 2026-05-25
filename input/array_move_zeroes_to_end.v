Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint array_move_zeroes_to_end_nonzero (l : list Z) : list Z :=
  match l with
  | nil => nil
  | x :: xs =>
      if Z.eq_dec x 0 then
        array_move_zeroes_to_end_nonzero xs
      else
        x :: array_move_zeroes_to_end_nonzero xs
  end.

Fixpoint array_move_zeroes_to_end_zeros (l : list Z) : list Z :=
  match l with
  | nil => nil
  | x :: xs =>
      if Z.eq_dec x 0 then
        0 :: array_move_zeroes_to_end_zeros xs
      else
        array_move_zeroes_to_end_zeros xs
  end.

Definition array_move_zeroes_to_end_spec (l : list Z) : list Z :=
  array_move_zeroes_to_end_nonzero l ++ array_move_zeroes_to_end_zeros l.
