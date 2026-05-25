Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint string_remove_char_to_output_spec (l : list Z) (c : Z) : list Z :=
  match l with
  | nil => nil
  | x :: xs =>
      if Z.eq_dec x c then
        string_remove_char_to_output_spec xs c
      else
        x :: string_remove_char_to_output_spec xs c
  end.
