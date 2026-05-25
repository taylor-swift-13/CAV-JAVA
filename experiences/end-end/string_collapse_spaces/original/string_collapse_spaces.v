Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint string_collapse_spaces_go (in_space : bool) (l : list Z) : list Z :=
  match l with
  | nil => nil
  | x :: xs =>
      if Z.eq_dec x 32 then
        if in_space then
          string_collapse_spaces_go true xs
        else
          32 :: string_collapse_spaces_go true xs
      else
        x :: string_collapse_spaces_go false xs
  end.

Definition string_collapse_spaces_spec (l : list Z) : list Z :=
  string_collapse_spaces_go false l.
