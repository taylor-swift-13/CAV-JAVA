Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint string_count_words_simple_go (in_word : bool) (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs =>
      if Z.eq_dec x 32 then
        string_count_words_simple_go false xs
      else
        if in_word then
          string_count_words_simple_go true xs
        else
          1 + string_count_words_simple_go true xs
  end.

Definition string_count_words_simple_spec (l : list Z) : Z :=
  string_count_words_simple_go false l.
