# Proof Reasoning

## Manual return witnesses after first symexec

Current generated file:

```text
output/verify_20260423_045417_string_trim_last_char/coq/generated/string_trim_last_char_proof_manual.v
```

`symexec` succeeded and generated two manual witnesses:

```coq
Lemma proof_of_string_trim_last_char_return_wit_1 : string_trim_last_char_return_wit_1.
Proof. Admitted.

Lemma proof_of_string_trim_last_char_return_wit_2 : string_trim_last_char_return_wit_2.
Proof. Admitted.
```

The first witness is the `n_pre <= 0` return branch. Together with the function precondition `0 <= n_pre`, the branch gives `n_pre = 0`. The postcondition is a QCP assertion-level disjunction; the correct proof must use `Left`, not Coq's lowercase `left`, then use `Exists (l ++ 0 :: nil)` for the existential `lr`. The remaining obligations are the list length `Zlength (l ++ 0 :: nil) = n_pre + 1`, the pure equality `n_pre = 0`, the witness equality, and the unchanged `CharArray.full` resource.

The second witness is the `n_pre > 0` branch after the store:

```coq
CharArray.full s_pre (n_pre + 1)
  (replace_Znth (n_pre - 1) 0 (l ++ 0 :: nil))
```

The correct postcondition branch is the right disjunct with witness
`replace_Znth (n_pre - 1) 0 (l ++ 0 :: nil)`. The pure side conditions need standard local helper lemmas:

```coq
Zlength (replace_Znth i x xs) = Zlength xs
Znth i (replace_Znth i x xs) d = x
Znth k (replace_Znth i x xs) d = Znth k xs d when k <> i
```

The prefix condition uses the different-index lemma because every `i < n_pre - 1` differs from `n_pre - 1`, then `app_Znth1` rewrites reads from `l ++ 0 :: nil` back to `l`. The final terminator condition uses the different-index lemma at index `n_pre`, then `app_Znth2` and `Znth0_cons` to read the appended `0`.

## First compile failure in return_wit_2

The first compile replay stopped at:

```text
File ".../string_trim_last_char_proof_manual.v", line 104, characters 4-54:
Error: Found no subterm matching
"Zlength (replace_Znth ?M6125 ?M6126 ?M6127)" in the current goal.
```

I checked the proof state with `coqtop` after:

```coq
pre_process.
Right.
Exists (replace_Znth (n_pre - 1) 0 (l ++ 0 :: nil)).
entailer!.
Show.
```

`entailer!` generated the pure obligations in this order:

```coq
1. Znth n_pre (replace_Znth (n_pre - 1) 0 (l ++ 0 :: nil)) 0 = 0
2. Znth (n_pre - 1) (replace_Znth (n_pre - 1) 0 (l ++ 0 :: nil)) 0 = 0
3. forall i, 0 <= i < n_pre - 1 -> ...
4. Zlength (replace_Znth (n_pre - 1) 0 (l ++ 0 :: nil)) = n_pre + 1
```

The script had assumed the length obligation came first. The fix is only to reorder the bullets: prove the final terminator read first, then the replaced last character, then the prefix preservation, then the length fact.
