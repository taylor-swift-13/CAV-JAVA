## 2026-04-23 02:06 - Manual obligations after fresh symexec

Fresh symbolic execution succeeded on the active annotated file `annotated/verify_20260423_020633_string_ends_with_char.c` and generated `coq/generated/string_ends_with_char_goal.v`, `string_ends_with_char_proof_auto.v`, `string_ends_with_char_proof_manual.v`, and `string_ends_with_char_goal_check.v`.

The generated manual file contains seven admitted obligations:

```coq
Lemma proof_of_string_ends_with_char_safety_wit_6 : string_ends_with_char_safety_wit_6.
Lemma proof_of_string_ends_with_char_safety_wit_9 : string_ends_with_char_safety_wit_9.
Lemma proof_of_string_ends_with_char_entail_wit_1 : string_ends_with_char_entail_wit_1.
Lemma proof_of_string_ends_with_char_entail_wit_2 : string_ends_with_char_entail_wit_2.
Lemma proof_of_string_ends_with_char_entail_wit_3 : string_ends_with_char_entail_wit_3.
Lemma proof_of_string_ends_with_char_return_wit_1 : string_ends_with_char_return_wit_1.
Lemma proof_of_string_ends_with_char_return_wit_3 : string_ends_with_char_return_wit_3.
```

The current VC bodies in `coq/generated/string_ends_with_char_goal.v` are proof-level obligations rather than annotation gaps:

- `safety_wit_6` and `safety_wit_9` require integer bounds for `i + 1`; the invariant has `0 <= i`, `i < n`, and `n < INT_MAX` is not explicitly in the invariant, but the local `Int` store for `i` and the generated context should let `entailer!`/`lia` solve these bounds.
- `entail_wit_1` initializes the loop invariant after the `s[0] != 0` branch. The key pure fact is that `Znth 0 (l ++ [0]) 0 <> 0` rules out `n = 0` because `Zlength l = n` and the appended terminator is exactly at index `n`.
- `entail_wit_2` preserves the invariant after `i++`. From `0 <= i`, `i < n`, and `Znth (i + 1) (l ++ [0]) 0 <> 0`, the new index must satisfy `i + 1 < n`; if `i + 1 = n`, the read would be the appended zero terminator.
- `entail_wit_3` proves the loop-exit assertion. From `Znth (i + 1) (l ++ [0]) 0 = 0`, the prefix nonzero contract, and `0 <= i < n`, the zero index must be `n`, so `i = n - 1`.
- `return_wit_1` is the empty-string branch and should choose the postcondition case `n = 0`.
- `return_wit_3` is the final false comparison branch. With `i = n - 1`, the premise `Znth i (l ++ [0]) 0 <> c` rewrites to `Znth (n - 1) l 0 <> c`, so it should choose the nonmatching nonempty postcondition case.

Planned proof edit: replace all seven stubs in `string_ends_with_char_proof_manual.v` with conservative local helper lemmas:

```coq
app_zero_at_length
app_zero_nonzero_implies_lt
app_zero_eq_zero_implies_length
app_zero_last_value
```

The witness proofs will use `pre_process`, `entailer!`, `Left`/`Right` for assertion-level disjunctions, and these helper lemmas to keep the main obligations short. No `Axiom` or `Admitted` will be added.

## 2026-04-23 02:12 - Regenerated obligations after invariant strengthening

After adding `n < INT_MAX` to the invariant and post-loop assertion, I cleared `coq/generated/*` and reran `symexec`. The fresh manual proof file now contains only five obligations:

```coq
proof_of_string_ends_with_char_entail_wit_1
proof_of_string_ends_with_char_entail_wit_2
proof_of_string_ends_with_char_entail_wit_3
proof_of_string_ends_with_char_return_wit_1
proof_of_string_ends_with_char_return_wit_3
```

The two previous manual safety witnesses moved to `proof_auto.v`, and the current manual goals are exactly the list/terminator obligations described above. I will reapply the local helper lemmas to the regenerated `proof_manual.v`, with hypothesis numbers adjusted to the new VC shape: return false branch now has `H` for `Znth i (l ++ [0]) 0 <> c_pre`, `H0` for `0 < n`, `H2` for `i = n - 1`, and `H3` for `Zlength l = n`.

## 2026-04-23 02:13 - `return_wit_3` disjunction shape

Compiling `proof_manual.v` after the regenerated proof edit solved `entail_wit_1`, `entail_wit_2`, `entail_wit_3`, and `return_wit_1`, but failed at:

```text
File ".../string_ends_with_char_proof_manual.v", line 145, characters 0-4:
Error:
 (in proof proof_of_string_ends_with_char_return_wit_3): Attempt to save an incomplete proof
```

`coqtop` showed that after `pre_process`, the postcondition disjunction is parsed as `(case_nonmatch || case_match) || case_empty`. The tactic `Left; entailer!` only chose the left side of the outer disjunction and left the remaining inner `case_nonmatch || case_match` goal:

```coq
CharArray.full ... |--
  [|0 < n|] && [|Znth (n - 1) l 0 <> c_pre|] && ...
  || [|0 < n|] && [|Znth (n - 1) l 0 = c_pre|] && ...
```

The correct assertion-level branch selection for the nonmatching case is therefore `Left. Left. entailer!.` after establishing:

```coq
Hlast : Znth (n - 1) l 0 <> c_pre
```
