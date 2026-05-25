# Verify Issues

## 1. Annotated copy initially lacked loop invariant and exit assertion

- Phenomenon: `annotated/verify_20260423_012416_string_count_vowels.c` was identical to `input/string_count_vowels.c`; the `while (1)` scan had no `Inv`, and the post-loop return had no assertion connecting the terminating read to `i == n`.
- Trigger: beginning verify after confirming the input contract was present and the workspace fingerprint was still an empty placeholder.
- Location: active annotated C around the `while (1)` loop.
- Relevant unannotated fragment:

```c
while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] == 97 || s[i] == 101 || s[i] == 105 ||
        s[i] == 111 || s[i] == 117) {
        cnt++;
    }
    i++;
}
return cnt;
```

- Fix action: added a prefix-count invariant with `exists l1 l2`, `l == app(l1, l2)`, `Zlength(l1) == i`, `cnt == string_count_vowels_spec(l1)`, preserved nonzero-prefix fact, and preserved `CharArray::full`. Added a post-loop assertion fixing `i == n`, `cnt == string_count_vowels_spec(l)`, and the same full string resource.
- Result: fresh `symexec` on the updated annotated file completed successfully and generated `string_count_vowels_goal.v`, `string_count_vowels_proof_auto.v`, `string_count_vowels_proof_manual.v`, and `string_count_vowels_goal_check.v`.

## 2. Manual proof needed five vowel branches plus one non-vowel branch

- Phenomenon: fresh `coq/generated/string_count_vowels_proof_manual.v` contained eight `Admitted.` placeholders:

```coq
proof_of_string_count_vowels_entail_wit_1
proof_of_string_count_vowels_entail_wit_2_1
proof_of_string_count_vowels_entail_wit_2_2
proof_of_string_count_vowels_entail_wit_2_3
proof_of_string_count_vowels_entail_wit_2_4
proof_of_string_count_vowels_entail_wit_2_5
proof_of_string_count_vowels_entail_wit_2_6
proof_of_string_count_vowels_entail_wit_3
```

- Trigger: `symexec` correctly split the nested vowel test into five increment-preservation VCs for `117`, `105`, `97`, `101`, and `111`, one non-vowel preservation VC, and one loop-exit VC.
- Location: `output/verify_20260423_012416_string_count_vowels/coq/generated/string_count_vowels_proof_manual.v`.
- Fix action: added local lemma `string_count_vowels_spec_app_single`, proving the recursive spec over `l ++ [x]`. Each preservation proof extracts the current suffix head `x` from `Znth i ((l1_2 ++ x :: xs) ++ 0 :: nil) 0`, rewrites the append-single lemma, chooses `l1_2 ++ x :: nil` and `xs` as existential witnesses, and closes with `entailer!`. The exit proof derives `i = n` from the terminating zero read and the nonzero-prefix precondition, then proves `l1_2 = l`.
- Result: `string_count_vowels_proof_manual.v` compiles, contains no `Admitted.`, and contains no new top-level `Axiom`.

## 3. Reusable Ltac helper initially matched the wrong proof-context names

- Phenomenon: several compile attempts failed in `proof_manual.v` before the final proof shape stabilized. Representative errors:

```text
line 79: Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as'
line 59: Error: The reference l was not found in the current environment.
line 136/126: Error: No matching clauses for match.
line 146: Attempt to save an incomplete proof
```

- Trigger: the first helper tactic tried to destruct `l2_2 as [| x xs]` inside a Ltac definition, then referred directly to theorem-local variables such as `l`, `n`, `i`, and `l1_2`. Later, a generic `finish_vowel_step` matched the wrong `Z` variable (`cnt` instead of the suffix head `x`), leaving goals such as:

```coq
cnt + 1 = string_count_vowels_spec (l1_2 ++ cnt :: nil)
l1_2 ++ x :: xs = (l1_2 ++ cnt :: nil) ++ xs
```

- Location: `output/verify_20260423_012416_string_count_vowels/coq/generated/string_count_vowels_proof_manual.v`, helper tactics and `proof_of_string_count_vowels_entail_wit_2_1`.
- Fix action: rewrote the helper to bind theorem-local names through `match goal` where needed, avoided overbroad variable selection for the final existential witnesses, and inlined the final `Happ`, `Hlen_prefix`, `Exists`, and `entailer!` sequence in each branch so the proof uses the actual suffix head `x`.
- Result: final compile replay succeeded through `string_count_vowels_goal_check.v`.

## 4. Final cleanup required removing Coq build intermediates

- Phenomenon: successful Coq compilation produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Trigger: normal `coqc` replay of `original/string_count_vowels.v`, `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`.
- Fix action: deleted all non-`.v` files under `output/verify_20260423_012416_string_count_vowels/coq`.
- Result: `find output/verify_20260423_012416_string_count_vowels/coq -type f ! -name '*.v'` returns no files. `input/` had no non-`.c`/non-`.v` intermediate files to remove.
