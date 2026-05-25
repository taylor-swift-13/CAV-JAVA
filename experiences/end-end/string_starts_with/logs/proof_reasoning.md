# Proof Reasoning

## Manual return witnesses after fresh symexec

Fresh `symexec` succeeded for `annotated/verify_20260423_042409_string_starts_with.c` and generated two manual obligations in `coq/generated/string_starts_with_proof_manual.v`:

```coq
Lemma proof_of_string_starts_with_return_wit_1 : string_starts_with_return_wit_1.
Proof. Admitted.

Lemma proof_of_string_starts_with_return_wit_2 : string_starts_with_return_wit_2.
Proof. Admitted.
```

The corresponding `goal.v` definitions show that both witnesses preserve the same `CharArray.full s_pre (n + 1) (l ++ 0 :: nil)` resource and only need to choose the correct disjunct of the postcondition.  In the `return 1` branch the key pure premise is:

```coq
Znth 0 (l ++ 0 :: nil) 0 = c_pre
```

For `0 < n`, `Zlength l = n` allows `rewrite app_Znth1` so the premise becomes `Znth 0 l 0 = c_pre`, matching the positive non-empty postcondition.  For `n = 0`, rewriting through the appended terminator with `app_Znth2` makes the premise simplify to `0 = c_pre`, matching the empty-string `c == 0` postcondition.

In the `return 0` branch the key pure premise is:

```coq
Znth 0 (l ++ 0 :: nil) 0 <> c_pre
```

The same split on `n = 0` proves either `Znth 0 l 0 <> c_pre` for the non-empty case, or `c_pre <> 0` for the empty-string case.  These are pure list/index bridge obligations; the generated VC already carries the heap resource, so no annotation change is needed.

Planned proof shape for each witness:

```coq
unfold <witness>.
pre_process.
destruct (Z.eq_dec n 0).
  (* empty-string terminator case *)
  ...
  entailer!.
  rewrite app_Znth2 in H by lia; simpl in H; lia.
  (* non-empty first-character case *)
  assert (0 < n) by lia.
  ...
  entailer!.
  rewrite <- H; rewrite app_Znth1; lia.
```

The disjunction constructors follow the generated postcondition order: non-empty mismatch, non-empty match, empty mismatch, empty match.  Therefore `return_wit_1` selects the second or fourth disjunct, and `return_wit_2` selects the first or third disjunct.

## First compile failure: disjunction associativity

The first compile replay reached `string_starts_with_proof_manual.v` and failed at line 28:

```text
Error: Found no subterm matching "?e || ?e0" in the current goal.
```

The failing branch was the empty-string `return_wit_1` proof:

```coq
Right.
Right.
Right.
entailer!.
```

This shows the generated four-way postcondition is parsed left-associatively as `(((A || B) || C) || D)`.  A single `Right` selects the fourth disjunct `D`; additional `Right` tactics fail because no disjunction remains.  The corrected navigation is:

```coq
(* A: non-empty mismatch *) Left. Left. Left.
(* B: non-empty match *)    Left. Left. Right.
(* C: empty mismatch *)     Left. Right.
(* D: empty match *)        Right.
```

I will update only the `Left`/`Right` tactic sequence; the pure `Znth` reasoning remains the same.

## Second compile failure: prove pure branch facts before `entailer!`

After fixing the disjunction constructors, the next compile replay failed at line 31:

```text
Error: Tactic failure:  Cannot find witness.
```

The failure occurred in the empty `return_wit_1` branch where the script selected the fourth disjunct and immediately called `entailer!`, leaving the branch fact `c_pre = 0` implicit in the source premise:

```coq
H : Znth 0 (l ++ 0 :: nil) 0 = c_pre
```

The fix is to prove the branch-specific pure facts before choosing the disjunct:

```coq
assert (Hc_zero : c_pre = 0).
{ rewrite app_Znth2 in H by lia. simpl in H. lia. }
Right.
entailer!.
```

The same pattern applies to the other branches: derive `Znth 0 l 0 = c_pre`, `Znth 0 l 0 <> c_pre`, or `c_pre <> 0` first, then select the generated disjunct and run `entailer!`.

The branch fact still needed an explicit normalization step after `app_Znth2`: the rewritten index is `0 - Zlength l`, and Coq does not reduce it syntactically even after `subst n`; it only knows `Zlength l = 0` from the precondition.  The stable sequence is:

```coq
rewrite app_Znth2 in H by lia.
replace (0 - Zlength l) with 0 in H by lia.
change (Znth 0 (0 :: nil) 0) with 0 in H.
```

This exposes `H : 0 = c_pre` or `H : 0 <> c_pre` directly for `lia`/contradiction.
