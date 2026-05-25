## Proof iteration 1

Fresh `symexec` succeeded for `annotated/verify_20260423_041041_string_reverse_copy.c` and generated three manual obligations in `coq/generated/string_reverse_copy_proof_manual.v`:

```coq
Lemma proof_of_string_reverse_copy_entail_wit_1 : string_reverse_copy_entail_wit_1.
Proof. Admitted.

Lemma proof_of_string_reverse_copy_entail_wit_2 : string_reverse_copy_entail_wit_2.
Proof. Admitted.

Lemma proof_of_string_reverse_copy_return_wit_1 : string_reverse_copy_return_wit_1.
Proof. Admitted.
```

The generated goals are pure list/heap-shape obligations after the automatic strategy has handled C execution:

- `entail_wit_1`: initialize the loop invariant. The destination must be rewritten from `d` to `app (rev (sublist (n_pre - 0) n_pre l)) (sublist 0 (n_pre + 1) d)`. With `Zlength d = n_pre + 1`, this is `[] ++ d`.
- `entail_wit_2`: preserve the invariant after writing `dst[i] = src[n - 1 - i]`. The key equality is:

```coq
replace_Znth i
  (Znth ((n_pre - 1) - i) (l ++ 0 :: nil) 0)
  (rev (sublist (n_pre - i) n_pre l) ++ sublist i (n_pre + 1) d)
=
rev (sublist (n_pre - (i + 1)) n_pre l) ++ sublist (i + 1) (n_pre + 1) d
```

This is the same proof pattern as `examples/reverse_copy/coq/generated/reverse_copy_proof_manual.v`, except that the destination suffix has upper bound `n + 1` and the source value is read from `l ++ [0]`. Since `0 <= n - 1 - i < n`, `Znth ((n - 1) - i) (l ++ [0]) 0 = Znth ((n - 1) - i) l 0`.

- `return_wit_1`: loop exit has `i >= n_pre` and `i <= n_pre`, so `i = n_pre`. The destination list is `replace_Znth n_pre 0 (rev (sublist 0 n_pre l) ++ sublist n_pre (n_pre + 1) d)`, which must normalize to `rev l ++ [0]`.

I will add local helper lemmas:

```coq
Lemma Zlength_rev_Z : forall (l : list Z), Zlength (rev l) = Zlength l.

Lemma string_reverse_copy_replace_Znth : ...

Lemma string_reverse_copy_final_replace : ...
```

The witness proofs will then be short `pre_process`, list rewrite/helper application, and `entailer!`. No generated goal files or `proof_auto.v` will be edited, and no `Axiom` or `Admitted` will be introduced.

## Proof iteration 2

The first compile replay got through `string_reverse_copy_goal.v` and `string_reverse_copy_proof_auto.v`, then failed in `string_reverse_copy_proof_manual.v`:

```text
File ".../string_reverse_copy_proof_manual.v", line 100, characters 25-28:
Error: Tactic failure: Cannot find witness.
```

The failing helper proof fragment was:

```coq
rewrite (sublist_split n (n + 1) (n + 1) d) by (pose proof (Zlength_correct d); lia).
rewrite sublist_nil by lia.
```

After the split, the intended rewrite is specifically for `sublist (n + 1) (n + 1) d = []`. The unqualified `rewrite sublist_nil by lia` leaves Coq to infer the list and bounds, and that inference failed even though the side condition is just `(n + 1) <= (n + 1)`. I will make the lemma instance explicit:

```coq
rewrite (sublist_nil d (n + 1) (n + 1)) by lia.
```

This is a proof-script robustness issue, not an annotation or VC-shape issue.

## Proof iteration 3

After making the `sublist_nil` instance explicit, the fail-fast compile replay succeeded:

```text
compile_start=2026-04-23 04:15:04 +0800
skip original/string_reverse_copy.v (not present)
compile string_reverse_copy_goal.v
compile string_reverse_copy_proof_auto.v
compile string_reverse_copy_proof_manual.v
compile string_reverse_copy_goal_check.v
compile_end=2026-04-23 04:15:09 +0800
compile_status=0
```

`proof_manual.v` now contains concrete proofs for all three manual witnesses and `rg -n "Admitted\\.|^\\s*Axiom\\b" coq/generated/string_reverse_copy_proof_manual.v` returns no matches. The remaining `Admitted.` lines are only in generated `proof_auto.v`, which belongs to the automatic strategy side and is not edited in the manual proof workflow.
