# Proof Reasoning

## Round 1

After the successful `symexec` run, `coq/generated/array_count_increasing_steps_proof_manual.v` contains five unfinished manual witnesses:

```coq
Lemma proof_of_array_count_increasing_steps_safety_wit_7 : array_count_increasing_steps_safety_wit_7.
Proof. Admitted.

Lemma proof_of_array_count_increasing_steps_entail_wit_1 : array_count_increasing_steps_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_count_increasing_steps_entail_wit_2_1 : array_count_increasing_steps_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_count_increasing_steps_entail_wit_2_2 : array_count_increasing_steps_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_array_count_increasing_steps_return_wit_1 : array_count_increasing_steps_return_wit_1.
Proof. Admitted.
```

The current invariant exposed in `goal.v` is the intended one:

```coq
0 <= i
i <= n_pre
0 < n_pre -> i + 1 <= n_pre
cnt = array_count_increasing_steps_spec (sublist 0 (i + 1) l)
```

The proof obligations are pure list/arithmetic obligations after separation-logic cleanup:

- `safety_wit_7` must show `cnt + 1` remains in signed range in the increment branch. The planned proof recovers `n_pre <= INT_MAX` from `store_int_range (&("n")) n_pre` and bounds `cnt` by the number of processed adjacent pairs in the current prefix.
- `entail_wit_1` is loop initialization. It reduces to showing the spec of an empty or one-element prefix is `0`.
- `entail_wit_2_1` and `entail_wit_2_2` are the branch and non-branch loop-step witnesses. Both need a helper lemma stating that extending the processed prefix from `i + 1` to `i + 2` adds exactly the comparison result for `Znth i l 0` and `Znth (i + 1) l 0`.
- `return_wit_1` needs to collapse `sublist 0 (i + 1) l` to `l` using the negated guard, invariant bounds, and `Zlength l = n_pre`.

I will add local helper lemmas directly above the witness proofs and then compile. The helper set is intentionally small:

```coq
sublist_prefix_full
array_count_increasing_steps_spec_short
array_count_increasing_steps_spec_app_single
array_count_increasing_steps_spec_nonempty_bounds
array_count_increasing_steps_spec_step
```
