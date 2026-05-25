## 2026-04-22T02:57:00+08:00 - Manual witnesses after successful symexec

After `symexec` succeeded, `coq/generated/array_copy_positive_proof_manual.v` contained three admitted lemmas:

```coq
Lemma proof_of_array_copy_positive_entail_wit_2_1 : array_copy_positive_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_copy_positive_entail_wit_2_2 : array_copy_positive_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_array_copy_positive_entail_wit_3 : array_copy_positive_entail_wit_3.
Proof. Admitted.
```

The relevant generated goals in `array_copy_positive_goal.v` are:

```coq
array_copy_positive_entail_wit_2_1:
  IntArray.full out_pre n_pre (replace_Znth i (Znth i la 0) lr_2) ** ...
  |-- EX lr, invariant at i + 1

array_copy_positive_entail_wit_2_2:
  IntArray.full out_pre n_pre (replace_Znth i 0 lr_2) ** ...
  |-- EX lr, invariant at i + 1

array_copy_positive_entail_wit_3:
  i >= n_pre, 0 <= i, i <= n_pre, prefix facts at i, ...
  |-- EX lr, loop-exit assertion with i = n_pre
```

These are not annotation failures: the invariant carries the input array unchanged, output heap shape, both processed-prefix implications, and untouched suffix facts. The remaining proof work is pure list/index reasoning around `replace_Znth`, plus the arithmetic fact `i = n_pre` at loop exit.

Plan:

1. Add local helper lemmas for `Zlength (replace_Znth ...)`, same-index `Znth`, and different-index `Znth`, following the stable pattern used by the existing `array_clamp_nonnegative` example.
2. For the positive branch witness, choose `replace_Znth i (Znth i la 0) lr_2` as the next logical output list. Split each quantified fact on whether `k = i`; the `k = i` positive case follows from `Znth_replace_Znth_same`, the nonpositive case is contradictory, and all old-prefix/suffix cases use `Znth_replace_Znth_diff`.
3. For the nonpositive branch witness, choose `replace_Znth i 0 lr_2`; the nonpositive `k = i` case is direct, the positive `k = i` case is contradictory, and old-prefix/suffix facts are preserved by the different-index lemma.
4. For the exit witness, prove `i = n_pre` by `lia`, choose `lr_2`, and let `entailer!` use the existing prefix facts.

## 2026-04-22T02:58:00+08:00 - First compile failure and bullet order correction

The first compile attempt failed in `array_copy_positive_proof_manual.v` at the first bullet of `proof_of_array_copy_positive_entail_wit_2_1`:

```text
File ".../array_copy_positive_proof_manual.v", line 93, characters 4-32:
Error: Found no subterm matching
"Zlength (replace_Znth ?M10553 ?M10554 ?M10555)" in the current goal.
```

I inspected the proof state with `coqtop` after:

```coq
pre_process.
Exists (replace_Znth i (Znth i la 0) lr_2).
entailer!.
entailer!.
Show.
```

The actual remaining subgoal order was not length first. It was:

```coq
1. forall k_3, i + 1 <= k_3 < n_pre ->
     Znth k_3 (replace_Znth i (Znth i la 0) lr_2) 0 = Znth k_3 lo 0
2. forall k_2, 0 <= k_2 < i + 1 /\ Znth k_2 la 0 <= 0 ->
     Znth k_2 (replace_Znth i (Znth i la 0) lr_2) 0 = 0
3. forall k, 0 <= k < i + 1 /\ Znth k la 0 > 0 ->
     Znth k (replace_Znth i (Znth i la 0) lr_2) 0 = Znth k la 0
4. Zlength (replace_Znth i (Znth i la 0) lr_2) = n_pre
```

The fix is to run two `entailer!` calls after `Exists` and reorder the bullets to suffix, nonpositive-prefix, positive-prefix, then length. The same order is expected for the `replace_Znth i 0 lr_2` nonpositive branch.
