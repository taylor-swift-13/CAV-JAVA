## 2026-04-22 proof round 1: discharge generated manual witnesses

Fresh symbolic execution succeeded for `annotated/verify_20260422_073534_array_replace_negative_zero.c` and generated the current Coq files under `output/verify_20260422_073534_array_replace_negative_zero/coq/generated/`.

The generated manual file currently contains three placeholders:

```coq
Lemma proof_of_array_replace_negative_zero_entail_wit_2_1 : array_replace_negative_zero_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_replace_negative_zero_entail_wit_2_2 : array_replace_negative_zero_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_array_replace_negative_zero_entail_wit_3 : array_replace_negative_zero_entail_wit_3.
Proof. Admitted.
```

The corresponding goals in `array_replace_negative_zero_goal.v` are:

- `entail_wit_2_1`: loop preservation for the true branch `a[i] < 0` after the assignment `a[i] = 0`; the heap list is `replace_Znth i 0 lc_2`, and the invariant must be re-established for `i + 1`.
- `entail_wit_2_2`: loop preservation for the false branch where the current value is not negative; the heap list remains `lc_2`, and the invariant must still be re-established for `i + 1`.
- `entail_wit_3`: the loop-exit assertion; from `i >= n_pre` plus the invariant bound `i <= n_pre`, prove `i = n_pre` and choose `lc_2` as the final list.

The first proof needs local list helpers for `replace_Znth`: unchanged length, same-index lookup after replacement, and different-index lookup after replacement. These helpers are pure list facts and are already used successfully by the nearby verified `array_clamp_nonnegative` pattern. I will add them locally to this workspace's `array_replace_negative_zero_proof_manual.v`.

Planned proof edits:

```coq
Exists (replace_Znth i 0 lc_2).
entailer!.
```

For the true branch, the suffix proof uses `Znth_replace_Znth_diff` because suffix indices after the next iteration satisfy `k >= i + 1`, hence `k <> i`. The nonnegative-prefix proof splits on `k = i`; at `k = i` the branch condition and suffix equality imply `l[i] < 0`, contradicting the requested `l[i] >= 0`, so `lia` closes it. The negative-prefix proof also splits on `k = i`; the same-index rewrite gives the newly written `0`, and older prefix indices use the old prefix invariant plus the different-index rewrite.

For the false branch, the witness is `lc_2`; no heap rewrite is needed. At `k = i`, the branch condition gives the current cell nonnegative, and the suffix equality transfers that to `l[i] >= 0`; older prefix indices reuse the old prefix facts.

For the exit witness, `pre_process` should expose the invariant assumptions and the loop exit condition; `assert (Hi : i = n_pre) by lia` aligns the invariant range with the postcondition range, then `Exists lc_2; entailer!.` should close the assertion-level existential.
