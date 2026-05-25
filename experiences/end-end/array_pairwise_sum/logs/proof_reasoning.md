# Proof Reasoning

## 2026-04-22 06:34 CST - Replace generated admits with prefix/suffix array proof

After the latest `symexec`, `coq/generated/array_pairwise_sum_proof_manual.v` contains six manual witness lemmas, all still generated as `Proof. Admitted.`:

```coq
proof_of_array_pairwise_sum_safety_wit_2
proof_of_array_pairwise_sum_entail_wit_1
proof_of_array_pairwise_sum_entail_wit_2
proof_of_array_pairwise_sum_return_wit_1
proof_of_array_pairwise_sum_which_implies_wit_1
proof_of_array_pairwise_sum_which_implies_wit_2
```

The generated `goal.v` witness set is the standard loop proof for an output array updated one element at a time. The key proof obligations are:

- `safety_wit_2`: use the contract overflow guard at the current loop index `i` to prove `a[i] + b[i]` is in signed-int range.
- `entail_wit_1`: initialize the loop invariant with computed prefix `nil` and suffix `lo`.
- `entail_wit_2`: rebuild the next loop invariant after extending the computed prefix by one element and changing the suffix to `sublist (i_2 + 1) n_pre lo`.
- `return_wit_1`: prove loop exit gives `i_3 = n_pre`, the suffix list has length zero, and `l1` is a valid postcondition witness.
- `which_implies_wit_1`: split full arrays into `missing_i` plus the focused cells required for the statement `out[i] = a[i] + b[i]`.
- `which_implies_wit_2`: merge the focused cells back into full arrays and normalize the updated `out` list to `app (l1 ++ [la[i] + lb[i]]) (sublist (i + 1) n_pre lo)`.

I found an archived verified proof for the same `array_pairwise_sum` shape under:

```text
./archieve/examples_backup_20260422_011624/array_pairwise_sum/coq/generated/array_pairwise_sum_proof_manual.v
```

That proof uses only local facts from `pre_process`, list lemmas already imported by the generated file, and `IntArray.full_split_to_missing_i` / `IntArray.missing_i_merge_to_full`. It does not introduce any `Axiom`, and it proves the same six witness names. I will transplant the proof bodies while preserving the current file's timestamped import:

```coq
From SimpleC.EE.CAV.verify_20260422_063057_array_pairwise_sum Require Import array_pairwise_sum_goal.
```

This should close the manual proof obligations because the current annotation was intentionally modeled after the same prefix/suffix invariant and bridge assertions.
