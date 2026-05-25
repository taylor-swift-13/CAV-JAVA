## 2026-04-22T01:46:18+08:00 - First manual proof plan after successful symexec

Generated manual proof file: `output/verify_20260422_014304_array_add/coq/generated/array_add_proof_manual.v`.

Current manual obligations:

```coq
Lemma proof_of_array_add_safety_wit_2 : array_add_safety_wit_2.
Proof. Admitted.

Lemma proof_of_array_add_entail_wit_1 : array_add_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_add_entail_wit_2 : array_add_entail_wit_2.
Proof. Admitted.

Lemma proof_of_array_add_return_wit_1 : array_add_return_wit_1.
Proof. Admitted.

Lemma proof_of_array_add_which_implies_wit_1 : array_add_which_implies_wit_1.
Proof. Admitted.

Lemma proof_of_array_add_which_implies_wit_2 : array_add_which_implies_wit_2.
Proof. Admitted.
```

Goal shape summary from `array_add_goal.v`:

- `array_add_safety_wit_2` is the overflow safety proof for `out[i] = a[i] + b[i]`. The precondition contains `i < n_pre`, `0 <= i`, and the contract premise `forall i_2, 0 <= i_2 < n_pre -> INT_MIN <= la[i_2] + lb[i_2] <= INT_MAX`, so the proof should be `pre_process; entailer!` plus the contract premise instantiated at `i`.
- `array_add_entail_wit_1` initializes the loop invariant. The natural witnesses are `l1 = nil` and `l2 = lo`; after `Exists lo nil`, the remaining facts are list length and vacuous prefix arithmetic, and the heap target is `IntArray.full out_pre n_pre (app nil lo)`.
- `array_add_entail_wit_2` re-establishes the loop invariant after one iteration. The generated `which_implies` obligation already produced `l1'` with the advanced prefix and the output heap shape `app l1' (sublist (i_2 + 1) n_pre lo)`, so the invariant witnesses should be `l1 = l1'` and `l2 = sublist (i_2 + 1) n_pre lo`.
- `array_add_return_wit_1` exits the loop. The assumptions include `i_3 >= n_pre`, `i_3 <= n_pre`, `Zlength l1 = i_3`, and `Zlength l2 = n_pre - i_3`, so first prove `i_3 = n_pre`. A stable witness is `lr = app l1 l2`; the final semantic condition follows from the invariant prefix fact because `i_3 = n_pre`.
- `array_add_which_implies_wit_1` decomposes three full arrays at index `i`. The proof must use the array strategy to split `IntArray.full` into `missing_i` plus `data_at`; for `out`, the visible cell must be rewritten from `(app l1 l2)[i]` to `lo[i]` using `Zlength l1 = i` and the suffix relation at offset `0`.
- `array_add_which_implies_wit_2` folds three `missing_i` predicates and the updated output cell back into full arrays, with existential prefix `l1'`. The expected witness is a list equivalent to `app l1 (cons (la[i] + lb[i]) nil)`, and the proof must normalize the rebuilt output list against `app l1' (sublist (i + 1) n_pre lo)`.

First tactic attempt: try conservative generated-VC tactics on each lemma:

```coq
Proof.
  pre_process.
  entailer!.
Qed.
```

If the simple script fails, the likely failure points are the two `which_implies` list-normalization goals and the return witness's full-prefix/empty-suffix normalization. In that case, inspect the failed theorem with `coqtop Show` and add local list helper lemmas rather than changing the C annotations.

## 2026-04-22T01:55:05+08:00 - Manual proofs completed

The first compile attempt with only `pre_process; entailer!` failed at:

```text
File ".../array_add_proof_manual.v", line 25, characters 0-4:
Error:
 (in proof proof_of_array_add_safety_wit_2): Attempt to save an incomplete proof
(there are remaining open goals).
```

`coqtop Show` after `pre_process; entailer!` for `array_add_safety_wit_2` left two pure arithmetic goals:

```coq
-2147483648 <= Znth i la 0 + Znth i lb 0
Znth i la 0 + Znth i lb 0 <= 2147483647
```

The available premise was:

```coq
H13 :
  forall i_2 : Z,
    0 <= i_2 < n_pre ->
    -2147483648 <= Znth i_2 la 0 + Znth i_2 lb 0 <= 2147483647
```

Fix: instantiate the premise at the loop index and finish both goals with `lia`:

```coq
pose proof (H13 i ltac:(lia)) as Hsum.
lia.
```

The invariant initialization witness `array_add_entail_wit_1` did not need new lemmas; it needed assertion-level existential witnesses:

```coq
Exists lo.
Exists nil.
entailer!.
```

The loop preservation witness `array_add_entail_wit_2` needed explicit witnesses and two sublist facts. The chosen suffix witness was `sublist (i_2 + 1) n_pre lo`, and the prefix witness was the already generated `l1'`:

```coq
Exists (sublist (i_2 + 1) n_pre lo).
Exists l1'.
entailer!.
- intros k Hk.
  rewrite Znth_sublist by lia.
  replace (k + (i_2 + 1)) with (i_2 + 1 + k) by lia.
  reflexivity.
- rewrite Zlength_sublist by lia.
  lia.
```

The return witness was solved by first deriving the loop exit equality and choosing the current heap list as the returned logical list:

```coq
assert (Hi : i_3 = n_pre) by lia.
subst i_3.
Exists (app l1 l2).
entailer!.
- intros i Hi_range.
  rewrite app_Znth1 by lia.
  apply H7; lia.
- rewrite Zlength_app.
  lia.
```

The first array-decomposition bridge `array_add_which_implies_wit_1` required direct use of `IntArray.full_split_to_missing_i` with default `0` for all three arrays, plus a proof that the current output cell in `app l1 l2` equals `lo[i]`:

```coq
sep_apply (IntArray.full_split_to_missing_i a_pre i n_pre la 0); try lia.
sep_apply (IntArray.full_split_to_missing_i b_pre i n_pre lb 0); try lia.
sep_apply (IntArray.full_split_to_missing_i out_pre i n_pre (app l1 l2) 0); try lia.
replace (Znth i (app l1 l2) 0) with (Znth i lo 0).
entailer!.
rewrite app_Znth2 by lia.
replace (i - Zlength l1) with 0 by lia.
rewrite H7 by lia.
replace (i + 0) with i by lia.
reflexivity.
```

The final fold-back bridge `array_add_which_implies_wit_2` was the main list-normalization proof. I reused the archived same-task pattern from `archieve/output_backup_20260422_011624/verify_20260422_014300001_array_add/coq/generated/array_add_proof_manual.v`: first prove `l2 = sublist i n_pre lo` with `list_eq_ext`, then choose `l1 ++ [la[i] + lb[i]]` as the advanced prefix, merge all three `missing_i` predicates back to full arrays, and normalize the output list using `replace_Znth_app_r`, `sublist_split`, and `sublist_single`.

Key Coq shape:

```coq
assert (l2 = sublist i n_pre lo) as Hl2.
...
Exists (l1 ++ cons (Znth i la 0 + Znth i lb 0) nil).
sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
rewrite replace_Znth_Znth by tauto.
rewrite replace_Znth_Znth by tauto.
rewrite replace_Znth_app_r by lia.
...
entailer!.
```

After these changes, `coqc` compiled `array_add_proof_manual.v` successfully, and a fail-fast full compile replay compiled `array_add_goal.v`, `array_add_proof_auto.v`, `array_add_proof_manual.v`, and `array_add_goal_check.v`.
