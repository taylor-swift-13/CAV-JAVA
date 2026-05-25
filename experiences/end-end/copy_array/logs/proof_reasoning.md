## 2026-04-22T13:41:18+08:00 - Prove generated copy-array manual witnesses

After a clean `symexec` run on the current annotated file, `coq/generated/copy_array_proof_manual.v` contains five manual obligations:

```coq
Lemma proof_of_copy_array_entail_wit_1 : copy_array_entail_wit_1.
Lemma proof_of_copy_array_entail_wit_2 : copy_array_entail_wit_2.
Lemma proof_of_copy_array_return_wit_1 : copy_array_return_wit_1.
Lemma proof_of_copy_array_which_implies_wit_1 : copy_array_which_implies_wit_1.
Lemma proof_of_copy_array_which_implies_wit_2 : copy_array_which_implies_wit_2.
```

The current `proof_manual.v` has `Admitted.` for all five, so `goal_check.v` cannot be considered verified. The generated goals in `copy_array_goal.v` show the following proof shape:

- `entail_wit_1` is invariant initialization. Choose `l1 = nil` and `l2 = ld`, then `app nil ld` matches the initial destination heap.
- `entail_wit_2` is loop preservation after the post-assignment bridge. Choose `l1 = l1'` and `l2 = sublist (i + 1) n_pre ld`, then prove the suffix relation by `Znth_sublist` and length by `Zlength_sublist`.
- `return_wit_1` is loop exit. From `i >= n_pre` and `i <= n_pre`, derive `i = n_pre`; then prove `app l1 l2 = ls` by extensional list equality. The prefix fact gives every element of `l1`, and the suffix has zero length.
- `which_implies_wit_1` opens `IntArray.full src` and `IntArray.full dst` at index `i` via `IntArray.full_split_to_missing_i`. The destination cell value needs the invariant suffix fact to rewrite `Znth i (app l1 l2) 0` into `Znth i ld 0`.
- `which_implies_wit_2` folds the two missing array chunks back with `IntArray.missing_i_merge_to_full`. The destination heap list after the write should normalize to `app (l1 ++ [Znth i ls 0]) (sublist (i + 1) n_pre ld)`, and the copied-prefix semantic fact splits on `k < i` or `k = i`.

This is the same proof pattern as the existing `array_add` output-array proof, simplified from two input arrays and a sum expression to one source array and a direct copied value. The first attempt will reuse the conservative pattern from `array_add_proof_manual.v`: `pre_process`, explicit `Exists`, `sep_apply` for array split/merge, list extensional equality for `return_wit_1`, and localized `rewrite`/`lia` for sublist and app normalization.

## 2026-04-22T13:42:24+08:00 - Fix copied variable names after first compile failure

The first compile attempt failed in `copy_array_proof_manual.v` before reaching the actual list reasoning:

```text
File ".../copy_array_proof_manual.v", line 32, characters 2-37:
Error: The variable i_2 was not found in the current environment.
```

This came from copying the `array_add` proof skeleton too literally. In `array_add_entail_wit_2`, `pre_process` names the loop index `i_2`; in this generated `copy_array_entail_wit_2`, the quantified variable is simply `i`, so the witness should be:

```coq
Exists (sublist (i + 1) n_pre ld).
```

The same risk applies to `return_wit_1`, where the copied skeleton used `i_3`. I will replace these copied names with the local `i` used by `copy_array_goal.v` before recompiling. No annotation change is needed because `symexec` already generated the intended witnesses.

## 2026-04-22T13:43:11+08:00 - Correct return witness equality direction

The next compile reached `return_wit_1` and failed at the list extensionality step:

```text
Error:
Unable to unify "l1 ++ l2 = ls" with "ls = l1 ++ l2".
```

This is not a semantic gap; it is the direction of the equality subgoal produced by:

```coq
replace (app l1 l2) with ls.
```

At that point `pre_process` has already normalized the loop index into `Zlength l1` and the exit facts give `Zlength l1 = n_pre`. The required replacement side condition is `ls = app l1 l2`, not `app l1 l2 = ls`. I will instantiate `list_eq_ext` as `list_eq_ext 0 ls (app l1 l2)` and use the prefix fact in the symmetric direction:

```coq
rewrite app_Znth1 by lia.
symmetry; apply H6; lia.
```

The zero-length suffix means `app_Znth1` is valid for all `0 <= k < Zlength ls` after the exit equality.

## 2026-04-22T13:43:56+08:00 - Avoid brittle hypothesis number in suffix equality

The next compile reached `which_implies_wit_2` and failed while proving `l2 = sublist i n_pre ld`:

```text
File ".../copy_array_proof_manual.v", line 88, characters 8-21:
Error: Found no subterm matching "Znth ?M6073 ls 0" in the current goal.
```

The failing line was:

```coq
rewrite <- H5.
```

In this generated proof state, `H5` is not reliably the `Zlength l2 = n_pre - i` fact after `pre_process`; it can refer to a different pure hypothesis, so rewriting by number is fragile. The goal only needs the range `0 <= k < n_pre - i` from the `list_eq_ext` range and the available length facts. I will replace the rewrite block with:

```coq
assert (0 <= k < n_pre - i) as Hrange by lia.
```

This keeps the proof tied to the semantic fact, not to an unstable hypothesis index.

## 2026-04-22T13:44:32+08:00 - Select suffix hypothesis by type

After removing the brittle length rewrite, compilation failed one line later:

```text
Error: The variable H7 was not found in the current environment.
```

This is the same generated-name instability. The needed fact is not its name but its shape:

```coq
forall k, 0 <= k < n_pre - i ->
  Znth k l2 0 = Znth (i + k) ld 0
```

I will use a `match goal with` pattern to find this suffix hypothesis by type and pose it for the current `k`. That keeps the proof stable if `pre_process` chooses different hypothesis numbers.

## 2026-04-22T13:45:18+08:00 - Name core invariant facts in `which_implies_wit_2`

Compilation then failed after the array chunks were merged:

```text
Error: Found no subterm matching "Zlength (sublist i n_pre ld)" in the current goal.
```

The proof was still using `rewrite H4`, copied from `array_add`, to mean `Zlength l1 = i`. In this proof state, `H4` does not have that meaning. The robust fix is to name the three invariant facts needed by the rest of the witness immediately after `pre_process`:

```coq
assert (Hlen_l1 : Zlength l1 = i) by lia.
assert (Hprefix_all : forall k, 0 <= k < i -> Znth k l1 0 = Znth k ls 0) by ...
assert (Hsuffix_all : forall k, 0 <= k < n_pre - i -> Znth k l2 0 = Znth (i + k) ld 0) by ...
```

Then all later list rewrites can use `Hlen_l1`, `Hprefix_all`, and `Hsuffix_all` instead of generated hypothesis numbers. This is still the same proof, just stabilized against `pre_process` naming.
