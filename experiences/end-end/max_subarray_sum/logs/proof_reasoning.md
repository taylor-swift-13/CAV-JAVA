## 2026-04-22 manual proof plan after fresh symexec

Fresh `symexec` succeeded on `annotated/verify_20260422_192331_max_subarray_sum.c` and generated current VC files under `output/verify_20260422_192331_max_subarray_sum/coq/generated/`. The manual proof file contains exactly these unresolved witnesses:

```coq
proof_of_max_subarray_sum_safety_wit_4
proof_of_max_subarray_sum_safety_wit_5
proof_of_max_subarray_sum_entail_wit_1
proof_of_max_subarray_sum_entail_wit_2_1
proof_of_max_subarray_sum_entail_wit_2_2
proof_of_max_subarray_sum_entail_wit_2_3
proof_of_max_subarray_sum_entail_wit_2_4
proof_of_max_subarray_sum_return_wit_1
```

The key generated invariant hypothesis in the loop witnesses is:

```coq
cur = sum (sublist lo_3 i l)
max_subarray_sum_acc cur best (sublist i n_pre l) =
  max_subarray_sum_spec l
```

The two safety witnesses must prove `cur + Znth i l 0` is in C int range. This is not a heap proof problem: after `entailer!`, the remaining pure proof should instantiate the contract overflow guard at `lo_2` and `i + 1`, then rewrite:

```coq
sum (sublist lo_2 (i + 1) l) =
  sum (sublist lo_2 i l) + Znth i l 0
```

using `cur = sum (sublist lo_2 i l)`.

The initialization witness should choose `lo_2 = 0`, prove the singleton prefix sum equals `Znth 0 l 0`, and show:

```coq
max_subarray_sum_acc (Znth 0 l 0) (Znth 0 l 0) (sublist 1 n_pre l) =
  max_subarray_sum_spec l
```

from `1 <= n_pre` and `Zlength l = n_pre`.

The four preservation witnesses all use the same accumulator equation. The proof should rewrite `sublist i n_pre l` to `Znth i l 0 :: sublist (i + 1) n_pre l`, simplify one accumulator step, then normalize `Z.max` using the branch facts:

```coq
cur + Znth i l 0 < Znth i l 0
cur + Znth i l 0 >= Znth i l 0
best < ...
best >= ...
```

For the two branches where `cur` becomes `Znth i l 0`, the existential witness is `lo_2 = i`; for the two branches where `cur` becomes `cur + Znth i l 0`, the witness is the previous `lo_3`.

The return witness only needs `i = n_pre`, then `sublist n_pre n_pre l = nil`, so the invariant accumulator equation simplifies to `best = max_subarray_sum_spec l`.

## 2026-04-22 proof iteration notes

The first compile replay stopped in the local helper lemma:

```text
line 55: Found no subterm matching "Zlength ?M2995" in the current goal.
```

The failing proof line was:

```coq
rewrite (sublist_split lo (i + 1) i l) by (rewrite Zlength_correct; lia).
```

The side condition expected `Z.of_nat (length l)` rather than a goal containing `Zlength l`, so rewriting `Zlength_correct` directly was not stable. I changed the side-condition proof to:

```coq
rewrite (sublist_split lo (i + 1) i l) by (pose proof Zlength_correct l; lia).
```

The next compile stopped at:

```text
line 69: Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as'
```

This came from `destruct l as [| x xs]` under the generated proof file's open scopes. The existing examples use `destruct l.` in this setting, so I changed the helper to avoid the `as` pattern:

```coq
destruct l.
```

The first safety proof then failed because my initial `solve_cur_plus_range` tactic matched the overflow guard too specifically. After `entailer!`, the guard appears as:

```coq
H14 :
  forall lo hi : Z,
    0 <= lo < hi /\ hi <= n_pre ->
    -2147483648 <= sum (sublist lo hi l) <= 2147483647
```

I relaxed the Ltac pattern to match any guard of shape:

```coq
forall lo0 hi0 : Z, _ -> _ <= sum (sublist lo0 hi0 l) <= _
```

and used `all: solve_cur_plus_range` because `entailer!` produced two arithmetic goals for the safety witness.

For `entail_wit_1` and the loop-preservation witnesses, `entailer!` produced pure goals in a different order than the textual order in the generated assertion. For example, `entail_wit_1` produced:

```coq
1. max_subarray_sum_acc (Znth 0 l 0) (Znth 0 l 0) (sublist 1 n_pre l) =
   max_subarray_sum_spec l
2. Znth 0 l 0 <= INT_MAX
3. Znth 0 l 0 <= INT_MAX
4. INT_MIN <= Znth 0 l 0
5. INT_MIN <= Znth 0 l 0
6. Znth 0 l 0 = sum (sublist 0 1 l)
```

The proof therefore first applies `max_subarray_sum_spec_nonempty_acc`, then uses the singleton overflow guard four times, and only proves the singleton sum equality last.

The branch witnesses needed branch-specific numbers of range goals. `entail_wit_2_1` needs two singleton upper-bound goals plus the singleton sum equality. `entail_wit_2_2` needs two upper-bound goals for `cur + Znth i l 0` plus the extended subarray sum equality. `entail_wit_2_3` needs only the lower bound for `cur + Znth i l 0`, because `best >= cur + Znth i l 0` and the invariant's `best <= INT_MAX` discharge the upper bound. `entail_wit_2_4` similarly needs only one singleton range goal before the singleton sum equality.

After adjusting those bullet orders, the final compile replay succeeded:

```text
compiled=original/max_subarray_sum.v
compiled=coq/generated/max_subarray_sum_goal.v
compiled=coq/generated/max_subarray_sum_proof_auto.v
compiled=coq/generated/max_subarray_sum_proof_manual.v
compiled=coq/generated/max_subarray_sum_goal_check.v
```

`max_subarray_sum_proof_manual.v` now has no `Admitted.`, no added `Axiom`, and no added `Parameter`.
