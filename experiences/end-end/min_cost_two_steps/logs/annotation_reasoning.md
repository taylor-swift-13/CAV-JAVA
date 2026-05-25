## 2026-04-22 20:24 +0800 - Loop invariant for two-state prefix DP

Current program point: the only loop in `annotated/verify_20260422_201546_min_cost_two_steps.c` is:

```c
for (i = 2; i < n; ++i) {
    if (prev1 < prev2) {
        cur = prev1 + cost[i];
    } else {
        cur = prev2 + cost[i];
    }
    prev2 = prev1;
    prev1 = cur;
}

return prev1;
```

The active annotated copy initially matches `input/min_cost_two_steps.c` and has no loop invariant.  Without an invariant, symbolic execution has no loop-head summary connecting the rolling scalar variables `prev2` and `prev1` to the postcondition `__return == min_cost_two_steps_spec(l)`, and it also lacks a loop-carried heap fact preserving `IntArray::full(cost, n, l)`.

At the `for` loop control point, `i` is the next array index to consume.  The prefix `[0, i)` has already been summarized by `prev1`, while `prev2` is the previous state for prefix `[0, i - 1)`.  The closed-form facts should therefore be:

```c
prev2 == min_cost_two_steps_spec(sublist(0, i - 1, l))
prev1 == min_cost_two_steps_spec(sublist(0, i, l))
```

This aligns with initialization after the `n == 1` early return.  At that point the remaining path has `n >= 2`, `i` is initialized to `2`, `prev2 == cost[0]`, and `prev1 == cost[0] + cost[1]`; these are exactly `min_cost_two_steps_spec(sublist(0, 1, l))` and `min_cost_two_steps_spec(sublist(0, 2, l))`.

The invariant must also preserve the unchanged input parameters `n == n@pre` and `cost == cost@pre`, the original length and element bounds, the prefix-sum overflow guard from the contract, and the unchanged heap `IntArray::full(cost, n@pre, l)`.  To make C integer additions in the branch provable, the invariant carries branch-sensitive guarded overflow facts for the next element:

```c
((i < n@pre && prev1 < prev2) => prev1 + l[i] <= INT_MAX)
((i < n@pre && prev1 >= prev2) => prev2 + l[i] <= INT_MAX)
```

These facts express exactly the two possible additions in the loop body.  They are derivable from the nonnegative input costs and the contract's prefix-sum bound because the selected DP state is bounded by the processed prefix sum; any remaining proof work should be pure arithmetic/list reasoning in Coq rather than missing heap or local-state information.

Planned annotation inserted immediately before the loop:

```c
/*@ Inv
      2 <= i && i <= n@pre &&
      n == n@pre &&
      cost == cost@pre &&
      Zlength(l) == n@pre &&
      (forall (t: Z),
        (0 <= t && t < n@pre) =>
        (0 <= l[t] && l[t] <= INT_MAX)) &&
      (forall (k: Z),
        (1 <= k && k <= n@pre) =>
        (0 <= sum(sublist(0, k, l)) &&
         sum(sublist(0, k, l)) <= INT_MAX)) &&
      prev2 == min_cost_two_steps_spec(sublist(0, i - 1, l)) &&
      prev1 == min_cost_two_steps_spec(sublist(0, i, l)) &&
      0 <= prev2 && 0 <= prev1 &&
      ((i < n@pre && prev1 < prev2) => prev1 + l[i] <= INT_MAX) &&
      ((i < n@pre && prev1 >= prev2) => prev2 + l[i] <= INT_MAX) &&
      IntArray::full(cost, n@pre, l)
*/
for (i = 2; i < n; ++i) {
```

Initialization: on the path reaching the loop, `n != 1` and the precondition `1 <= n` imply `2 <= n`.  The reads `cost[0]` and `cost[1]` expose the first two elements of `l`, and the prefix-sum bound for `k == 2` proves `cost[0] + cost[1] <= INT_MAX`.  Thus the scalar equalities and nonnegativity facts match the two initial DP prefixes, and the heap remains the full input array.

Preservation: assuming the invariant and guard `i < n@pre`, the branch condition decides whether `cur` is `prev1 + l[i]` or `prev2 + l[i]`, matching the `Z.min prev1 prev2 + x` step in `min_cost_two_steps_acc`.  The assignments `prev2 = prev1; prev1 = cur` shift the two prefix summaries so the next loop head has `prev2` for prefix `i` and `prev1` for prefix `i + 1`.

Exit usability: when the loop exits, the invariant gives `i <= n@pre` and the negated guard gives `i >= n@pre`, so `i == n@pre`.  Then `prev1 == min_cost_two_steps_spec(sublist(0, n@pre, l))`, and `Zlength(l) == n@pre` reduces that sublist to the full logical input list.  The preserved `IntArray::full(cost, n@pre, l)` is exactly the postcondition heap.

## 2026-04-22 20:31 +0800 - Remove future-overflow facts from invariant

After the first successful `symexec`, the generated preservation witnesses `min_cost_two_steps_entail_wit_2_1` and `min_cost_two_steps_entail_wit_2_2` showed that the two guarded overflow facts in the invariant force the proof to establish overflow safety for the *next* iteration at every loop-preservation step:

```coq
((((i_2 + 1) < n_pre) /\
  ((prev1 + Znth i_2 l 0) >= prev1)) ->
 ((prev1 + Znth (i_2 + 1) l 0) <= INT_MAX))
```

This is semantically true but not needed as a loop-carried invariant.  The actual C safety checks only need the current branch addition to be in range, and each branch safety witness already knows the current loop guard, current branch condition, current DP scalar equalities, nonnegative input elements, and the prefix-sum bound.  Therefore the cleaner invariant is:

```c
prev2 == min_cost_two_steps_spec(sublist(0, i - 1, l)) &&
prev1 == min_cost_two_steps_spec(sublist(0, i, l)) &&
0 <= prev2 && 0 <= prev1 &&
IntArray::full(cost, n@pre, l)
```

with no guarded future-overflow implications.  This keeps exactly the semantic state needed for recurrence preservation and final return.  The branch safety proofs will instead use a local Coq lemma that the selected DP state is bounded by the processed prefix sum, then combine it with the contract's `sum(sublist(0, i + 1, l)) <= INT_MAX`.

## 2026-04-22 20:34 +0800 - Add state-independent prefix DP bound

The cleaned invariant still leaves each branch safety witness to reprove from scratch that the selected DP state is bounded by the processed prefix sum.  That fact is independent of the current loop state: it follows only from the unchanged logical input list `l` and the nonnegative element bounds.  To avoid duplicating the same pure argument in every branch witness, I am adding a forall prefix bound to the invariant:

```c
(forall (k: Z),
  (1 <= k && k <= n@pre) =>
  (0 <= min_cost_two_steps_spec(sublist(0, k, l)) &&
   min_cost_two_steps_spec(sublist(0, k, l)) <= sum(sublist(0, k, l))))
```

Initialization will generate one pure proof that all nonempty prefixes satisfy this DP bound.  Preservation can copy the same forall unchanged because neither `l`, `n`, nor the input array is modified.  Branch safety then becomes direct: in the `prev1 < prev2` branch, `prev1` is `spec(prefix i)`, and in the other branch `prev2` is `spec(prefix i-1)`; the selected state is nonnegative and no larger than the corresponding prefix sum, so adding the nonnegative current element is bounded by `sum(sublist(0, i + 1, l)) <= INT_MAX`.
