## 2026-04-22 17:27 +0800 - Loop invariant for prefix DP state

Current program point: the only loop in `annotated/verify_20260422_171952_house_robber.c` is:

```c
for (i = 0; i < n; ++i) {
    take = prev2 + a[i];
    if (take > prev1) {
        cur = take;
    } else {
        cur = prev1;
    }
    prev2 = prev1;
    prev1 = cur;
}

return prev1;
```

The active annotated copy initially matched `input/house_robber.c` and had no `Inv`. Without a loop invariant, symbolic execution has no reusable summary connecting the scalar variables `prev2` and `prev1` to the postcondition `__return == house_robber_spec(l)`, and it also has no loop-carried heap fact preserving `IntArray::full(a, n, l)`.

At the `for` loop control point, `i` is the number of processed array elements and the next index to read. The natural closed form is:

```c
prev1 == house_robber_spec(sublist(0, i, l))
```

because `prev1` is the best value after the processed prefix. The previous DP state is the best value for the prefix ending one element earlier; at `i == 0` that state is the initial accumulator `0`, and at `i > 0` it is:

```c
prev2 == house_robber_spec(sublist(0, i - 1, l))
```

The invariant must also keep `a == a@pre`, `n == n@pre`, the array length fact, the input element bounds, the prefix result bounds, and `IntArray::full(a, n@pre, l)`. These facts are required by the array read `a[i]`, by the arithmetic safety proof for `take = prev2 + a[i]`, and by the final postcondition that preserves the input array.

Planned annotation inserted immediately before the loop:

```c
/*@ Inv
      0 <= i && i <= n@pre &&
      n == n@pre &&
      a == a@pre &&
      0 <= n@pre && n@pre <= INT_MAX &&
      Zlength(l) == n@pre &&
      (forall (t: Z),
        (0 <= t && t < n@pre) =>
        (0 <= l[t] && l[t] <= INT_MAX)) &&
      (forall (k: Z),
        (0 <= k && k <= n@pre) =>
        (0 <= house_robber_spec(sublist(0, k, l)) &&
         house_robber_spec(sublist(0, k, l)) <= INT_MAX)) &&
      prev1 == house_robber_spec(sublist(0, i, l)) &&
      ((i == 0) => prev2 == 0) &&
      ((i > 0) => prev2 == house_robber_spec(sublist(0, i - 1, l))) &&
      ((i < n@pre) => prev2 + l[i] <= INT_MAX) &&
      IntArray::full(a, n@pre, l)
*/
for (i = 0; i < n; ++i) {
```

Initialization: before the first condition check, `i == 0`, `prev1 == 0`, and `prev2 == 0`. `house_robber_spec(sublist(0, 0, l))` unfolds to the accumulator on `nil`, so the `prev1` equality and `i == 0` branch of the `prev2` relation match the concrete state. The heap is exactly the function precondition heap, and the pure input bounds are copied from the contract.

Preservation: assuming the invariant and loop guard `i < n@pre`, the read `a[i]` exposes `l[i]`. The guarded overflow fact is intended to justify `take = prev2 + a[i]` as an `int` addition. The branch assigns `cur` to the larger of `prev2 + l[i]` and `prev1`, exactly matching one step of the Coq definition of `house_robber_spec` over `sublist(0, i + 1, l)`. The assignments `prev2 = prev1; prev1 = cur` shift the prefix-DP state so that the next loop head satisfies the same `prev2` and `prev1` formulas for `i + 1`.

Exit usability: when the loop exits, the invariant gives `i <= n@pre` and the negated guard gives `i >= n@pre`, so `i == n@pre`. Then `prev1 == house_robber_spec(sublist(0, n@pre, l))`, and `Zlength(l) == n@pre` reduces the sublist to the full logical input list. The preserved `IntArray::full(a, n@pre, l)` is exactly the postcondition heap.
