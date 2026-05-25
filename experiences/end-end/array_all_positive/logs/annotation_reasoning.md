## 2026-04-22 annotation plan: prefix-positive invariant

Current program point:

```c
for (i = 0; i < n; ++i) {
    if (a[i] <= 0) {
        return 0;
    }
}

return 1;
```

The loop scans `a[0..n)` and returns early when the current element is non-positive. The existing annotated copy has no invariant, so symbolic execution has no persistent fact describing the already processed prefix. The postcondition has two cases: return `0` requires an existential bad index, and return `1` requires a universal fact for all indices in the array.

Planned invariant:

```c
/*@ Inv
      0 <= i && i <= n@pre &&
      n == n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      (forall (j: Z), (0 <= j && j < i) => l[j] > 0) &&
      IntArray::full(a, n@pre, l)
*/
for (i = 0; i < n; ++i) {
    if (a[i] <= 0) {
        return 0;
    }
}
```

Why this is the right control point: for a C `for` loop, the invariant describes the state after initialization and before the loop condition check. At that point `i` is the next index to inspect, so the processed part is exactly the prefix `0 <= j < i`.

Initialization: after `i = 0`, `0 <= i <= n@pre` follows from the precondition `0 <= n`, and the prefix property is vacuous because there is no `j` with `0 <= j < 0`. The heap predicate is the original `IntArray::full(a, n, l)`, and `n@pre == Zlength(l)` follows from the precondition.

Preservation: if the loop body reaches the increment, the branch `a[i] <= 0` was false, so the current array element is positive. Together with the old prefix fact for `j < i`, this establishes the prefix fact for `j < i + 1`. The array is only read, so `IntArray::full(a, n@pre, l)` and the parameter equalities are preserved.

Early return branch: inside `if (a[i] <= 0)`, the loop condition gives `i < n`, the invariant gives `0 <= i`, and the branch condition gives `l[i] <= 0` after reading `a[i]`, so the existential postcondition can use witness `i`. The heap is preserved because the function only reads.

Loop exit and final return: when the loop exits normally, the invariant gives positivity for all `j < i`; the failed loop condition plus `i <= n@pre` gives `i == n@pre`, so the universal postcondition for `return 1` follows over the full array range. The empty-loop case `n == 0` is covered because the invariant initializes at `i == 0` and the universal range is empty.
