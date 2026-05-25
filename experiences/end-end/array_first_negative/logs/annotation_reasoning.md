## 2026-04-22 04:17:34 +0800 - Add scan invariant and loop-exit assertion

Current active annotated file initially contains the input contract but no Verify annotations inside the body:

```c
int i;

for (i = 0; i < n; ++i) {
    if (a[i] < 0) {
        return i;
    }
}

return -1;
```

The proof obligation needs two facts that are not available without a loop invariant:

1. At the start of each loop test, `i` is the next index to inspect and all previously inspected elements are nonnegative.
2. The array memory and unchanged parameters `a` and `n` are still connected to the pre-state contract so the final `Ensure` can mention the original list `l`.

The invariant should be placed immediately before the `for` loop because the C `for` invariant describes the state after `i = 0` initialization and before each loop-condition check. The planned invariant is:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      (forall (j: Z), (0 <= j && j < i) => l[j] >= 0) &&
      IntArray::full(a, n, l)
*/
for (i = 0; i < n; ++i) {
```

Initialization holds because `i == 0`, `0 <= n` is a precondition, and the quantified prefix `0 <= j < 0` is empty. Preservation holds because when the body does not return, the branch condition gives `a[i] >= 0`; with `IntArray::full(a, n, l)` and `0 <= i < n`, this is the needed new prefix fact `l[i] >= 0`, so after `++i` the prefix property extends to the next loop-control point. The memory predicate is read-only and therefore preserved.

The early return branch should then have enough facts to prove the second disjunct of the postcondition: `0 <= i`, `i < n`, current read `l[i] < 0`, and all earlier elements nonnegative from the invariant.

The final `return -1` needs the first disjunct over the entire range. After loop exit, the condition is false, so together with `0 <= i && i <= n` it should imply `i == n`. I will add a minimal exit assertion immediately after the loop:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      (forall (j: Z), (0 <= j && j < n) => l[j] >= 0) &&
      IntArray::full(a, n, l)
*/
return -1;
```

This assertion is deliberately adjacent to the loop exit, before the return, so it serves only as a bridge from the loop invariant plus failed loop condition to the final postcondition and does not try to compensate for missing ownership or prefix facts later in local-variable cleanup.
