# Annotation reasoning

## 2026-04-22 first-match prefix invariant for `find_first_equal`

Program point: the only loop is `for (i = 0; i < n; ++i)` in `find_first_equal`. The input contract gives `0 <= n`, `Zlength(l) == n`, and `IntArray::full(a, n, l)`. The implementation is read-only with respect to the array: it scans `a[0..n)` from left to right, returns `i` immediately when `a[i] == k`, and returns `-1` after the loop if no element matched.

Current annotated C has no loop invariant:

```c
int i;

for (i = 0; i < n; ++i) {
    if (a[i] == k) {
        return i;
    }
}

return -1;
```

This is too weak for symbolic execution because both returns need accumulated scan semantics. The in-loop `return i` needs to know not only that the current read equals `k`, but also that every earlier element in `l[0..i)` is different from `k`, making `i` the first matching index. The final `return -1` needs the same no-match fact extended to the entire range `l[0..n)`.

Planned loop invariant:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      k == k@pre &&
      (forall (j: Z), (0 <= j && j < i) => l[j] != k) &&
      IntArray::full(a, n, l)
*/
for (i = 0; i < n; ++i) {
```

Initialization: after the `for` initializer sets `i = 0`, the bound `0 <= i && i <= n` follows from the precondition `0 <= n`. The prefix property is vacuous because no integer `j` satisfies `0 <= j && j < 0`. The parameters `a`, `n`, and `k` have not changed, and the full array resource is still exactly `IntArray::full(a, n, l)`.

Preservation: at the loop body, the loop condition gives `i < n`, so the read `a[i]` is within the `IntArray::full(a, n, l)` range. If `a[i] == k`, the function returns immediately; the invariant supplies `0 <= i`, `i < n` comes from the loop condition, the branch supplies `l[i] == k`, and the invariant supplies the "no earlier match" fact, exactly matching the successful-return disjunct. If `a[i] != k`, execution continues to `++i`, and the failed comparison extends the no-match prefix from `[0, i)` to `[0, i + 1)`.

Exit usability: when the loop exits, the negated condition gives `i >= n`; together with the invariant bound `i <= n`, this yields `i == n`. A minimal loop-exit assertion should expose `i == n` and restate the prefix fact over `[0, n)` immediately before the final return:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      k == k@pre &&
      (forall (j: Z), (0 <= j && j < n) => l[j] != k) &&
      IntArray::full(a, n, l)
*/
return -1;
```

This assertion is intentionally placed directly after the loop and before local cleanup, following the successful `array_contains` pattern in `examples/array_contains/annotated/array_contains.c`.
