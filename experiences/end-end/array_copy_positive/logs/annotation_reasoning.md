## 2026-04-22T02:56:00+08:00 - Initial loop invariant for output prefix transform

Program point: the single loop

```c
for (i = 0; i < n; ++i) {
    if (a[i] > 0) {
        out[i] = a[i];
    } else {
        out[i] = 0;
    }
}
```

The active annotated file initially copied the contract input exactly and had no `Inv` before the `for` loop. This loop writes `out` progressively while preserving `a`, so `symexec` needs a loop-head description of the current logical contents of `out`, the unchanged input array, the index bounds, and the value relation already established for the processed prefix.

Planned invariant:

```c
/*@ Inv exists lr,
      0 <= i && i <= n@pre &&
      n == n@pre &&
      a == a@pre &&
      out == out@pre &&
      n@pre == Zlength(la) &&
      n@pre == Zlength(lo) &&
      Zlength(lr) == n@pre &&
      (forall (k: Z), (0 <= k && k < i && la[k] > 0) => lr[k] == la[k]) &&
      (forall (k: Z), (0 <= k && k < i && la[k] <= 0) => lr[k] == 0) &&
      (forall (k: Z), (i <= k && k < n@pre) => lr[k] == lo[k]) &&
      IntArray::full(a, n@pre, la) *
      IntArray::full(out, n@pre, lr)
*/
```

Why it is positioned at the right control point: for a C `for (i = 0; i < n; ++i)`, the invariant describes the state after initialization and before testing `i < n`. At that point `i` is exactly the next index to process; `0 <= k < i` is the processed prefix, and `i <= k < n@pre` is the untouched suffix.

Initialization: before the first test, `i == 0`, so both processed-prefix implications are vacuous. Choosing `lr = lo` satisfies `Zlength(lr) == n@pre`, the suffix fact for all `0 <= k < n@pre`, and the heap assertion `IntArray::full(out, n@pre, lr)`. The input heap remains `IntArray::full(a, n@pre, la)`.

Preservation: inside the loop, `0 <= i < n@pre`. The branch `a[i] > 0` writes `out[i] = a[i]`, extending the positive-case prefix fact to index `i`; the branch `a[i] <= 0` writes `out[i] = 0`, extending the nonpositive-case prefix fact to index `i`. All earlier indices keep their prefix facts, all later indices keep the suffix relation to `lo`, and `a` remains unchanged.

Exit use: when the loop exits, the invariant gives `0 <= i <= n@pre` and the negated loop condition gives `i >= n`, while `n == n@pre`, so `i == n`. A small exit assertion will expose the postcondition shape with `0 <= k < n@pre` rather than `0 <= k < i`:

```c
/*@ Assert exists lr,
      i == n &&
      n == n@pre &&
      a == a@pre &&
      out == out@pre &&
      n@pre == Zlength(la) &&
      n@pre == Zlength(lo) &&
      Zlength(lr) == n@pre &&
      (forall (k: Z), (0 <= k && k < n@pre && la[k] > 0) => lr[k] == la[k]) &&
      (forall (k: Z), (0 <= k && k < n@pre && la[k] <= 0) => lr[k] == 0) &&
      IntArray::full(a, n@pre, la) *
      IntArray::full(out, n@pre, lr)
*/
```

This assertion is deliberately placed immediately after the loop, before local variable cleanup, and only fixes the loop-exit facts needed by the function postcondition.
