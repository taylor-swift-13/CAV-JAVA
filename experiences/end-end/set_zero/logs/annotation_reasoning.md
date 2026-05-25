## Annotation iteration 1

Current source point: `set_zero` has a single `for (i = 0; i < n; ++i)` loop whose body writes `a[i] = 0`. The original annotated copy has no loop invariant, so symbolic execution cannot preserve the heap shape or the semantic fact needed by the postcondition:

```c
for (i = 0; i < n; ++i) {
    a[i] = 0;
}
```

The postcondition requires an existential result list `lr` with `Zlength(lr) == n` and every valid element equal to zero:

```c
exists lr,
  Zlength(lr) == n &&
  (forall (i: Z), (0 <= i && i < n) => lr[i] == 0) &&
  IntArray::full(a, n, lr)
```

The invariant will model the current whole array as an existential `lr`. At the loop guard control point, `i` is the next index to write, so `[0, i)` is already zero and `[i, n)` still equals the original input list `l`. It must also retain `a == a@pre`, `n@pre == Zlength(l)`, and the current full array heap:

```c
/*@ Inv exists lr,
      0 <= i && i <= n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      Zlength(lr) == n@pre &&
      (forall (k: Z), (0 <= k && k < i) => lr[k] == 0) &&
      (forall (k: Z), (i <= k && k < n@pre) => lr[k] == l[k]) &&
      IntArray::full(a, n@pre, lr)
*/
```

Initialization: after `i = 0`, the prefix condition is vacuous, the suffix condition covers the whole array, and the precondition already provides `Zlength(l) == n` and `IntArray::full(a, n, l)`, so choosing `lr = l` satisfies the invariant.

Preservation: inside the loop, the condition gives `i < n`, so the current cell is within bounds. Before `a[i] = 0`, a bridge converts the full array into `IntArray::missing_i(a, i, 0, n@pre, lr)` plus the current cell `data_at(..., l[i])`; this is justified by the suffix property because `i <= i < n@pre`. After the store, a second bridge reassembles the full array with a fresh `lr'`, whose prefix through `i` is zero and whose suffix after `i` still equals `l`.

Exit: when the loop exits, the invariant gives `0 <= i <= n@pre` and the failed guard gives `i >= n@pre`, so `i == n@pre`. The prefix-zero fact then covers every valid index required by the postcondition, and the suffix fact is vacuous. No separate loop-exit assertion is planned unless `symexec` shows that the return witness needs one.
