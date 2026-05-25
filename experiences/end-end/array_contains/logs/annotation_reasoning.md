# Annotation reasoning

## 2026-04-22 scan invariant for `array_contains`

Program point: the only loop is `for (i = 0; i < n; ++i)` in `array_contains`. The precondition gives `0 <= n`, `Zlength(l) == n`, and `IntArray::full(a, n, l)`. The implementation is read-only: it only reads `a[i]` and returns either `1` from inside the loop or `0` after the loop.

Current annotated C has no `Inv` before the `for` loop:

```c
int i;

for (i = 0; i < n; ++i) {
    if (a[i] == k) {
        return 1;
    }
}

return 0;
```

This is too weak for symbolic execution because the final `return 0` postcondition requires the universal fact `(forall (i: Z), (0 <= i && i < n) => l[i] != k)`. That fact is accumulated one element at a time: after each failed comparison in the loop body, the scanned element is known to be different from `k`, so the stable loop fact should be that every processed prefix index is different from `k`.

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

Initialization: after `i = 0`, `0 <= i && i <= n` follows from `0 <= n`; the prefix property is vacuous because there is no `j` with `0 <= j < 0`; `a`, `n`, and `k` are unchanged; and the original `IntArray::full(a, n, l)` resource is still available.

Preservation: at the loop body, the loop condition gives `i < n`, so reading `a[i]` is within the array bounds. If `a[i] == k`, the branch returns `1` and can use the current index `i` as the existential witness for the postcondition. If the branch does not return, the comparison gives `l[i] != k`, extending the processed-prefix fact from `[0, i)` to `[0, i + 1)` for the next loop check after `++i`; the array remains unchanged.

Exit usability: when the loop exits, `i >= n` combined with the invariant bound `i <= n` gives `i == n`. A minimal loop-exit assertion should expose this equality and restate the prefix fact over `[0, n)` so the final `return 0` can consume the exact universal postcondition.

Planned loop-exit assertion:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      k == k@pre &&
      (forall (j: Z), (0 <= j && j < n) => l[j] != k) &&
      IntArray::full(a, n, l)
*/
return 0;
```
