
## 2026-04-22 scan invariant for `array_equal`

Program point: the only loop is `for (i = 0; i < n; ++i)` in `array_equal`. The contract gives `0 <= n`, `Zlength(la) == n`, `Zlength(lb) == n`, and the preserved read-only heap resources `IntArray::full(a, n, la) * IntArray::full(b, n, lb)`. The implementation only reads `a[i]` and `b[i]`; it returns `0` immediately on a mismatch and returns `1` only after every index has been scanned.

Current annotated C has no loop invariant or exit assertion:

```c
int i;

for (i = 0; i < n; ++i) {
    if (a[i] != b[i]) {
        return 0;
    }
}

return 1;
```

This is too weak for symbolic execution. The final `return 1` postcondition requires the universal fact `(forall (i: Z), (0 <= i && i < n) => la[i] == lb[i])`, which is accumulated only by seeing each failed mismatch test. The early `return 0` branch also needs a concrete existential witness index with `la[i] != lb[i]`; the current loop index is that witness, provided the invariant keeps bounds and both input arrays available.

Planned loop invariant:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      b == b@pre &&
      n == n@pre &&
      (forall (j: Z), (0 <= j && j < i) => la[j] == lb[j]) &&
      IntArray::full(a, n, la) *
      IntArray::full(b, n, lb)
*/
for (i = 0; i < n; ++i) {
```

Initialization: after the `for` initializer sets `i = 0`, `0 <= i && i <= n` follows from `0 <= n`. The processed-prefix equality fact is vacuous for `[0, 0)`. The parameters `a`, `b`, and `n` have not changed, and both full-array heap predicates still describe the original arrays.

Preservation: at the top of an iteration the loop condition gives `i < n`, so both array reads are in bounds. If `a[i] != b[i]`, the branch returns `0`; the current `i`, together with `0 <= i && i < n` and the loaded values from the two full arrays, supplies the existential mismatch required by the postcondition. If the branch does not return, the negated condition gives `la[i] == lb[i]`, extending the prefix equality from `[0, i)` to `[0, i + 1)` for the next loop head after `++i`. The function does not write either array, so the heap predicates are preserved.

Exit usability: when the loop exits, the condition is false, so `i >= n`; together with the invariant bound `i <= n`, this yields `i == n`. The final return needs the universal equality fact over `[0, n)`, so a minimal loop-exit assertion should expose `i == n` and restate the prefix invariant with upper bound `n`.

Planned loop-exit assertion:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      b == b@pre &&
      n == n@pre &&
      (forall (j: Z), (0 <= j && j < n) => la[j] == lb[j]) &&
      IntArray::full(a, n, la) *
      IntArray::full(b, n, lb)
*/
return 1;
```
