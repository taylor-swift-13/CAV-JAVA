# Annotation reasoning

## 2026-04-22 prefix maximum invariant for `array_max`

Program point: the only loop is `for (i = 1; i < n; ++i)` in `array_max`. The contract precondition gives `1 <= n`, `Zlength(l) == n`, and `IntArray::full(a, n, l)`. The implementation is read-only: it initializes `ret` from `a[0]`, scans the remaining indices, and conditionally assigns `ret = a[i]` when the current element is larger.

Current annotated C has no loop invariant:

```c
int i;
int ret = a[0];

for (i = 1; i < n; ++i) {
    if (a[i] > ret) {
        ret = a[i];
    }
}

return ret;
```

This is too weak for symbolic execution because the postcondition requires both parts of the maximum property: `ret` must be equal to some input element, and every input element must be less than or equal to `ret`. These facts are accumulated over the processed prefix. At the loop control point, `i` is the next index to inspect, so the processed prefix is `[0, i)`.

Planned loop invariant:

```c
/*@ Inv
      1 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      (exists j, 0 <= j && j < i && l[j] == ret) &&
      (forall (j: Z), (0 <= j && j < i) => l[j] <= ret) &&
      IntArray::full(a, n, l)
*/
for (i = 1; i < n; ++i) {
```

Initialization: after `ret = a[0]` and the `for` initialization `i = 1`, the bound `1 <= i && i <= n` follows from `1 <= n`. The existential maximum witness is `j = 0`, because `0 <= 0 < 1` and `ret` was loaded from `a[0]`, which corresponds to `l[0]`. The universal upper-bound fact over `[0, 1)` also follows from that same equality. The array heap is unchanged.

Preservation: at the loop body, the condition gives `i < n`, so `a[i]` is in bounds. If `a[i] > ret`, assigning `ret = a[i]` makes the new witness `j = i`; all older prefix elements were `<= old ret`, and `old ret < new ret`, while the new element equals the new `ret`, so the prefix property extends to `[0, i + 1)`. If `a[i] <= ret`, `ret` remains unchanged; the old existential witness is still within `[0, i + 1)`, all old prefix elements remain bounded by `ret`, and the new element is bounded by the failed branch condition. `a`, `n`, and the `IntArray::full` resource are preserved.

Exit usability: when the loop exits, `i >= n` combined with the invariant bound `i <= n` gives `i == n`. The invariant facts over `[0, i)` then become exactly the postcondition facts over `[0, n)`. A minimal loop-exit assertion should expose `i == n`, preserve unchanged parameters, restate the two maximum facts over `[0, n)`, and keep `IntArray::full(a, n, l)` for the return.

Planned loop-exit assertion:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      (exists j, 0 <= j && j < n && l[j] == ret) &&
      (forall (j: Z), (0 <= j && j < n) => l[j] <= ret) &&
      IntArray::full(a, n, l)
*/
return ret;
```
