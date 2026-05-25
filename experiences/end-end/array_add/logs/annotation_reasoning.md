## 2026-04-22T01:43:53+08:00 - Add prefix invariant and array-access bridges

Current program point: the unannotated `for (i = 0; i < n; ++i)` loop in `annotated/verify_20260422_014304_array_add.c` writes one output cell per iteration:

```c
for (i = 0; i < n; ++i) {
    out[i] = a[i] + b[i];
}
```

The postcondition requires an existential output list `lr` with `Zlength(lr) == n` and `forall i, 0 <= i < n => lr[i] == la[i] + lb[i]`, while preserving the full heap ownership of `a` and `b` and returning full ownership of `out`. Without a loop invariant, symbolic execution has no durable description of the already-written output prefix or the untouched suffix, so the final `lr` witness cannot be reconstructed from the loop state.

Planned invariant at the `for` loop judgment point:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n@pre &&
      a == a@pre &&
      b == b@pre &&
      out == out@pre &&
      n@pre == Zlength(la) &&
      n@pre == Zlength(lb) &&
      n@pre == Zlength(lo) &&
      Zlength(l1) == i &&
      Zlength(l2) == n@pre - i &&
      (forall (k: Z), (0 <= k && k < i) => l1[k] == la[k] + lb[k]) &&
      (forall (k: Z), (0 <= k && k < n@pre - i) => l2[k] == lo[i + k]) &&
      IntArray::full(a, n@pre, la) *
      IntArray::full(b, n@pre, lb) *
      IntArray::full(out, n@pre, app(l1, l2))
*/
```

Why this invariant should be valid:

- Initialization: after `i = 0`, choose `l1 = nil` and `l2 = lo`. The prefix relation is vacuous, the suffix relation is exactly `lo[0 + k]`, and `IntArray::full(out, n@pre, app(nil, lo))` matches the pre-state output array.
- Preservation: at the start of an iteration with `i < n@pre`, `out` is `app(l1, l2)`, where the prefix `l1` already contains sums and the suffix `l2` mirrors the original `lo` from offset `i`. Reading `a[i]`, `b[i]`, and `out[i]` requires a `missing_i` bridge for each array. After assigning `out[i] = la[i] + lb[i]`, the output can be folded back into `app(l1', sublist(i + 1, n@pre, lo))`, where `l1'` is the old prefix plus the new sum cell.
- Exit usability: when the loop exits, the invariant gives `0 <= i <= n@pre` and the failed guard gives `i >= n@pre`, hence `i == n@pre`. Then `l2` has length `0`, `app(l1, l2)` is the completed output, and the prefix relation over `0 <= k < i` becomes the required postcondition relation over `0 <= k < n`.

Bridge before `out[i] = a[i] + b[i]`:

```c
/*@ exists l1 l2, ... IntArray::full(out, n@pre, app(l1, l2))
    which implies
      IntArray::missing_i(a, i, 0, n@pre, la) *
      data_at(a + (i * sizeof(int)), int, la[i]) *
      IntArray::missing_i(b, i, 0, n@pre, lb) *
      data_at(b + (i * sizeof(int)), int, lb[i]) *
      IntArray::missing_i(out, i, 0, n@pre, app(l1, l2)) *
      data_at(out + (i * sizeof(int)), int, lo[i])
*/
```

This bridge directly exposes the three cells consumed by the C assignment. The current output cell value is `lo[i]` because the suffix relation says `l2[0] == lo[i]` and `Zlength(l1) == i`.

Bridge after the assignment:

```c
/*@ exists l1 l2, ... data_at(out + (i * sizeof(int)), int, la[i] + lb[i])
    which implies
      exists l1',
        Zlength(l1') == i + 1 &&
        (forall (k: Z), (0 <= k && k < i + 1) => l1'[k] == la[k] + lb[k]) &&
      IntArray::full(a, n@pre, la) *
      IntArray::full(b, n@pre, lb) *
      IntArray::full(out, n@pre, app(l1', sublist(i + 1, n@pre, lo)))
*/
```

This bridge folds the isolated cell back into a full output array and advances the prefix by one element. It is expected to fix the missing loop-state and array-cell decomposition problems before running `symexec`.
