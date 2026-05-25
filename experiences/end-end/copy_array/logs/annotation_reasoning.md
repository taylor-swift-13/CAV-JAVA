## 2026-04-22T13:39:04+08:00 - Add copy-prefix invariant and array-cell bridges

Current program point: the unannotated `for (i = 0; i < n; ++i)` loop in `annotated/verify_20260422_133747_copy_array.c` copies one integer cell from `src` to `dst` per iteration:

```c
for (i = 0; i < n; ++i) {
    dst[i] = src[i];
}
```

The postcondition requires `IntArray::full(src, n, ls)` and `IntArray::full(dst, n, ls)`. The source array must remain exactly `ls`, while the destination array must be transformed from its old list `ld` into the same list `ls`. Without an invariant, symbolic execution has no persistent description of which destination prefix has already been copied and which suffix is still the original `ld`, so the final destination witness cannot be reconstructed at loop exit.

Planned invariant at the `for` loop judgment point:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n@pre &&
      src == src@pre &&
      dst == dst@pre &&
      n@pre == Zlength(ls) &&
      n@pre == Zlength(ld) &&
      Zlength(l1) == i &&
      Zlength(l2) == n@pre - i &&
      (forall (k: Z), (0 <= k && k < i) => l1[k] == ls[k]) &&
      (forall (k: Z), (0 <= k && k < n@pre - i) => l2[k] == ld[i + k]) &&
      IntArray::full(src, n@pre, ls) *
      IntArray::full(dst, n@pre, app(l1, l2))
*/
```

Why this invariant should be valid:

- Initialization: after `i = 0`, choose `l1 = nil` and `l2 = ld`. The copied-prefix property is vacuous, the untouched suffix relation is `l2[k] == ld[0 + k]`, and the heap is exactly the pre-state `IntArray::full(dst, n@pre, ld)`.
- Preservation: at an iteration start with `i < n@pre`, `src` is still the full list `ls`, and `dst` is `app(l1, l2)` where `l1` has length `i` and already equals `ls[0..i)`. The assignment needs a bridge that opens `src[i]` and `dst[i]`; because `dst[i]` is the first element of the untouched suffix, its old value is `ld[i]`. After writing `src[i]`, the destination can be folded into `app(l1', sublist(i + 1, n@pre, ld))`, where `l1'` has length `i + 1` and equals `ls[0..i+1)`.
- Exit usability: when the guard fails, the invariant gives `0 <= i <= n@pre` and the failed condition gives `i >= n@pre`, so `i == n@pre`. The suffix length is then zero, and `app(l1, l2)` is just the completed copied list. The prefix fact over `0 <= k < i` becomes exactly the postcondition relation needed for `dst`.

Bridge before `dst[i] = src[i]`:

```c
/*@ exists l1 l2, ... IntArray::full(dst, n@pre, app(l1, l2))
    which implies
      IntArray::missing_i(src, i, 0, n@pre, ls) *
      data_at(src + (i * sizeof(int)), int, ls[i]) *
      IntArray::missing_i(dst, i, 0, n@pre, app(l1, l2)) *
      data_at(dst + (i * sizeof(int)), int, ld[i])
*/
```

This bridge directly exposes the two cells consumed by the C assignment. The current destination cell value is `ld[i]` because the untouched suffix starts at offset `i` and still mirrors the original destination list.

Bridge after the assignment:

```c
/*@ exists l1 l2, ... data_at(dst + (i * sizeof(int)), int, ls[i])
    which implies
      exists l1',
        Zlength(l1') == i + 1 &&
        (forall (k: Z), (0 <= k && k < i + 1) => l1'[k] == ls[k]) &&
      IntArray::full(src, n@pre, ls) *
      IntArray::full(dst, n@pre, app(l1', sublist(i + 1, n@pre, ld)))
*/
```

This bridge folds the updated destination cell back into a full destination array and advances the copied prefix by one element. It is expected to fix both the loop-state preservation problem and the final return witness problem before running `symexec`.
