## 2026-04-22 23:59 Annotation iteration 1

Current program point:

```c
int i = 0;

while (1) {
    if (src[i] == 0) {
        break;
    }
    dst[i] = src[i];
    i++;
}
dst[i] = 0;
```

The loop has no invariant in the input annotation, but it reads `src[i]`, copies each nonzero source character to `dst[i]`, and exits only when `src[i] == 0`. The postcondition requires preserving the full source buffer and changing the whole destination buffer to `app(l, cons(0, nil))`. Therefore the loop invariant must retain both heap resources and say that the destination prefix already equals the processed source prefix.

Planned invariant:

```c
/*@ Inv exists l1 d1,
      0 <= i && i <= n &&
      src == src@pre &&
      dst == dst@pre &&
      Zlength(l1) == i &&
      Zlength(d1) == n + 1 - i &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      (forall (k: Z), (0 <= k && k < i) => l1[k] == l[k]) &&
      CharArray::full(src, n + 1, app(l, cons(0, nil))) *
      CharArray::full(dst, n + 1, app(l1, d1))
*/
```

Initialization: before the first loop test, `i == 0`, so choose `l1 == nil` and `d1 == d`; the destination is still the original `CharArray::full(dst, n + 1, d)`, and the copied-prefix condition is vacuous.

Preservation: if `src[i] != 0`, the precondition's nonzero-prefix fact and the source heap imply the current character is the `i`th element of `l` for `i < n`; writing `dst[i] = src[i]` extends the destination prefix from `l1` to a one-character-longer prefix matching `l`, while `i++` makes `Zlength(l1') == i + 1`. The source heap and pointer equalities are unchanged.

Exit usability: when `src[i] == 0`, the invariant plus the nonzero-prefix property should force `i == n`, because all `0 <= k < n` source characters are nonzero and the terminator is at index `n`. The final `dst[i] = 0` then appends the terminator after the copied prefix, which should match `app(l, cons(0, nil))`. If `symexec` cannot derive `i == n` automatically, the next annotation iteration should add a minimal loop-exit assertion immediately after the loop.
