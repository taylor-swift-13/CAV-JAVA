# Annotation Reasoning

## 2026-04-22 06:30 CST - Add prefix/suffix invariant for output array update

Current program point:

```c
int i;

for (i = 0; i < n; ++i) {
    out[i] = a[i] + b[i];
}
```

The active annotated C file initially has no `Inv` before the `for` loop and no bridge assertions around the statement `out[i] = a[i] + b[i];`. This loop writes `out` one element at a time while preserving both input arrays. The postcondition requires an existential result list `lr` of length `n` such that every index satisfies `lr[i] == la[i] + lb[i]`, plus unchanged `IntArray::full(a, n, la)` and `IntArray::full(b, n, lb)`.

The invariant should describe the loop head state, which is after `i = 0` and before checking `i < n`. At that point, `i` is the number of elements already written. I will use two existential lists:

```c
exists l1 l2,
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
```

Initialization: when `i == 0`, `l1` can be the empty prefix and `l2` can be `lo`; the computed-prefix property is vacuous and the heap shape is the original `out` full array.

Preservation: inside a body iteration, the guard gives `0 <= i && i < n@pre`. The first bridge assertion exposes `data_at` cells for `a[i]`, `b[i]`, and `out[i]` using `IntArray::missing_i`. The write updates only `out[i]`. The second bridge assertion rebuilds full arrays and introduces a new prefix `l1'` of length `i + 1`, whose last element is `la[i] + lb[i]`; the suffix becomes `sublist(i + 1, n@pre, lo)`. This matches the next loop-head invariant after `++i`.

Exit usability: when the loop exits, the invariant gives `i <= n@pre` and the negated guard gives `!(i < n)`, so `i == n@pre`. Then `Zlength(l2) == 0`, `out` is `app(l1, l2)`, and the prefix property on `l1` covers all indices in `[0, n)`, which is exactly the postcondition witness for `lr`.

I am adding these annotations to `annotated/verify_20260422_063057_array_pairwise_sum.c` before running `symexec`, because the unannotated loop does not expose enough intermediate state for the verifier to prove the array update contract.
