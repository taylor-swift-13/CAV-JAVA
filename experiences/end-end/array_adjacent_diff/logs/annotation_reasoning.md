## 2026-04-22 annotation iteration 1

Program point: the single `for (i = 0; i + 1 < n; ++i)` loop in `array_adjacent_diff` currently has no loop invariant. `symexec` cannot verify a loop without an invariant that describes the heap and the processed prefix of `out`.

Relevant original C/contract fragment:
```c
for (i = 0; i + 1 < n; ++i) {
    out[i] = a[i + 1] - a[i];
}
```

The postcondition requires an existential result list `lr` of length `n - 1` such that every index `0 <= i < n - 1` contains `la[i + 1] - la[i]`, while preserving `IntArray::full(a, n, la)`. During the loop, `i` is the next output index and also the length of the processed prefix. The invariant should therefore keep a witness list `l1` for `out[0..i)`, leave `out[i..n-1)` equal to the old `lo` suffix, and keep the input array unchanged.

Planned invariant fragment:
```c
/*@ Inv exists l1,
      0 <= i && i <= n@pre - 1 &&
      a == a@pre &&
      out == out@pre &&
      n == n@pre &&
      n@pre == Zlength(la) &&
      n@pre - 1 == Zlength(lo) &&
      Zlength(l1) == i &&
      (forall (k: Z), (0 <= k && k < i) => l1[k] == la[k + 1] - la[k]) &&
      IntArray::full(a, n@pre, la) *
      IntArray::full(out, n@pre - 1, app(l1, sublist(i, n@pre - 1, lo)))
*/
```

Why this should work: initialization uses `i == 0`, `l1 == nil`, and `app(nil, sublist(0, n - 1, lo)) == lo`, so the original `out` resource matches. The body writes exactly index `i`, extending the prefix with `la[i + 1] - la[i]`; the precondition overflow guard covers the subtraction because the loop guard gives `i + 1 < n`, equivalent to `i < n - 1` for integer indices. Preservation keeps `a`, `out`, and `n` tied to their pre-state values so the return witness is not polluted by changed parameters. On exit, the invariant and the negated guard imply `i == n - 1`, so `l1` is the final result list and the remaining suffix is empty.

