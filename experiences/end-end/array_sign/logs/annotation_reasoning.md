## Round 1: prefix/suffix invariant and single-write annotated copy

Program point: the only loop is `for (i = 0; i < n; ++i)` in `annotated/verify_20260422_083344_array_sign.c`. The current active annotated copy has no `Inv`, so symbolic execution has no stable loop state describing which output prefix has already been written or why the final `out` array satisfies the contract.

The contract requires an existential result list `lr` of length `n`. For every in-bounds index, `lr[i]` must be `1` when `la[i] > 0`, `-1` when `la[i] < 0`, and `0` when `la[i] == 0`. The input array `a` must remain `la`; the output array `out` is updated in place.

Planned invariant before the loop:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n@pre &&
      a == a@pre &&
      out == out@pre &&
      n == n@pre &&
      n@pre == Zlength(la) &&
      n@pre == Zlength(lo) &&
      Zlength(l1) == i &&
      Zlength(l2) == n@pre - i &&
      (forall (t: Z), (0 <= t && t < i && la[t] > 0) => l1[t] == 1) &&
      (forall (t: Z), (0 <= t && t < i && la[t] < 0) => l1[t] == -1) &&
      (forall (t: Z), (0 <= t && t < i && la[t] == 0) => l1[t] == 0) &&
      (forall (t: Z), (0 <= t && t < n@pre - i) => l2[t] == lo[i + t]) &&
      IntArray::full(a, n@pre, la) *
      IntArray::full(out, n@pre, app(l1, l2))
*/
```

Here `l1` is the processed prefix of `out`, length `i`, and `l2` is the original unprocessed suffix, length `n@pre - i`. Initialization uses `l1 = nil` and `l2 = lo`, so the processed-prefix facts are vacuous and the output heap is still the original `lo`. Preservation consumes one element from `l2`, writes the sign value, and rebuilds `out` as `app(l1', sublist(i + 1, n@pre, lo))`. Exit with `i == n` makes the suffix empty, so the invariant gives the full result list needed by the postcondition.

The original loop writes `out[i]` separately in each branch. A prior same-task verification showed that this shape makes `symexec` spend too much effort splitting and rebuilding the output array three times. I will normalize only the active annotated working copy by introducing local scalars `v` and `s`: read `v = a[i]`, compute `s` in the three-way branch, then perform a single `out[i] = s`. This preserves the same program semantics and keeps the official input contract untouched, but it gives the verifier one heap write and one prefix-extension bridge per iteration.

The bridge before the single write will expose the focused output cell:

```c
/*@ exists l1 l2, ... IntArray::full(out@pre, n@pre, app(l1, l2))
    which implies
      (la[i] > 0 => s == 1) &&
      (la[i] < 0 => s == -1) &&
      (la[i] == 0 => s == 0) &&
      IntArray::missing_i(out@pre, i, 0, n@pre, app(l1, l2)) *
      data_at(out@pre + (i * sizeof(int)), int, lo[i])
*/
```

The bridge after the write will rebuild the next invariant by existentially introducing `l1'` of length `i + 1` with the same three split implications over the extended processed prefix. The three sign cases are intentionally written as three independent quantified implications rather than one large consequent or a disjunction; this avoids the frontend's known `Multiple cases inside pre- or post-condition` and clause-explosion behavior for this task.
