## 2026-04-22 02:36:18 +0800 - Initial loop invariant for in-place clamp

Program point: the only loop is `for (i = 0; i < n; ++i)` in `array_clamp_nonnegative`. The input contract gives `0 <= n`, `Zlength(l) == n`, and `IntArray::full(a, n, l)`. The postcondition needs an existential result list `l0` of length `n` such that every index in `[0,n)` is mapped by the clamp relation: original negative values become `0`, and original nonnegative values remain unchanged. The function mutates `a` in place and has no scalar return.

The unannotated loop has no invariant, so symbolic execution would not have a persistent description of the already processed prefix after the first iteration. The natural loop control point for a C `for` invariant is after `i = 0` initialization and before the loop condition. At that point, `i` is the next index to process. Therefore the invariant should describe two regions of the current array contents:

```c
/* processed prefix: 0 <= k < i */
(forall (k: Z), (0 <= k && k < i && l[k] < 0) => lc[k] == 0)
(forall (k: Z), (0 <= k && k < i && l[k] >= 0) => lc[k] == l[k])

/* untouched suffix: i <= k < n@pre */
(forall (k: Z), (i <= k && k < n@pre) => lc[k] == l[k])
```

The invariant will existentially quantify `lc`, the current logical contents of `a`, and keep the unchanged parameters and bounds:

```c
/*@ Inv exists lc,
      0 <= i && i <= n@pre &&
      n == n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      Zlength(lc) == n@pre &&
      ...prefix clamp facts... &&
      ...suffix unchanged fact... &&
      IntArray::full(a, n@pre, lc)
*/
```

Initialization: before the first condition check, `i == 0`, so the processed-prefix implications are vacuous. The suffix fact covers all valid indices and is satisfied by choosing `lc = l` from the precondition heap.

Preservation: at the start of an iteration, `i < n@pre`. The suffix fact gives `lc[i] == l[i]`, so the branch test `a[i] < 0` is testing the original value at index `i`. If the branch writes `0`, then the new array contents satisfy the negative case at index `i`; if the branch does not write, the branch condition gives the nonnegative case and the value remains `l[i]`. Existing prefix facts for `k < i` are preserved, and the untouched suffix for the next iteration begins at `i + 1`.

Exit usability: when the loop exits, the invariant plus `!(i < n)` and `0 <= i <= n@pre` should establish `i == n@pre`. Then every valid index is in the processed prefix, so `lc` directly serves as the existential `l0` in the postcondition. A small loop-exit `Assert` may be useful to expose `i == n` and the full-range clamp facts to the return witness.
