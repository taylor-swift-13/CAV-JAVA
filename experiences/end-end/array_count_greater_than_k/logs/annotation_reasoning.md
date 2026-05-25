## 2026-04-22 03:23:00 +0800 - Prefix-count invariant for array_count_greater_than_k

The active annotated file initially copied the contract input exactly and had no Verify annotation around the `for` loop:

```c
int i;
int cnt = 0;

for (i = 0; i < n; ++i) {
    if (a[i] > k) {
        cnt++;
    }
}

return cnt;
```

The contract requires the return value to equal `array_count_greater_than_k_spec(l, k@pre)` while preserving `IntArray::full(a, n, l)`. The loop is a left-to-right read-only scan. At the loop guard control point for `for (i = 0; i < n; ++i)`, `i` is the number of already processed elements and the next index that will be read if the guard succeeds. Therefore the accumulator invariant should state the exact count for the processed prefix:

```c
cnt == array_count_greater_than_k_spec(sublist(0, i, l), k)
```

The invariant also needs bounds for safe array access and exit reasoning, stable parameter equalities for the postcondition's `@pre` references, and the unchanged array ownership:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      k == k@pre &&
      cnt == array_count_greater_than_k_spec(sublist(0, i, l), k) &&
      IntArray::full(a, n, l)
*/
```

Initialization: after `cnt = 0` and the `for` initialization sets `i = 0`, the processed prefix is `sublist(0, 0, l)`, so the Coq spec unfolds to `0` and matches `cnt`.

Preservation: assuming the invariant at the start of an iteration with `i < n`, the body reads `a[i]`. If `a[i] > k`, `cnt++` corresponds to the new element contributing `1` to the prefix count. If `a[i] <= k`, `cnt` is unchanged and the new element contributes `0`. The array is not written, and `n`, `a`, and `k` are not assigned, so the heap predicate and stable parameter facts remain valid.

Exit usability: when the loop exits, `i < n` is false and the invariant has `i <= n`, so `i == n`. A minimal loop-exit assertion directly records the final prefix count as the whole-list count and keeps the array predicate before local-variable cleanup:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      k == k@pre &&
      cnt == array_count_greater_than_k_spec(l, k@pre) &&
      IntArray::full(a, n, l)
*/
return cnt;
```

This annotation should allow symbolic execution to generate the prefix-extension and final-return witnesses. Any remaining difficulty is expected to be pure Coq reasoning about `array_count_greater_than_k_spec`, `sublist`, and the branch condition `a[i] > k`.
