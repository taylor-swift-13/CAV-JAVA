## 2026-04-22T02:07:48+08:00 - First loop invariant for read-only universal array scan

Current annotated C before this change has no `Inv` before the `for` loop:

```c
int i;

for (i = 0; i < n; ++i) {
    if (a[i] >= k) {
        return 0;
    }
}

return 1;
```

This is not enough for Verify because the function postcondition has two semantic cases:

```c
(__return == 1 &&
  (forall (i: Z), (0 <= i && i < n) => l[i] < k)) ||
(__return == 0 &&
  (exists i, 0 <= i && i < n && l[i] >= k))
```

At the loop head, `i` is the next index to inspect, so the already processed segment is exactly the prefix `l[0..i)`. The invariant must preserve:

- bounds: `0 <= i && i <= n@pre`;
- unchanged scalar/pointer parameters needed at return: `n == n@pre`, `a == a@pre`, and `k == k@pre`;
- the original input length fact: `n@pre == Zlength(l)`;
- the read-only heap resource: `IntArray::full(a, n@pre, l)`;
- the processed-prefix fact: every `j` in `0 <= j < i` satisfies `l[j] < k@pre`.

Planned annotation:

```c
/*@ Inv
      0 <= i && i <= n@pre &&
      n == n@pre &&
      a == a@pre &&
      k == k@pre &&
      n@pre == Zlength(l) &&
      (forall (j: Z), (0 <= j && j < i) => l[j] < k@pre) &&
      IntArray::full(a, n@pre, l)
*/
for (i = 0; i < n; ++i) {
    if (a[i] >= k) {
        return 0;
    }
}
```

Initialization should hold after `i = 0`: `0 <= 0 <= n@pre` follows from the function precondition `0 <= n`, the prefix property is vacuous, and the full array resource is exactly the function precondition resource.

Preservation should hold on the path that continues past the `if`: the loop guard gives `i < n`, the false branch of `a[i] >= k` gives `a[i] < k`, and the array read connects `a[i]` to `l[i]`; therefore the prefix property extends from `j < i` to `j < i + 1`. The heap stays `IntArray::full(a, n@pre, l)` because the loop only reads `a[i]`.

Exit usability should hold without a separate loop-exit assertion in the first attempt: the loop exits when `i < n` is false, and together with `i <= n@pre` and `n == n@pre` this should establish `i == n`; substituting into the prefix property yields the universal postcondition for the `return 1` path. On the early `return 0` path, the current index `i` is within bounds by the invariant and loop guard, and the true branch condition plus the array read should provide the existential witness for an element `>= k`.
