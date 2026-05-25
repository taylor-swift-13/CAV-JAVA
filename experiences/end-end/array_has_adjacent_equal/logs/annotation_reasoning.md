## 2026-04-22T05:00:00+08:00 - Initial loop invariant for adjacent-equality scan

The active annotated file initially matches the contract input exactly and has no `Inv` before:

```c
for (i = 1; i < n; ++i) {
    if (a[i] == a[i - 1]) {
        return 1;
    }
}

return 0;
```

This loop is a read-only scan over adjacent pairs. At the loop-head control point, `i` is the next adjacent-pair right index to inspect, and the processed prefix is the set of indices `j` with `1 <= j < i`. If the function has not returned yet, every processed adjacent pair must be unequal:

```c
(forall (j: Z), (1 <= j && j < i) => l[j] != l[j - 1])
```

The invariant also has to preserve the unchanged parameters and the full array permission:

```c
a == a@pre &&
n == n@pre &&
IntArray::full(a, n, l)
```

The boundary needs care because `for (i = 1; i < n; ++i)` initializes `i` before checking the guard. The precondition allows `n == 0`, so `i <= n` is false at the first loop-head state when `n == 0`. A stable bound is instead:

```c
1 <= i && i <= n + 1
```

For initialization, `i == 1`, the quantified processed-prefix condition is vacuous, and `1 <= i <= n + 1` follows from `0 <= n`. For preservation, the loop body only reaches `++i` when the guard gives `i < n`; the false branch of `if (a[i] == a[i - 1])` establishes the new adjacent inequality at index `i`, so after incrementing, all indices `1 <= j < i + 1` are known unequal. For early return, the true branch has `1 <= i && i < n && l[i] == l[i - 1]`, which provides the existential witness required by the `__return == 1` postcondition.

After the loop exits, the negated guard gives `!(i < n)`, and the invariant gives all processed pairs below `i`. The postcondition for `return 0` needs:

```c
(forall (j: Z), (1 <= j && j < n) => l[j] != l[j - 1])
```

This follows because every `j < n` is also below the final `i`. I will add a loop-exit `Assert` with this exact return-oriented universal fact, directly before `return 0`, so `symexec` can use it without reconstructing the guard arithmetic at local-variable cleanup time.

## 2026-04-22T05:01:00+08:00 - Remove misplaced loop-exit assertion after local-permission failure

The first `symexec` run after adding the invariant and loop-exit assertion failed before proof generation with:

```text
fatal error: Error: Fail to Remove Memory Permission of i:96 in
annotated/verify_20260422_045045_array_has_adjacent_equal.c:40:4
Address found : nullCurrent assertion is :
```

The failure points to the assertion immediately before `return 0`:

```c
/*@ Assert
      a == a@pre &&
      n == n@pre &&
      (forall (j: Z), (1 <= j && j < n) => l[j] != l[j - 1]) &&
      IntArray::full(a, n, l)
*/
return 0;
```

This matches the documented assertion pitfall: a loop-exit assertion placed too late can disrupt removal of the local variable permission for `i`. The invariant already carries:

```c
1 <= i && i <= n + 1 &&
(forall (j: Z), (1 <= j && j < i) => l[j] != l[j - 1]) &&
IntArray::full(a, n, l)
```

At loop exit, `!(i < n)` is enough to bridge any `j < n` into `j < i`, so the explicit exit assertion is not necessary. I will remove only that `Assert`, keep the invariant unchanged, clear generated Coq files, and rerun `symexec`.
