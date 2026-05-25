## 2026-04-22 15:13:24 CST - Initial loop invariant for count_equal_to_k

Current annotated C has no `Inv` before the loop:

```c
int i;
int ret = 0;

for (i = 0; i < n; ++i) {
    if (a[i] == k) {
        ret++;
    }
}

return ret;
```

The program point that needs annotation is the `for (i = 0; i < n; ++i)` loop.  At the loop guard, `i` is the number of array elements already processed and also the next array index to inspect.  The accumulator `ret` must equal the specification applied to the processed prefix, namely `count_equal_to_k_spec(sublist(0, i, l), k)`.  The input array is read-only, so the invariant must keep `IntArray::full(a, n, l)` unchanged.  The scalar parameters `a`, `n`, and `k` are not assigned in the function; keeping `a == a@pre`, `n == n@pre`, and `k == k@pre` prevents the return witness from having to reconstruct parameter preservation later.

Planned invariant:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      k == k@pre &&
      ret == count_equal_to_k_spec(sublist(0, i, l), k) &&
      IntArray::full(a, n, l)
*/
for (i = 0; i < n; ++i) {
    if (a[i] == k) {
        ret++;
    }
}
```

Initialization should hold after `i = 0` and before the first guard: `0 <= 0 <= n` follows from the precondition `0 <= n`, `ret == 0`, and `count_equal_to_k_spec(sublist(0, 0, l), k)` is the empty-prefix count.  Preservation should split on `a[i] == k`: in the true branch `ret++` matches adding one for the newly processed element, and in the false branch `ret` remains the count for the longer prefix because the new element contributes zero.  The array memory remains full because the loop only reads `a[i]`.

The postcondition needs `ret == count_equal_to_k_spec(l, k)` and `IntArray::full(a, n, l)`.  On loop exit the guard gives `!(i < n)`, and the invariant gives `i <= n`, so `i == n`.  I will add a loop-exit `Assert` immediately after the loop so the return witness receives the normalized facts `i == n`, `k == k@pre`, and `ret == count_equal_to_k_spec(l, k@pre)`:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      k == k@pre &&
      ret == count_equal_to_k_spec(l, k@pre) &&
      IntArray::full(a, n, l)
*/
return ret;
```

This assertion is placed directly after the loop, before local variable cleanup around `return`, matching the documented loop-exit assertion pattern and avoiding a late assertion that would interfere with local permissions.
