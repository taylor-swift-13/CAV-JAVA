## 2026-04-22 08:40:36 +0800 - Prefix-sum invariant for array_sum

The active annotated file initially has no Verify annotation around the `for` loop:

```c
int i;
int ret = 0;

for (i = 0; i < n; ++i) {
    ret += a[i];
}

return ret;
```

The contract requires `__return == sum(l)` and preserves `IntArray::full(a, n, l)`.  At the `for` loop guard control point, after the `for` initializer has run and before checking `i < n`, the variable `i` is exactly the length of the already processed prefix and the next array index to read.  The accumulator should therefore be modeled as the exact sum of that processed prefix:

```c
ret == sum(sublist(0, i, l))
```

The invariant must also keep the array heap predicate and stable parameter equalities.  The function never writes `a`, and the return postcondition is over the original array/list and original length, so the invariant records:

```c
0 <= i && i <= n &&
a == a@pre &&
n == n@pre &&
ret == sum(sublist(0, i, l)) &&
IntArray::full(a, n, l)
```

Initialization: after `ret = 0` and the `for` initializer `i = 0`, the processed prefix is `sublist(0, 0, l)`, whose sum is 0, so `ret == sum(sublist(0, i, l))` matches the concrete state.

Preservation: during one iteration, the body reads `a[i]` and executes `ret += a[i]`.  Under the invariant and loop guard, `0 <= i < n`, so the array read is within `IntArray::full(a, n, l)`.  The next loop guard point has `i + 1` processed elements, and the accumulator should equal `sum(sublist(0, i + 1, l))`, which is the old prefix sum plus `l[i]`.  The array is read-only, so `IntArray::full(a, n, l)` remains unchanged.

Exit usability: when the loop exits, the invariant gives `0 <= i <= n` and the negated guard gives `!(i < n)`, so `i == n`.  A loop-exit assertion immediately after the loop records the whole-list form needed by the postcondition:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      ret == sum(l) &&
      IntArray::full(a, n, l)
*/
return ret;
```

This annotation should let `symexec` generate the usual prefix-extension VC for `sum(sublist(0, i + 1, l))` and a final return witness over the full preserved array.
