## Annotation iteration 1

Current target:

```c
int array_sum_even_indices(int n, int *a)
/*@ With l
    Require
      0 <= n && n <= INT_MAX &&
      Zlength(l) == n &&
      ...
      IntArray::full(a, n, l)
    Ensure
      __return == array_sum_even_indices_spec(l) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int sum = 0;

    for (i = 0; i < n; ++i) {
        if (i % 2 == 0) {
            sum += a[i];
        }
    }

    return sum;
}
```

The loop has no invariant, but the postcondition requires the final return value to equal the Coq specification over the whole list and requires the input array predicate to be preserved. The control point for a C `for (i = 0; i < n; ++i)` invariant is after initialization and before checking `i < n`, so the invariant must describe the prefix `[0, i)` already processed. At that point `sum` should equal `array_sum_even_indices_spec(sublist(0, i, l))`: initially `i == 0` and the spec on the empty prefix is `0`; after one iteration the branch either adds `a[i]` for even `i` or leaves `sum` unchanged for odd `i`, matching the recursive even-index specification on the prefix extended to `i + 1`.

The array is read-only, so the invariant must keep `IntArray::full(a, n, l)` unchanged. It also explicitly records `a == a@pre` and `n == n@pre`, matching the existing array accumulation examples and preventing the return witness from needing to reconstruct unchanged parameters. The integer overflow side condition for `sum += a[i]` is intended to follow from the input contract's prefix-bound assumption for every `0 <= k <= n`, especially `k == i + 1`.

Planned annotation before the loop:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      sum == array_sum_even_indices_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
for (i = 0; i < n; ++i) { ... }
```

At loop exit, the invariant plus `!(i < n)` should give `i == n`, so a minimal loop-exit assertion will expose the whole-list postcondition:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      sum == array_sum_even_indices_spec(l) &&
      IntArray::full(a, n, l)
*/
return sum;
```

This should give symexec enough shape and pure state to generate the Coq goals: the remaining hard work, if any, should be pure list/arithmetic witness proof showing how the recursive spec changes when the prefix grows by one.
