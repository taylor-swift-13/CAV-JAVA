# Annotation Reasoning

## Initial loop invariant for distinct-run scan

Context: the active file is `annotated/verify_20260422_030111_array_count_distinct_sorted.c`.  The input contract is trusted and states that `l` has length `n`, `0 <= n <= INT_MAX`, the array is sorted by the pairwise condition

```c
(forall (i: Z) (j: Z),
  (0 <= i && i <= j && j < n) => l[i] <= l[j])
```

and the function must preserve `IntArray::full(a, n, l)` while returning `array_count_distinct_sorted_spec(l)`.

The unannotated loop is:

```c
int count = 1;
int i = 1;
while (i < n) {
    if (a[i] != a[i - 1]) {
        count++;
    }
    i++;
}
return count;
```

At the loop guard, `i` is the length of the already processed prefix `sublist(0, i, l)`.  Because the `n == 0` branch has already returned, initialization reaches the loop only with `n > 0`, `i == 1`, and `count == 1`.  This matches the Coq spec on a one-element prefix: `array_count_distinct_sorted_spec(sublist(0, 1, l)) == 1`.

The invariant to add immediately before `while (i < n)` is:

```c
/*@ Inv
      1 <= i && i <= n &&
      1 <= count && count <= i &&
      a == a@pre &&
      n == n@pre &&
      count == array_count_distinct_sorted_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
```

Why this should be sufficient:

- Initialization: after `count = 1; i = 1;`, the nonzero branch gives `1 <= i <= n`; the full array resource is unchanged; `a` and `n` still equal their pre-state values; and the one-element prefix has distinct count `1`.
- Preservation: each iteration reads `a[i]` and `a[i - 1]` under `i < n`, then increments `count` exactly in the same case where the spec for extending the processed prefix by `l[i]` adds one distinct run.  The array is read-only, so `IntArray::full(a, n, l)` remains stable.
- Exit: when the loop exits, invariant plus `!(i < n)` gives `i == n`; therefore the invariant equality rewrites `count` to `array_count_distinct_sorted_spec(sublist(0, n, l))`, which should reduce to `array_count_distinct_sorted_spec(l)` using `Zlength(l) == n`.

No separate loop-exit assertion is added in this first attempt because the invariant already contains the return-level semantic equality and `i == n` should be derivable from the invariant bounds and loop exit condition.
