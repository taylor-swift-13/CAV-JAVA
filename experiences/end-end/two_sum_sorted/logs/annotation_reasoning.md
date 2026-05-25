## Initial two-pointer invariant

The active annotated file `annotated/verify_20260423_052427_two_sum_sorted.c` currently has no `Inv` before:

```c
while (left < right) {
    s = a[left] + a[right];
    if (s == target) {
        return 1;
    }
    if (s < target) {
        left++;
    } else {
        right--;
    }
}
```

Without an invariant, symbolic execution has no persistent semantic fact describing which pairs have already been ruled out. The postcondition for `return 0` needs:

```c
forall (i: Z) (j: Z),
  (0 <= i && i < j && j < n) => l[i] + l[j] != target
```

The two-pointer algorithm maintains a remaining interval `[left, right]`. Two eliminated regions are enough:

```c
(forall (i: Z) (j: Z),
  (0 <= i && i < left && i < j && j < n) => l[i] + l[j] != target)
(forall (i: Z) (j: Z),
  (0 <= i && i < j && j < n && right < j) => l[i] + l[j] != target)
```

Initialization holds because `left == 0` makes the first eliminated region empty and `right == n - 1` makes the second region empty. Bounds must allow the empty-loop case `n == 0`, so `right` is allowed to be `-1`, and the stable relationship is `left <= right + 1`.

For preservation, if `s < target`, then `left` increments. For the newly eliminated index `old_left`, any `j <= old_right` has `l[j] <= l[old_right]` by sortedness, so `l[old_left] + l[j] <= s < target`; any `j > old_right` was already covered by the right-eliminated fact. If `s > target`, then `right` decrements. For the newly eliminated index `old_right`, any `i >= old_left` has `l[old_left] <= l[i]`, so `s < = l[i] + l[old_right]` and `target < l[i] + l[old_right]`; any `i < old_left` was already covered by the left-eliminated fact. The `s == target` branch returns `1` and uses the loop bounds `0 <= left < right < n` as the witness pair.

On loop exit, the negated condition gives `left >= right`. Together with `left <= right + 1`, every valid pair `i < j` is covered by one of the eliminated regions: if `i < left`, the first fact applies; otherwise `left <= i`, so `right < j`, and the second fact applies. This should make the final `return 0` witness semantic rather than requiring a separate exit assertion. The invariant also preserves the sortedness, pair-sum overflow guard, unchanged C parameters, and `IntArray::full(a, n, l)` heap resource needed for array reads and final memory preservation.
