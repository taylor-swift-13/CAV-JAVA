## Annotation iteration 1

Program point: the `while (left < right)` loop in `annotated/verify_20260422_093407_binary_search_last.c` currently has no `Inv`, so symexec would not have a stable loop summary for the upper-bound binary-search state. The loop maintains a search window `[left, right)` in a sorted list `l`: elements strictly before `left` have been proved `<= target`, and elements from `right` to `n` have been proved `target < l[i]`.

Current C fragment before the edit:

```c
while (left < right) {
    mid = left + (right - left) / 2;
    if (a[mid] <= target) {
        left = mid + 1;
    } else {
        right = mid;
    }
}
```

Planned invariant and assertion:

```c
/*@ Inv
      0 <= n && n <= INT_MAX && Zlength(l) == n &&
      sorted nondecreasing relation on l &&
      0 <= left && left <= right && right <= n &&
      a == a@pre && n == n@pre && target == target@pre &&
      (forall i, 0 <= i && i < left => l[i] <= target) &&
      (forall i, right <= i && i < n => target < l[i]) &&
      IntArray::full(a, n, l)
*/
while (left < right) {
    mid = left + (right - left) / 2;
    /*@ Assert ... 0 <= mid && mid < n && left <= mid && mid < right ... */
```

Why this should initialize: initially `left == 0` and `right == n`, so both quantified ranges are empty, `0 <= left <= right <= n` follows from the precondition, and the array ownership is exactly the required `IntArray::full(a, n, l)`.

Why this should be preserved: if `a[mid] <= target`, sortedness gives every index `i <= mid` has `l[i] <= l[mid] <= target`, so after `left = mid + 1` the prefix fact remains true while the suffix fact is unchanged. If `a[mid] > target`, sortedness gives every index `i >= mid` has `target < l[i]`, so after `right = mid` the suffix fact remains true while the prefix fact is unchanged.

Why this should support exit: on loop exit, `left == right`. The invariant says all positions before `left` are `<= target` and all positions from `left` onward are `> target`. If `left > 0` and `l[left - 1] == target`, returning `left - 1` satisfies the last-occurrence postcondition because every larger index is in the `> target` suffix. If the final branch fails, either `left == 0`, making the whole array `> target`, or `left > 0` and `l[left - 1] != target`; combined with `l[left - 1] <= target` and sortedness, the entire prefix is `< target`, while the suffix is `> target`, so no element equals `target`.

This edit mirrors the repository example `examples/binary_search_first/annotated/binary_search_first.c`, with the comparison directions flipped for last occurrence / upper-bound search.

