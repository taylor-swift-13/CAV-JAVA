# Annotation Reasoning

## 2026-04-22 invariant for `array_replace_k`

Current annotated file before this change has the original contract but no loop invariant:

```c
for (i = 0; i < n; ++i) {
    if (a[i] == old_k) {
        a[i] = new_k;
    }
}
```

This is a single forward scan over `a[0..n)`. At the loop guard, `i` is the number of already processed elements and also the next candidate index. The postcondition requires a final list `l0` such that each original element equal to `old_k` is replaced by `new_k`, while every original element not equal to `old_k` is preserved. Therefore the loop invariant must describe the current array as a processed prefix and an untouched suffix.

The invariant to add before the `for` loop is:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n@pre &&
      a == a@pre &&
      n == n@pre &&
      old_k == old_k@pre &&
      new_k == new_k@pre &&
      n@pre == Zlength(l) &&
      Zlength(l1) == i &&
      Zlength(l2) == n@pre - i &&
      (forall (t: Z),
        (0 <= t && t < i) =>
        ((l[t] == old_k => l1[t] == new_k) &&
         (l[t] != old_k => l1[t] == l[t]))) &&
      (forall (t: Z), (0 <= t && t < n@pre - i) => l2[t] == l[i + t]) &&
      IntArray::full(a, n@pre, app(l1, l2))
*/
```

Initialization: after `i = 0`, choose `l1 = nil` and `l2 = l`. The processed-prefix quantified condition is vacuous, `Zlength(l1) == 0`, `Zlength(l2) == n@pre`, and `IntArray::full(a, n@pre, app(nil, l))` matches the precondition.

Preservation: assume the invariant at index `i` and the loop condition `i < n@pre`. The suffix condition gives the current cell value as `l[i]`. If `a[i] == old_k`, then writing `new_k` creates a new processed prefix of length `i + 1` whose new last element satisfies the first implication. If `a[i] != old_k`, no write occurs and the original value `l[i]` remains in place, satisfying the second implication for the new last prefix element. All earlier prefix facts are reused, and the suffix shifts from `l2` to `sublist(i + 1, n@pre, l)`.

Exit usability: when the loop exits, the invariant gives `0 <= i <= n@pre` and the negated loop guard gives `i >= n@pre`, so `i == n@pre`. Then `l2` has length zero and the full array is `app(l1, nil)`. The prefix property over `0 <= t < n@pre` is exactly the final elementwise relation required for the existential `l0`.
