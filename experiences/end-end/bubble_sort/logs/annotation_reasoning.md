## 2026-04-22 13:01 +0800 - Initial nested-loop invariant plan

Program point: `bubble_sort` has two nested `for` loops in `annotated/verify_20260422_130100_bubble_sort.c`:

```c
for (i = 0; i < n; ++i) {
    for (j = 0; j + 1 < n - i; ++j) {
        if (a[j] > a[j + 1]) {
            int t = a[j];
            a[j] = a[j + 1];
            a[j + 1] = t;
        }
    }
}
```

The active annotated copy currently has no `Inv` before either loop. This is not enough for symbolic execution: the function mutates the `IntArray::full(a, n, l)` heap resource by adjacent swaps, and the postcondition needs both a sorted final list and `Permutation(l, l0)`. Without loop invariants, there is no stable ghost list for the current array contents, no proof that adjacent swaps preserve permutation, and no relation explaining why the suffix accumulated by bubble-sort passes is sorted.

Planned outer-loop annotation:

```c
/*@ Inv exists lc,
      0 <= i && i <= n@pre &&
      n == n@pre &&
      a == a@pre &&
      Zlength(l) == n@pre &&
      Zlength(lc) == n@pre &&
      Permutation(l, lc) &&
      (forall (p: Z) (q: Z),
        (n@pre - i <= p && p <= q && q < n@pre) => lc[p] <= lc[q]) &&
      (forall (p: Z) (q: Z),
        (0 <= p && p < n@pre - i && n@pre - i <= q && q < n@pre) => lc[p] <= lc[q]) &&
      IntArray::full(a, n@pre, lc)
*/
```

At the outer-loop head, `i` is the number of completed passes. The suffix `[n - i, n)` is already sorted, and every element still in the unsorted prefix `[0, n - i)` is no greater than every element in that suffix. Initialization holds with `i == 0` and `lc = l`: the suffix is empty, the cross-boundary condition is vacuous, `Permutation(l, l)` is available as a pure Coq obligation, and the original `IntArray::full(a, n, l)` supplies the heap. Preservation will follow from the inner loop moving the maximum of the current prefix into index `n - i - 1`, thereby extending the sorted suffix leftward by one. Exit is direct: `i == n`, so the suffix is the whole array and the first quantified condition is exactly the sortedness relation required by the postcondition; `Permutation(l, lc)` and `IntArray::full(a, n, lc)` supply the remaining postcondition witness.

Planned inner-loop annotation:

```c
/*@ Inv exists lc,
      0 <= j && j + 1 <= n@pre - i &&
      0 <= i && i < n@pre &&
      n == n@pre &&
      a == a@pre &&
      Zlength(l) == n@pre &&
      Zlength(lc) == n@pre &&
      Permutation(l, lc) &&
      (forall (p: Z) (q: Z),
        (n@pre - i <= p && p <= q && q < n@pre) => lc[p] <= lc[q]) &&
      (forall (p: Z) (q: Z),
        (0 <= p && p < n@pre - i && n@pre - i <= q && q < n@pre) => lc[p] <= lc[q]) &&
      (forall (p: Z), (0 <= p && p < j) => lc[p] <= lc[j]) &&
      IntArray::full(a, n@pre, lc)
*/
```

At the inner-loop head, `j` is the right edge of the already scanned prefix for the current pass. The local fact `forall p, 0 <= p < j => lc[p] <= lc[j]` states that `a[j]` is the maximum among positions already crossed by the adjacent-swap sweep. It initializes vacuously at `j == 0`. In the branch `a[j] > a[j + 1]`, swapping makes the old maximum become the new `a[j + 1]`; in the else branch, `a[j + 1]` was already at least `a[j]`, so it becomes the new maximum for the enlarged scanned prefix. The loop only touches positions before `n - i`, so the existing sorted suffix and prefix-to-suffix ordering from the outer invariant remain valid. On inner-loop exit, `j + 1 == n - i`; the local maximum fact and the cross-boundary ordering show that position `n - i - 1` can be prepended to the sorted suffix for the next outer iteration.

I will add only these two invariants in the active annotated copy, then clear any old generated files and run `symexec`. If symbolic execution succeeds and leaves pure permutation / adjacent-swap obligations, those belong to the manual Coq proof phase rather than another annotation change.
