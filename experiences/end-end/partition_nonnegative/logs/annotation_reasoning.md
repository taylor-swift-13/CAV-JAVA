## 2026-04-22 20:47:00 +0800 - Initial two-pointer partition invariant

The active annotated file initially matches the input C exactly and has no `Inv` before the only loop:

```c
int i = 0;
int j = n - 1;
int tmp;

while (i <= j) {
    if (a[i] < 0) {
        i++;
    } else {
        tmp = a[i];
        a[i] = a[j];
        a[j] = tmp;
        j--;
    }
}

return i;
```

Without an invariant, symbolic execution has no durable facts for the return postcondition. The postcondition requires the return value to be a partition boundary, the final array to still have length `n@pre`, the left segment to contain only negative values, the right segment to contain only nonnegative values, the final list to be a permutation of the original input list `l`, and the heap to still be `IntArray::full(a, n@pre, lr)`.

The loop has the standard partition shape. At the loop head, `i` is the first not-yet-classified position from the left and `j` is the first not-yet-classified position from the right. Therefore the processed prefix is `[0, i)`, the processed suffix is `(j, n)`, and the unprocessed middle is `[i, j]` when `i <= j`. I will represent the current heap list by an existential `lc` and preserve exactly the facts needed by both branches:

```c
/*@ Inv exists lc,
      0 <= i && i <= j + 1 &&
      j < n@pre &&
      -1 <= j &&
      n == n@pre &&
      a == a@pre &&
      Zlength(l) == n@pre &&
      Zlength(lc) == n@pre &&
      (forall (k: Z), (0 <= k && k < i) => lc[k] < 0) &&
      (forall (k: Z), (j < k && k < n@pre) => lc[k] >= 0) &&
      Permutation(l, lc) &&
      IntArray::full(a, n@pre, lc)
*/
while (i <= j) {
```

Initialization is valid when `i == 0` and `j == n - 1`: the prefix and suffix predicates are vacuous, `Zlength(lc) == n@pre` is provided by the precondition with `lc = l`, and `Permutation(l, l)` is reflexive. The edge case `n == 0` gives `j == -1`, so `0 <= i && i <= j + 1` and `-1 <= j && j < n@pre` both hold and the loop is skipped.

The `a[i] < 0` branch increments `i`. Under the loop guard, old `i <= j`, so `i` is in bounds; adding `lc[i] < 0` extends the processed prefix, and the suffix and permutation facts are unchanged.

The `else` branch has `a[i] >= 0`, swaps `a[i]` with `a[j]`, and decrements `j`. The new suffix is old `(j, n)` plus old position `i` now written at old position `j`, so it satisfies the nonnegative suffix predicate. The prefix `[0, i)` is untouched. The list changes by a swap, so the invariant keeps the abstract `Permutation(l, lc)` fact rather than trying to express the exact swap in C annotation.

On loop exit, `!(i <= j)` plus `i <= j + 1` gives `i == j + 1`. The prefix predicate directly gives all returned-left elements negative. The suffix predicate applies to every `k` with `i <= k < n@pre` because then `j < k`, giving all returned-right elements nonnegative. This should make the return VC a small combination of range arithmetic, array ownership, and permutation reasoning.
