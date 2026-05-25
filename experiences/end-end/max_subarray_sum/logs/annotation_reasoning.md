# Annotation reasoning: max_subarray_sum

## 2026-04-22 initial loop invariant

The target loop is:

```c
int cur = a[0];
int best = a[0];

for (i = 1; i < n; ++i) {
    if (cur + a[i] < a[i]) {
        cur = a[i];
    } else {
        cur = cur + a[i];
    }
    if (best < cur) {
        best = cur;
    }
}

return best;
```

At the `for (i = 1; i < n; ++i)` loop-check point, the next array cell to process is `i`; therefore the processed prefix is `sublist(0, i, l)` and the unprocessed suffix is `sublist(i, n, l)`. The Coq model starts from the first element and folds over the remaining list:

```coq
max_subarray_sum_spec l =
  match l with
  | nil => 0
  | x :: xs => max_subarray_sum_acc x x xs
  end.
```

Since the C precondition has `1 <= n` and `Zlength(l) == n`, initialization before the first loop check has `i == 1`, `cur == l[0]`, and `best == l[0]`. The invariant should therefore preserve the equation:

```c
max_subarray_sum_acc(cur, best, sublist(i, n, l)) ==
  max_subarray_sum_spec(l)
```

This is strong enough for loop exit: when the loop exits, the invariant gives `i == n`, so the suffix is empty and the accumulator equation reduces to `best == max_subarray_sum_spec(l)`, which is exactly the return postcondition together with the preserved `IntArray::full(a, n, l)`.

The non-obvious verification point is the expression `cur + a[i]`. C evaluates this addition before the branch, so the verifier must know it is still in signed int range. The contract gives an overflow guard for every non-empty subarray sum:

```c
(forall (lo: Z), (forall (hi: Z),
  (0 <= lo && lo < hi && hi <= n) =>
  (INT_MIN <= sum(sublist(lo, hi, l)) &&
   sum(sublist(lo, hi, l)) <= INT_MAX)))
```

To connect `cur + a[i]` to that guard, the invariant must remember that `cur` is a sum of some non-empty subarray ending at the previous processed position:

```c
exists lo,
  0 <= lo && lo < i &&
  cur == sum(sublist(lo, i, l))
```

Then on an iteration with `i < n`, `cur + a[i]` is equal to `sum(sublist(lo, i + 1, l))`, a non-empty subarray sum covered by the contract. The same guard also gives `a[i]` range from the singleton subarray `sublist(i, i + 1, l)`. The branch assignment `cur = a[i]` re-establishes the existential with `lo = i`; the branch assignment `cur = cur + a[i]` reuses the previous `lo`.

The annotation to add is:

```c
/*@ Extern Coq (max_subarray_sum_acc : Z -> Z -> list Z -> Z) */

/*@ Inv exists lo,
      1 <= i && i <= n &&
      n == n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      0 <= lo && lo < i &&
      cur == sum(sublist(lo, i, l)) &&
      INT_MIN <= cur && cur <= INT_MAX &&
      INT_MIN <= best && best <= INT_MAX &&
      max_subarray_sum_acc(cur, best, sublist(i, n, l)) ==
        max_subarray_sum_spec(l) &&
      IntArray::full(a, n, l)
*/
```

This keeps the array ownership unchanged, preserves the scalar parameter relationships needed by the return witness, carries the exact Coq accumulator state, and provides the arithmetic bridge needed for overflow checks in the loop body.
