# Annotation Reasoning

## Initial loop invariant plan after baseline symexec failure

Baseline command:

```text
QualifiedCProgramming/linux-binary/symexec \
  --goal-file=output/verify_20260422_220436_selection_sort/coq/generated/selection_sort_goal.v \
  --proof-auto-file=output/verify_20260422_220436_selection_sort/coq/generated/selection_sort_proof_auto.v \
  --proof-manual-file=output/verify_20260422_220436_selection_sort/coq/generated/selection_sort_proof_manual.v \
  --goal-check-file=output/verify_20260422_220436_selection_sort/coq/generated/selection_sort_goal_check.v \
  --input-file=annotated/verify_20260422_220436_selection_sort.c \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_220436_selection_sort
```

Observed failure:

```text
fatal error: Error: Lack of assertions in some paths for the loop! in annotated/verify_20260422_220436_selection_sort.c:30:8
```

The active annotated file had no invariants:

```c
for (i = 0; i < n; ++i) {
    min_idx = i;
    for (j = i + 1; j < n; ++j) {
        if (a[j] < a[min_idx]) {
            min_idx = j;
        }
    }
    tmp = a[i];
    a[i] = a[min_idx];
    a[min_idx] = tmp;
}
```

This cannot verify selection sort because the postcondition requires a final list `lr` with `Zlength(lr) == n@pre`, pairwise nondecreasing order, `Permutation(l, lr)`, and the final `IntArray::full(a, n@pre, lr)`. The symbolic executor also needs an invariant at each loop path in a nested loop.

Planned outer invariant before `for (i = 0; i < n; ++i)`: introduce a current array list `l_outer` with:

```c
exists l_outer,
  0 <= i && i <= n@pre &&
  n == n@pre && a == a@pre &&
  Zlength(l_outer) == n@pre &&
  Permutation(l, l_outer) &&
  (forall (p: Z) (q: Z),
    (0 <= p && p <= q && q < i) => l_outer[p] <= l_outer[q]) &&
  (forall (p: Z) (q: Z),
    (0 <= p && p < i && i <= q && q < n@pre) => l_outer[p] <= l_outer[q]) &&
  IntArray::full(a, n@pre, l_outer)
```

This invariant is initialized by choosing the original list `l` when `i == 0`: the sorted-prefix and prefix-to-suffix properties are vacuous, `Zlength(l) == n@pre` comes from the function precondition, and the heap is exactly the input heap. It is useful at exit because `i == n@pre` makes the pairwise sorted-prefix property cover the whole final list, while `Permutation(l, l_outer)` and `IntArray::full` directly match the remaining postcondition resources.

Planned inner invariant before `for (j = i + 1; j < n; ++j)`: introduce a current array list `l_inner` with the outer facts plus current scan bounds and a minimum fact:

```c
exists l_inner,
  0 <= i && i < n@pre &&
  i + 1 <= j && j <= n@pre &&
  i <= min_idx && min_idx < j &&
  n == n@pre && a == a@pre &&
  Zlength(l_inner) == n@pre &&
  Permutation(l, l_inner) &&
  (forall (p: Z) (q: Z),
    (0 <= p && p <= q && q < i) => l_inner[p] <= l_inner[q]) &&
  (forall (p: Z) (q: Z),
    (0 <= p && p < i && i <= q && q < n@pre) => l_inner[p] <= l_inner[q]) &&
  (forall (k: Z),
    (i <= k && k < j) => l_inner[min_idx] <= l_inner[k]) &&
  IntArray::full(a, n@pre, l_inner)
```

At initialization `j == i + 1` and `min_idx == i`, so the scanned interval is only index `i`; the minimum fact reduces to reflexivity. In the branch `a[j] < a[min_idx]`, assigning `min_idx = j` makes the new element the minimum for `[i, j + 1)`. In the else branch, the previous minimum remains no greater than the new element, so it remains the minimum for the extended scanned interval.

After the inner loop exits, `j == n@pre`, so `min_idx` is a minimum over the whole suffix `[i, n@pre)`. The two assignments to `a[i]` and `a[min_idx]` perform a two-index swap. The outer invariant for the next `i + 1` should hold because swapping preserves list length and permutation, leaves the old prefix unchanged, places the suffix minimum at index `i`, and therefore extends the sorted prefix while preserving prefix-to-suffix order.
