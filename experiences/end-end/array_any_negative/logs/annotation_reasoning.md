## 2026-04-22 02:30:32 +0800 - add scan-prefix loop invariant

Current program point: the only loop is:

```c
for (i = 0; i < n; ++i) {
    if (a[i] < 0) {
        return 1;
    }
}

return 0;
```

The original annotated working copy has no `Inv` before this `for` loop, so symbolic execution cannot know what is preserved across iterations or why the final `return 0` implies the universal postcondition. The postcondition has two cases:

```c
(__return == 1 &&
  (exists i, 0 <= i && i < n && l[i] < 0))
||
(__return == 0 &&
  (forall (i: Z), (0 <= i && i < n) => l[i] >= 0))
```

At the loop head, `i` is the next index to inspect, so the processed prefix is `[0, i)`. If execution has not returned 1 before reaching the next loop head, every processed element must be nonnegative. The invariant therefore needs to record:

```c
0 <= i && i <= n@pre &&
n == n@pre &&
a == a@pre &&
n@pre == Zlength(l) &&
(forall (j: Z), (0 <= j && j < i) => l[j] >= 0) &&
IntArray::full(a, n@pre, l)
```

Initialization: after `i = 0`, the bounds `0 <= i <= n@pre` follow from the precondition `0 <= n`, and the prefix fact is vacuous because there is no `j` with `0 <= j < 0`. The array predicate is exactly the input heap.

Preservation: inside a continuing iteration, the branch condition `a[i] < 0` is false, so the current element satisfies `l[i] >= 0` while the invariant already covers all earlier `j < i`. After `++i`, the prefix fact extends from `[0, i)` to `[0, i + 1)`. The function only reads `a[i]`, so `IntArray::full(a, n@pre, l)`, `n == n@pre`, and `a == a@pre` remain valid.

Early return: if `a[i] < 0`, the invariant gives `0 <= i && i < n@pre`, `n == n@pre`, and the array read gives `l[i] < 0`, which is the existential witness required for `__return == 1`.

Loop exit: when the loop exits normally, the invariant plus failed condition gives `i >= n` and `i <= n@pre`; with `n == n@pre`, this fixes `i == n`. The prefix universal over `j < i` then covers the whole range `0 <= j < n`, which is exactly the `__return == 0` postcondition. No separate loop-exit `Assert` is planned initially because the closely matching `array_all_positive` example verifies with only this invariant shape.
