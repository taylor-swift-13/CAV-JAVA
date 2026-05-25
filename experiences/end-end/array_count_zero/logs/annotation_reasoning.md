# Annotation reasoning

## 2026-04-22 initial invariant for `array_count_zero`

Current source fragment before annotation:

```c
int i;
int count = 0;

for (i = 0; i < n; ++i) {
    if (a[i] == 0) {
        count++;
    }
}

return count;
```

The loop is a single forward scan over the immutable input array. At the `for (i = 0; i < n; ++i)` loop judgment point, `i` is the number of already processed elements and the next element to read if the guard is true. The accumulator `count` must therefore summarize exactly the processed prefix, not the whole array and not the current element after the body.

Planned invariant:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      count == array_count_zero_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
```

Initialization holds after `i = 0` and before the first guard check because `count == 0`, `sublist(0, 0, l)` is empty, and `array_count_zero_spec(nil) == 0`. The bounds `0 <= i && i <= n` are true because the precondition gives `0 <= n`. The array is never written, so the full heap predicate stays `IntArray::full(a, n, l)`, and the parameter identities `a == a@pre` and `n == n@pre` preserve the original contract variables for the return witness.

Preservation follows by splitting on `a[i] == 0`. If the branch increments `count`, the processed prefix changes from `sublist(0, i, l)` to `sublist(0, i + 1, l)` by appending `Znth i l 0`, which is zero in that branch, so the spec increases by one. In the else branch, the appended element is nonzero, so the spec does not increase. The heap remains unchanged in both branches.

Planned loop-exit assertion:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      count == array_count_zero_spec(l) &&
      IntArray::full(a, n, l)
*/
```

At loop exit, the invariant gives `0 <= i <= n` and the negated guard gives `i >= n`, so `i == n`. With `Zlength(l) == n`, `sublist(0, i, l)` rewrites to `l`, which directly matches the postcondition `__return == array_count_zero_spec(l)` while preserving the array heap.
