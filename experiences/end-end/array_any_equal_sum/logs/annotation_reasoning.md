## Annotation iteration 1: add prefix-search invariant and loop-exit assertion

Current program point:

```c
int i;
int target = x + y;

for (i = 0; i < n; ++i) {
    if (a[i] == target) {
        return 1;
    }
}

return 0;
```

The input contract already gives `0 <= n`, `INT_MIN <= x + y`, `x + y <= INT_MAX`, `Zlength(l) == n`, and `IntArray::full(a, n, l)`. The loop is a read-only scan. The `return 1` branch needs the current index as the existential witness for the postcondition:

```c
exists i, 0 <= i && i < n && l[i] == x + y
```

The `return 0` branch needs the universal no-match property over the whole array:

```c
forall (i: Z), (0 <= i && i < n) => l[i] != x + y
```

The unannotated loop does not preserve that no-match property for the processed prefix, so after the loop symbolic execution has no local fact that all earlier elements differ from `target`. The invariant should describe the real `for` control point: after `i = 0` and before each loop-condition check, indices `0 <= j < i` have already been checked and were not equal to `target`.

Planned invariant:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      x == x@pre &&
      y == y@pre &&
      target == x + y &&
      INT_MIN <= target && target <= INT_MAX &&
      (forall (j: Z), (0 <= j && j < i) => l[j] != target) &&
      IntArray::full(a, n, l)
*/
```

Initialization: after `i = 0`, `0 <= i && i <= n` follows from `0 <= n`; the prefix `0 <= j < 0` is empty; the array is still `IntArray::full(a, n, l)`; `target == x + y` holds immediately after `int target = x + y`; and the overflow guard on `target` follows from the precondition guard on `x + y`.

Preservation: at loop entry, the condition gives `i < n`. If `a[i] == target`, the function returns `1` and uses the current index as the existential witness. Otherwise the `if` branch is skipped with `a[i] != target`, so after `++i` the prefix no-match fact extends from `0 <= j < old_i` to `0 <= j < old_i + 1`. The loop does not modify `a`, `n`, `x`, `y`, or `target`, so the parameter equalities and heap predicate remain valid.

Exit usability: when the loop exits, the loop condition is false and the invariant gives `i <= n`, so `i == n`. A small loop-exit assertion will expose that equality and rewrite the prefix fact from `j < i` to `j < n`, exactly matching the `return 0` postcondition.

Planned exit assertion:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      x == x@pre &&
      y == y@pre &&
      target == x + y &&
      INT_MIN <= target && target <= INT_MAX &&
      (forall (j: Z), (0 <= j && j < n) => l[j] != target) &&
      IntArray::full(a, n, l)
*/
```

This assertion is placed immediately after the loop and before `return 0`, so it only fixes the loop-exit pure facts and keeps the local variable cleanup path simple.
