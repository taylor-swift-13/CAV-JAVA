# Annotation Reasoning

## Iteration 1: add prefix-count invariant for the read-only array scan

Program point: the active annotated C currently matches `input/count_positive.c` and has no verification annotations around the only loop:

```c
int i;
int cnt = 0;

for (i = 0; i < n; ++i) {
    if (a[i] > 0) {
        cnt++;
    }
}

return cnt;
```

The contract gives `0 <= n`, `Zlength(l) == n`, and `IntArray::full(a, n, l)`. The loop reads `a[i]`, conditionally increments `cnt`, and never writes to the array. The postcondition requires the final scalar result to equal `count_positive_spec(l)` and the same full array resource to be preserved. Without an invariant at the `for` guard, symbolic execution has no stable fact connecting `cnt` to the processed prefix and no explicit preservation facts for `a` and `n`.

Planned annotation before the loop:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      cnt == count_positive_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
for (i = 0; i < n; ++i) { ... }
```

This invariant is placed at the real C `for` control point: after `i = 0` and before checking `i < n`. Initialization holds because `cnt` is `0`, `i` is `0`, and `count_positive_spec(sublist(0, 0, l))` is the count over the empty prefix. Preservation follows by splitting on `a[i] > 0`: the true branch increments `cnt`, matching the one-element extension of `count_positive_spec` over `sublist(0, i + 1, l)`; the false branch keeps `cnt`, matching a zero contribution from the new element. The array resource remains `IntArray::full(a, n, l)` because the loop only reads it.

Planned loop-exit assertion:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      cnt == count_positive_spec(l) &&
      IntArray::full(a, n, l)
*/
return cnt;
```

On exit, the invariant gives `i <= n` and the failed guard gives `i >= n`, so `i == n`. Together with `Zlength(l) == n`, the processed prefix `sublist(0, i, l)` is the whole input list. The assertion fixes that normalized return state immediately after the loop, before local-variable cleanup.
