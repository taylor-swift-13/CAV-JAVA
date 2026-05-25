# Annotation Reasoning

## Iteration 1

The target loop is:

```c
int cnt = 0;

for (i = 0; i + 1 < n; ++i) {
    if (a[i] < a[i + 1]) {
        cnt++;
    }
}
```

At the loop head, `i` is the left endpoint of the next adjacent pair to inspect. The comparisons already processed are exactly the adjacent pairs inside the prefix ending at index `i`, so the natural semantic summary is:

```c
cnt == array_count_increasing_steps_spec(sublist(0, i + 1, l))
```

This works at initialization as well: with `i == 0`, the prefix has length at most one when `n == 0` or `n > 0`, and the adjacent-increase count of an empty or one-element list is `0`, matching `cnt == 0`.

The invariant must also preserve unchanged input state because the postcondition mentions the original array value:

```c
a == a@pre &&
n == n@pre &&
IntArray::full(a, n, l)
```

The guard expression itself evaluates `i + 1`, so the proof also needs a loop-head arithmetic fact strong enough to show this addition stays in signed range. A frontend-compatible form is:

```c
0 < n => i + 1 <= n
```

This is initialized because if `0 < n` and `i == 0`, then `i + 1 <= n`. It is preserved because the loop body only executes under `i + 1 < n`; after `++i`, the next loop head needs old `i + 2 <= n`, which follows directly from the guard. It is also enough for signed safety because the local `n` integer cell supplies the signed upper bound for `n`.

The complete annotation inserted immediately before the `for` loop is:

```c
/*@ Inv
      0 <= i && i <= n &&
      (0 < n => i + 1 <= n) &&
      a == a@pre &&
      n == n@pre &&
      cnt == array_count_increasing_steps_spec(sublist(0, i + 1, l)) &&
      IntArray::full(a, n, l)
*/
```

No separate loop-exit assertion is added in this pass. On exit, the generated return witness should combine the negated guard `!(i + 1 < n)`, the invariant bound, and `Zlength(l) == n` to collapse `sublist(0, i + 1, l)` back to `l`.
