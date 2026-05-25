# Annotation Reasoning

## 2026-04-23 05:42:17 +0800 - Add scalar recurrence loop invariant

Current annotated file initially matches the contract input and has no invariant before:

```c
for (i = 2; i <= n; ++i) {
    c = a + b;
    a = b;
    b = c;
}
```

This loop is the only point where the function can connect the C scalar state to the Coq specification `ways_to_reach_z`. The function handles `n == 0` by an early return. On the remaining path, `n != 0` plus the precondition gives `1 <= n <= 45`; therefore the loop initializer `i = 2` is valid at the loop test point, and the loop may be skipped when `n == 1`.

At the loop-head control point, before checking `i <= n`, the state should represent the recurrence values for the next iteration:

```c
a == ways_to_reach_z(i - 2)
b == ways_to_reach_z(i - 1)
```

Initialization: before the first loop test, `i == 2`, `a == 1`, and `b == 1`. The Coq model has `ways_to_reach_z(0) == 1` and `ways_to_reach_z(1) == 1`, so the two accumulator equalities hold. The bound should be `2 <= i && i <= n + 1`, not `i <= n`, because for `n == 1` the loop is skipped after initializing `i = 2`.

Preservation: when `i <= n`, the body computes `c = a + b`, then shifts `a = b` and `b = c`. With the invariant equalities, this corresponds to moving from pair `(ways_to_reach_z(i - 2), ways_to_reach_z(i - 1))` to `(ways_to_reach_z(i - 1), ways_to_reach_z(i))`; after `++i`, the next loop-head state again has `a == ways_to_reach_z(i - 2)` and `b == ways_to_reach_z(i - 1)` for the incremented `i`.

Exit usability: when the loop exits, the invariant gives `2 <= i <= n + 1` and the failed condition gives `i > n`, so arithmetic yields `i == n + 1`. Then `b == ways_to_reach_z(i - 1)` directly yields `b == ways_to_reach_z(n)`. The invariant also carries `n == n@pre` so the return statement can satisfy the postcondition.

The planned annotation is:

```c
/*@ Inv
      1 <= n && n <= 45 &&
      n == n@pre &&
      2 <= i && i <= n + 1 &&
      a == ways_to_reach_z(i - 2) &&
      b == ways_to_reach_z(i - 1)
*/
for (i = 2; i <= n; ++i) {
    c = a + b;
    a = b;
    b = c;
}
```

This should fix the missing loop summary before `symexec` and should leave only pure arithmetic or recurrence witnesses for Coq.
