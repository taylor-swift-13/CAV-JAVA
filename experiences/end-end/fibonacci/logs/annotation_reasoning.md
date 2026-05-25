## 2026-04-22 Annotation round 1

Current program point: the only loop is `for (i = 2; i <= n; ++i)` in `annotated/verify_20260422_163304_fibonacci.c`. The original annotated copy has no `Inv`, so symbolic execution cannot justify either the loop body state or the final `return b` against the postcondition `__return == fib_z(n@pre)`.

Relevant current C fragment before the change:

```c
int i;
int a = 0;
int b = 1;
int c;

if (n == 0) {
    return 0;
}

for (i = 2; i <= n; ++i) {
    c = a + b;
    a = b;
    b = c;
}

return b;
```

Loop-state reasoning: after the `if (n == 0)` branch, the continuing path has `1 <= n <= 46`. The loop control point for this `for` loop is after initializing `i = 2` and before testing `i <= n`. At that point `a == 0 == fib_z(0)` and `b == 1 == fib_z(1)`, so the natural invariant is `a == fib_z(i - 2)` and `b == fib_z(i - 1)`. During one loop iteration, `c = a + b`, then `a = b`, then `b = c`; this shifts the pair from `(fib_z(i - 2), fib_z(i - 1))` to `(fib_z(i - 1), fib_z(i))`, matching the next control point after `++i`.

The invariant also needs `n == n@pre`; otherwise the final return witness may be polluted by having to relate current `n` back to the pre-state name used in the postcondition. The bounds `2 <= i && i <= n + 1` match the real `for` control point. They hold initially even when `n == 1` and the loop is skipped (`i == 2 == n + 1`), are preserved by `++i`, and with loop exit `!(i <= n)` they give `i == n + 1`. Therefore the exit state has `b == fib_z(i - 1) == fib_z(n@pre)`, which is exactly the return postcondition.

Planned annotation inserted immediately before the loop:

```c
/*@ Inv
      1 <= n && n <= 46 &&
      n == n@pre &&
      2 <= i && i <= n + 1 &&
      a == fib_z(i - 2) &&
      b == fib_z(i - 1)
*/
for (i = 2; i <= n; ++i) {
    c = a + b;
    a = b;
    b = c;
}
```

This is intentionally minimal: no heap facts are needed because the function uses only scalar locals and `emp`, and no fact about `c` is needed because `c` is only a temporary assigned inside the loop before use and is not read after a skipped loop.
