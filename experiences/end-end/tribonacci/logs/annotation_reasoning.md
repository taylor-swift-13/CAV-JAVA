## 2026-04-23 05:25 CST - Loop invariant for scalar Tribonacci recurrence

Current program point: the only loop is `for (i = 3; i <= n; ++i)` in the active annotated file `annotated/verify_20260423_051744_tribonacci.c`. The active copy initially matches `input/tribonacci.c` and has no invariant before this loop.

Current issue before editing: the postcondition is `__return == tribonacci_z(n@pre) && emp`, but after the two early returns the symbolic executor needs a loop summary relating the scalar locals `a`, `b`, `c`, and `i` to the Coq recurrence `tribonacci_z`. Without that invariant, the loop body `d = a + b + c; a = b; b = c; c = d;` has no persistent mathematical meaning for the return witness.

Invariant design at the real `for` control point: after the early returns, the continuing path has `2 <= n && n <= 37`. At the loop check, `i` is the next Tribonacci index to compute, and the registers represent the three preceding values:

```c
/*@ Inv
      2 <= n && n <= 37 &&
      n == n@pre &&
      3 <= i && i <= n + 1 &&
      a == tribonacci_z(i - 3) &&
      b == tribonacci_z(i - 2) &&
      c == tribonacci_z(i - 1)
*/
for (i = 3; i <= n; ++i) {
    d = a + b + c;
    a = b;
    b = c;
    c = d;
}
```

Why initialization holds: before the first loop check, `i == 3`, `a == 0`, `b == 1`, and `c == 1`. From `tribonacci.v`, these are exactly `tribonacci_z(0)`, `tribonacci_z(1)`, and `tribonacci_z(2)`. The early returns have removed `n == 0` and `n == 1`, so `2 <= n`; the original precondition gives `n <= 37`, and `n` is not modified.

Why preservation should hold: assuming the invariant and `i <= n`, `d = a + b + c` computes `tribonacci_z(i - 3) + tribonacci_z(i - 2) + tribonacci_z(i - 1)`, which is `tribonacci_z(i)` by the recurrence. The assignments shift the registers so the next loop check at `i + 1` has `a == tribonacci_z((i + 1) - 3)`, `b == tribonacci_z((i + 1) - 2)`, and `c == tribonacci_z((i + 1) - 1)`. Since the body only runs under `i <= n`, the next bound remains `i + 1 <= n + 1`.

Why exit is useful: on loop exit, the invariant gives `3 <= i <= n + 1` and the negated condition gives `i > n`, hence `i == n + 1`. Therefore `c == tribonacci_z(i - 1) == tribonacci_z(n)`, and `n == n@pre` bridges the result to the postcondition. For the skip-loop case `n == 2`, the initial loop check already has `i == 3 == n + 1`, so returning the initialized `c == tribonacci_z(2)` is covered by the same invariant.

I will add exactly this invariant before the `for` loop in the active annotated copy, then rerun `symexec` so the generated Coq witnesses match the updated annotation.
