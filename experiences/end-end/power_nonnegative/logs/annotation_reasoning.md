# Annotation reasoning

## 2026-04-22 loop invariant for `power_nonnegative`

The unannotated C loop is:

```c
int i;
int ans = 1;

for (i = 0; i < exp; ++i) {
    ans = ans * base;
}

return ans;
```

At the `for` invariant control point, after initialization and before the loop condition is tested, `i` denotes the number of multiplications already completed. Therefore the accumulator should equal the mathematical prefix power at exponent `i`, not at `i + 1`.

The invariant I am adding is:

```c
/*@ Inv
      0 <= i && i <= exp &&
      base == base@pre &&
      exp == exp@pre &&
      ans == power_nonnegative_z(base@pre, i) &&
      (forall (k: Z), (0 <= k && k <= exp@pre) =>
        (INT_MIN <= power_nonnegative_z(base@pre, k) &&
         power_nonnegative_z(base@pre, k) <= INT_MAX))
*/
```

Initialization is expected to hold because after `i = 0` and `ans = 1`, `power_nonnegative_z(base@pre, 0)` unfolds to `1`; the precondition gives `0 <= exp`, and the unchanged parameter equalities connect current `base`/`exp` with their `@pre` values. The invariant is useful at exit because `!(i < exp)` plus `0 <= i && i <= exp` gives `i == exp`, and with `exp == exp@pre` the return value matches `power_nonnegative_z(base@pre, exp@pre)`.

Inside the loop, under `i < exp`, the next exponent `i + 1` is still within the precondition's prefix range. I am adding a full assertion before the multiplication to expose the body-state facts and a full assertion after the multiplication to state the recurrence result:

```c
/*@ 0 <= i && i < exp@pre &&
    base == base@pre &&
    exp == exp@pre &&
    ans == power_nonnegative_z(base@pre, i) &&
    (forall (k: Z), (0 <= k && k <= exp@pre) =>
      (INT_MIN <= power_nonnegative_z(base@pre, k) &&
       power_nonnegative_z(base@pre, k) <= INT_MAX))
*/
ans = ans * base;
/*@ 0 <= i && i < exp@pre &&
    base == base@pre &&
    exp == exp@pre &&
    ans == power_nonnegative_z(base@pre, i + 1) &&
    (forall (k: Z), (0 <= k && k <= exp@pre) =>
      (INT_MIN <= power_nonnegative_z(base@pre, k) &&
       power_nonnegative_z(base@pre, k) <= INT_MAX))
*/
```

The expected proof obligation after multiplication is the pure recurrence `power_nonnegative_z(base, i + 1) = power_nonnegative_z(base, i) * base`; if automatic proof cannot solve it, it belongs in manual Coq proof rather than in a stronger C assertion. The prefix range condition is carried unchanged so the overflow witness for `ans * base` can instantiate the precondition with `k = i + 1`.
