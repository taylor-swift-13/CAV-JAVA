## 2026-04-22 Annotation round 1

Current program point: the only loop is `for (i = 2; i <= n; ++i)` in `annotated/verify_20260422_164639_fibonacci_mod.c`. The current annotated copy has no `Inv`, so symbolic execution has no way to summarize the loop body or connect the final `return b` to the postcondition `__return == fib_mod_z(n@pre, mod@pre)`.

Relevant C fragment before the change:

```c
int i;
int a = 0;
int b = 1 % mod;
int c;

if (n == 0) {
    return 0;
}

for (i = 2; i <= n; ++i) {
    c = (a + b) % mod;
    a = b;
    b = c;
}

return b;
```

Loop-state reasoning: after the `if (n == 0)` branch, the continuing path has `1 <= n`, with the original precondition still giving `n < 2147483647`, `0 < mod`, and `mod <= 1073741824`. The `for` invariant is checked after `i = 2` and before testing `i <= n`, so `i` is the next Fibonacci index to compute. At that control point, `a` represents `fib_mod_z(i - 2, mod)` and `b` represents `fib_mod_z(i - 1, mod)`. Initially this is `a == fib_mod_z(0, mod)` and `b == fib_mod_z(1, mod)`, matching the Coq model where `fib_mod_z 0 mod` is `0` and `fib_mod_z 1 mod` is `1 rem mod`.

The invariant must also preserve `n == n@pre` and `mod == mod@pre`; otherwise the final return witness would have to rediscover that the C parameters were not modified before proving `b == fib_mod_z(n@pre, mod@pre)`. The bounds `2 <= i && i <= n + 1` match the true `for` control point and still hold when `n == 1` and the loop is skipped. On loop exit, the invariant plus `!(i <= n)` gives `i == n + 1`, so `b == fib_mod_z(i - 1, mod) == fib_mod_z(n@pre, mod@pre)`.

The invariant also carries `0 <= a && a < mod` and `0 <= b && b < mod`. These are not just decorative: the loop body computes `c = (a + b) % mod`, and from two residue bounds plus `mod <= 1073741824`, the verifier can establish `0 <= a + b <= 2147483646`, which is within signed `int`. After the modulo assignment, `c` is again a residue for positive `mod`, so the next iteration's range facts should hold.

Planned annotation inserted immediately before the loop:

```c
/*@ Inv
      1 <= n && n < 2147483647 &&
      0 < mod && mod <= 1073741824 &&
      n == n@pre && mod == mod@pre &&
      2 <= i && i <= n + 1 &&
      a == fib_mod_z(i - 2, mod) &&
      b == fib_mod_z(i - 1, mod) &&
      0 <= a && a < mod &&
      0 <= b && b < mod
*/
for (i = 2; i <= n; ++i) {
    c = (a + b) % mod;
    a = b;
    b = c;
}
```

This annotation is intentionally scalar-only: no heap predicate is needed because the function owns no heap memory beyond `emp`, and no invariant fact about `c` is needed because `c` is assigned before use inside the loop and is not used after the loop.
