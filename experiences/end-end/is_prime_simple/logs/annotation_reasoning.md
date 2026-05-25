## 2026-04-22 divisor-scan invariant

Current program point: the only loop is `for (d = 2; d < n; ++d)` in the active annotated file `annotated/verify_20260422_180530_is_prime_simple.c`. The raw input currently has no `Inv`, so symbolic execution cannot preserve the semantic fact needed by the final `return 1`: every already-tested divisor has nonzero remainder.

Relevant raw C fragment before this edit:

```c
if (n < 2) {
    return 0;
}

for (d = 2; d < n; ++d) {
    if (n % d == 0) {
        return 0;
    }
}

return 1;
```

The loop variable `d` is the next candidate divisor. At the loop guard, the processed range is exactly `2 <= k < d`. The invariant should therefore keep `n == n@pre`, range facts for `n` and `d`, and the processed-prefix summary `(forall (k: Z), (2 <= k && k < d) => n % k != 0)`. Initialization holds because after the `n < 2` early return, the only path reaching the loop has `2 <= n`, and at `d = 2` the processed range is empty. Preservation holds because the loop body only reaches `++d` when `n % d != 0`, so the processed range can grow from `[2, d)` to `[2, d + 1)`. Exit is useful because the loop guard is false while the invariant still has `d <= n`, so a loop-exit assertion can expose `d == n` and the full divisor range `(forall k, 2 <= k < n -> n % k != 0)` for `is_prime_z n`.

Planned annotation fragment:

```c
/*@ Inv
      0 <= n && n <= INT_MAX &&
      n == n@pre &&
      2 <= d && d <= n &&
      (forall (k: Z), (2 <= k && k < d) => n % k != 0) &&
      emp
*/
for (d = 2; d < n; ++d) {
    if (n % d == 0) {
        return 0;
    }
}

/*@ Assert
      n == n@pre &&
      d == n &&
      (forall (k: Z), (2 <= k && k < n) => n % k != 0) &&
      emp
*/
return 1;
```

This assertion is placed immediately after loop exit, not after local variables are being destroyed. It only fixes pure facts needed by the final return witness and should keep the symbolic executor from reconstructing the loop-exit arithmetic in the Coq proof.

## 2026-04-22 local integer upper-bound bridge

After the first successful `symexec`, the generated manual theorem `is_prime_simple_entail_wit_1` showed that the invariant initialization had this left side:

```coq
forall (n_pre: Z),
  [| n_pre >= 2 |] && [| 0 <= n_pre |] && emp |--
  [| n_pre <= INT_MAX |] && ...
```

This is not a pure consequence of the formal `Require`, which only states `0 <= n`. The fact is true because `n` is a C `int` parameter, but it must be extracted while the local store for `n` is still available. Per `experiences/general/ASSERTION.md` section 8, the stable annotation shape is a local bridge:

```c
/*@ n <= INT_MAX by local */
```

I am placing it immediately after the `n < 2` early-return branch and before the loop invariant. The updated invariant can then consume `n <= INT_MAX` as an explicit pure fact, and the regenerated initialization witness should no longer ask Coq to prove the upper bound from only `0 <= n`.

## 2026-04-22 preserve lower bound at loop exit

After regenerating with the local upper-bound bridge, the remaining manual theorem `is_prime_simple_return_wit_3` had this proof state after `pre_process; entailer!`:

```coq
n_pre, d : Z
H : d = n_pre
H0 : forall k : Z, 2 <= k < n_pre -> n_pre % k <> 0
============================
is_prime_simple_spec n_pre 1
```

This state is missing `1 < n_pre`, which is required by `is_prime_z n_pre`. The loop invariant does carry `n >= 2`, but the explicit loop-exit `Assert` did not keep it, so the return witness dropped the lower-bound fact. I am changing the exit assertion from:

```c
n == n@pre &&
d == n &&
(forall (k: Z), (2 <= k && k < n) => n % k != 0) &&
emp
```

to:

```c
n == n@pre &&
2 <= n &&
d == n &&
(forall (k: Z), (2 <= k && k < n) => n % k != 0) &&
emp
```

This is a pure consequence of the invariant and the path that passed the early `n < 2` return. It gives the final proof exactly the two conjuncts needed for `is_prime_z n`.
