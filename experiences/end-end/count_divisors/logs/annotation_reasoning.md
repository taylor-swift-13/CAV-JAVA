## 2026-04-22 14:56 CST - Initial loop invariant for divisor-count scan

The active annotated C initially matches `input/count_divisors.c` and has no `Inv` before the only loop:

```c
int d;
int cnt = 0;

for (d = 1; d <= n; ++d) {
    if (n % d == 0) {
        cnt++;
    }
}

return cnt;
```

That is too weak for symbolic execution to connect the accumulator `cnt` with the imported postcondition:

```c
Ensure
  __return == count_divisors_spec(n@pre) && emp
```

The companion Coq file defines `count_divisors_spec n` as `count_divisors_upto n (Z.to_nat n)`. At the `for (d = 1; d <= n; ++d)` invariant control point, the initialized state has `d == 1` and no divisors have been processed, so the processed range is empty and the right summary is `count_divisors_upto(n, Z.to_nat(d - 1))`, i.e. fuel zero. After one loop body with current `d`, the branch increments `cnt` exactly when `n % d == 0`, which matches the `S k` case of `count_divisors_upto` for the newly included divisor candidate. The loop step then increments `d`, so the same invariant describes the next control point.

I will add this invariant immediately before the loop:

```c
/*@ Inv
      1 <= n && n < INT_MAX &&
      n == n@pre &&
      1 <= d && d <= n + 1 &&
      0 <= cnt && cnt <= n &&
      cnt == count_divisors_upto(n, Z.to_nat(d - 1))
*/
```

The bounds `1 <= d && d <= n + 1` are valid at the `for` control point because the precondition gives `1 <= n`, the initialization sets `d = 1`, and the final failed test occurs at `d == n + 1`. The `n == n@pre` relation keeps the unmodified parameter aligned with the postcondition. The `cnt` range is not the semantic core, but it is needed to keep the returned C `int` value in range for generated VCs. After the loop, I will add a minimal exit assertion:

```c
/*@ Assert
      d == n + 1 &&
      n == n@pre &&
      cnt == count_divisors_spec(n@pre)
*/
```

This assertion is placed directly after the loop, before local-variable cleanup at `return cnt`, so it only bridges the invariant plus failed loop condition to the function postcondition.

## 2026-04-22 15:00 CST - Replace qualified `Z.to_nat` with a workspace helper

The first `symexec` run failed before generating useful Coq files because the invariant used a qualified Coq identifier directly:

```c
cnt == count_divisors_upto(n, Z.to_nat(d - 1))
```

The log reported:

```text
fatal error: Use of undeclared identifier `Z' in annotated/verify_20260422_145616_count_divisors.c:24:4
```

This is a front-end parsing problem, not a proof problem. The semantic invariant is still the right one: `cnt` must be the count over fuel `d - 1`. To express that without a qualified identifier in the C annotation, I will add a workspace-local helper module:

```coq
Definition count_divisors_upto_z (n fuel : Z) : Z :=
  count_divisors_upto n (Z.to_nat fuel).
```

Then the invariant can use the plain helper name:

```c
cnt == count_divisors_upto_z(n, d - 1)
```

The helper is only an abbreviation over the existing Contract-provided `count_divisors_upto`; it does not change the function contract. The loop-exit assertion remains:

```c
cnt == count_divisors_spec(n@pre)
```

because at exit the invariant gives `d == n + 1`, hence `d - 1 == n`, and the helper unfolds to `count_divisors_upto n (Z.to_nat n)`, exactly the definition of `count_divisors_spec`.

## 2026-04-22 15:08 CST - Strengthen count bound for increment safety

After the helper parsing fixes, manual proof replay of `count_divisors_entail_wit_2_1` showed that the generated preservation VC for the dividing branch retains two pure goals after `pre_process; entailer!`:

```coq
cnt + 1 = count_divisors_upto_z n_pre (d + 1 - 1)
cnt + 1 <= n_pre
```

The semantic equality follows from the one-step helper lemma, but the bound `cnt + 1 <= n_pre` is not derivable from the existing invariant fact `cnt <= n_pre` alone. A model with `cnt = n_pre` would satisfy that weak bound but fail the increment bound, even though such a state cannot occur in this loop.

The missing program-state fact belongs in the loop invariant: before testing candidate `d`, the loop has processed exactly the candidates `1..d-1`, so the count cannot exceed the number of processed candidates. I will strengthen:

```c
0 <= cnt && cnt <= n &&
cnt == count_divisors_upto_z(n, d - 1)
```

to:

```c
0 <= cnt && cnt <= d - 1 && cnt <= n &&
cnt == count_divisors_upto_z(n, d - 1)
```

Initialization holds because `d == 1` and `cnt == 0`, so `cnt <= d - 1` is `0 <= 0`. In the dividing branch, the old bound gives `cnt <= d - 1`, hence `cnt + 1 <= d`, and the loop guard gives `d <= n`; therefore `cnt + 1 <= n`. In the non-dividing branch, `cnt` is unchanged and the next control point has `d + 1`, so `cnt <= d - 1` implies `cnt <= (d + 1) - 1`. This is a genuine invariant strengthening, so after editing the annotated file I must clear and rerun `symexec`.
