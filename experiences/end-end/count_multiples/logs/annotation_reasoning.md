## 2026-04-22 15:24 CST - Initial loop invariant for multiple-count scan

The active annotated C initially matches `input/count_multiples.c` and has no loop invariant before the only loop:

```c
int i;
int cnt = 0;

for (i = 1; i <= n; ++i) {
    if (i % k == 0) {
        cnt++;
    }
}

return cnt;
```

This is too weak for symbolic execution to connect the accumulator `cnt` with the postcondition:

```c
Ensure
  __return == count_multiples_spec(n@pre, k@pre) && emp
```

The companion Coq file defines `count_multiples_spec n k` as `count_multiples_upto k (Z.to_nat n)`, where each recursive step adds one exactly when the current index is a multiple of `k`. At the `for (i = 1; i <= n; ++i)` invariant control point, the initialized state has `i == 1` and no candidates have been processed, so the processed range is empty and `cnt` must be the count for fuel `i - 1 == 0`. After the loop body processes current `i`, the branch increments `cnt` exactly when `i % k == 0`; this matches adding the next recursive step for fuel `i`. The `++i` step then moves to the next control point where the invariant should describe processed candidates `1..i-1`.

The C annotation parser should not use qualified Coq syntax such as `Z.to_nat(i - 1)` directly, because similar scalar counting tasks have failed with an undeclared `Z` parse error. I will add a workspace-local helper module:

```coq
Definition count_multiples_upto_z (k fuel : Z) : Z :=
  count_multiples_upto k (Z.to_nat fuel).
```

Then I will import that helper in the active annotated C and add this invariant immediately before the loop:

```c
/*@ Inv
      1 <= n && n < INT_MAX &&
      1 <= k &&
      n == n@pre &&
      k == k@pre &&
      1 <= i && i <= n + 1 &&
      0 <= cnt && cnt <= i - 1 && cnt <= n &&
      cnt == count_multiples_upto_z(k, i - 1)
*/
```

Initialization holds because `i == 1`, `cnt == 0`, and the helper with fuel zero unfolds to `0`. The bound `cnt <= i - 1` is needed for increment safety: in the multiple branch, old `cnt <= i - 1` gives `cnt + 1 <= i`, and the loop guard gives `i <= n`, hence `cnt + 1 <= n`. The parameter equalities `n == n@pre` and `k == k@pre` keep the unmodified inputs aligned with the postcondition.

After the loop exits, the failed condition together with the invariant gives `i == n + 1`, so the processed fuel is `i - 1 == n`. I will add this loop-exit assertion directly after the loop:

```c
/*@ Assert
      i == n + 1 &&
      n == n@pre &&
      k == k@pre &&
      cnt == count_multiples_spec(n@pre, k@pre)
*/
```

This assertion bridges the invariant to the return witness without moving the assertion after local-variable cleanup.
