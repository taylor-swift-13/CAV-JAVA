## 2026-04-23 05:01 +0800 - Initial arithmetic-series invariant

The active annotated C initially has no loop invariant:

```c
int i;
int ret = 0;

for (i = 1; i <= n; ++i) {
    ret += i;
}

return ret;
```

This cannot be verified as-is because the verifier has no loop-head summary connecting `ret` with the already processed values. The loop control point for `for (i = 1; i <= n; ++i)` is after assigning `i = 1` and before testing `i <= n`. Because the precondition permits `n == 0`, the invariant cannot require `i <= n`; it must allow the skip-loop state `i == 1` when `n == 0`.

The intended invariant is:

```c
/*@ Inv
      1 <= i && i <= n + 1 &&
      n == n@pre &&
      ret == (i - 1) * i / 2
*/
for (i = 1; i <= n; ++i) {
    /*@ 1 <= i && i <= n@pre && n == n@pre &&
        ret == (i - 1) * i / 2
    */
    ret += i;
    /*@ 1 <= i && i <= n@pre && n == n@pre &&
        ret == i * (i + 1) / 2
    */
}
```

Initialization holds because after `ret = 0` and `i = 1`, `(i - 1) * i / 2` is `0`. Preservation holds because when the body runs, the guard gives `i <= n`; after `ret += i`, the accumulator is the old `(i - 1) * i / 2 + i`, i.e. `i * (i + 1) / 2`; after the `++i` step, this is exactly `(i - 1) * i / 2` for the next loop-head value. The invariant keeps `n == n@pre` because the postcondition is written with `n@pre`.

At loop exit, the invariant gives `1 <= i <= n + 1` and the negated guard gives `i > n`, so `i == n + 1`. Therefore `ret == n * (n + 1) / 2`, which is the postcondition. I will add this explicit loop-exit assertion immediately after the loop:

```c
/*@ i == n@pre + 1 &&
    n == n@pre &&
    ret == n@pre * (n@pre + 1) / 2
*/
return ret;
```

The assertion is placed directly at loop exit, before returning, so it bridges only the arithmetic form needed by the return witness rather than trying to repair a weak invariant later.
