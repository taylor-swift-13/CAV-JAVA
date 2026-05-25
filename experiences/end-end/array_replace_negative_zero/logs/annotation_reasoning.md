## 2026-04-22 invariant for `array_replace_negative_zero`

Program point: the only loop is `for (i = 0; i < n; ++i)` in `array_replace_negative_zero`. The input contract gives `0 <= n`, `Zlength(l) == n`, and `IntArray::full(a, n, l)`. The postcondition needs an existential final list `l0` with the same length as the input and, for each index in `[0, n)`, negative original values mapped to `0` while nonnegative original values are preserved. The function mutates `a` in place and returns no scalar value.

The active annotated file currently has no loop invariant:

```c
for (i = 0; i < n; ++i) {
    if (a[i] < 0) {
        a[i] = 0;
    }
}
```

Without an invariant, symbolic execution has no persistent logical list for the current contents of `a` and no prefix relation tying updated cells back to the original list `l`. I will add an invariant immediately before the `for` loop:

```c
/*@ Inv exists lc,
      0 <= i && i <= n@pre &&
      n == n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      Zlength(lc) == n@pre &&
      (forall (k: Z), (0 <= k && k < i && l[k] < 0) => lc[k] == 0) &&
      (forall (k: Z), (0 <= k && k < i && l[k] >= 0) => lc[k] == l[k]) &&
      (forall (k: Z), (i <= k && k < n@pre) => lc[k] == l[k]) &&
      IntArray::full(a, n@pre, lc)
*/
```

Here `i` is the next index to process, so `[0, i)` is the processed prefix and `[i, n)` is the untouched suffix. The existential `lc` is the current full-array contents. The first two quantified facts express the postcondition relation over the processed prefix, split into separate implications for the negative and nonnegative cases. The suffix fact states that every unprocessed cell still equals its original input value.

Initialization: after `i = 0`, choose `lc = l`. The prefix facts are vacuous because there is no `k` with `0 <= k < 0`; the suffix fact is exactly the original array contents over `[0, n)`. `0 <= i <= n@pre` follows from `i == 0` and the precondition `0 <= n`.

Preservation: when the loop body runs, the guard gives `0 <= i < n@pre`. If `a[i] < 0`, the assignment writes `0` at the current index, so the next invariant can use the updated current contents while extending the negative-case prefix fact to `i`. If the branch is skipped, the current suffix fact and branch condition imply `l[i] >= 0`, so the nonnegative-case prefix fact is extended while the heap list remains unchanged. In both cases, the new suffix starts at `i + 1` and still equals the original input list.

Exit: after the loop, `i == n` and the invariant's processed-prefix facts cover the whole range `[0, n)`. I will add the following loop-exit assertion immediately after the loop to make that conversion explicit before local variable cleanup:

```c
/*@ Assert exists lc,
      i == n &&
      n == n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      Zlength(lc) == n@pre &&
      (forall (k: Z), (0 <= k && k < n@pre && l[k] < 0) => lc[k] == 0) &&
      (forall (k: Z), (0 <= k && k < n@pre && l[k] >= 0) => lc[k] == l[k]) &&
      IntArray::full(a, n@pre, lc)
*/
```

This assertion should let the return witness choose `l0 = lc`; the contract's combined implication follows from the two split implications.
