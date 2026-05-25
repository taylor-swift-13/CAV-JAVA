## 2026-04-22 07:12 annotation pass 1

Current C has a `while (i < n)` loop with no invariant:

```c
int write = 0;
int i = 0;
while (i < n) {
    if (a[i] != k) {
        out[write] = a[i];
        write++;
    }
    i++;
}
return write;
```

The postcondition requires the returned `write` to equal `Zlength(array_remove_value_to_output_spec(la, k@pre))`, and requires `out` to contain that filtered list as a prefix followed by an existential tail. The loop state needed for this is not just bounds on `i`; it must preserve the exact relation between `write`, the processed prefix `sublist(0, i, la)`, and the already written prefix of `out`.

Planned invariant before the `while` condition:

```c
/*@ Inv exists lout,
      0 <= i && i <= n@pre &&
      0 <= write && write <= i &&
      n == n@pre &&
      a == a@pre &&
      out == out@pre &&
      k == k@pre &&
      n@pre == Zlength(la) &&
      n@pre == Zlength(lo) &&
      Zlength(lout) == n@pre &&
      write == Zlength(array_remove_value_to_output_spec(sublist(0, i, la), k@pre)) &&
      (forall (p: Z),
        (0 <= p && p < write) =>
        lout[p] == array_remove_value_to_output_spec(sublist(0, i, la), k@pre)[p]) &&
      (forall (p: Z),
        (write <= p && p < n@pre) =>
        lout[p] == lo[p]) &&
      IntArray::full(a, n@pre, la) *
      IntArray::full(out, n@pre, lout)
*/
```

Initialization: before the first condition check, `i == 0` and `write == 0`; `array_remove_value_to_output_spec(sublist(0, 0, la), k@pre)` is empty, so the written-prefix condition is vacuous and the whole `out` list can be the original `lo`.

Preservation: if `a[i] == k`, then no output cell is written, `write` is unchanged, and moving to `i + 1` keeps the filtered prefix unchanged. If `a[i] != k`, then `out[write]` is assigned `a[i]`, the filtered prefix gains exactly `la[i]` at the end, and `write` increments to the new filtered-prefix length. In both cases `a` is preserved and the output suffix from the new `write` onward remains original `lo`.

Exit: when the loop exits, the invariant gives `i == n@pre` from `0 <= i <= n@pre`, `n == n@pre`, and `!(i < n)`. Then `sublist(0, i, la)` is the whole input list, so `write` is the required return length and the `lout` decomposition can provide the postcondition's existential `tail`.
