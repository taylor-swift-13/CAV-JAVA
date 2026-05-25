# Annotation reasoning: array_move_zeroes_to_end

## 2026-04-22 06:11:41 +0800 - Initial loop invariant plan

Current active annotated C has no `Inv` before either `while`:

```c
int write = 0;
int i = 0;

while (i < n) {
    if (a[i] != 0) {
        a[write] = a[i];
        write++;
    }
    i++;
}

while (write < n) {
    a[write] = 0;
    write++;
}
```

This is not enough for the verifier because both loops mutate the same `IntArray::full(a, n, l)` resource. At the first loop head, `i` is the processed input-prefix length and `write` is the number of nonzero values already copied into the output prefix. The heap list is no longer just `l`: positions `0 <= k < write` contain `array_move_zeroes_to_end_nonzero(sublist(0, i, l))[k]`, while positions `i <= k < n` are still the original unprocessed suffix `l[k]`. The middle region `write <= k < i` may contain stale values and is intentionally left unconstrained because the second phase will overwrite all positions from the final nonzero count to `n`.

The first loop invariant I will add is:

```c
/*@ Inv exists lc,
      0 <= i && i <= n@pre &&
      0 <= write && write <= i &&
      a == a@pre &&
      n == n@pre &&
      n@pre == Zlength(l) &&
      Zlength(lc) == n@pre &&
      write == Zlength(array_move_zeroes_to_end_nonzero(sublist(0, i, l))) &&
      (forall (k: Z),
        (0 <= k && k < write) =>
        lc[k] == array_move_zeroes_to_end_nonzero(sublist(0, i, l))[k]) &&
      (forall (k: Z),
        (i <= k && k < n@pre) =>
        lc[k] == l[k]) &&
      IntArray::full(a, n@pre, lc)
*/
```

Initialization holds with `i = 0`, `write = 0`, and `lc = l`: the processed prefix is empty, so the nonzero-prefix length is zero, and all positions are still part of the unprocessed suffix. Preservation splits on `a[i] != 0`. In the true branch, writing `a[i]` to `a[write]` appends the current nonzero element to the compacted prefix and increments `write`; then `i++` extends the processed prefix. In the false branch, `write` stays equal to the nonzero-prefix length because the appended element is zero; then `i++` only shrinks the unconstrained middle/original suffix boundary. The invariant keeps `a == a@pre` and `n == n@pre` so the final postcondition can use the pre-state array pointer and length.

At first-loop exit, `i == n` follows from the invariant and failed guard, so `write` equals `Zlength(array_move_zeroes_to_end_nonzero(l))` and the prefix `0 <= k < write` already contains the nonzero part of the final spec. The second loop must fill positions from that `write` value up to `n` with zero. Its invariant should therefore preserve the nonzero prefix and track the already-zeroed suffix:

```c
/*@ Inv exists lc,
      Zlength(array_move_zeroes_to_end_nonzero(l)) <= write && write <= n@pre &&
      a == a@pre &&
      n == n@pre &&
      n@pre == Zlength(l) &&
      Zlength(lc) == n@pre &&
      (forall (k: Z),
        (0 <= k && k < Zlength(array_move_zeroes_to_end_nonzero(l))) =>
        lc[k] == array_move_zeroes_to_end_nonzero(l)[k]) &&
      (forall (k: Z),
        (Zlength(array_move_zeroes_to_end_nonzero(l)) <= k && k < write) =>
        lc[k] == 0) &&
      IntArray::full(a, n@pre, lc)
*/
```

The second loop body writes exactly one zero at index `write`. I will add bridge assertions around `a[write] = 0` to expose `IntArray::missing_i` at the write index and then fold the updated cell back into `IntArray::full` with a new ghost list `lc1`. This bridge is local to the write and avoids making the invariant carry an unnecessarily expanded array shape.

The input `.v` defines `array_move_zeroes_to_end_nonzero`, `array_move_zeroes_to_end_zeros`, and `array_move_zeroes_to_end_spec`, but the active C only declares the spec as an `Extern Coq`. To make the invariant names parse, I will add `Extern Coq` declarations for the two helper functions without changing the `Require` / `Ensure` contract.
