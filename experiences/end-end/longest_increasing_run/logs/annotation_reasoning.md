# Annotation Reasoning

## 2026-04-22 18:43 initial loop invariant for `longest_increasing_run`

Current program point: the only loop is the `for` loop that starts after the
nonempty case initializes `cur` and `best`:

```c
cur = 1;
best = 1;
for (i = 1; i < n; ++i) {
    if (a[i - 1] < a[i]) {
        cur++;
    } else {
        cur = 1;
    }
    if (best < cur) {
        best = cur;
    }
}
return best;
```

The active annotated file initially had no loop invariant at this control
point. That is not enough for symbolic execution because the postcondition
requires both `__return == longest_increasing_run_spec(l)` and preservation of
`IntArray::full(a, n, l)`. At the `for` loop head, before checking `i < n`,
the verifier must know that `i` is the next index to read, that `cur` and
`best` are bounded accumulator values for the already processed prefix, that
`n` and `a` are unchanged, and that continuing the Coq accumulator over the
unprocessed suffix gives the original specification.

The invariant to add immediately before `for (i = 1; i < n; ++i)` is:

```c
/*@ Inv
      1 <= i && i <= n@pre &&
      1 <= cur && cur <= i &&
      1 <= best && best <= i &&
      n == n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      longest_increasing_run_acc(l[i - 1], cur, best, sublist(i, n@pre, l)) ==
        longest_increasing_run_spec(l) &&
      IntArray::full(a, n@pre, l)
*/
```

This invariant is written at the real `for` loop control point. In the nonempty
case, after `cur = 1`, `best = 1`, and `i = 1`, the processed prefix is exactly
the first element of `l`; therefore the previous value passed to the Coq
accumulator is `l[0]`, the current run length is `1`, the best run length is
`1`, and the remaining suffix is `sublist(1, n, l)`. This matches the
definition of `longest_increasing_run_spec` on a nonempty list.

Preservation follows the two C branches. If `a[i - 1] < a[i]`, then the Coq
accumulator on head `l[i]` takes its increasing branch, advances the current run
to `cur + 1`, and updates the best value with `Z.max best (cur + 1)`, matching
the C code's `cur++` followed by `if (best < cur) best = cur`. If the comparison
is false, the Coq accumulator resets the current run to `1` and keeps the old
best, matching `cur = 1` and the following best update, which is a no-op because
`best >= 1`. The bounds `cur <= i` and `best <= i`, together with the loop
guard `i < n` and `n <= INT_MAX`, make the integer-range obligations for
`cur++`, `best = cur`, and `return best` explicit. The equalities `n == n@pre`
and `a == a@pre` avoid a return witness that has to rediscover unchanged
parameters.

At loop exit, the invariant gives `i <= n@pre`; the failed guard plus
`n == n@pre` gives `i >= n@pre`, hence `i == n@pre`. The suffix
`sublist(i, n@pre, l)` is empty, so the accumulator equation reduces to
`best == longest_increasing_run_spec(l)`, which is exactly the return value
obligation. The preserved `IntArray::full(a, n@pre, l)` and `n == n@pre` give
the required array ownership.

Because this invariant refers to `longest_increasing_run_acc`, the active
annotated file also needs an `Extern Coq` declaration for that helper from the
already provided input `.v` file:

```c
/*@ Extern Coq (longest_increasing_run_acc : Z -> Z -> Z -> list Z -> Z) */
```

This exposes an existing Coq definition to the annotation parser; it does not
change the contract or the C implementation.

## 2026-04-22 18:47 restore active annotated file and adjust index expression

After the first corrected `symexec` command shape, `logs/qcp_run.log` reported
exit status 0 but did not print strategy parsing lines or
`Symbolic Execution into function longest_increasing_run`. The generated
`coq/generated/longest_increasing_run_goal.v` contained only an empty
`Module Type VC_Correct`:

```coq
Module Type VC_Correct.

End VC_Correct.
```

Inspection showed the direct cause: the active annotated file
`annotated/verify_20260422_184334_longest_increasing_run.c` had become a
zero-byte file, so `symexec` had no C function to parse. The fix is to restore
the active annotated file from the verified input C plus the intended helper
declaration and invariant.

While restoring, the invariant also uses the explicit list-index expression
from a prior successful same-task run:

```c
longest_increasing_run_acc(Znth(i - 1, l, 0), cur, best, sublist(i, n, l)) ==
  longest_increasing_run_spec(l) &&
IntArray::full(a, n, l)
```

This is semantically the same as the earlier plan because the invariant still
carries `n == n@pre`. The explicit `Znth(i - 1, l, 0)` avoids relying on
bracket notation inside an imported Coq helper call. The accumulator argument
order remains `prev, cur, best, suffix`, matching the current
`input/longest_increasing_run.v`.
