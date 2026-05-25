# Annotation Reasoning

## 2026-04-22 05:46 annotation plan for `array_longest_nonnegative_run`

Current program point: the only loop is

```c
while (i < n) {
    if (a[i] >= 0) {
        current++;
        if (current > best) {
            best = current;
        }
    } else {
        current = 0;
    }
    i++;
}
```

The active annotated file initially has no loop invariant:

```c
int best = 0;
int current = 0;
int i = 0;

while (i < n) {
    ...
}

return best;
```

That is not enough for symbolic execution because the postcondition requires
`__return == array_longest_nonnegative_run_spec(l)` and the array ownership
`IntArray::full(a, n, l)`. At the loop head the verifier must know: `i` is the
next index to read, `current` and `best` are bounded integer accumulators, `n`
and `a` are unchanged from entry, the array is still fully owned with the
original list `l`, and the current accumulator state is semantically equivalent
to processing the unvisited suffix.

The invariant to add immediately before `while (i < n)` is:

```c
/*@ Inv
      0 <= i && i <= n@pre &&
      0 <= current && current <= i &&
      0 <= best && best <= i &&
      n == n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      array_longest_nonnegative_run_acc(current, best, sublist(i, n@pre, l)) ==
        array_longest_nonnegative_run_spec(l) &&
      IntArray::full(a, n@pre, l)
*/
```

This invariant is written at the real while-loop control point: before checking
`i < n`, `i` counts the already processed prefix and the next element to inspect.
Initialization holds because initially `i = 0`, `current = 0`, `best = 0`, and
`sublist(0, n, l)` is the whole list, so the accumulator expression reduces to
`array_longest_nonnegative_run_spec(l)`. Preservation matches the C update:
when `a[i] >= 0`, the Coq accumulator moves to `current + 1` and `Z.max best
(current + 1)`, which corresponds to the nested `if (current > best)`; when
`a[i] < 0`, the accumulator resets `current` to zero and keeps `best`.
The bounds `current <= i` and `best <= i` make the `int` range obligations for
`current++`, assignment to `best`, and final return manageable under
`n <= INT_MAX`. The parameter equalities `n == n@pre` and `a == a@pre` prevent
the return witness from having to reconstruct unchanged arguments.

At loop exit, the condition gives `i >= n` while the invariant has `i <= n@pre`
and `n == n@pre`, hence `i == n`. The suffix `sublist(i, n@pre, l)` is empty,
so the accumulator expression becomes `best == array_longest_nonnegative_run_spec(l)`.
The preserved `IntArray::full(a, n@pre, l)` plus `n == n@pre` gives the required
postcondition ownership.

Because the invariant refers to `array_longest_nonnegative_run_acc`, the active
annotated file must also expose that Coq symbol to the annotation parser:

```c
/*@ Extern Coq (array_longest_nonnegative_run_acc : Z -> Z -> list Z -> Z) */
```

This is not changing the contract; it only makes a helper from the already
provided input `.v` usable in the loop invariant.
