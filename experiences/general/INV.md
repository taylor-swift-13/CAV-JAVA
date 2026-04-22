# Invariant Experience

Loop invariants are the main OpenJML proof aid for iterative Java code.

## General Pattern

- Bound invariant: track the loop variable range, for example
  `0 <= i && i <= n`.
- Frame invariant: state what parts of arrays or objects remain unchanged.
- Accumulator invariant: relate the current accumulator to a prefix or processed
  segment.
- Exit usefulness: ensure the invariant plus loop negation implies the
  postcondition.

## Arrays

- State array non-nullness before any indexed access.
- Use quantified formulas over processed and unprocessed ranges.
- Separate read-only preservation from modified-prefix facts.

## Termination

- Add `decreases` when OpenJML cannot infer loop progress.
- The decreases expression must be non-negative at loop entry and strictly
  decrease on every iteration.

## Manual Notes

From `doc/openjml-tutorial/Loops.html`:

- In deductive verification, every loop normally needs a loop specification.
  OpenJML does not infer the full effect of a loop body from all iterations.
- A useful loop specification has four parts:
  - index bounds, including the exit value;
  - an inductive progress fact describing what has been processed so far;
  - a loop frame condition for locations modified by the loop;
  - a termination measure.
- OpenJML accepts `maintaining` as loop invariant syntax; this project also
  uses `loop_invariant` when that is clearer. Keep the style consistent within
  a file.
- Use `loop_writes` or the local equivalent when a loop writes arrays or object
  fields. If a loop mutates `a[i]`, the frame should mention the array region
  rather than rely on a method-level frame alone.
- The canonical array loop pattern is:

```java
//@ maintaining 0 <= i && i <= a.length;
//@ maintaining (\forall int k; 0 <= k && k < i; a[k] == k);
//@ loop_writes i, a[*];
//@ decreases a.length - i;
for (int i = 0; i < a.length; i++) {
    a[i] = i;
}
```

From `doc/openjml-tutorial/WellDefinedExpressions.html`:

- Invariants must be well-defined at loop entry, preservation, and exit. For an
  invariant that mentions `a[k]`, first establish `a != null` and quantified
  bounds for `k`.
- If OpenJML reports `UndefinedNegativeIndex` or `UndefinedTooLargeIndex` at an
  invariant or assertion, strengthen bounds before adding algebraic facts.

From `doc/openjml-tutorial/Invariants.html`:

- Object invariants are assumed in method pre-states and must be re-established
  by constructors and method exits. Do not introduce a class invariant unless
  every relevant constructor and mutating method can preserve it.
- Public invariants that mention private fields require a visibility solution
  such as `spec_public` or a model abstraction.
