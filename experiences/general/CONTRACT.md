# Contract Experience

The contract stage turns raw task text into one Java file with executable Java
code and JML method contracts.

## Rules

- Preserve the intended algorithm and public behavior from the raw task.
- Use JML `requires`, `ensures`, and `assignable` clauses for the target method.
- Prefer explicit integer overflow preconditions when arithmetic may exceed
  Java `int` range.
- For arrays, require non-null arrays and valid length/index ranges before
  dereferencing.
- Keep contract output free of loop invariants and proof-only assertions unless
  the raw task itself includes them.
- Do not add assumptions, axioms, native methods, or tool suppression pragmas.

## Manual Notes

From `doc/openjml-tutorial/Preconditions.html`:

- Preconditions describe when a method is well-defined. Use `requires` for
  non-empty collections, non-null inputs, index bounds, divisor nonzero facts,
  and integer ranges needed by the implementation.
- The order of `requires` clauses matters when later clauses dereference an
  earlier value. Write `a != null` before `0 <= i && i < a.length`.
- JML treats reference-typed values as non-null by default unless the
  specification or command-line mode says otherwise. Still write explicit
  non-null requirements for array/string parameters in generated contracts so
  the proof obligation is obvious.

From `doc/openjml-tutorial/Postconditions.html`:

- Postconditions specify what a method does, not how it does it. Prefer result
  properties using `\result` and input/output relations.
- For choice-like results, combine membership and ordering facts. Example
  pattern: result equals one candidate and is at least every candidate.

From `doc/openjml-tutorial/FrameConditions.html`:

- State side effects explicitly. Use `assignable \nothing;` for methods that do
  not mutate state.
- For mutating methods, name only the locations that may change. Postconditions
  that mention old values should use `\old(...)`.
- If a called method has no precise frame condition, OpenJML may treat unrelated
  memory as changed, causing later assertions to fail.

From `doc/openjml-tutorial/WellDefinedExpressions.html`:

- Every JML expression must be well-defined. Array reads need non-nullness and
  index bounds; field/method dereferences need non-null receivers; division and
  modulo need nonzero divisors.
- Write contracts so every `ensures`, `requires`, and quantifier body is itself
  well-defined.

From `doc/openjml-tutorial/ArithmeticModes.html`:

- OpenJML uses safe arithmetic for Java code by default and reports possible
  overflow/underflow. Specifications are mathematical by default.
- Add explicit range preconditions for `+`, `-`, `*`, negation, and casts when
  the mathematical result must fit in Java `int` or `long`.

From `doc/openjml-tutorial/SpecifyingExceptions.html`:

- If normal execution is intended, avoid underspecified exceptional paths by
  adding preconditions that exclude null dereference, division by zero, and bad
  indexes.
- If exceptions are part of the task, use `signals` and `signals_only` rather
  than leaving the exceptional behavior implicit.

## Output

Write:

- `input/<name>.java`
- `logs/reasoning.md`
- `logs/issues.md`
- `logs/metrics.md`

`reasoning.md` must explain the raw semantics, selected Java signature, memory
or nullness assumptions, integer-range assumptions, and why any helper method is
needed.
