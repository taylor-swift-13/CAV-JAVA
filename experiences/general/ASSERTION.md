# Assertion Experience

Assertions are local proof bridges. They should explain a fact that follows from
the current program state; they must not replace a missing invariant.

## Good Uses

- Bridge a loop-exit fact to a postcondition.
- Expose arithmetic bounds before an operation that OpenJML flags as overflow.
- Split a quantified proof into a smaller local fact.
- Document a case split immediately after an `if` branch.

## Bad Uses

- Repeating the postcondition without enough invariants.
- Using an assertion where the only proof is an unchecked assumption.
- Adding assertions to hide an implementation bug.

## Manual Notes

From `doc/openjml-tutorial/AssertStatement.html`:

- A JML `assert` is a proof obligation at one program point. OpenJML must prove
  it from the current path condition, method contract, loop invariants, and
  prior checked facts.
- Assertions are not part of the public method interface. Use them for local
  proof structure, debugging, and small bridge facts.
- An assertion that is almost true but misses an equality or boundary case will
  fail. For example, `neg <= 0` may verify where `neg < 0` does not because the
  zero case is feasible.

From `doc/openjml-tutorial/InspectingCounterexamples.html`:

- When an assertion or postcondition fails, classify the failure name first
  (`Assert`, `Postcondition`, `Precondition`, `UndefinedTooLargeIndex`, etc.).
  It indicates whether the problem is a false fact, missing precondition,
  undefined expression, or missing loop information.
- A temporary `show` statement can expose counterexample values while debugging,
  but do not leave debugging-only statements in the final verified file unless
  they are part of the intended proof log.

From `doc/openjml-tutorial/WellDefinedExpressions.html`:

- Assertions must be well-defined before OpenJML can prove their truth. Add
  bounds and non-null facts before asserting array contents or object fields.

## Logging

Before adding or changing assertions in a verify task, append to
`logs/annotation_reasoning.md` with:

- OpenJML failure location.
- The exact assertion to add.
- Why it follows from existing code and specs.
- Which failure it is expected to repair.
