# OpenJML Experience

## Commands

Run ESC:

```bash
./scripts/run_openjml_verify.sh input/example.java
```

Direct command:

```bash
source ./scripts/env-openjml.sh
openjml -esc input/example.java
```

## Common Failures

- Visibility: public specs cannot reference private fields unless the field is
  `spec_public` or exposed through a model field.
- Arithmetic overflow: add explicit range preconditions or prove intermediate
  bounds.
- Loop proof failure: add bounds, accumulator, frame, and exit-useful invariants.
- Assignable failure: use `assignable \nothing;` for pure read-only methods and
  precise locations for mutating methods.

## Success

OpenJML exit code 0 is necessary but not sufficient. The anti-cheating scanner
must also pass.

## Manual Notes

From `doc/openjml-documentation/checks.shtml.html`:

- Java runtime safety checks appear as verification failures. Common names:
  `PossiblyNullDeReference`, `PossiblyNegativeIndex`,
  `PossiblyTooLargeIndex`, `PossiblyDivideByZero`,
  `PossiblyNegativeSize`, and arithmetic/range checks.
- JML proof failures name the violated obligation, such as `Precondition`,
  `Postcondition`, `Invariant`, `Assert`, or loop-related obligations. Use the
  failure name to choose whether to strengthen a contract, invariant, assertion,
  or implementation.

From `doc/openjml-tutorial/Visibility.html`:

- Specification visibility follows Java visibility. A public spec cannot
  mention a private field unless it is made visible for specifications, for
  example with `spec_public`, or hidden behind an appropriate model field.
- Prefer `spec_public` for small examples with simple private fields; use model
  fields only when the public abstraction differs meaningfully from concrete
  representation.

From `doc/openjml-tutorial/Nullness.html`:

- JML references are non-null by default. Nullable values require explicit
  `nullable` annotations or command-line/default settings.
- If OpenJML reports nullness failures, decide whether the API should reject
  null inputs (`requires x != null`) or explicitly support them.

From `doc/openjml-tutorial/InspectingCounterexamples.html`:

- The first diagnostic often gives the obligation class and source location;
  the associated declaration points back to the spec clause that generated the
  obligation.
- Counterexample inspection is a debugging aid. Final success still requires
  checked specifications and no forbidden proof shortcuts.
