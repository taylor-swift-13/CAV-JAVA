# Eval Experience

Eval checks concrete examples against an existing Java/JML implementation. It is
independent from contract generation and full verification repair.

## Purpose

Generate 20 concrete harness cases:

- 10 positive cases that satisfy the JML spec and should be proved by OpenJML.
- 10 negative cases that violate a precondition or intentionally assert a result
  that contradicts the spec, and therefore should fail OpenJML.

This is not JUnit-style execution. It is static checking of concrete harness
methods against the existing JML specification.

## Positive Cases

Positive cases should:

- Use legal concrete inputs.
- Exercise boundary values, normal values, and small structural cases.
- Assert the expected result or expected post-state.
- Pass `openjml -esc`.

Example shape:

```java
public static void positive01() {
    int r = Impl.add(1, 2);
    //@ assert r == 3;
}
```

## Negative Cases

Negative cases should:

- Be deterministic and concrete.
- Target one failure per method.
- Prefer precondition failures when testing invalid inputs.
- Use contradictory assertions when testing wrong expected outputs.
- Be documented as expected to fail.

Example shape:

```java
public static void negative01_precondition() {
    Impl.add(Integer.MAX_VALUE, 1);
}

public static void negative02_wrongExpected() {
    int r = Impl.add(1, 2);
    //@ assert r == 4;
}
```

OpenJML must report a failure for each negative case. If a negative case passes,
the eval has failed.

## Manual Notes

From `doc/openjml-tutorial/Preconditions.html`:

- Positive harness calls must satisfy every `requires` clause, including
  well-definedness prerequisites such as non-null arrays and valid indexes.
- Negative precondition cases should call the target in a way that violates one
  clear precondition, not several unrelated requirements at once.

From `doc/openjml-tutorial/Postconditions.html` and
`doc/openjml-tutorial/AssertStatement.html`:

- Positive harnesses should assert facts that follow from the target
  postconditions, not from unstated implementation details.
- Negative wrong-output cases should use a contradictory `assert` after a legal
  call. The contradiction should be directly related to the method spec.

From `doc/openjml-tutorial/WellDefinedExpressions.html`:

- Harness assertions must themselves be well-defined. For array and object
  assertions, establish non-nullness and bounds before reading values.

From `doc/openjml-tutorial/SpecifyingExceptions.html`:

- If the target spec intentionally allows exceptional behavior, negative cases
  must distinguish expected exceptional paths from genuine spec violations.
  Otherwise prefer ordinary precondition-violation and wrong-assertion tests.

## Recommended Layout

For a target `input/Foo.java`, use an eval workspace:

```text
output/eval_<timestamp>_foo/
  harness/FooPositiveHarness.java
  harness/FooNegativeHarness.java
  logs/test_reasoning.md
  logs/issues.md
  logs/metrics.md
  logs/final_result.md
```

Keep positive and negative harnesses separate so the positive proof can pass
cleanly while negative cases are expected to fail.

## Final Judgment

Eval must write `logs/final_result.md` and `logs/metrics.md`.

`Final Result: Success` is allowed only when all conditions hold:

- exactly 10 positive cases are present;
- exactly 10 negative cases are present;
- anti-cheating scan passes for implementation and both harnesses;
- positive harness passes OpenJML;
- negative harness fails OpenJML for documented spec-related reasons.

If any case is missing, any scan is skipped, or either OpenJML command is not
run, the final line must be:

```text
Final Result: Fail
```

## Anti-Cheating

The harness is not allowed to use:

- `assume`
- `axiom`
- `skipesc`
- `nowarn`
- unreachable-path tricks
- impossible helper preconditions

Run `scripts/check_jml_cheating.py` on both implementation and harness files.
