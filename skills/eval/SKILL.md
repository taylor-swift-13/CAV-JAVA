---
name: java-openjml-eval
description: Generate positive and negative OpenJML harness tests for an existing Java implementation/spec.
---

Use this workflow independently from the contract and verify stages. The goal is
to evaluate whether concrete examples satisfy the existing JML spec, not to
change the implementation or weaken the spec.

## Read First

- `experiences/general/EVAL.md`
- `experiences/general/ANTI_CHEATING.md`
- `experiences/general/OPENJML.md`

## Inputs

- Implementation/spec Java file.
- Target class and method.
- Workspace path.
- Output harness directory.

## Output

- Exactly 10 positive cases and 10 negative cases.
- Prefer two harness files:
  - `<ClassName>PositiveHarness.java`
  - `<ClassName>NegativeHarness.java`
- `logs/test_reasoning.md`
- `logs/issues.md`
- `logs/metrics.md`
- `logs/final_result.md`
- OpenJML stdout/stderr logs for the positive and negative harness checks.

## Harness Requirements

- Do not modify the implementation/spec file.
- Generate positive cases that satisfy the target method's preconditions and
  prove expected postcondition facts with JML `assert`.
- Generate negative cases that are intentionally invalid with respect to the
  spec. Each negative case must target one clear failure mode:
  - precondition violation, or
  - expected-output assertion that contradicts the spec.
- Negative cases must be checked in a separate harness or mode where OpenJML is
  expected to fail. A negative case passing is an eval failure unless the case
  is explicitly documented as an accepted vacuity check.
- Each case must be deterministic and concrete.
- Prefer small primitive/array inputs that OpenJML can reason about directly.

## Anti-Cheating Rules

- No `assume`, `axiom`, `Admitted`, `skipesc`, broad `nowarn`, `native`,
  reflection, or impossible path tricks.
- Do not weaken or delete target specs.
- Do not encode negative tests by making methods unreachable.
- Do not claim a negative case is successful unless OpenJML reports the expected
  precondition/assertion failure.

## Proof Commands

Run anti-cheating scan on the implementation and harnesses:

```bash
scripts/check_jml_cheating.py <impl.java>
scripts/check_jml_cheating.py <positive-harness.java>
scripts/check_jml_cheating.py <negative-harness.java>
```

Run positive cases:

```bash
scripts/run_openjml_verify.sh <impl.java> <positive-harness.java>
```

Run negative cases:

```bash
scripts/run_openjml_verify.sh <impl.java> <negative-harness.java>
```

The positive command must exit 0. The negative command must exit non-zero with
the expected failure locations recorded in `logs/issues.md`.

## Completion

- Exactly 10 positive and 10 negative cases are present.
- Positive harness passes OpenJML.
- Negative harness fails OpenJML for documented spec-related reasons.
- Logs record which cases passed or failed and why.
- `logs/final_result.md` records the final judgment.
- If eval did not fully generate, scan, and run all required cases, write
  `Final Result: Fail`, not `Final Result: Success`.
