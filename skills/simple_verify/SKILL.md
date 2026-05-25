---
name: simple_verify
description: Minimal verify skill. Consume an existing contract and run annotation, symbolic execution, proof, and compilation.
---

Simple Verify consumes a contract that has already been prepared by the contract stage. It does not design or modify function preconditions/postconditions.

This skill intentionally omits document reading, retrieval, fingerprinting, and experience accumulation. It only defines the verification flow.

## Inputs

- `input/<name>.c`
- `input/<name>.v`, if present
- Target function name
- Workspace `output/verify_<timestamp>_<name>/`
- Active annotated C copy `annotated/verify_<timestamp>_<name>.c`

## Outputs

- Updated annotated C copy
- Generated verification conditions and proof files
- Completed manual proof file, if residual goals exist
- Final compilation result
- `logs/metrics.md`

## Hard Rules

- Treat `input/<name>.c` and `input/<name>.v` as immutable contract input.
- Do not rewrite `Require`, `Ensure`, or task-specific Rocq definitions from the contract stage.
- Do not modify the target C implementation to make verification easier.
- Add only verification annotations in the annotated C copy: `Inv`, `Assert`, `which implies`, bridge assertions, and loop-exit assertions.
- Rerun symbolic execution after every annotation change.
- Do not leave `Admitted.` in proof files.
- Do not introduce new `Axiom`.
- A task succeeds only when the generated proof compiles end to end.

## Flow

1. Inspect `input/<name>.c` and `input/<name>.v`, if present.
2. Create or update the active annotated C copy.
3. Add loop invariants, assertions, bridge facts, and loop-exit assertions as needed.
4. Run symbolic execution.
5. If symbolic execution fails, revise the annotations and rerun symbolic execution.
6. If symbolic execution succeeds, inspect the generated proof obligations.
7. If no manual goals remain, proceed to final compilation.
8. If manual goals remain, complete them in the manual proof file.
9. If proof compilation fails:
   - If the proof script is wrong, repair the proof and compile again.
   - If the annotations are insufficient or wrong, return to annotation and regenerate verification conditions.
   - If the contract is wrong, stop and report contract failure.
10. Compile the generated proof.
11. Scan for cheats and hacks.
12. Clean non-source intermediate files.
13. Write `logs/metrics.md`.
14. Report success or failure.

## Metrics

Write `logs/metrics.md` at the end of the run. Keep it minimal but real:

- Target function
- Workspace
- Verify start time
- Verify end time
- Total verify wall-clock seconds
- Optional sub-step timings such as symbolic execution or compile replay
- Final status: `Success` or `Fail`
- Failure category, if failed: annotation, symbolic execution, proof, contract, cheat scan, timeout, or other
- Token/time/tool cost, if available

## Completion Criteria

- Symbolic execution succeeds on the latest annotated C copy.
- All residual proof obligations are completed.
- Generated proof compiles end to end.
- No `Admitted.` remains.
- No new `Axiom` is introduced.
- Intermediate non-source build artifacts are cleaned.
