---
name: java-openjml-verify
description: Verify Java/JML source with Codex-assisted OpenJML iteration.
---

Use this workflow for the Java/OpenJML verify stage. This skill consumes an
existing Java implementation/spec and repairs only the verified working copy
until OpenJML ESC passes without cheating.

## Pipeline Position

This is the final proof stage of the Java/OpenJML workflow.

Input:

- `input/<name>.java`

Output:

- `output/verify_<timestamp>_<name>/original/<name>.java`
- `output/verify_<timestamp>_<name>/verified/<name>.java`
- `output/verify_<timestamp>_<name>/logs/workspace_fingerprint.json`
- `output/verify_<timestamp>_<name>/logs/annotation_reasoning.md`
- `output/verify_<timestamp>_<name>/logs/issues.md`
- `output/verify_<timestamp>_<name>/logs/metrics.md`
- runtime OpenJML and scanner logs under the same workspace logs directory.

Command shape:

```bash
python3 scripts/run_codex_verify.py input/<name>.java --class-name <ClassName>
```

On success, the runner exports a CAV-style compact example snapshot under
`experiences/end-end/<name>/` with only:

- `original/<name>.java`
- `verified/<name>.java`
- `logs/workspace_fingerprint.json`
- `logs/annotation_reasoning.md`
- `logs/issues.md`

Do not export runtime-only logs such as Codex stdout/stderr, OpenJML stdout,
OpenJML stderr, scanner stdout/stderr, or metrics into `experiences/end-end`.

## Inputs

- Original input Java file.
- Verified working Java file.
- Workspace path.
- Class name.

## Required References

Read these local references before making verification edits:

- `/home/yangfp/CAV-JAVA/experiences/general/INV.md`
- `/home/yangfp/CAV-JAVA/experiences/general/ASSERTION.md`
- `/home/yangfp/CAV-JAVA/experiences/general/LEMMA.md`
- `/home/yangfp/CAV-JAVA/experiences/general/ANTI_CHEATING.md`
- `/home/yangfp/CAV-JAVA/experiences/general/OPENJML.md`
- `/home/yangfp/CAV-JAVA/experiences/INDEX.md`

Search completed end-to-end examples before making verification edits:

- `/home/yangfp/CAV-JAVA/experiences/end-end`

Use prior examples as concrete evidence for successful Java/JML patterns,
workspace layout, fingerprint format, and issue-log style. Prefer examples with
similar control flow, data type, or OpenJML diagnostic. Record the selected
example path in `logs/annotation_reasoning.md` when it informs a change.

Useful commands:

```bash
find /home/yangfp/CAV-JAVA/experiences/end-end -maxdepth 4 -type f | sort
rg -n "requires|ensures|assignable|loop_invariant|assert|pure|Final Result|workspace_fingerprint" /home/yangfp/CAV-JAVA/experiences/end-end
```

Before OpenJML success can be reported, update
`logs/workspace_fingerprint.json` so:

- `semantic_description` is non-empty;
- `keywords` is non-empty;
- every `keywords` key and value comes from
  `/home/yangfp/CAV-JAVA/experiences/INDEX.md`;
- no free-form synonym is invented.

Use these official OpenJML resources as the local reference corpus:

- `/home/yangfp/CAV-JAVA/doc`
- `/home/yangfp/CAV-JAVA/doc/openjml-tutorial`
- `/home/yangfp/CAV-JAVA/doc/openjml-documentation`
- `/home/yangfp/CAV-JAVA/doc/openjml-specs`
- `/home/yangfp/CAV-JAVA/examples`
- `/home/yangfp/CAV-JAVA/examples/openjml-tutorial`
- `/home/yangfp/CAV-JAVA/examples/openjml-demos`
- `/home/yangfp/CAV-JAVA/examples/openjml-userguide`

Do not bulk-read all of `doc` or `examples`. Search them selectively. Useful
queries include:

```bash
rg -n "loop_invariant|decreases|assignable|assert|pure|model|ghost|spec_public" /home/yangfp/CAV-JAVA/doc /home/yangfp/CAV-JAVA/examples
rg -n "ArithmeticOperationRange|InvariantExit|Precondition|PossiblyNull|LoopInvariant" /home/yangfp/CAV-JAVA/doc /home/yangfp/CAV-JAVA/examples
```

## Boundaries

- Modify only the verified working Java file and files under the current
  workspace logs.
- Never modify the original input Java file.
- Preserve baseline `requires`, `ensures`, and `assignable` clauses. Do not
  weaken, delete, or make them vacuous.
- Keep the implementation semantically aligned with the input. If the input
  implementation/spec is fundamentally wrong, record the issue and fail the
  verify stage instead of silently changing the problem.

## Verification Aids

Allowed aids:

- `loop_invariant` clauses.
- `decreases` clauses.
- JML `assert` statements used as local bridge facts.
- Verified `pure` helper methods with executable bodies.
- `spec_public`, model fields, or ghost state only when needed and documented.

Forbidden aids:

- `assume`.
- `axiom`.
- `Admitted`.
- `skipesc`.
- broad `nowarn`.
- `native` helpers.
- reflection.
- impossible preconditions.
- unreachable-path tricks.

## Iteration Procedure

1. Read the original Java and the verified working Java.
2. Run anti-cheating scan before edits:

   ```bash
   scripts/check_jml_cheating.py --baseline <original> <verified>
   ```

3. Run OpenJML:

   ```bash
   scripts/run_openjml_verify.sh <verified>
   ```

4. Classify the first concrete OpenJML failure:
   - arithmetic overflow or range proof;
   - nullness or array bounds;
   - missing `assignable`;
   - loop invariant initialization;
   - loop invariant preservation;
   - loop exit not strong enough;
   - visibility/spec-public issue;
   - helper lemma/pure method issue;
   - anti-cheating violation.
5. Search `/home/yangfp/CAV-JAVA/experiences/end-end` first for a similar
   completed task, then search `/home/yangfp/CAV-JAVA/doc` and
   `/home/yangfp/CAV-JAVA/examples`
   for the closest OpenJML pattern before editing.
6. Append to `logs/annotation_reasoning.md` before changing annotations. Include:
   - command that failed;
   - exact OpenJML message;
   - file and line;
   - local code/spec snippet;
   - selected reference path from `doc` or `examples`, when used;
   - planned invariant/assertion/lemma change;
   - why the change follows from the program state.
7. Edit only the verified Java file.
8. Rerun anti-cheating scan and OpenJML.
9. Repeat until both pass or the blocker is determined to require contract or
   implementation changes outside verify scope.

## Invariant Rules

- Every loop needs enough facts for initialization, preservation, and exit.
- Track loop bounds explicitly.
- Track modified and unmodified array regions separately.
- Track accumulators as prefix or segment facts.
- Add `decreases` when OpenJML cannot prove termination.
- Do not use an assertion to compensate for a missing loop invariant if the
  fact must hold across iterations.

## Assertion Rules

- Use JML `assert` only for facts derivable at that program point.
- Prefer assertions for branch facts, arithmetic bounds, and loop-exit bridges.
- Do not assert the postcondition directly unless the current invariants and
  branch facts already imply it.
- Do not introduce `assume`; assertions must be checked by OpenJML.

## Lemma Rules

- Helper lemmas must be Java/JML artifacts OpenJML can check.
- Prefer small `pure` methods with executable bodies and contracts.
- Do not use `native`, empty bodies, impossible preconditions, or unchecked
  model methods.
- If a helper lemma is added, OpenJML must verify it in the same run as the
  target class.

## Logs

Maintain these logs in the workspace:

- `logs/annotation_reasoning.md`
- `logs/issues.md`
- `logs/metrics.md`

`logs/issues.md` must record every representative blocker with:

- stage;
- command;
- failing file and line;
- OpenJML message;
- diagnosis;
- edit made;
- result after rerun.

`logs/metrics.md` must end with one of:

```text
Final Result: Success
Final Result: Fail
```

## Completion

Success requires all of the following:

- `scripts/check_jml_cheating.py --baseline <original> <verified>` exits 0.
- `scripts/run_openjml_verify.sh <verified>` exits 0.
- No forbidden proof aid remains in the verified Java file.
- Baseline contract clauses are preserved.
- Logs are complete.
- `logs/workspace_fingerprint.json` has a non-empty `semantic_description` and
  controlled `keywords` from `/home/yangfp/CAV-JAVA/experiences/INDEX.md`.
- Reusable lessons are recorded in `/home/yangfp/CAV-JAVA/experiences/general`
  when applicable. Typical targets are `INV.md`, `ASSERTION.md`, `LEMMA.md`,
  `OPENJML.md`, and `ANTI_CHEATING.md`.
- If no reusable lesson was found, `logs/annotation_reasoning.md`,
  `logs/issues.md`, or `logs/metrics.md` says so explicitly.

If any condition is missing, write `Final Result: Fail`.
