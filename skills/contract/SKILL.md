---
name: java-openjml-contract
description: Produce Java source with JML contracts from raw task text.
---

Use this workflow for the Java/OpenJML contract stage.

## Pipeline Position

This is stage 1 of the Java/OpenJML workflow.

Input:

- `raw/<name>.md`

Output:

- `input/<name>.java`
- `output/contract_<timestamp>_<name>/logs/reasoning.md`
- `output/contract_<timestamp>_<name>/logs/issues.md`
- `output/contract_<timestamp>_<name>/logs/metrics.md`

Command shape:

```bash
python3 scripts/run_codex_contract.py raw/<name>.md --function-name <method_or_class>
```

The next normal stage is verify. If batch eval is enabled, the order is
`contract -> eval -> verify`; otherwise it is `contract -> verify`.

## Read First

- `experiences/general/CONTRACT.md`
- `experiences/general/ANTI_CHEATING.md`

## Search Prior Examples

Before writing the Java file, search completed examples under
`/home/yangfp/CAV-JAVA/experiences/end-end`.

Use the existing examples as concrete patterns for class layout, JML clause
style, anti-cheating-safe specifications, and workspace log expectations. Do
not copy an unrelated example blindly; cite the closest example path in
`logs/reasoning.md` when one influenced the contract.

Useful commands:

```bash
find /home/yangfp/CAV-JAVA/experiences/end-end -maxdepth 3 -type f | sort
rg -n "requires|ensures|assignable|loop_invariant|assert|pure" /home/yangfp/CAV-JAVA/experiences/end-end
```

## Inputs

- Raw markdown path.
- Target function or class name.
- Output Java path.
- Workspace path.

## Rules

- Write `logs/reasoning.md` before creating or changing the output Java file.
- Generate a single Java file with Java implementation and JML contract.
- Include `requires`, `ensures`, and `assignable`.
- Do not add loop invariants, assertions, assumptions, axioms, suppressions, or
  unchecked helpers in the contract stage.
- If a helper is necessary, make it pure, executable, and specified.
- If the run reveals a reusable contract-generation lesson, update the relevant
  file under `/home/yangfp/CAV-JAVA/experiences/general` before finishing.
  Typical targets are `CONTRACT.md` and `ANTI_CHEATING.md`.
- If no reusable lesson was found, record that explicitly in
  `logs/reasoning.md` or `logs/metrics.md`.

## Completion

- `input/<name>.java` exists.
- `logs/reasoning.md`, `logs/issues.md`, and `logs/metrics.md` exist.
- `scripts/check_jml_cheating.py input/<name>.java` passes.
- Reusable general experience is updated under `experiences/general/` when
  applicable, or the logs explain why no update was needed.
- `logs/metrics.md` ends with `Final Result: Success` only when the generated
  Java file exists and the anti-cheating scan passes.
