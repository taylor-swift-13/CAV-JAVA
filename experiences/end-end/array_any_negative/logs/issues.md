# Verification Issues

## Issue 1: initial fingerprint had empty semantic metadata

- Phenomenon: `logs/workspace_fingerprint.json` was still in its bootstrap state with an empty `semantic_description` and `{}` keywords:

```json
"semantic_description": "",
"keywords": {}
```

- Trigger: the verify workflow requires the fingerprint to be filled early, and the keywords must use only the controlled vocabulary from `doc/retrieval/INDEX.md`.
- Localization: `output/verify_20260422_022938_array_any_negative/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then described the function as a read-only array search that returns `1` on an element `l[i] < 0`, returns `0` only when all elements are nonnegative, preserves `IntArray::full`, and may skip the loop when `n == 0`. Keywords were restricted to controlled values including `search`, `for_loop`, `if`, `array`, `pointer`, `preserve_input`, `loop_invariant`, `case_split`, `heap_reasoning`, `nonnegative_input`, `int_range`, and `empty_loop_possible`.
- Result: the fingerprint is non-empty and, after final `goal_check` success, includes `"verification_status": "goal_check_passed"`.

## Issue 2: the unannotated scan loop did not preserve the no-negative prefix fact

- Phenomenon: the active annotated file initially had the same bare loop as the input:

```c
for (i = 0; i < n; ++i) {
    if (a[i] < 0) {
        return 1;
    }
}

return 0;
```

- Trigger: the normal `return 0` branch must prove:

```c
forall (i: Z), (0 <= i && i < n) => l[i] >= 0
```

Without a loop invariant, symbolic execution has no stable fact saying that every already scanned index is nonnegative. The early `return 1` branch also needs unchanged `n`, `a`, and `IntArray::full(a, n, l)` facts to satisfy the postcondition.
- Localization: `annotated/verify_20260422_022938_array_any_negative.c`, immediately before `for (i = 0; i < n; ++i)`.
- Fix action: before editing the annotated C file, wrote `logs/annotation_reasoning.md` with initialization, preservation, early-return, and loop-exit reasoning. Then added this loop-head invariant:

```c
/*@ Inv
      0 <= i && i <= n@pre &&
      n == n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      (forall (j: Z), (0 <= j && j < i) => l[j] >= 0) &&
      IntArray::full(a, n@pre, l)
*/
```

- Result: the invariant is initialized at `i == 0` by a vacuous prefix property, preserved by the false branch of `a[i] < 0` which gives `l[i] >= 0`, supports the existential witness on early `return 1`, and proves the full universal property at loop exit when `i >= n` and `i <= n@pre`.

## Issue 3: symbolic execution had to be rerun after adding the invariant

- Phenomenon: changing an `Inv` invalidates any old generated Coq files, even though this workspace initially had none.
- Trigger: the verify workflow requires clearing generated files and rerunning `symexec` after any annotation change.
- Localization: generated targets under `output/verify_20260422_022938_array_any_negative/coq/generated/` and `logs/qcp_run.log`.
- Fix action: removed the task-specific generated files and ran:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --input-file=annotated/verify_20260422_022938_array_any_negative.c \
  --goal-file=output/verify_20260422_022938_array_any_negative/coq/generated/array_any_negative_goal.v \
  --proof-auto-file=output/verify_20260422_022938_array_any_negative/coq/generated/array_any_negative_proof_auto.v \
  --proof-manual-file=output/verify_20260422_022938_array_any_negative/coq/generated/array_any_negative_proof_manual.v
```

- Result: `logs/qcp_run.log` ended with:

```text
Successfully finished symbolic execution
symexec_end=2026-04-22T02:31:19+08:00
symexec_elapsed=0
symexec_status=0
```

Fresh `array_any_negative_goal.v`, `array_any_negative_proof_auto.v`, `array_any_negative_proof_manual.v`, and `array_any_negative_goal_check.v` were generated.

## Issue 4: no manual proof obligations remained, but this still needed explicit checking

- Phenomenon: `coq/generated/array_any_negative_proof_manual.v` contained only imports and scope openings, with no `Lemma`, `Theorem`, `Admitted.`, or local `Axiom`.
- Trigger: the prefix invariant gave `symexec` and the auto proof enough information for this read-only scan; no manual witness script was needed.
- Localization: `output/verify_20260422_022938_array_any_negative/coq/generated/array_any_negative_proof_manual.v`.
- Fix action: searched for unfinished or forbidden declarations with:

```bash
rg -n "Admitted\.|^\s*Axiom\b|Theorem|Lemma|Instance|Obligation" coq/generated/array_any_negative_proof_manual.v
```

- Result: no matches appeared. Because there was no concrete theorem to prove, `logs/proof_reasoning.md` was intentionally not created.

## Issue 5: full Coq compilation and cleanup were required after successful symbolic execution

- Phenomenon: `symexec` success alone is not enough for Verify success. The generated modules must compile in order, `goal_check.v` must pass, and Coq intermediate files must be removed afterward.
- Trigger: compiling generated Coq files creates `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` artifacts under `coq/generated/`.
- Localization: `output/verify_20260422_022938_array_any_negative/coq/generated/` and `logs/compile.log`.
- Fix action: from `QualifiedCProgramming/SeparationLogic`, compiled with the documented base load path plus:

```bash
-Q "$ORIG" ""
-R "$GEN" SimpleC.EE.CAV.verify_20260422_022938_array_any_negative
```

The compile log records:

```text
compiled array_any_negative_goal.v
compiled array_any_negative_proof_auto.v
compiled array_any_negative_proof_manual.v
compiled array_any_negative_goal_check.v
```

Then all non-`.v` files under `coq/` were deleted.
- Result: after cleanup, the generated directory contains only:

```text
coq/generated/array_any_negative_goal.v
coq/generated/array_any_negative_goal_check.v
coq/generated/array_any_negative_proof_auto.v
coq/generated/array_any_negative_proof_manual.v
```

The final verification status is success.
