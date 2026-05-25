# Verify Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: no

## Issue 1: workspace fingerprint had empty retrieval fields

- Phenomenon: `logs/workspace_fingerprint.json` initially contained `"semantic_description": ""` and `"keywords": {}`.
- Trigger: the verify workflow requires filling these fields early, and every `keywords` key and value must come from `doc/retrieval/INDEX.md`.
- Localization: `output/verify_20260422_021145_array_all_positive/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled a semantic description for the read-only all-positive array scan and used controlled vocabulary entries:
  - `algorithm_family: search`
  - `control_flow: [for_loop, if]`
  - `data_shape: [array, pointer]`
  - `semantic_intent: preserve_input`
  - `proof_pattern: [loop_invariant, case_split, heap_reasoning]`
  - `numeric_properties: [nonnegative_input, int_range]`
  - `edge_case_behavior: empty_loop_possible`
- Result: the fingerprint now has a non-empty semantic summary and controlled keywords. After final `goal_check` success it was also updated with `verification_status: goal_check_passed`.

## Issue 2: loop initially had no invariant

- Phenomenon: the active annotated C initially had a bare read-only scan loop:

```c
int i;

for (i = 0; i < n; ++i) {
    if (a[i] <= 0) {
        return 0;
    }
}

return 1;
```

- Trigger: the postcondition for `return 1` requires proving every element in `l[0..n)` is positive, while the early `return 0` path requires an existential index whose value is non-positive. Without a loop invariant, symbolic execution has no persistent fact describing the already inspected prefix.
- Localization: `annotated/verify_20260422_021145_array_all_positive.c`.
- Fix action: before editing the annotated C, recorded the invariant reasoning in `logs/annotation_reasoning.md`, then added this loop-head invariant:

```c
/*@ Inv
      0 <= i && i <= n@pre &&
      n == n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      (forall (j: Z), (0 <= j && j < i) => l[j] > 0) &&
      IntArray::full(a, n@pre, l)
*/
for (i = 0; i < n; ++i) {
    if (a[i] <= 0) {
        return 0;
    }
}
```

- Why this fixes the VC shape: at the loop head, `i` is the next index to inspect, so `0 <= j < i` is exactly the processed prefix. The false branch of `a[i] <= 0` extends that prefix with `l[i] > 0`, while the true branch can use current `i` as the existential witness for the `return 0` postcondition. The array is only read, so `IntArray::full(a, n@pre, l)` is preserved.
- Result: the invariant was sufficient; no extra `Assert`, `which implies`, or loop-exit assertion was needed.

## Issue 3: first `symexec` command used positional input and generated malformed empty goals

- Phenomenon: the first `symexec` run printed:

```text
Start to symbolic execution on program : (null)
Start to print Coq files for the program (null)
Successfully finished symbolic execution
```

It produced `array_all_positive_goal.v`, but that file had only imports and an empty `Module Type VC_Correct`; it was also missing `Import naive_C_Rules` and strategy imports before `Local Open Scope sac`.

- Trigger: the annotated C path was passed as a positional argument instead of with `--input-file=...`. The tool returned status `0`, but did not actually symbolically execute `array_all_positive`.
- Localization: `logs/qcp_run.log` from the first run and the malformed `coq/generated/array_all_positive_goal.v` observed immediately afterward.
- Fix action: cleared generated files again and reran `symexec` with the explicit input option:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --input-file=annotated/verify_20260422_021145_array_all_positive.c \
  --goal-file=output/verify_20260422_021145_array_all_positive/coq/generated/array_all_positive_goal.v \
  --proof-auto-file=output/verify_20260422_021145_array_all_positive/coq/generated/array_all_positive_proof_auto.v \
  --proof-manual-file=output/verify_20260422_021145_array_all_positive/coq/generated/array_all_positive_proof_manual.v \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_021145_array_all_positive \
  --no-exec-info
```

- Result: the corrected run printed `Symbolic Execution into function array_all_positive`, ended with `Successfully finished symbolic execution`, and generated full VC files with the expected strategy imports.

## Issue 4: no manual proof obligations remained

- Phenomenon: the generated manual proof file contained only imports and scope openings, with no theorem body to complete:

```coq
From SimpleC.EE.CAV.verify_20260422_021145_array_all_positive Require Import array_all_positive_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.
```

- Trigger: the prefix-positive invariant gave the automatic proof enough information for this read-only scan. The remaining generated obligations are in `proof_auto.v`; `proof_manual.v` has no manual theorem or admitted proof to repair.
- Localization: `output/verify_20260422_021145_array_all_positive/coq/generated/array_all_positive_proof_manual.v`.
- Fix action: skipped `logs/proof_reasoning.md` and did not edit `proof_manual.v`, because there was no failed manual theorem or remaining subgoal to analyze. Verified with:

```bash
rg -n "Admitted\.|^\s*Axiom\b" coq/generated/array_all_positive_proof_manual.v
```

- Result: the search produced no matches. `proof_manual.v` contains no `Admitted.` and no newly added `Axiom`.

## Issue 5: full Coq compile and cleanup were required after `symexec`

- Phenomenon: `symexec` success alone is insufficient for Verify success; `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` must compile in order, and non-`.v` Coq intermediates must be removed.
- Trigger: the workflow requires the complete compile template from `experiences/general/COMPILE.md`.
- Localization: `logs/compile.log` and `coq/generated/`.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` with the base `_CoqProject` load paths plus:

```bash
-Q "$ORIG" "" -R "$GEN" SimpleC.EE.CAV.verify_20260422_021145_array_all_positive
```

Then compiled:

```text
array_all_positive_goal.v
array_all_positive_proof_auto.v
array_all_positive_proof_manual.v
array_all_positive_goal_check.v
```

- Result: `logs/compile.log` records all four files compiled successfully through `array_all_positive_goal_check.v`. After cleanup, `coq/` contains only:

```text
coq/generated/array_all_positive_goal.v
coq/generated/array_all_positive_goal_check.v
coq/generated/array_all_positive_proof_auto.v
coq/generated/array_all_positive_proof_manual.v
```
