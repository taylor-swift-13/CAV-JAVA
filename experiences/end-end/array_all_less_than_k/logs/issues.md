# Verify Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: no

## Issue 1: workspace fingerprint had empty retrieval fields

- Phenomenon: `logs/workspace_fingerprint.json` initially contained `"semantic_description": ""` and `"keywords": {}`.
- Trigger: the verify workflow requires these fields to be filled early, and every `keywords` key and value must come from the controlled vocabulary in `doc/retrieval/INDEX.md`.
- Localization: `output/verify_20260422_020645_array_all_less_than_k/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled the semantic description for the read-only array scan and used controlled vocabulary entries:
  - `algorithm_family: search`
  - `control_flow: [for_loop, if]`
  - `data_shape: [array, pointer]`
  - `semantic_intent: preserve_input`
  - `proof_pattern: [loop_invariant, case_split, range_bound, heap_reasoning]`
  - `numeric_properties: [nonnegative_input, int_range]`
  - `edge_case_behavior: empty_loop_possible`
- Result: the fingerprint now has a non-empty semantic summary and controlled keywords. After final `goal_check` success it was also updated with `verification_status: goal_check_passed`.

## Issue 2: loop initially had no invariant

- Phenomenon: the active annotated C initially had a bare scan loop:

```c
int i;

for (i = 0; i < n; ++i) {
    if (a[i] >= k) {
        return 0;
    }
}

return 1;
```

- Trigger: the postcondition for `return 1` requires a universal property over all array indexes, while the early `return 0` path requires an existential violating index. Without a loop invariant, symbolic execution has no persistent fact saying that all previously inspected elements are less than `k`.
- Localization: `annotated/verify_20260422_020645_array_all_less_than_k.c`.
- Fix action: before editing the annotated C, recorded the invariant reasoning in `logs/annotation_reasoning.md`, then added this loop-head invariant:

```c
/*@ Inv
      0 <= i && i <= n@pre &&
      n == n@pre &&
      a == a@pre &&
      k == k@pre &&
      n@pre == Zlength(l) &&
      (forall (j: Z), (0 <= j && j < i) => l[j] < k@pre) &&
      IntArray::full(a, n@pre, l)
*/
for (i = 0; i < n; ++i) {
    if (a[i] >= k) {
        return 0;
    }
}
```

- Why this fixes the VC shape: `i` is the next index to inspect, so `0 <= j < i` is exactly the processed prefix. The false branch of `a[i] >= k` extends that prefix by one element, while the true branch can use current `i` as the existential witness for the `return 0` postcondition. The array is read-only, so `IntArray::full(a, n@pre, l)` stays unchanged across all paths.
- Result: the invariant was sufficient; no extra loop-exit assertion or branch assertion was needed.

## Issue 3: `symexec` had to be rerun after annotation changes

- Phenomenon: the workspace had no Coq artifacts generated from the updated invariant.
- Trigger: the workflow requires clearing generated Coq files and rerunning `symexec` after any `Inv`, `Assert`, `which implies`, or loop-exit assertion change.
- Localization: `logs/qcp_run.log`.
- Fix action: cleared stale generated targets and ran:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --input-file=annotated/verify_20260422_020645_array_all_less_than_k.c \
  --goal-file=output/verify_20260422_020645_array_all_less_than_k/coq/generated/array_all_less_than_k_goal.v \
  --proof-auto-file=output/verify_20260422_020645_array_all_less_than_k/coq/generated/array_all_less_than_k_proof_auto.v \
  --proof-manual-file=output/verify_20260422_020645_array_all_less_than_k/coq/generated/array_all_less_than_k_proof_manual.v \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_020645_array_all_less_than_k \
  --no-exec-info
```

- Result: `symexec` exited with status `0`. `logs/qcp_run.log` contains:

```text
Successfully finished symbolic execution
symexec_end=2026-04-22T02:08:24+08:00
symexec_status=0
```

Fresh `array_all_less_than_k_goal.v`, `array_all_less_than_k_proof_auto.v`, `array_all_less_than_k_proof_manual.v`, and `array_all_less_than_k_goal_check.v` were generated.

## Issue 4: no manual proof obligations remained

- Phenomenon: the generated manual proof file contained only imports and scope openings, with no theorem body to finish:

```coq
From SimpleC.EE.CAV.verify_20260422_020645_array_all_less_than_k Require Import array_all_less_than_k_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.
```

- Trigger: the prefix invariant gave `symexec` enough information for this read-only scan, so remaining obligations were discharged automatically in `proof_auto.v`.
- Localization: `output/verify_20260422_020645_array_all_less_than_k/coq/generated/array_all_less_than_k_proof_manual.v`.
- Fix action: skipped `logs/proof_reasoning.md` and did not edit `proof_manual.v`, because there was no failed manual theorem or remaining subgoal to analyze. Verified with:

```bash
rg -n "Admitted\.|^\s*Axiom\b" output/verify_20260422_020645_array_all_less_than_k/coq/generated/array_all_less_than_k_proof_manual.v
```

- Result: the search produced no matches. The file contains no `Admitted.` and no newly added `Axiom`.

## Issue 5: full Coq compile and cleanup were required after `symexec`

- Phenomenon: `symexec` success alone is insufficient; Verify success requires compiling `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`, then deleting non-`.v` intermediates.
- Trigger: the workflow requires `goal_check.v` to compile under the current workspace logical path and leaves `.vo`, `.glob`, `.vos`, `.vok`, and `.aux` files after compilation.
- Localization: `output/verify_20260422_020645_array_all_less_than_k/logs/compile.log`.
- Fix action: ran the full fail-fast compile chain from `QualifiedCProgramming/SeparationLogic` with the base `_CoqProject` load paths and workspace-specific path `-R "$GEN" SimpleC.EE.CAV.verify_20260422_020645_array_all_less_than_k`.
- Result: `logs/compile.log` records:

```text
compiled array_all_less_than_k_goal.v
compiled array_all_less_than_k_proof_auto.v
compiled array_all_less_than_k_proof_manual.v
compiled array_all_less_than_k_goal_check.v
```

After compilation, all non-`.v` files under `coq/` were deleted. The remaining generated files are exactly:

```text
array_all_less_than_k_goal.v
array_all_less_than_k_goal_check.v
array_all_less_than_k_proof_auto.v
array_all_less_than_k_proof_manual.v
```

## Final outcome

- `symexec` succeeded on the latest annotated C file.
- `array_all_less_than_k_goal.v`, `array_all_less_than_k_proof_auto.v`, `array_all_less_than_k_proof_manual.v`, and `array_all_less_than_k_goal_check.v` all compiled successfully.
- `array_all_less_than_k_proof_manual.v` contains no `Admitted.` and no newly added `Axiom`.
- Non-`.v` files under `coq/` were deleted after final compilation.
