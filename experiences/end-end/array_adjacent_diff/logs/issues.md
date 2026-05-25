# Verify Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: yes

## Issue 1: workspace fingerprint had empty retrieval fields

- Phenomenon: `logs/workspace_fingerprint.json` was initialized with `"semantic_description": ""` and `"keywords": {}`.
- Trigger: the verify workflow requires these fields to be filled early, and the `keywords` values must come only from the controlled vocabulary in `doc/retrieval/INDEX.md`.
- Localization: `output/verify_20260422_015904_array_adjacent_diff/logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, then filled the fingerprint with a semantic summary of the adjacent-difference loop and controlled keywords:
  - `control_flow: for_loop`
  - `data_shape: [array, pointer]`
  - `proof_pattern: [loop_invariant, range_bound, heap_reasoning]`
  - `numeric_properties: [overflow_guard, int_range]`
  - `edge_case_behavior: empty_loop_possible`
- Result: the fingerprint is non-empty and uses only the retrieval-index controlled vocabulary.

## Issue 2: loop initially had no invariant

- Phenomenon: the active annotated C file initially had a bare loop:

```c
for (i = 0; i + 1 < n; ++i) {
    out[i] = a[i + 1] - a[i];
}
```

- Trigger: `symexec` needs a loop-head assertion that describes the processed output prefix, the untouched output suffix, and the unchanged input array.
- Localization: `annotated/verify_20260422_015904_array_adjacent_diff.c`.
- Fix: before editing the annotated C, recorded the invariant reasoning in `logs/annotation_reasoning.md`, then added:

```c
/*@ Inv exists l1,
      0 <= i && i <= n@pre - 1 &&
      a == a@pre &&
      out == out@pre &&
      n == n@pre &&
      n@pre == Zlength(la) &&
      n@pre - 1 == Zlength(lo) &&
      Zlength(l1) == i &&
      (forall (k: Z), (0 <= k && k < i) => l1[k] == la[k + 1] - la[k]) &&
      IntArray::full(a, n@pre, la) *
      IntArray::full(out, n@pre - 1, app(l1, sublist(i, n@pre - 1, lo)))
*/
```

- Result: the invariant supplies the exact final witness prefix. The loop step extends `l1` by one adjacent difference, and loop exit plus `i + 1 >= n` yields `i == n - 1`.

## Issue 3: `symexec` had to be rerun after annotation changes

- Phenomenon: the workspace had no fresh Coq artifacts for the newly added invariant.
- Trigger: the workflow requires clearing generated files and rerunning `symexec` after any `Inv` / `Assert` / `which implies` change.
- Localization: `logs/qcp_run.log`.
- Fix: deleted stale generated files and ran:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --input-file=annotated/verify_20260422_015904_array_adjacent_diff.c \
  --goal-file=output/verify_20260422_015904_array_adjacent_diff/coq/generated/array_adjacent_diff_goal.v \
  --proof-auto-file=output/verify_20260422_015904_array_adjacent_diff/coq/generated/array_adjacent_diff_proof_auto.v \
  --proof-manual-file=output/verify_20260422_015904_array_adjacent_diff/coq/generated/array_adjacent_diff_proof_manual.v \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_015904_array_adjacent_diff \
  --no-exec-info
```

- Result: `logs/qcp_run.log` records `Successfully finished symbolic execution`, `symexec_status=0`, and fresh `array_adjacent_diff_goal.v`, `array_adjacent_diff_proof_auto.v`, `array_adjacent_diff_proof_manual.v`, and `array_adjacent_diff_goal_check.v` were generated.

## Issue 4: manual proof obligations remained after symbolic execution

- Phenomenon: the generated `array_adjacent_diff_proof_manual.v` contained four admitted lemmas:
  - `proof_of_array_adjacent_diff_safety_wit_4`
  - `proof_of_array_adjacent_diff_entail_wit_1`
  - `proof_of_array_adjacent_diff_entail_wit_2`
  - `proof_of_array_adjacent_diff_return_wit_1`
- Trigger: the remaining goals were pure range and list-normalization witnesses, not missing annotation state.
- Localization: `output/verify_20260422_015904_array_adjacent_diff/coq/generated/array_adjacent_diff_proof_manual.v`.
- Fix: recorded proof reasoning in `logs/proof_reasoning.md`, then added a local helper:

```coq
Lemma adjacent_diff_step_list :
  forall (la lo l1 : list Z) (i n : Z),
    0 <= i ->
    i + 1 < n ->
    Zlength la = n ->
    Zlength lo = n - 1 ->
    Zlength l1 = i ->
    replace_Znth i (Znth (i + 1) la 0 - Znth i la 0)
      (app l1 (sublist i (n - 1) lo)) =
    app (l1 ++ (Znth (i + 1) la 0 - Znth i la 0) :: nil)
        (sublist (i + 1) (n - 1) lo).
```

- Fix details:
  - `safety_wit_4`: used the contract overflow hypothesis at index `i`; the loop guard gives `i + 1 < n_pre`, and `lia` derives `i < n_pre - 1`.
  - `entail_wit_1`: instantiated the initial processed prefix with `nil` and normalized `sublist 0 (n_pre - 1) lo`.
  - `entail_wit_2`: used `adjacent_diff_step_list` and split the new prefix property into the old prefix case and the newly written index.
  - `return_wit_1`: derived `i_3 = n_pre - 1`, rewrote `sublist_nil`, and used `l1` as the existential result list.
- Result: `array_adjacent_diff_proof_manual.v` compiles and contains no `Admitted.` or newly added `Axiom`.

## Issue 5: first compile replay used the wrong working directory

- Phenomenon: the first compile attempt emitted load-path failures such as:

```text
Error: Cannot find a physical path bound to logical path
int_auto with prefix AUXLib.
```

- Trigger: the command was run from `QualifiedCProgramming`, but this checkout's `_CoqProject` paths such as `auxlibs`, `examples`, and `unifysl` are relative to `QualifiedCProgramming/SeparationLogic`.
- Localization: overwritten compile evidence was replaced by the successful final `logs/compile.log`; the failure was caused by the compile command working directory.
- Fix: reran the complete compile chain from `QualifiedCProgramming/SeparationLogic` with the base `_CoqProject` `-R` paths and workspace-specific `-R "$GEN" SimpleC.EE.CAV.verify_20260422_015904_array_adjacent_diff`.
- Result: the final `logs/compile.log` records:

```text
compiled array_adjacent_diff_goal.v
compiled array_adjacent_diff_proof_auto.v
compiled array_adjacent_diff_proof_manual.v
compiled array_adjacent_diff_goal_check.v
```

## Final outcome

- `symexec` succeeded on the latest annotated C file.
- `array_adjacent_diff_goal.v`, `array_adjacent_diff_proof_auto.v`, `array_adjacent_diff_proof_manual.v`, and `array_adjacent_diff_goal_check.v` all compiled successfully.
- `array_adjacent_diff_proof_manual.v` contains no `Admitted.` and no newly added `Axiom`.
- Non-`.v` files under `coq/` were deleted after the final compile replay.
