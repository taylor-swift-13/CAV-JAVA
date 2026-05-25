# Verification Issues

## Fingerprint Completion

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: the workspace was initialized before task-specific semantic classification.
- Localization: `logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, then filled a concrete description for in-place left rotation and used only controlled vocabulary values: `simulation`, `for_loop`, `array`, `pointer`, `in_place_update`, `loop_invariant`, `range_bound`, `heap_reasoning`, `int_range`, `overflow_guard`. After final verification, added controlled `verification_status` values.
- Result: the fingerprint is non-empty and uses only controlled vocabulary.

## Missing Loop Invariant

- Phenomenon: the active annotated C initially matched the input and had no invariant for:

```c
for (i = 0; i < n - 1; ++i) {
    a[i] = a[i + 1];
}
a[n - 1] = first;
```

- Trigger: the loop mutates the array in place, so the verifier needs a loop-head summary of the shifted prefix and untouched suffix.
- Localization: `annotated/verify_20260422_215602_rotate_left_by_one.c`.
- Fix: appended detailed reasoning to `logs/annotation_reasoning.md`; added an existential-prefix invariant:

```c
/*@ Inv exists l1,
      0 <= i && i <= n@pre - 1 &&
      n == n@pre &&
      a == a@pre &&
      Zlength(l) == n@pre &&
      first == l[0] &&
      Zlength(l1) == i &&
      (forall (k: Z), (0 <= k && k < i) => l1[k] == l[k + 1]) &&
      IntArray::full(a, n@pre, app(l1, sublist(i, n@pre, l)))
*/
```

- Result: `symexec` completed successfully and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## Avoided Brittle Final-Store Bridge

- Phenomenon: an older archived failed workspace for this exact function showed that adding a post-loop single-hole bridge before `a[n - 1] = first` can make `symexec` fail with `cannot write null value to memory`.
- Trigger: the bridge opened `IntArray::full` around the final slot but the frontend lost the concrete writable cell at `(a + (n - 1) * sizeof(int))`.
- Localization: archived log `./archieve/output_backup_20260422_011624/verify_20260418_191920_rotate_left_by_one/logs/qcp_run.log`, and the current avoided point immediately before the final assignment.
- Fix: used the archived successful annotation shape from `CAV/archieve/examples_backup_20260422_011624/rotate_left_by_one/annotated/rotate_left_by_one.c`: keep the loop state as a full array with an existential shifted prefix and do not add the brittle post-loop `Assert`.
- Result: the current `symexec` run reached `Successfully finished symbolic execution`.

## Symexec Option Form

- Phenomenon: the first manual `symexec` attempt failed before parsing the C file:

```text
goal file not specified
Start to symbolic execution on program : (null)
```

- Trigger: this `symexec` binary expects file-path long options in `--flag=value` form; the failed command used `--goal-file <path>`.
- Localization: `logs/qcp_run.log` from the failed run before rerun.
- Fix: reran with:

```text
--goal-file=...
--proof-auto-file=...
--proof-manual-file=...
--goal-check-file=...
--input-file=...
```

- Result: the rerun succeeded, and `logs/qcp_run.log` ends with `symexec_status: 0`.

## Manual Proof Obligations

- Phenomenon: generated `coq/generated/rotate_left_by_one_proof_manual.v` contained three admitted manual obligations:

```coq
proof_of_rotate_left_by_one_entail_wit_1
proof_of_rotate_left_by_one_entail_wit_2
proof_of_rotate_left_by_one_return_wit_1
```

- Trigger: the remaining VCs were pure list normalization obligations for loop initialization, one shift step, and final rotated list construction.
- Localization: `coq/generated/rotate_left_by_one_goal.v` definitions `rotate_left_by_one_entail_wit_1`, `rotate_left_by_one_entail_wit_2`, and `rotate_left_by_one_return_wit_1`.
- Fix: appended proof reasoning to `logs/proof_reasoning.md`; added helper lemmas `rotate_left_by_one_step_list` and `rotate_left_by_one_final_list`; replaced all three manual `Admitted.` bodies with proofs using `pre_process`, `Exists`, `entailer!`, list rewrites, and `lia`.
- Result: `coq/generated/rotate_left_by_one_proof_manual.v` compiles and contains no `Admitted.` or top-level `Axiom`.

## Compile Replay And Cleanup

- Phenomenon: final verification required compiling all generated files under the workspace-specific logical path and then cleaning Coq intermediates.
- Trigger: the verify workflow only succeeds after `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` compile, and the workspace `coq/` tree contains only `.v` files.
- Localization: compile logs under `logs/compile_goal.log`, `logs/compile_proof_auto.log`, `logs/compile_proof_manual.log`, and `logs/compile_goal_check.log`.
- Fix: compiled from `QualifiedCProgramming/SeparationLogic` using the documented `BASE` load path and `-R "$GEN" SimpleC.EE.CAV.verify_20260422_215602_rotate_left_by_one`; then deleted all non-`.v` files under `coq/`.
- Result: all four compile logs are empty, indicating success; `find coq -type f ! -name '*.v'` returns no files.
