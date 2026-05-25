# Verify Issues

## Empty workspace fingerprint placeholders

- Phenomenon: early workspace inspection showed `logs/workspace_fingerprint.json` still had empty retrieval fields:

```json
"semantic_description": "",
"keywords": {}
```

- Trigger: the workspace had been initialized but the verify pass had not filled task-specific retrieval metadata.
- Localization: `output/verify_20260422_061035_array_move_zeroes_to_end/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled `semantic_description` with the in-place stable nonzero compaction behavior and used only controlled vocabulary keys/values: `two_pointers`, `selection`, `while_loop`, `array`, `in_place_update`, `loop_invariant`, `heap_reasoning`, `range_bound`, `int_range`, and `empty_loop_possible`.
- Result: the fingerprint now has non-empty semantic metadata. After final verification, `verification_status` was updated to include `goal_check_passed` and `proof_check_passed`.

## Missing loop invariants for the two-phase in-place array update

- Phenomenon: the active annotated file initially matched the input and had no loop invariant before either `while`:

```c
while (i < n) {
    if (a[i] != 0) {
        a[write] = a[i];
        write++;
    }
    i++;
}

while (write < n) {
    a[write] = 0;
    write++;
}
```

Without invariants, `symexec` would not know that the first loop has copied exactly the nonzero prefix of `sublist(0, i, l)` into the array prefix, nor that the second loop preserves that prefix while filling zeros.
- Trigger: the function mutates the input array in place and changes different array regions in two phases.
- Localization: `annotated/verify_20260422_061035_array_move_zeroes_to_end.c`.
- Fix action: before editing the annotated file, wrote the invariant reasoning in `logs/annotation_reasoning.md`; then added a first-loop invariant with ghost list `lc`:

```c
write == Zlength(array_move_zeroes_to_end_nonzero(sublist(0, i, l))) &&
(forall (k: Z),
  (0 <= k && k < write) =>
  lc[k] == array_move_zeroes_to_end_nonzero(sublist(0, i, l))[k]) &&
(forall (k: Z),
  (i <= k && k < n@pre) =>
  lc[k] == l[k]) &&
IntArray::full(a, n@pre, lc)
```

and a second-loop invariant preserving the final nonzero prefix while tracking the zero-filled range:

```c
(forall (k: Z),
  (0 <= k && k < Zlength(array_move_zeroes_to_end_nonzero(l))) =>
  lc[k] == array_move_zeroes_to_end_nonzero(l)[k]) &&
(forall (k: Z),
  (Zlength(array_move_zeroes_to_end_nonzero(l)) <= k && k < write) =>
  lc[k] == 0) &&
IntArray::full(a, n@pre, lc)
```

- Result: with these invariants and bridges, symbolic execution generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## Helper functions from the input `.v` needed explicit C annotation declarations

- Phenomenon: the loop invariants need the helper functions `array_move_zeroes_to_end_nonzero` and `array_move_zeroes_to_end_zeros`, but the input C only exposed:

```c
/*@ Extern Coq (array_move_zeroes_to_end_spec : list Z -> list Z) */
/*@ Import Coq Require Import array_move_zeroes_to_end */
```

- Trigger: the C annotation parser requires `Extern Coq` declarations for Coq symbols referenced directly in annotations, even when they are defined in the imported task `.v`.
- Localization: top of `annotated/verify_20260422_061035_array_move_zeroes_to_end.c`.
- Fix action: added:

```c
/*@ Extern Coq (array_move_zeroes_to_end_nonzero : list Z -> list Z) */
/*@ Extern Coq (array_move_zeroes_to_end_zeros : list Z -> list Z) */
```

without changing the function `Require` / `Ensure` contract.
- Result: `symexec` parsed the helper names and completed VC generation.

## Zero-fill assignment needed explicit `IntArray` cell bridges

- Phenomenon: the second loop writes a single array cell while the invariant owns the whole array as `IntArray::full(a, n@pre, lc)`:

```c
while (write < n) {
    a[write] = 0;
    write++;
}
```

The assignment executor needs the target cell exposed.
- Trigger: `IntArray::full` is too abstract for a direct element assignment at `a[write]`.
- Localization: the statement `a[write] = 0` in `annotated/verify_20260422_061035_array_move_zeroes_to_end.c`.
- Fix action: inserted a pre-assignment bridge:

```c
IntArray::missing_i(a, write, 0, n@pre, lc) *
data_at(a + (write * sizeof(int)), int, lc[write])
```

and a post-assignment bridge that re-closes the heap with existential `lc1`, preserving the nonzero prefix and extending the zero-filled range to `write + 1`.
- Result: `logs/qcp_run.log` records `Successfully finished symbolic execution` for the latest annotated file.

## Initial manual `symexec` wrapper wrote the log marker outside the workspace

- Phenomenon: the first manual launch command exited before invoking `symexec`:

```text
/bin/bash: line 1: logs/qcp_run.log: No such file or directory
```

- Trigger: the command ran from `QualifiedCProgramming` but wrote the initial `date` marker to relative `logs/qcp_run.log`.
- Localization: shell command setup for `logs/qcp_run.log`, before the real `symexec` command.
- Fix action: reran with all log and generated-output paths rooted at `output/verify_20260422_061035_array_move_zeroes_to_end`.
- Result: the corrected command completed and `logs/qcp_run.log` contains:

```text
Successfully finished symbolic execution
symexec_end 2026-04-22 06:13:18 +0800
```

## Manual proof required list and `replace_Znth` helper lemmas

- Phenomenon: after successful `symexec`, `coq/generated/array_move_zeroes_to_end_proof_manual.v` contained seven generated `Admitted.` placeholders:

```coq
proof_of_array_move_zeroes_to_end_entail_wit_1
proof_of_array_move_zeroes_to_end_entail_wit_2_1
proof_of_array_move_zeroes_to_end_entail_wit_2_2
proof_of_array_move_zeroes_to_end_entail_wit_3
proof_of_array_move_zeroes_to_end_return_wit_1
proof_of_array_move_zeroes_to_end_which_implies_wit_1
proof_of_array_move_zeroes_to_end_which_implies_wit_2
```

- Trigger: the preservation and return witnesses require pure list facts about extending `sublist 0 i l` by one element, the nonzero/zero helper functions, and the heap list produced by `replace_Znth`.
- Localization: `output/verify_20260422_061035_array_move_zeroes_to_end/coq/generated/array_move_zeroes_to_end_proof_manual.v`.
- Fix action: added local helper lemmas for `replace_nth` length/index behavior, `replace_Znth` length/index behavior, nonzero-prefix snoc behavior, spec length, and the fact that `array_move_zeroes_to_end_zeros` contains only zero values. The main witnesses then use `pre_process`, `Exists`, `entailer!`, `sublist_split`, `sublist_single`, `app_Znth1`, `app_Znth2`, and `lia`.
- Result: `array_move_zeroes_to_end_proof_manual.v` compiles and no longer contains `Admitted.` or top-level `Axiom`.

## Proof script iteration errors during compile

- Phenomenon: the first proof compile attempt after patching the manual file failed with:

```text
line 48, characters 33-35:
Error: Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as'
```

The offending tactic was:

```coq
induction (sublist 0 i l) as [|x xs IH]; simpl.
```

- Trigger: this Coq parser rejected induction directly over that expression with the supplied `as` pattern.
- Fix action: replaced the inline inductions with named helper lemmas `amz_nonzero_snoc_nonzero` and `amz_nonzero_snoc_zero`, then used those helpers inside the branch witnesses.
- Result: the next compile advanced past this syntax error.

- Phenomenon: the next compile failed because the attempted lemma names were unavailable:

```text
Error: The variable Znth_replace_Znth_diff was not found in the current environment.
```

- Trigger: the current imports do not expose those `replace_Znth` rewrite names.
- Fix action: added local lemmas `amz_Znth_replace_Znth_same`, `amz_Znth_replace_Znth_other`, and `amz_replace_Znth_length` derived from `replace_nth`.
- Result: the proof advanced, then a mechanical replacement had accidentally renamed the helper declaration to `amz_amz_Znth_replace_Znth_same`. Renaming it back to `amz_Znth_replace_Znth_same` fixed the remaining proof compile issue.

## Compile command replay and cleanup

- Phenomenon: the first compile command used `-R . SimpleC.SL` from `QualifiedCProgramming/SeparationLogic`, which remapped load paths incorrectly and produced:

```text
The file .../SeparationLogic/Mem.vo contains library
SimpleC.SL.Mem and not library SimpleC.SL.SeparationLogic.Mem.
```

It also kept running after errors because the command block did not use `set -e`.
- Trigger: the stable project mapping comes from `_CoqProject` and requires `-R SeparationLogic SimpleC.SL` when running from `QualifiedCProgramming/SeparationLogic`.
- Fix action: reran with `set -euo pipefail` and the documented `_CoqProject` base mappings plus the workspace mappings:

```bash
EXTRA=(
  -Q "$ORIG" ""
  -R "$GEN" "$LP"
)
```

- Result: final replay compiled `original/array_move_zeroes_to_end.v`, `array_move_zeroes_to_end_goal.v`, `array_move_zeroes_to_end_proof_auto.v`, `array_move_zeroes_to_end_proof_manual.v`, and `array_move_zeroes_to_end_goal_check.v`. After success, all non-`.v` files under `coq/` were deleted, and `find coq -type f ! -name '*.v'` returned no files.
